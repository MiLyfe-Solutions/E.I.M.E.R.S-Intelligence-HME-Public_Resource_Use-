import V185TrunkScan23Chunk0157

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_934075 : List Nat := [1, 1, 1, 1, 1, 2, 6, 2, 3, 5]
def baseStart_934075 : Nat := 118140960795 + 934075 * 2 ^ 59
def prefixEnd_934075 : Nat := 4983230072969 + 3 ^ 40 * 934075 * 2
def baseEnd_934075 : Nat := 159876480782846053655591

theorem tailTrace_934075 : CollatzResearch.WordTrace tailWord_934075 prefixEnd_934075 159876480782846053655591 := by
  unfold tailWord_934075
  simp only [CollatzResearch.WordTrace]
  refine ⟨34068514091013277154491679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22712342727342184769661119 34068514091013277154491679)
  ·
    refine ⟨51102771136519915731737519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34068514091013277154491679 51102771136519915731737519)
    ·
      refine ⟨76654156704779873597606279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51102771136519915731737519 76654156704779873597606279)
      ·
        refine ⟨114981235057169810396409419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76654156704779873597606279 114981235057169810396409419)
        ·
          refine ⟨172471852585754715594614129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114981235057169810396409419 172471852585754715594614129)
          ·
            refine ⟨129353889439316036695960597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172471852585754715594614129 129353889439316036695960597)
            ·
              refine ⟨6063463567467939220123153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 129353889439316036695960597 6063463567467939220123153)
              ·
                refine ⟨4547597675600954415092365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6063463567467939220123153 4547597675600954415092365)
                ·
                  refine ⟨1705349128350357905659637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4547597675600954415092365 1705349128350357905659637)
                  ·
                    refine ⟨159876480782846053655591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1705349128350357905659637 159876480782846053655591)
                    ·
                      rfl

theorem cell23_934075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 2, 3, 5].length) (baseStart_934075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_934075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_934075 prefixEnd_934075 := by exact prefixLift 934075
  have htrace : WordTrace (prefixWord ++ tailWord_934075) baseStart_934075 baseEnd_934075 := by
    simpa [prefixWord, tailWord_934075, baseEnd_934075] using wordTrace_append hprefix tailTrace_934075
  have hstable : (prefixWord ++ tailWord_934075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934075).length < 2 ^ (prefixWord ++ tailWord_934075).sum := by decide
  have hdescent : baseEnd_934075 < baseStart_934075 := by decide
  rcases family_descends (prefixWord ++ tailWord_934075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934105 : List Nat := [1, 2, 1, 2, 3, 1, 3, 1, 3, 6]
def baseStart_934105 : Nat := 118140960795 + 934105 * 2 ^ 59
def prefixEnd_934105 : Nat := 4983230072969 + 3 ^ 40 * 934105 * 2
def baseEnd_934105 : Nat := 159881615589391014530545

theorem tailTrace_934105 : CollatzResearch.WordTrace tailWord_934105 prefixEnd_934105 159881615589391014530545 := by
  unfold tailWord_934105
  simp only [CollatzResearch.WordTrace]
  refine ⟨34069608280904592278083769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22713072187269728185389179 34069608280904592278083769)
  ·
    refine ⟨25552206210678444208562827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34069608280904592278083769 25552206210678444208562827)
    ·
      refine ⟨38328309316017666312844241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25552206210678444208562827 38328309316017666312844241)
      ·
        refine ⟨28746231987013249734633181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38328309316017666312844241 28746231987013249734633181)
        ·
          refine ⟨10779836995129968650487443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28746231987013249734633181 10779836995129968650487443)
          ·
            refine ⟨16169755492694952975731165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10779836995129968650487443 16169755492694952975731165)
            ·
              refine ⟨6063658309760607365899187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16169755492694952975731165 6063658309760607365899187)
              ·
                refine ⟨9095487464640911048848781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6063658309760607365899187 9095487464640911048848781)
                ·
                  refine ⟨3410807799240341643318293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9095487464640911048848781 3410807799240341643318293)
                  ·
                    refine ⟨159881615589391014530545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3410807799240341643318293 159881615589391014530545)
                    ·
                      rfl

theorem cell23_934105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 1, 3, 6].length) (baseStart_934105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_934105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_934105 prefixEnd_934105 := by exact prefixLift 934105
  have htrace : WordTrace (prefixWord ++ tailWord_934105) baseStart_934105 baseEnd_934105 := by
    simpa [prefixWord, tailWord_934105, baseEnd_934105] using wordTrace_append hprefix tailTrace_934105
  have hstable : (prefixWord ++ tailWord_934105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934105).length < 2 ^ (prefixWord ++ tailWord_934105).sum := by decide
  have hdescent : baseEnd_934105 < baseStart_934105 := by decide
  rcases family_descends (prefixWord ++ tailWord_934105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934173 : List Nat := [1, 4, 2, 3, 2, 2, 1, 2, 2, 4]
def baseStart_934173 : Nat := 118140960795 + 934173 * 2 ^ 59
def prefixEnd_934173 : Nat := 4983230072969 + 3 ^ 40 * 934173 * 2
def baseEnd_934173 : Nat := 159893254484226259180441

theorem tailTrace_934173 : CollatzResearch.WordTrace tailWord_934173 prefixEnd_934173 159893254484226259180441 := by
  unfold tailWord_934173
  simp only [CollatzResearch.WordTrace]
  refine ⟨34072088444658239891559173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22714725629772159927706115 34072088444658239891559173)
  ·
    refine ⟨6388516583373419979667345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34072088444658239891559173 6388516583373419979667345)
    ·
      refine ⟨4791387437530064984750509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6388516583373419979667345 4791387437530064984750509)
      ·
        refine ⟨1796770289073774369281441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4791387437530064984750509 1796770289073774369281441)
        ·
          refine ⟨1347577716805330776961081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1796770289073774369281441 1347577716805330776961081)
          ·
            refine ⟨1010683287603998082720811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1347577716805330776961081 1010683287603998082720811)
            ·
              refine ⟨1516024931405997124081217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1010683287603998082720811 1516024931405997124081217)
              ·
                refine ⟨1137018698554497843060913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1516024931405997124081217 1137018698554497843060913)
                ·
                  refine ⟨852764023915873382295685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1137018698554497843060913 852764023915873382295685)
                  ·
                    refine ⟨159893254484226259180441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 852764023915873382295685 159893254484226259180441)
                    ·
                      rfl

theorem cell23_934173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 1, 2, 2, 4].length) (baseStart_934173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_934173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_934173 prefixEnd_934173 := by exact prefixLift 934173
  have htrace : WordTrace (prefixWord ++ tailWord_934173) baseStart_934173 baseEnd_934173 := by
    simpa [prefixWord, tailWord_934173, baseEnd_934173] using wordTrace_append hprefix tailTrace_934173
  have hstable : (prefixWord ++ tailWord_934173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934173).length < 2 ^ (prefixWord ++ tailWord_934173).sum := by decide
  have hdescent : baseEnd_934173 < baseStart_934173 := by decide
  rcases family_descends (prefixWord ++ tailWord_934173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934179 : List Nat := [1, 1, 1, 4, 2, 2, 3, 1, 4, 1, 3]
def baseStart_934179 : Nat := 118140960795 + 934179 * 2 ^ 59
def prefixEnd_934179 : Nat := 4983230072969 + 3 ^ 40 * 934179 * 2
def baseEnd_934179 : Nat := 479682844336605754066295

theorem tailTrace_934179 : CollatzResearch.WordTrace tailWord_934179 prefixEnd_934179 479682844336605754066295 := by
  unfold tailWord_934179
  simp only [CollatzResearch.WordTrace]
  refine ⟨34072307282636502916277591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22714871521757668610851727 34072307282636502916277591)
  ·
    refine ⟨51108460923954754374416387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34072307282636502916277591 51108460923954754374416387)
    ·
      refine ⟨76662691385932131561624581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51108460923954754374416387 76662691385932131561624581)
      ·
        refine ⟨14374254634862274667804609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76662691385932131561624581 14374254634862274667804609)
        ·
          refine ⟨10780690976146706000853457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14374254634862274667804609 10780690976146706000853457)
          ·
            refine ⟨8085518232110029500640093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10780690976146706000853457 8085518232110029500640093)
            ·
              refine ⟨3032069337041261062740035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8085518232110029500640093 3032069337041261062740035)
              ·
                refine ⟨4548104005561891594110053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3032069337041261062740035 4548104005561891594110053)
                ·
                  refine ⟨852769501042854673895635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4548104005561891594110053 852769501042854673895635)
                  ·
                    refine ⟨1279154251564282010843453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 852769501042854673895635 1279154251564282010843453)
                    ·
                      refine ⟨479682844336605754066295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1279154251564282010843453 479682844336605754066295)
                      ·
                        rfl

theorem cell23_934179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 1, 4, 1, 3].length) (baseStart_934179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_934179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_934179 prefixEnd_934179 := by exact prefixLift 934179
  have htrace : WordTrace (prefixWord ++ tailWord_934179) baseStart_934179 baseEnd_934179 := by
    simpa [prefixWord, tailWord_934179, baseEnd_934179] using wordTrace_append hprefix tailTrace_934179
  have hstable : (prefixWord ++ tailWord_934179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934179).length < 2 ^ (prefixWord ++ tailWord_934179).sum := by decide
  have hdescent : baseEnd_934179 < baseStart_934179 := by decide
  rcases family_descends (prefixWord ++ tailWord_934179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934183 : List Nat := [1, 1, 8, 1, 1, 1, 1, 2, 1, 1, 5]
def baseStart_934183 : Nat := 118140960795 + 934183 * 2 ^ 59
def prefixEnd_934183 : Nat := 4983230072969 + 3 ^ 40 * 934183 * 2
def baseEnd_934183 : Nat := 479684898259223738416277

theorem tailTrace_934183 : CollatzResearch.WordTrace tailWord_934183 prefixEnd_934183 479684898259223738416277 := by
  unfold tailWord_934183
  simp only [CollatzResearch.WordTrace]
  refine ⟨34072453174622011599423203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22714968783081341066282135 34072453174622011599423203)
  ·
    refine ⟨51108679761933017399134805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34072453174622011599423203 51108679761933017399134805)
    ·
      refine ⟨598929840960152547646111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 51108679761933017399134805 598929840960152547646111)
      ·
        refine ⟨898394761440228821469167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 598929840960152547646111 898394761440228821469167)
        ·
          refine ⟨1347592142160343232203751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 898394761440228821469167 1347592142160343232203751)
          ·
            refine ⟨2021388213240514848305627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1347592142160343232203751 2021388213240514848305627)
            ·
              refine ⟨3032082319860772272458441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2021388213240514848305627 3032082319860772272458441)
              ·
                refine ⟨2274061739895579204343831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3032082319860772272458441 2274061739895579204343831)
                ·
                  refine ⟨3411092609843368806515747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2274061739895579204343831 3411092609843368806515747)
                  ·
                    refine ⟨5116638914765053209773621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3411092609843368806515747 5116638914765053209773621)
                    ·
                      refine ⟨479684898259223738416277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5116638914765053209773621 479684898259223738416277)
                      ·
                        rfl

theorem cell23_934183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_934183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_934183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_934183 prefixEnd_934183 := by exact prefixLift 934183
  have htrace : WordTrace (prefixWord ++ tailWord_934183) baseStart_934183 baseEnd_934183 := by
    simpa [prefixWord, tailWord_934183, baseEnd_934183] using wordTrace_append hprefix tailTrace_934183
  have hstable : (prefixWord ++ tailWord_934183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934183).length < 2 ^ (prefixWord ++ tailWord_934183).sum := by decide
  have hdescent : baseEnd_934183 < baseStart_934183 := by decide
  rcases family_descends (prefixWord ++ tailWord_934183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934190 : List Nat := [4, 1, 3, 3, 1, 1, 3, 1, 2, 4]
def baseStart_934190 : Nat := 118140960795 + 934190 * 2 ^ 59
def prefixEnd_934190 : Nat := 4983230072969 + 3 ^ 40 * 934190 * 2
def baseEnd_934190 : Nat := 159896164207935070342915

theorem tailTrace_934190 : CollatzResearch.WordTrace tailWord_934190 prefixEnd_934190 159896164207935070342915 := by
  unfold tailWord_934190
  simp only [CollatzResearch.WordTrace]
  refine ⟨4259088560699581474366003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22715138990397767863285349 4259088560699581474366003)
  ·
    refine ⟨6388632841049372211549005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4259088560699581474366003 6388632841049372211549005)
    ·
      refine ⟨2395737315393514579330877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6388632841049372211549005 2395737315393514579330877)
      ·
        refine ⟨898401493272567967249079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2395737315393514579330877 898401493272567967249079)
        ·
          refine ⟨1347602239908851950873619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 898401493272567967249079 1347602239908851950873619)
          ·
            refine ⟨2021403359863277926310429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1347602239908851950873619 2021403359863277926310429)
            ·
              refine ⟨758026259948729222366411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2021403359863277926310429 758026259948729222366411)
              ·
                refine ⟨1137039389923093833549617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 758026259948729222366411 1137039389923093833549617)
                ·
                  refine ⟨852779542442320375162213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1137039389923093833549617 852779542442320375162213)
                  ·
                    refine ⟨159896164207935070342915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 852779542442320375162213 159896164207935070342915)
                    ·
                      rfl

theorem cell23_934190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 3, 1, 2, 4].length) (baseStart_934190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_934190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_934190 prefixEnd_934190 := by exact prefixLift 934190
  have htrace : WordTrace (prefixWord ++ tailWord_934190) baseStart_934190 baseEnd_934190 := by
    simpa [prefixWord, tailWord_934190, baseEnd_934190] using wordTrace_append hprefix tailTrace_934190
  have hstable : (prefixWord ++ tailWord_934190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934190).length < 2 ^ (prefixWord ++ tailWord_934190).sum := by decide
  have hdescent : baseEnd_934190 < baseStart_934190 := by decide
  rcases family_descends (prefixWord ++ tailWord_934190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934196 : List Nat := [2, 5, 1, 1, 1, 2, 3, 1, 1, 3, 3]
def baseStart_934196 : Nat := 118140960795 + 934196 * 2 ^ 59
def prefixEnd_934196 : Nat := 4983230072969 + 3 ^ 40 * 934196 * 2
def baseEnd_934196 : Nat := 479691573507732187553717

theorem tailTrace_934196 : CollatzResearch.WordTrace tailWord_934196 prefixEnd_934196 479691573507732187553717 := by
  unfold tailWord_934196
  simp only [CollatzResearch.WordTrace]
  refine ⟨17036463661787457409823221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22715284882383276546430961 17036463661787457409823221)
  ·
    refine ⟨1597168468292574132170927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17036463661787457409823221 1597168468292574132170927)
    ·
      refine ⟨2395752702438861198256391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1597168468292574132170927 2395752702438861198256391)
      ·
        refine ⟨3593629053658291797384587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2395752702438861198256391 3593629053658291797384587)
        ·
          refine ⟨5390443580487437696076881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3593629053658291797384587 5390443580487437696076881)
          ·
            refine ⟨4042832685365578272057661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5390443580487437696076881 4042832685365578272057661)
            ·
              refine ⟨1516062257012091852021623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4042832685365578272057661 1516062257012091852021623)
              ·
                refine ⟨2274093385518137778032435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1516062257012091852021623 2274093385518137778032435)
                ·
                  refine ⟨3411140078277206667048653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2274093385518137778032435 3411140078277206667048653)
                  ·
                    refine ⟨1279177529353952500143245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3411140078277206667048653 1279177529353952500143245)
                    ·
                      refine ⟨479691573507732187553717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1279177529353952500143245 479691573507732187553717)
                      ·
                        rfl

theorem cell23_934196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 3, 1, 1, 3, 3].length) (baseStart_934196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_934196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_934196 prefixEnd_934196 := by exact prefixLift 934196
  have htrace : WordTrace (prefixWord ++ tailWord_934196) baseStart_934196 baseEnd_934196 := by
    simpa [prefixWord, tailWord_934196, baseEnd_934196] using wordTrace_append hprefix tailTrace_934196
  have hstable : (prefixWord ++ tailWord_934196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934196).length < 2 ^ (prefixWord ++ tailWord_934196).sum := by decide
  have hdescent : baseEnd_934196 < baseStart_934196 := by decide
  rcases family_descends (prefixWord ++ tailWord_934196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934232 : List Nat := [2, 1, 2, 2, 1, 1, 2, 4, 2, 2, 4]
def baseStart_934232 : Nat := 118140960795 + 934232 * 2 ^ 59
def prefixEnd_934232 : Nat := 4983230072969 + 3 ^ 40 * 934232 * 2
def baseEnd_934232 : Nat := 479710058811294046703551

theorem tailTrace_934232 : CollatzResearch.WordTrace tailWord_934232 prefixEnd_934232 479710058811294046703551 := by
  unfold tailWord_934232
  simp only [CollatzResearch.WordTrace]
  refine ⟨17037120175722246483978475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22716160234296328645304633 17037120175722246483978475)
  ·
    refine ⟨25555680263583369725967713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17037120175722246483978475 25555680263583369725967713)
    ·
      refine ⟨19166760197687527294475785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25555680263583369725967713 19166760197687527294475785)
      ·
        refine ⟨14375070148265645470856839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19166760197687527294475785 14375070148265645470856839)
        ·
          refine ⟨21562605222398468206285259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14375070148265645470856839 21562605222398468206285259)
          ·
            refine ⟨32343907833597702309427889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21562605222398468206285259 32343907833597702309427889)
            ·
              refine ⟨24257930875198276732070917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32343907833597702309427889 24257930875198276732070917)
              ·
                refine ⟨4548362039099676887263297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24257930875198276732070917 4548362039099676887263297)
                ·
                  refine ⟨3411271529324757665447473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4548362039099676887263297 3411271529324757665447473)
                  ·
                    refine ⟨2558453646993568249085605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3411271529324757665447473 2558453646993568249085605)
                    ·
                      refine ⟨479710058811294046703551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2558453646993568249085605 479710058811294046703551)
                      ·
                        rfl

theorem cell23_934232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 4, 2, 2, 4].length) (baseStart_934232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_934232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_934232 prefixEnd_934232 := by exact prefixLift 934232
  have htrace : WordTrace (prefixWord ++ tailWord_934232) baseStart_934232 baseEnd_934232 := by
    simpa [prefixWord, tailWord_934232, baseEnd_934232] using wordTrace_append hprefix tailTrace_934232
  have hstable : (prefixWord ++ tailWord_934232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934232).length < 2 ^ (prefixWord ++ tailWord_934232).sum := by decide
  have hdescent : baseEnd_934232 < baseStart_934232 := by decide
  rcases family_descends (prefixWord ++ tailWord_934232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934253 : List Nat := [1, 5, 1, 1, 1, 2, 3, 3, 2, 2, 2]
def baseStart_934253 : Nat := 118140960795 + 934253 * 2 ^ 59
def prefixEnd_934253 : Nat := 4983230072969 + 3 ^ 40 * 934253 * 2
def baseEnd_934253 : Nat := 479720841905038464540955

theorem tailTrace_934253 : CollatzResearch.WordTrace tailWord_934253 prefixEnd_934253 479720841905038464540955 := by
  unfold tailWord_934253
  simp only [CollatzResearch.WordTrace]
  refine ⟨34075006284368413554471413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22716670856245609036314275 34075006284368413554471413)
  ·
    refine ⟨3194531839159538770731695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34075006284368413554471413 3194531839159538770731695)
    ·
      refine ⟨4791797758739308156097543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3194531839159538770731695 4791797758739308156097543)
      ·
        refine ⟨7187696638108962234146315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4791797758739308156097543 7187696638108962234146315)
        ·
          refine ⟨10781544957163443351219473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7187696638108962234146315 10781544957163443351219473)
          ·
            refine ⟨8086158717872582513414605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10781544957163443351219473 8086158717872582513414605)
            ·
              refine ⟨3032309519202218442530477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8086158717872582513414605 3032309519202218442530477)
              ·
                refine ⟨1137116069700831915948929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3032309519202218442530477 1137116069700831915948929)
                ·
                  refine ⟨852837052275623936961697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1137116069700831915948929 852837052275623936961697)
                  ·
                    refine ⟨639627789206717952721273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 852837052275623936961697 639627789206717952721273)
                    ·
                      refine ⟨479720841905038464540955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 639627789206717952721273 479720841905038464540955)
                      ·
                        rfl

theorem cell23_934253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 3, 2, 2, 2].length) (baseStart_934253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_934253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_934253 prefixEnd_934253 := by exact prefixLift 934253
  have htrace : WordTrace (prefixWord ++ tailWord_934253) baseStart_934253 baseEnd_934253 := by
    simpa [prefixWord, tailWord_934253, baseEnd_934253] using wordTrace_append hprefix tailTrace_934253
  have hstable : (prefixWord ++ tailWord_934253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934253).length < 2 ^ (prefixWord ++ tailWord_934253).sum := by decide
  have hdescent : baseEnd_934253 < baseStart_934253 := by decide
  rcases family_descends (prefixWord ++ tailWord_934253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934296 : List Nat := [2, 1, 2, 5, 1, 1, 1, 1, 2, 5, 2]
def baseStart_934296 : Nat := 118140960795 + 934296 * 2 ^ 59
def prefixEnd_934296 : Nat := 4983230072969 + 3 ^ 40 * 934296 * 2
def baseEnd_934296 : Nat := 479742921573181796303257

theorem tailTrace_934296 : CollatzResearch.WordTrace tailWord_934296 prefixEnd_934296 479742921573181796303257 := by
  unfold tailWord_934296
  simp only [CollatzResearch.WordTrace]
  refine ⟨17038287311606315949143371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22717716415475087932191161 17038287311606315949143371)
  ·
    refine ⟨25557430967409473923715057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17038287311606315949143371 25557430967409473923715057)
    ·
      refine ⟨19168073225557105442786293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25557430967409473923715057 19168073225557105442786293)
      ·
        refine ⟨1797006864895978635261215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19168073225557105442786293 1797006864895978635261215)
        ·
          refine ⟨2695510297343967952891823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1797006864895978635261215 2695510297343967952891823)
          ·
            refine ⟨4043265446015951929337735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2695510297343967952891823 4043265446015951929337735)
            ·
              refine ⟨6064898169023927894006603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4043265446015951929337735 6064898169023927894006603)
              ·
                refine ⟨9097347253535891841009905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6064898169023927894006603 9097347253535891841009905)
                ·
                  refine ⟨6823010440151918880757429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9097347253535891841009905 6823010440151918880757429)
                  ·
                    refine ⟨639657228764242395071009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6823010440151918880757429 639657228764242395071009)
                    ·
                      refine ⟨479742921573181796303257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 639657228764242395071009 479742921573181796303257)
                      ·
                        rfl

theorem cell23_934296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 1, 2, 5, 2].length) (baseStart_934296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_934296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_934296 prefixEnd_934296 := by exact prefixLift 934296
  have htrace : WordTrace (prefixWord ++ tailWord_934296) baseStart_934296 baseEnd_934296 := by
    simpa [prefixWord, tailWord_934296, baseEnd_934296] using wordTrace_append hprefix tailTrace_934296
  have hstable : (prefixWord ++ tailWord_934296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934296).length < 2 ^ (prefixWord ++ tailWord_934296).sum := by decide
  have hdescent : baseEnd_934296 < baseStart_934296 := by decide
  rcases family_descends (prefixWord ++ tailWord_934296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934419 : List Nat := [1, 1, 1, 2, 1, 5, 1, 4, 1, 1, 5]
def baseStart_934419 : Nat := 118140960795 + 934419 * 2 ^ 59
def prefixEnd_934419 : Nat := 4983230072969 + 3 ^ 40 * 934419 * 2
def baseEnd_934419 : Nat := 479806079693684815065191

theorem tailTrace_934419 : CollatzResearch.WordTrace tailWord_934419 prefixEnd_934419 479806079693684815065191 := by
  unfold tailWord_934419
  simp only [CollatzResearch.WordTrace]
  refine ⟨34081060801767023905014311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22720707201178015936676207 34081060801767023905014311)
  ·
    refine ⟨51121591202650535857521467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34081060801767023905014311 51121591202650535857521467)
    ·
      refine ⟨76682386803975803786282201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51121591202650535857521467 76682386803975803786282201)
      ·
        refine ⟨57511790102981852839711651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76682386803975803786282201 57511790102981852839711651)
        ·
          refine ⟨86267685154472779259567477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57511790102981852839711651 86267685154472779259567477)
          ·
            refine ⟨8087595483231823055584451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 86267685154472779259567477 8087595483231823055584451)
            ·
              refine ⟨12131393224847734583376677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8087595483231823055584451 12131393224847734583376677)
              ·
                refine ⟨2274636229658950234383127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12131393224847734583376677 2274636229658950234383127)
                ·
                  refine ⟨3411954344488425351574691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2274636229658950234383127 3411954344488425351574691)
                  ·
                    refine ⟨5117931516732638027362037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3411954344488425351574691 5117931516732638027362037)
                    ·
                      refine ⟨479806079693684815065191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5117931516732638027362037 479806079693684815065191)
                      ·
                        rfl

theorem cell23_934419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 4, 1, 1, 5].length) (baseStart_934419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_934419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_934419 prefixEnd_934419 := by exact prefixLift 934419
  have htrace : WordTrace (prefixWord ++ tailWord_934419) baseStart_934419 baseEnd_934419 := by
    simpa [prefixWord, tailWord_934419, baseEnd_934419] using wordTrace_append hprefix tailTrace_934419
  have hstable : (prefixWord ++ tailWord_934419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934419).length < 2 ^ (prefixWord ++ tailWord_934419).sum := by decide
  have hdescent : baseEnd_934419 < baseStart_934419 := by decide
  rcases family_descends (prefixWord ++ tailWord_934419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934433 : List Nat := [1, 2, 3, 2, 2, 1, 2, 1, 5, 2, 2]
def baseStart_934433 : Nat := 118140960795 + 934433 * 2 ^ 59
def prefixEnd_934433 : Nat := 4983230072969 + 3 ^ 40 * 934433 * 2
def baseEnd_934433 : Nat := 479813268422847760290127

theorem tailTrace_934433 : CollatzResearch.WordTrace tailWord_934433 prefixEnd_934433 479813268422847760290127 := by
  unfold tailWord_934433
  simp only [CollatzResearch.WordTrace]
  refine ⟨34081571423716304296023953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22721047615810869530682635 34081571423716304296023953)
  ·
    refine ⟨25561178567787228222017965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34081571423716304296023953 25561178567787228222017965)
    ·
      refine ⟨9585441962920210583256737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25561178567787228222017965 9585441962920210583256737)
      ·
        refine ⟨7189081472190157937442553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9585441962920210583256737 7189081472190157937442553)
        ·
          refine ⟨5391811104142618453081915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7189081472190157937442553 5391811104142618453081915)
          ·
            refine ⟨8087716656213927679622873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5391811104142618453081915 8087716656213927679622873)
            ·
              refine ⟨6065787492160445759717155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8087716656213927679622873 6065787492160445759717155)
              ·
                refine ⟨9098681238240668639575733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6065787492160445759717155 9098681238240668639575733)
                ·
                  refine ⟨853001366085062684960225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9098681238240668639575733 853001366085062684960225)
                  ·
                    refine ⟨639751024563797013720169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 853001366085062684960225 639751024563797013720169)
                    ·
                      refine ⟨479813268422847760290127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 639751024563797013720169 479813268422847760290127)
                      ·
                        rfl

theorem cell23_934433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 1, 5, 2, 2].length) (baseStart_934433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_934433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_934433 prefixEnd_934433 := by exact prefixLift 934433
  have htrace : WordTrace (prefixWord ++ tailWord_934433) baseStart_934433 baseEnd_934433 := by
    simpa [prefixWord, tailWord_934433, baseEnd_934433] using wordTrace_append hprefix tailTrace_934433
  have hstable : (prefixWord ++ tailWord_934433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934433).length < 2 ^ (prefixWord ++ tailWord_934433).sum := by decide
  have hdescent : baseEnd_934433 < baseStart_934433 := by decide
  rcases family_descends (prefixWord ++ tailWord_934433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934469 : List Nat := [1, 3, 1, 1, 1, 5, 1, 1, 2, 7]
def baseStart_934469 : Nat := 118140960795 + 934469 * 2 ^ 59
def prefixEnd_934469 : Nat := 4983230072969 + 3 ^ 40 * 934469 * 2
def baseEnd_934469 : Nat := 159943917908803206479987

theorem tailTrace_934469 : CollatzResearch.WordTrace tailWord_934469 prefixEnd_934469 159943917908803206479987 := by
  unfold tailWord_934469
  simp only [CollatzResearch.WordTrace]
  refine ⟨34082884451585882444334461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22721922967723921629556307 34082884451585882444334461)
  ·
    refine ⟨12781081669344705916625423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34082884451585882444334461 12781081669344705916625423)
    ·
      refine ⟨19171622504017058874938135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12781081669344705916625423 19171622504017058874938135)
      ·
        refine ⟨28757433756025588312407203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19171622504017058874938135 28757433756025588312407203)
        ·
          refine ⟨43136150634038382468610805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28757433756025588312407203 43136150634038382468610805)
          ·
            refine ⟨4044014121941098356432263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43136150634038382468610805 4044014121941098356432263)
            ·
              refine ⟨6066021182911647534648395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4044014121941098356432263 6066021182911647534648395)
              ·
                refine ⟨9099031774367471301972593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6066021182911647534648395 9099031774367471301972593)
                ·
                  refine ⟨6824273830775603476479445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9099031774367471301972593 6824273830775603476479445)
                  ·
                    refine ⟨159943917908803206479987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6824273830775603476479445 159943917908803206479987)
                    ·
                      rfl

theorem cell23_934469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 1, 2, 7].length) (baseStart_934469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_934469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_934469 prefixEnd_934469 := by exact prefixLift 934469
  have htrace : WordTrace (prefixWord ++ tailWord_934469) baseStart_934469 baseEnd_934469 := by
    simpa [prefixWord, tailWord_934469, baseEnd_934469] using wordTrace_append hprefix tailTrace_934469
  have hstable : (prefixWord ++ tailWord_934469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934469).length < 2 ^ (prefixWord ++ tailWord_934469).sum := by decide
  have hdescent : baseEnd_934469 < baseStart_934469 := by decide
  rcases family_descends (prefixWord ++ tailWord_934469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934470 : List Nat := [6, 1, 1, 1, 2, 1, 1, 2, 3, 2, 3]
def baseStart_934470 : Nat := 118140960795 + 934470 * 2 ^ 59
def prefixEnd_934470 : Nat := 4983230072969 + 3 ^ 40 * 934470 * 2
def baseEnd_934470 : Nat := 479832267207064115527457

theorem tailTrace_934470 : CollatzResearch.WordTrace tailWord_934470 prefixEnd_934470 479832267207064115527457 := by
  unfold tailWord_934470
  simp only [CollatzResearch.WordTrace]
  refine ⟨1065091278893195612972527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 22721947283054839743413909 1065091278893195612972527)
  ·
    refine ⟨1597636918339793419458791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1065091278893195612972527 1597636918339793419458791)
    ·
      refine ⟨2396455377509690129188187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1597636918339793419458791 2396455377509690129188187)
      ·
        refine ⟨3594683066264535193782281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2396455377509690129188187 3594683066264535193782281)
        ·
          refine ⟨2696012299698401395336711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3594683066264535193782281 2696012299698401395336711)
          ·
            refine ⟨4044018449547602093005067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2696012299698401395336711 4044018449547602093005067)
            ·
              refine ⟨6066027674321403139507601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4044018449547602093005067 6066027674321403139507601)
              ·
                refine ⟨4549520755741052354630701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6066027674321403139507601 4549520755741052354630701)
                ·
                  refine ⟨1706070283402894632986513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4549520755741052354630701 1706070283402894632986513)
                  ·
                    refine ⟨1279552712552170974739885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1706070283402894632986513 1279552712552170974739885)
                    ·
                      refine ⟨479832267207064115527457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1279552712552170974739885 479832267207064115527457)
                      ·
                        rfl

theorem cell23_934470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 2, 3, 2, 3].length) (baseStart_934470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_934470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_934470 prefixEnd_934470 := by exact prefixLift 934470
  have htrace : WordTrace (prefixWord ++ tailWord_934470) baseStart_934470 baseEnd_934470 := by
    simpa [prefixWord, tailWord_934470, baseEnd_934470] using wordTrace_append hprefix tailTrace_934470
  have hstable : (prefixWord ++ tailWord_934470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934470).length < 2 ^ (prefixWord ++ tailWord_934470).sum := by decide
  have hdescent : baseEnd_934470 < baseStart_934470 := by decide
  rcases family_descends (prefixWord ++ tailWord_934470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934499 : List Nat := [1, 1, 1, 5, 1, 2, 1, 2, 1, 8]
def baseStart_934499 : Nat := 118140960795 + 934499 * 2 ^ 59
def prefixEnd_934499 : Nat := 4983230072969 + 3 ^ 40 * 934499 * 2
def baseEnd_934499 : Nat := 159949052715348167354941

theorem tailTrace_934499 : CollatzResearch.WordTrace tailWord_934499 prefixEnd_934499 159949052715348167354941 := by
  unfold tailWord_934499
  simp only [CollatzResearch.WordTrace]
  refine ⟨34083978641477197567926551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22722652427651465045284367 34083978641477197567926551)
  ·
    refine ⟨51125967962215796351889827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34083978641477197567926551 51125967962215796351889827)
    ·
      refine ⟨76688951943323694527834741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51125967962215796351889827 76688951943323694527834741)
      ·
        refine ⟨7189589244686596361984507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 76688951943323694527834741 7189589244686596361984507)
        ·
          refine ⟨10784383867029894542976761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7189589244686596361984507 10784383867029894542976761)
          ·
            refine ⟨8088287900272420907232571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10784383867029894542976761 8088287900272420907232571)
            ·
              refine ⟨12132431850408631360848857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8088287900272420907232571 12132431850408631360848857)
              ·
                refine ⟨9099323887806473520636643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12132431850408631360848857 9099323887806473520636643)
                ·
                  refine ⟨13648985831709710280954965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9099323887806473520636643 13648985831709710280954965)
                  ·
                    refine ⟨159949052715348167354941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 13648985831709710280954965 159949052715348167354941)
                    ·
                      rfl

theorem cell23_934499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 2, 1, 8].length) (baseStart_934499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_934499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_934499 prefixEnd_934499 := by exact prefixLift 934499
  have htrace : WordTrace (prefixWord ++ tailWord_934499) baseStart_934499 baseEnd_934499 := by
    simpa [prefixWord, tailWord_934499, baseEnd_934499] using wordTrace_append hprefix tailTrace_934499
  have hstable : (prefixWord ++ tailWord_934499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934499).length < 2 ^ (prefixWord ++ tailWord_934499).sum := by decide
  have hdescent : baseEnd_934499 < baseStart_934499 := by decide
  rcases family_descends (prefixWord ++ tailWord_934499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934504 : List Nat := [2, 1, 4, 3, 3, 1, 2, 1, 1, 2, 3]
def baseStart_934504 : Nat := 118140960795 + 934504 * 2 ^ 59
def prefixEnd_934504 : Nat := 4983230072969 + 3 ^ 40 * 934504 * 2
def baseEnd_934504 : Nat := 479849725549316982502301

theorem tailTrace_934504 : CollatzResearch.WordTrace tailWord_934504 prefixEnd_934504 479849725549316982502301 := by
  unfold tailWord_934504
  simp only [CollatzResearch.WordTrace]
  refine ⟨17042080503229541710929283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22722774004306055614572377 17042080503229541710929283)
  ·
    refine ⟨25563120754844312566393925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17042080503229541710929283 25563120754844312566393925)
    ·
      refine ⟨4793085141533308606198861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25563120754844312566393925 4793085141533308606198861)
      ·
        refine ⟨1797406928074990727324573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4793085141533308606198861 1797406928074990727324573)
        ·
          refine ⟨674027598028121522746715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1797406928074990727324573 674027598028121522746715)
          ·
            refine ⟨1011041397042182284120073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 674027598028121522746715 1011041397042182284120073)
            ·
              refine ⟨758281047781636713090055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1011041397042182284120073 758281047781636713090055)
              ·
                refine ⟨1137421571672455069635083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 758281047781636713090055 1137421571672455069635083)
                ·
                  refine ⟨1706132357508682604452625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1137421571672455069635083 1706132357508682604452625)
                  ·
                    refine ⟨1279599268131511953339469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1706132357508682604452625 1279599268131511953339469)
                    ·
                      refine ⟨479849725549316982502301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1279599268131511953339469 479849725549316982502301)
                      ·
                        rfl

theorem cell23_934504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 2, 1, 1, 2, 3].length) (baseStart_934504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_934504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_934504 prefixEnd_934504 := by exact prefixLift 934504
  have htrace : WordTrace (prefixWord ++ tailWord_934504) baseStart_934504 baseEnd_934504 := by
    simpa [prefixWord, tailWord_934504, baseEnd_934504] using wordTrace_append hprefix tailTrace_934504
  have hstable : (prefixWord ++ tailWord_934504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934504).length < 2 ^ (prefixWord ++ tailWord_934504).sum := by decide
  have hdescent : baseEnd_934504 < baseStart_934504 := by decide
  rcases family_descends (prefixWord ++ tailWord_934504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934586 : List Nat := [3, 1, 1, 1, 2, 3, 3, 1, 1, 2, 5]
def baseStart_934586 : Nat := 118140960795 + 934586 * 2 ^ 59
def prefixEnd_934586 : Nat := 4983230072969 + 3 ^ 40 * 934586 * 2
def baseEnd_934586 : Nat := 479891830962985661676923

theorem tailTrace_934586 : CollatzResearch.WordTrace tailWord_934586 prefixEnd_934586 479891830962985661676923 := by
  unfold tailWord_934586
  simp only [CollatzResearch.WordTrace]
  refine ⟨8521787948040502856585903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22724767861441340950895741 8521787948040502856585903)
  ·
    refine ⟨12782681922060754284878855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8521787948040502856585903 12782681922060754284878855)
    ·
      refine ⟨19174022883091131427318283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12782681922060754284878855 19174022883091131427318283)
      ·
        refine ⟨28761034324636697140977425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19174022883091131427318283 28761034324636697140977425)
        ·
          refine ⟨21570775743477522855733069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28761034324636697140977425 21570775743477522855733069)
          ·
            refine ⟨8089040903804071070899901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21570775743477522855733069 8089040903804071070899901)
            ·
              refine ⟨3033390338926526651587463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8089040903804071070899901 3033390338926526651587463)
              ·
                refine ⟨4550085508389789977381195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3033390338926526651587463 4550085508389789977381195)
                ·
                  refine ⟨6825128262584684966071793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4550085508389789977381195 6825128262584684966071793)
                  ·
                    refine ⟨5118846196938513724553845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6825128262584684966071793 5118846196938513724553845)
                    ·
                      refine ⟨479891830962985661676923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5118846196938513724553845 479891830962985661676923)
                      ·
                        rfl

theorem cell23_934586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 1, 1, 2, 5].length) (baseStart_934586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_934586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_934586 prefixEnd_934586 := by exact prefixLift 934586
  have htrace : WordTrace (prefixWord ++ tailWord_934586) baseStart_934586 baseEnd_934586 := by
    simpa [prefixWord, tailWord_934586, baseEnd_934586] using wordTrace_append hprefix tailTrace_934586
  have hstable : (prefixWord ++ tailWord_934586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934586).length < 2 ^ (prefixWord ++ tailWord_934586).sum := by decide
  have hdescent : baseEnd_934586 < baseStart_934586 := by decide
  rcases family_descends (prefixWord ++ tailWord_934586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934610 : List Nat := [3, 2, 2, 2, 3, 1, 2, 1, 2, 5]
def baseStart_934610 : Nat := 118140960795 + 934610 * 2 ^ 59
def prefixEnd_934610 : Nat := 4983230072969 + 3 ^ 40 * 934610 * 2
def baseEnd_934610 : Nat := 159968051499564522592271

theorem tailTrace_934610 : CollatzResearch.WordTrace tailWord_934610 prefixEnd_934610 159968051499564522592271 := by
  unfold tailWord_934610
  simp only [CollatzResearch.WordTrace]
  refine ⟨8522006786018765881304321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22725351429383375683478189 8522006786018765881304321)
  ·
    refine ⟨6391505089514074410978241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8522006786018765881304321 6391505089514074410978241)
    ·
      refine ⟨4793628817135555808233681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6391505089514074410978241 4793628817135555808233681)
      ·
        refine ⟨3595221612851666856175261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4793628817135555808233681 3595221612851666856175261)
        ·
          refine ⟨1348208104819375071065723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3595221612851666856175261 1348208104819375071065723)
          ·
            refine ⟨2022312157229062606598585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1348208104819375071065723 2022312157229062606598585)
            ·
              refine ⟨1516734117921796954948939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2022312157229062606598585 1516734117921796954948939)
              ·
                refine ⟨2275101176882695432423409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1516734117921796954948939 2275101176882695432423409)
                ·
                  refine ⟨1706325882662021574317557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2275101176882695432423409 1706325882662021574317557)
                  ·
                    refine ⟨159968051499564522592271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1706325882662021574317557 159968051499564522592271)
                    ·
                      rfl

theorem cell23_934610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 2, 1, 2, 5].length) (baseStart_934610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_934610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_934610 prefixEnd_934610 := by exact prefixLift 934610
  have htrace : WordTrace (prefixWord ++ tailWord_934610) baseStart_934610 baseEnd_934610 := by
    simpa [prefixWord, tailWord_934610, baseEnd_934610] using wordTrace_append hprefix tailTrace_934610
  have hstable : (prefixWord ++ tailWord_934610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934610).length < 2 ^ (prefixWord ++ tailWord_934610).sum := by decide
  have hdescent : baseEnd_934610 < baseStart_934610 := by decide
  rcases family_descends (prefixWord ++ tailWord_934610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934633 : List Nat := [1, 2, 1, 1, 1, 2, 6, 2, 2, 2, 3]
def baseStart_934633 : Nat := 118140960795 + 934633 * 2 ^ 59
def prefixEnd_934633 : Nat := 4983230072969 + 3 ^ 40 * 934633 * 2
def baseEnd_934633 : Nat := 479915964553746977789207

theorem tailTrace_934633 : CollatzResearch.WordTrace tailWord_934633 prefixEnd_934633 479915964553746977789207 := by
  unfold tailWord_934633
  simp only [CollatzResearch.WordTrace]
  refine ⟨34088866022991738453304553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22725910681994492302203035 34088866022991738453304553)
  ·
    refine ⟨25566649517243803839978415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34088866022991738453304553 25566649517243803839978415)
    ·
      refine ⟨38349974275865705759967623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25566649517243803839978415 38349974275865705759967623)
      ·
        refine ⟨57524961413798558639951435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38349974275865705759967623 57524961413798558639951435)
        ·
          refine ⟨86287442120697837959927153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57524961413798558639951435 86287442120697837959927153)
          ·
            refine ⟨64715581590523378469945365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86287442120697837959927153 64715581590523378469945365)
            ·
              refine ⟨3033542887055783365778689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 64715581590523378469945365 3033542887055783365778689)
              ·
                refine ⟨2275157165291837524334017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3033542887055783365778689 2275157165291837524334017)
                ·
                  refine ⟨1706367873968878143250513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2275157165291837524334017 1706367873968878143250513)
                  ·
                    refine ⟨1279775905476658607437885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1706367873968878143250513 1279775905476658607437885)
                    ·
                      refine ⟨479915964553746977789207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1279775905476658607437885 479915964553746977789207)
                      ·
                        rfl

theorem cell23_934633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 2, 2, 2, 3].length) (baseStart_934633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_934633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_934633 prefixEnd_934633 := by exact prefixLift 934633
  have htrace : WordTrace (prefixWord ++ tailWord_934633) baseStart_934633 baseEnd_934633 := by
    simpa [prefixWord, tailWord_934633, baseEnd_934633] using wordTrace_append hprefix tailTrace_934633
  have hstable : (prefixWord ++ tailWord_934633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934633).length < 2 ^ (prefixWord ++ tailWord_934633).sum := by decide
  have hdescent : baseEnd_934633 < baseStart_934633 := by decide
  rcases family_descends (prefixWord ++ tailWord_934633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934640 : List Nat := [2, 1, 1, 1, 3, 1, 5, 4, 1, 4]
def baseStart_934640 : Nat := 118140960795 + 934640 * 2 ^ 59
def prefixEnd_934640 : Nat := 4983230072969 + 3 ^ 40 * 934640 * 2
def baseEnd_934640 : Nat := 159973186306109483467225

theorem tailTrace_934640 : CollatzResearch.WordTrace tailWord_934640 prefixEnd_934640 159973186306109483467225 := by
  unfold tailWord_934640
  simp only [CollatzResearch.WordTrace]
  refine ⟨17044560666983189324404687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22726080889310919099206249 17044560666983189324404687)
  ·
    refine ⟨25566841000474783986607031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17044560666983189324404687 25566841000474783986607031)
    ·
      refine ⟨38350261500712175979910547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25566841000474783986607031 38350261500712175979910547)
      ·
        refine ⟨57525392251068263969865821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38350261500712175979910547 57525392251068263969865821)
        ·
          refine ⟨21572022094150598988699683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57525392251068263969865821 21572022094150598988699683)
          ·
            refine ⟨32358033141225898483049525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21572022094150598988699683 32358033141225898483049525)
            ·
              refine ⟨3033565606989927982785893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32358033141225898483049525 3033565606989927982785893)
              ·
                refine ⟨568793551310611496772355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3033565606989927982785893 568793551310611496772355)
                ·
                  refine ⟨853190326965917245158533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 568793551310611496772355 853190326965917245158533)
                  ·
                    refine ⟨159973186306109483467225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 853190326965917245158533 159973186306109483467225)
                    ·
                      rfl

theorem cell23_934640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 4, 1, 4].length) (baseStart_934640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_934640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_934640 prefixEnd_934640 := by exact prefixLift 934640
  have htrace : WordTrace (prefixWord ++ tailWord_934640) baseStart_934640 baseEnd_934640 := by
    simpa [prefixWord, tailWord_934640, baseEnd_934640] using wordTrace_append hprefix tailTrace_934640
  have hstable : (prefixWord ++ tailWord_934640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934640).length < 2 ^ (prefixWord ++ tailWord_934640).sum := by decide
  have hdescent : baseEnd_934640 < baseStart_934640 := by decide
  rcases family_descends (prefixWord ++ tailWord_934640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934703 : List Nat := [1, 1, 2, 1, 2, 1, 2, 1, 4, 6, 2]
def baseStart_934703 : Nat := 118140960795 + 934703 * 2 ^ 59
def prefixEnd_934703 : Nat := 4983230072969 + 3 ^ 40 * 934703 * 2
def baseEnd_934703 : Nat := 479951908199561703913885

theorem tailTrace_934703 : CollatzResearch.WordTrace tailWord_934703 prefixEnd_934703 479951908199561703913885 := by
  unfold tailWord_934703
  simp only [CollatzResearch.WordTrace]
  refine ⟨34091419132738140408352763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22727612755158760272235175 34091419132738140408352763)
  ·
    refine ⟨51137128699107210612529145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34091419132738140408352763 51137128699107210612529145)
    ·
      refine ⟨38352846524330407959396859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51137128699107210612529145 38352846524330407959396859)
      ·
        refine ⟨57529269786495611939095289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38352846524330407959396859 57529269786495611939095289)
        ·
          refine ⟨43146952339871708954321467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57529269786495611939095289 43146952339871708954321467)
          ·
            refine ⟨64720428509807563431482201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43146952339871708954321467 64720428509807563431482201)
            ·
              refine ⟨48540321382355672573611651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64720428509807563431482201 48540321382355672573611651)
              ·
                refine ⟨72810482073533508860417477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48540321382355672573611651 72810482073533508860417477)
                ·
                  refine ⟨13651965388787532911328277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72810482073533508860417477 13651965388787532911328277)
                  ·
                    refine ⟨639935877599415605218513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13651965388787532911328277 639935877599415605218513)
                    ·
                      refine ⟨479951908199561703913885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 639935877599415605218513 479951908199561703913885)
                      ·
                        rfl

theorem cell23_934703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 4, 6, 2].length) (baseStart_934703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_934703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_934703 prefixEnd_934703 := by exact prefixLift 934703
  have htrace : WordTrace (prefixWord ++ tailWord_934703) baseStart_934703 baseEnd_934703 := by
    simpa [prefixWord, tailWord_934703, baseEnd_934703] using wordTrace_append hprefix tailTrace_934703
  have hstable : (prefixWord ++ tailWord_934703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934703).length < 2 ^ (prefixWord ++ tailWord_934703).sum := by decide
  have hdescent : baseEnd_934703 < baseStart_934703 := by decide
  rcases family_descends (prefixWord ++ tailWord_934703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934717 : List Nat := [1, 4, 1, 4, 2, 1, 2, 2, 1, 5]
def baseStart_934717 : Nat := 118140960795 + 934717 * 2 ^ 59
def prefixEnd_934717 : Nat := 4983230072969 + 3 ^ 40 * 934717 * 2
def baseEnd_934717 : Nat := 159986365642908216379607

theorem tailTrace_934717 : CollatzResearch.WordTrace tailWord_934717 prefixEnd_934717 159986365642908216379607 := by
  unfold tailWord_934717
  simp only [CollatzResearch.WordTrace]
  refine ⟨34091929754687420799362405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22727953169791613866241603 34091929754687420799362405)
  ·
    refine ⟨6392236829003891399880451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34091929754687420799362405 6392236829003891399880451)
    ·
      refine ⟨9588355243505837099820677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6392236829003891399880451 9588355243505837099820677)
      ·
        refine ⟨1797816608157344456216377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9588355243505837099820677 1797816608157344456216377)
        ·
          refine ⟨1348362456118008342162283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1797816608157344456216377 1348362456118008342162283)
          ·
            refine ⟨2022543684177012513243425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1348362456118008342162283 2022543684177012513243425)
            ·
              refine ⟨1516907763132759384932569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2022543684177012513243425 1516907763132759384932569)
              ·
                refine ⟨1137680822349569538699427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1516907763132759384932569 1137680822349569538699427)
                ·
                  refine ⟨1706521233524354308049141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1137680822349569538699427 1706521233524354308049141)
                  ·
                    refine ⟨159986365642908216379607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1706521233524354308049141 159986365642908216379607)
                    ·
                      rfl

theorem cell23_934717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 2, 2, 1, 5].length) (baseStart_934717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_934717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_934717 prefixEnd_934717 := by exact prefixLift 934717
  have htrace : WordTrace (prefixWord ++ tailWord_934717) baseStart_934717 baseEnd_934717 := by
    simpa [prefixWord, tailWord_934717, baseEnd_934717] using wordTrace_append hprefix tailTrace_934717
  have hstable : (prefixWord ++ tailWord_934717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934717).length < 2 ^ (prefixWord ++ tailWord_934717).sum := by decide
  have hdescent : baseEnd_934717 < baseStart_934717 := by decide
  rcases family_descends (prefixWord ++ tailWord_934717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934743 : List Nat := [1, 1, 3, 2, 4, 3, 9]
def baseStart_934743 : Nat := 118140960795 + 934743 * 2 ^ 59
def prefixEnd_934743 : Nat := 4983230072969 + 3 ^ 40 * 934743 * 2
def baseEnd_934743 : Nat := 5925585770688167252021

theorem tailTrace_934743 : CollatzResearch.WordTrace tailWord_934743 prefixEnd_934743 5925585770688167252021 := by
  unfold tailWord_934743
  simp only [CollatzResearch.WordTrace]
  refine ⟨34092878052593227239808883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22728585368395484826539255 34092878052593227239808883)
  ·
    refine ⟨51139317078889840859713325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34092878052593227239808883 51139317078889840859713325)
    ·
      refine ⟨19177243904583690322392497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51139317078889840859713325 19177243904583690322392497)
      ·
        refine ⟨14382932928437767741794373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19177243904583690322392497 14382932928437767741794373)
        ·
          refine ⟨2696799924082081451586445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14382932928437767741794373 2696799924082081451586445)
          ·
            refine ⟨1011299971530780544344917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2696799924082081451586445 1011299971530780544344917)
            ·
              refine ⟨5925585770688167252021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1011299971530780544344917 5925585770688167252021)
              ·
                rfl

theorem cell23_934743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 9].length) (baseStart_934743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_934743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_934743 prefixEnd_934743 := by exact prefixLift 934743
  have htrace : WordTrace (prefixWord ++ tailWord_934743) baseStart_934743 baseEnd_934743 := by
    simpa [prefixWord, tailWord_934743, baseEnd_934743] using wordTrace_append hprefix tailTrace_934743
  have hstable : (prefixWord ++ tailWord_934743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934743).length < 2 ^ (prefixWord ++ tailWord_934743).sum := by decide
  have hdescent : baseEnd_934743 < baseStart_934743 := by decide
  rcases family_descends (prefixWord ++ tailWord_934743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934753 : List Nat := [1, 2, 3, 1, 1, 1, 2, 1, 5, 3, 3]
def baseStart_934753 : Nat := 118140960795 + 934753 * 2 ^ 59
def prefixEnd_934753 : Nat := 4983230072969 + 3 ^ 40 * 934753 * 2
def baseEnd_934753 : Nat := 479977582232286508288655

theorem tailTrace_934753 : CollatzResearch.WordTrace tailWord_934753 prefixEnd_934753 479977582232286508288655 := by
  unfold tailWord_934753
  simp only [CollatzResearch.WordTrace]
  refine ⟨34093242782556998947672913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22728828521704665965115275 34093242782556998947672913)
  ·
    refine ⟨25569932086917749210754685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34093242782556998947672913 25569932086917749210754685)
    ·
      refine ⟨9588724532594155954033007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25569932086917749210754685 9588724532594155954033007)
      ·
        refine ⟨14383086798891233931049511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9588724532594155954033007 14383086798891233931049511)
        ·
          refine ⟨21574630198336850896574267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14383086798891233931049511 21574630198336850896574267)
          ·
            refine ⟨32361945297505276344861401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21574630198336850896574267 32361945297505276344861401)
            ·
              refine ⟨24271458973128957258646051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32361945297505276344861401 24271458973128957258646051)
              ·
                refine ⟨36407188459693435887969077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24271458973128957258646051 36407188459693435887969077)
                ·
                  refine ⟨3413173918096259614497101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36407188459693435887969077 3413173918096259614497101)
                  ·
                    refine ⟨1279940219286097355436413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3413173918096259614497101 1279940219286097355436413)
                    ·
                      refine ⟨479977582232286508288655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1279940219286097355436413 479977582232286508288655)
                      ·
                        rfl

theorem cell23_934753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 5, 3, 3].length) (baseStart_934753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_934753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_934753 prefixEnd_934753 := by exact prefixLift 934753
  have htrace : WordTrace (prefixWord ++ tailWord_934753) baseStart_934753 baseEnd_934753 := by
    simpa [prefixWord, tailWord_934753, baseEnd_934753] using wordTrace_append hprefix tailTrace_934753
  have hstable : (prefixWord ++ tailWord_934753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934753).length < 2 ^ (prefixWord ++ tailWord_934753).sum := by decide
  have hdescent : baseEnd_934753 < baseStart_934753 := by decide
  rcases family_descends (prefixWord ++ tailWord_934753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934774 : List Nat := [5, 1, 1, 3, 1, 1, 3, 2, 1, 2, 3]
def baseStart_934774 : Nat := 118140960795 + 934774 * 2 ^ 59
def prefixEnd_934774 : Nat := 4983230072969 + 3 ^ 40 * 934774 * 2
def baseEnd_934774 : Nat := 479988365326030926126059

theorem tailTrace_934774 : CollatzResearch.WordTrace tailWord_934774 prefixEnd_934774 479988365326030926126059 := by
  unfold tailWord_934774
  simp only [CollatzResearch.WordTrace]
  refine ⟨2130875544717557470886711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22729339143653946356124917 2130875544717557470886711)
  ·
    refine ⟨3196313317076336206330067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2130875544717557470886711 3196313317076336206330067)
    ·
      refine ⟨4794469975614504309495101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3196313317076336206330067 4794469975614504309495101)
      ·
        refine ⟨1797926240855439116060663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4794469975614504309495101 1797926240855439116060663)
        ·
          refine ⟨2696889361283158674090995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1797926240855439116060663 2696889361283158674090995)
          ·
            refine ⟨4045334041924738011136493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2696889361283158674090995 4045334041924738011136493)
            ·
              refine ⟨1517000265721776754176185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4045334041924738011136493 1517000265721776754176185)
              ·
                refine ⟨1137750199291332565632139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1517000265721776754176185 1137750199291332565632139)
                ·
                  refine ⟨1706625298936998848448209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1137750199291332565632139 1706625298936998848448209)
                  ·
                    refine ⟨1279968974202749136336157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1706625298936998848448209 1279968974202749136336157)
                    ·
                      refine ⟨479988365326030926126059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1279968974202749136336157 479988365326030926126059)
                      ·
                        rfl

theorem cell23_934774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_934774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_934774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_934774 prefixEnd_934774 := by exact prefixLift 934774
  have htrace : WordTrace (prefixWord ++ tailWord_934774) baseStart_934774 baseEnd_934774 := by
    simpa [prefixWord, tailWord_934774, baseEnd_934774] using wordTrace_append hprefix tailTrace_934774
  have hstable : (prefixWord ++ tailWord_934774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934774).length < 2 ^ (prefixWord ++ tailWord_934774).sum := by decide
  have hdescent : baseEnd_934774 < baseStart_934774 := by decide
  rcases family_descends (prefixWord ++ tailWord_934774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934804 : List Nat := [2, 4, 2, 1, 1, 1, 4, 2, 2, 1, 3]
def baseStart_934804 : Nat := 118140960795 + 934804 * 2 ^ 59
def prefixEnd_934804 : Nat := 4983230072969 + 3 ^ 40 * 934804 * 2
def baseEnd_934804 : Nat := 480003769745665808750921

theorem tailTrace_934804 : CollatzResearch.WordTrace tailWord_934804 prefixEnd_934804 480003769745665808750921 := by
  unfold tailWord_934804
  simp only [CollatzResearch.WordTrace]
  refine ⟨17047551452686117328889733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22730068603581489771852977 17047551452686117328889733)
  ·
    refine ⟨3196415897378646999166825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17047551452686117328889733 3196415897378646999166825)
    ·
      refine ⟨2397311923033985249375119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3196415897378646999166825 2397311923033985249375119)
      ·
        refine ⟨3595967884550977874062679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2397311923033985249375119 3595967884550977874062679)
        ·
          refine ⟨5393951826826466811094019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3595967884550977874062679 5393951826826466811094019)
          ·
            refine ⟨8090927740239700216641029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5393951826826466811094019 8090927740239700216641029)
            ·
              refine ⟨1517048951294943790620193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8090927740239700216641029 1517048951294943790620193)
              ·
                refine ⟨1137786713471207842965145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1517048951294943790620193 1137786713471207842965145)
                ·
                  refine ⟨853340035103405882223859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1137786713471207842965145 853340035103405882223859)
                  ·
                    refine ⟨1280010052655108823335789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 853340035103405882223859 1280010052655108823335789)
                    ·
                      refine ⟨480003769745665808750921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1280010052655108823335789 480003769745665808750921)
                      ·
                        rfl

theorem cell23_934804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 4, 2, 2, 1, 3].length) (baseStart_934804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_934804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_934804 prefixEnd_934804 := by exact prefixLift 934804
  have htrace : WordTrace (prefixWord ++ tailWord_934804) baseStart_934804 baseEnd_934804 := by
    simpa [prefixWord, tailWord_934804, baseEnd_934804] using wordTrace_append hprefix tailTrace_934804
  have hstable : (prefixWord ++ tailWord_934804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934804).length < 2 ^ (prefixWord ++ tailWord_934804).sum := by decide
  have hdescent : baseEnd_934804 < baseStart_934804 := by decide
  rcases family_descends (prefixWord ++ tailWord_934804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934860 : List Nat := [2, 2, 1, 4, 1, 1, 1, 1, 4, 3, 3]
def baseStart_934860 : Nat := 118140960795 + 934860 * 2 ^ 59
def prefixEnd_934860 : Nat := 4983230072969 + 3 ^ 40 * 934860 * 2
def baseEnd_934860 : Nat := 480032524662317589650663

theorem tailTrace_934860 : CollatzResearch.WordTrace tailWord_934860 prefixEnd_934860 480032524662317589650663 := by
  unfold tailWord_934860
  simp only [CollatzResearch.WordTrace]
  refine ⟨17048572696584678110909017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22731430262112904147878689 17048572696584678110909017)
  ·
    refine ⟨12786429522438508583181763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17048572696584678110909017 12786429522438508583181763)
    ·
      refine ⟨19179644283657762874772645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12786429522438508583181763 19179644283657762874772645)
      ·
        refine ⟨3596183303185830539019871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19179644283657762874772645 3596183303185830539019871)
        ·
          refine ⟨5394274954778745808529807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3596183303185830539019871 5394274954778745808529807)
          ·
            refine ⟨8091412432168118712794711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5394274954778745808529807 8091412432168118712794711)
            ·
              refine ⟨12137118648252178069192067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8091412432168118712794711 12137118648252178069192067)
              ·
                refine ⟨18205677972378267103788101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12137118648252178069192067 18205677972378267103788101)
                ·
                  refine ⟨3413564619820925081960269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18205677972378267103788101 3413564619820925081960269)
                  ·
                    refine ⟨1280086732432846905735101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3413564619820925081960269 1280086732432846905735101)
                    ·
                      refine ⟨480032524662317589650663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1280086732432846905735101 480032524662317589650663)
                      ·
                        rfl

theorem cell23_934860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 4, 3, 3].length) (baseStart_934860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_934860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_934860 prefixEnd_934860 := by exact prefixLift 934860
  have htrace : WordTrace (prefixWord ++ tailWord_934860) baseStart_934860 baseEnd_934860 := by
    simpa [prefixWord, tailWord_934860, baseEnd_934860] using wordTrace_append hprefix tailTrace_934860
  have hstable : (prefixWord ++ tailWord_934860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934860).length < 2 ^ (prefixWord ++ tailWord_934860).sum := by decide
  have hdescent : baseEnd_934860 < baseStart_934860 := by decide
  rcases family_descends (prefixWord ++ tailWord_934860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934877 : List Nat := [1, 4, 3, 1, 2, 1, 2, 1, 2, 3, 3]
def baseStart_934877 : Nat := 118140960795 + 934877 * 2 ^ 59
def prefixEnd_934877 : Nat := 4983230072969 + 3 ^ 40 * 934877 * 2
def baseEnd_934877 : Nat := 480041253833444023138085

theorem tailTrace_934877 : CollatzResearch.WordTrace tailWord_934877 prefixEnd_934877 480041253833444023138085 := by
  unfold tailWord_934877
  simp only [CollatzResearch.WordTrace]
  refine ⟨34097765434107768125186885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22731843622738512083457923 34097765434107768125186885)
  ·
    refine ⟨6393331018895206523472541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34097765434107768125186885 6393331018895206523472541)
    ·
      refine ⟨2397499132085702446302203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6393331018895206523472541 2397499132085702446302203)
      ·
        refine ⟨3596248698128553669453305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2397499132085702446302203 3596248698128553669453305)
        ·
          refine ⟨2697186523596415252089979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3596248698128553669453305 2697186523596415252089979)
          ·
            refine ⟨4045779785394622878134969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2697186523596415252089979 4045779785394622878134969)
            ·
              refine ⟨3034334839045967158601227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4045779785394622878134969 3034334839045967158601227)
              ·
                refine ⟨4551502258568950737901841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3034334839045967158601227 4551502258568950737901841)
                ·
                  refine ⟨3413626693926713053426381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4551502258568950737901841 3413626693926713053426381)
                  ·
                    refine ⟨1280110010222517395034893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3413626693926713053426381 1280110010222517395034893)
                    ·
                      refine ⟨480041253833444023138085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1280110010222517395034893 480041253833444023138085)
                      ·
                        rfl

theorem cell23_934877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 1, 2, 3, 3].length) (baseStart_934877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_934877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_934877 prefixEnd_934877 := by exact prefixLift 934877
  have htrace : WordTrace (prefixWord ++ tailWord_934877) baseStart_934877 baseEnd_934877 := by
    simpa [prefixWord, tailWord_934877, baseEnd_934877] using wordTrace_append hprefix tailTrace_934877
  have hstable : (prefixWord ++ tailWord_934877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934877).length < 2 ^ (prefixWord ++ tailWord_934877).sum := by decide
  have hdescent : baseEnd_934877 < baseStart_934877 := by decide
  rcases family_descends (prefixWord ++ tailWord_934877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_934974 : List Nat := [4, 2, 1, 3, 1, 2, 2, 2, 6]
def baseStart_934974 : Nat := 118140960795 + 934974 * 2 ^ 59
def prefixEnd_934974 : Nat := 4983230072969 + 3 ^ 40 * 934974 * 2
def baseEnd_934974 : Nat := 53343451272992238180571

theorem tailTrace_934974 : CollatzResearch.WordTrace tailWord_934974 prefixEnd_934974 53343451272992238180571 := by
  unfold tailWord_934974
  simp only [CollatzResearch.WordTrace]
  refine ⟨4262662914344544211433497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22734202209837569127645317 4262662914344544211433497)
  ·
    refine ⟨3196997185758408158575123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4262662914344544211433497 3196997185758408158575123)
    ·
      refine ⟨4795495778637612237862685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3196997185758408158575123 4795495778637612237862685)
      ·
        refine ⟨1798310916989104589198507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4795495778637612237862685 1798310916989104589198507)
        ·
          refine ⟨2697466375483656883797761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1798310916989104589198507 2697466375483656883797761)
          ·
            refine ⟨2023099781612742662848321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2697466375483656883797761 2023099781612742662848321)
            ·
              refine ⟨1517324836209556997136241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2023099781612742662848321 1517324836209556997136241)
              ·
                refine ⟨1137993627157167747852181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1517324836209556997136241 1137993627157167747852181)
                ·
                  refine ⟨53343451272992238180571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1137993627157167747852181 53343451272992238180571)
                  ·
                    rfl

theorem cell23_934974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 2, 2, 6].length) (baseStart_934974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_934974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_934974 prefixEnd_934974 := by exact prefixLift 934974
  have htrace : WordTrace (prefixWord ++ tailWord_934974) baseStart_934974 baseEnd_934974 := by
    simpa [prefixWord, tailWord_934974, baseEnd_934974] using wordTrace_append hprefix tailTrace_934974
  have hstable : (prefixWord ++ tailWord_934974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_934974).length < 2 ^ (prefixWord ++ tailWord_934974).sum := by decide
  have hdescent : baseEnd_934974 < baseStart_934974 := by decide
  rcases family_descends (prefixWord ++ tailWord_934974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935007 : List Nat := [1, 1, 2, 3, 1, 1, 4, 4, 1, 1, 4]
def baseStart_935007 : Nat := 118140960795 + 935007 * 2 ^ 59
def prefixEnd_935007 : Nat := 4983230072969 + 3 ^ 40 * 935007 * 2
def baseEnd_935007 : Nat := 480108006318528514512487

theorem tailTrace_935007 : CollatzResearch.WordTrace tailWord_935007 prefixEnd_935007 480108006318528514512487 := by
  unfold tailWord_935007
  simp only [CollatzResearch.WordTrace]
  refine ⟨34102506923636800327419275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22735004615757866884946183 34102506923636800327419275)
  ·
    refine ⟨51153760385455200491128913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34102506923636800327419275 51153760385455200491128913)
    ·
      refine ⟨38365320289091400368346685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51153760385455200491128913 38365320289091400368346685)
      ·
        refine ⟨14386995108409275138130007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38365320289091400368346685 14386995108409275138130007)
        ·
          refine ⟨21580492662613912707195011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14386995108409275138130007 21580492662613912707195011)
          ·
            refine ⟨32370738993920869060792517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21580492662613912707195011 32370738993920869060792517)
            ·
              refine ⟨6069513561360162948898597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32370738993920869060792517 6069513561360162948898597)
              ·
                refine ⟨1138033792755030552918487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6069513561360162948898597 1138033792755030552918487)
                ·
                  refine ⟨1707050689132545829377731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1138033792755030552918487 1707050689132545829377731)
                  ·
                    refine ⟨2560576033698818744066597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1707050689132545829377731 2560576033698818744066597)
                    ·
                      refine ⟨480108006318528514512487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2560576033698818744066597 480108006318528514512487)
                      ·
                        rfl

theorem cell23_935007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 4, 1, 1, 4].length) (baseStart_935007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_935007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_935007 prefixEnd_935007 := by exact prefixLift 935007
  have htrace : WordTrace (prefixWord ++ tailWord_935007) baseStart_935007 baseEnd_935007 := by
    simpa [prefixWord, tailWord_935007, baseEnd_935007] using wordTrace_append hprefix tailTrace_935007
  have hstable : (prefixWord ++ tailWord_935007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935007).length < 2 ^ (prefixWord ++ tailWord_935007).sum := by decide
  have hdescent : baseEnd_935007 < baseStart_935007 := by decide
  rcases family_descends (prefixWord ++ tailWord_935007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935018 : List Nat := [3, 1, 3, 2, 2, 2, 2, 3, 1, 1, 3]
def baseStart_935018 : Nat := 118140960795 + 935018 * 2 ^ 59
def prefixEnd_935018 : Nat := 4983230072969 + 3 ^ 40 * 935018 * 2
def baseEnd_935018 : Nat := 480113654605727971474937

theorem tailTrace_935018 : CollatzResearch.WordTrace tailWord_935018 prefixEnd_935018 480113654605727971474937 := by
  unfold tailWord_935018
  simp only [CollatzResearch.WordTrace]
  refine ⟨8525727031649237301517427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22735272084397966137379805 8525727031649237301517427)
  ·
    refine ⟨12788590547473855952276141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8525727031649237301517427 12788590547473855952276141)
    ·
      refine ⟨4795721455302695982103553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12788590547473855952276141 4795721455302695982103553)
      ·
        refine ⟨3596791091477021986577665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4795721455302695982103553 3596791091477021986577665)
        ·
          refine ⟨2697593318607766489933249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3596791091477021986577665 2697593318607766489933249)
          ·
            refine ⟨2023194988955824867449937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2697593318607766489933249 2023194988955824867449937)
            ·
              refine ⟨1517396241716868650587453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2023194988955824867449937 1517396241716868650587453)
              ·
                refine ⟨569023590643825743970295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1517396241716868650587453 569023590643825743970295)
                ·
                  refine ⟨853535385965738615955443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 569023590643825743970295 853535385965738615955443)
                  ·
                    refine ⟨1280303078948607923933165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 853535385965738615955443 1280303078948607923933165)
                    ·
                      refine ⟨480113654605727971474937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1280303078948607923933165 480113654605727971474937)
                      ·
                        rfl

theorem cell23_935018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 2, 3, 1, 1, 3].length) (baseStart_935018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_935018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_935018 prefixEnd_935018 := by exact prefixLift 935018
  have htrace : WordTrace (prefixWord ++ tailWord_935018) baseStart_935018 baseEnd_935018 := by
    simpa [prefixWord, tailWord_935018, baseEnd_935018] using wordTrace_append hprefix tailTrace_935018
  have hstable : (prefixWord ++ tailWord_935018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935018).length < 2 ^ (prefixWord ++ tailWord_935018).sum := by decide
  have hdescent : baseEnd_935018 < baseStart_935018 := by decide
  rcases family_descends (prefixWord ++ tailWord_935018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935021 : List Nat := [1, 5, 1, 1, 2, 4, 2, 1, 1, 5]
def baseStart_935021 : Nat := 118140960795 + 935021 * 2 ^ 59
def prefixEnd_935021 : Nat := 4983230072969 + 3 ^ 40 * 935021 * 2
def baseEnd_935021 : Nat := 160038398349230486579141

theorem tailTrace_935021 : CollatzResearch.WordTrace tailWord_935021 prefixEnd_935021 160038398349230486579141 := by
  unfold tailWord_935021
  simp only [CollatzResearch.WordTrace]
  refine ⟨34103017545586080718428917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22735345030390720478952611 34103017545586080718428917)
  ·
    refine ⟨3197157894898695067352711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34103017545586080718428917 3197157894898695067352711)
    ·
      refine ⟨4795736842348042601029067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3197157894898695067352711 4795736842348042601029067)
      ·
        refine ⟨7193605263522063901543601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4795736842348042601029067 7193605263522063901543601)
        ·
          refine ⟨5395203947641547926157701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7193605263522063901543601 5395203947641547926157701)
          ·
            refine ⟨1011600740182790236154569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5395203947641547926157701 1011600740182790236154569)
            ·
              refine ⟨758700555137092677115927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1011600740182790236154569 758700555137092677115927)
              ·
                refine ⟨1138050832705639015673891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 758700555137092677115927 1138050832705639015673891)
                ·
                  refine ⟨1707076249058458523510837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1138050832705639015673891 1707076249058458523510837)
                  ·
                    refine ⟨160038398349230486579141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1707076249058458523510837 160038398349230486579141)
                    ·
                      rfl

theorem cell23_935021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 2, 1, 1, 5].length) (baseStart_935021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_935021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_935021 prefixEnd_935021 := by exact prefixLift 935021
  have htrace : WordTrace (prefixWord ++ tailWord_935021) baseStart_935021 baseEnd_935021 := by
    simpa [prefixWord, tailWord_935021, baseEnd_935021] using wordTrace_append hprefix tailTrace_935021
  have hstable : (prefixWord ++ tailWord_935021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935021).length < 2 ^ (prefixWord ++ tailWord_935021).sum := by decide
  have hdescent : baseEnd_935021 < baseStart_935021 := by decide
  rcases family_descends (prefixWord ++ tailWord_935021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935024 : List Nat := [2, 1, 1, 1, 5, 1, 1, 2, 5, 2, 2]
def baseStart_935024 : Nat := 118140960795 + 935024 * 2 ^ 59
def prefixEnd_935024 : Nat := 4983230072969 + 3 ^ 40 * 935024 * 2
def baseEnd_935024 : Nat := 480116735489654947999909

theorem tailTrace_935024 : CollatzResearch.WordTrace tailWord_935024 prefixEnd_935024 480116735489654947999909 := by
  unfold tailWord_935024
  simp only [CollatzResearch.WordTrace]
  refine ⟨17051563482287606115394063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22735417976383474820525417 17051563482287606115394063)
  ·
    refine ⟨25577345223431409173091095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17051563482287606115394063 25577345223431409173091095)
    ·
      refine ⟨38366017835147113759636643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25577345223431409173091095 38366017835147113759636643)
      ·
        refine ⟨57549026752720670639454965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38366017835147113759636643 57549026752720670639454965)
        ·
          refine ⟨5395221258067562872448903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 57549026752720670639454965 5395221258067562872448903)
          ·
            refine ⟨8092831887101344308673355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5395221258067562872448903 8092831887101344308673355)
            ·
              refine ⟨12139247830652016463010033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8092831887101344308673355 12139247830652016463010033)
              ·
                refine ⟨9104435872989012347257525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12139247830652016463010033 9104435872989012347257525)
                ·
                  refine ⟨853540863092719907555393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9104435872989012347257525 853540863092719907555393)
                  ·
                    refine ⟨640155647319539930666545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 853540863092719907555393 640155647319539930666545)
                    ·
                      refine ⟨480116735489654947999909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 640155647319539930666545 480116735489654947999909)
                      ·
                        rfl

theorem cell23_935024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 2, 5, 2, 2].length) (baseStart_935024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_935024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_935024 prefixEnd_935024 := by exact prefixLift 935024
  have htrace : WordTrace (prefixWord ++ tailWord_935024) baseStart_935024 baseEnd_935024 := by
    simpa [prefixWord, tailWord_935024, baseEnd_935024] using wordTrace_append hprefix tailTrace_935024
  have hstable : (prefixWord ++ tailWord_935024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935024).length < 2 ^ (prefixWord ++ tailWord_935024).sum := by decide
  have hdescent : baseEnd_935024 < baseStart_935024 := by decide
  rcases family_descends (prefixWord ++ tailWord_935024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935041 : List Nat := [1, 2, 4, 2, 2, 1, 1, 3, 3, 2, 2]
def baseStart_935041 : Nat := 118140960795 + 935041 * 2 ^ 59
def prefixEnd_935041 : Nat := 4983230072969 + 3 ^ 40 * 935041 * 2
def baseEnd_935041 : Nat := 480125464660781381487331

theorem tailTrace_935041 : CollatzResearch.WordTrace tailWord_935041 prefixEnd_935041 480125464660781381487331 := by
  unfold tailWord_935041
  simp only [CollatzResearch.WordTrace]
  refine ⟨34103747005513624134156977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22735831337009082756104651 34103747005513624134156977)
  ·
    refine ⟨25577810254135218100617733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34103747005513624134156977 25577810254135218100617733)
    ·
      refine ⟨4795839422650353393865825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25577810254135218100617733 4795839422650353393865825)
      ·
        refine ⟨3596879566987765045399369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4795839422650353393865825 3596879566987765045399369)
        ·
          refine ⟨2697659675240823784049527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3596879566987765045399369 2697659675240823784049527)
          ·
            refine ⟨4046489512861235676074291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2697659675240823784049527 4046489512861235676074291)
            ·
              refine ⟨6069734269291853514111437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4046489512861235676074291 6069734269291853514111437)
              ·
                refine ⟨2276150350984445067791789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6069734269291853514111437 2276150350984445067791789)
                ·
                  refine ⟨853556381619166900421921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2276150350984445067791789 853556381619166900421921)
                  ·
                    refine ⟨640167286214375175316441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 853556381619166900421921 640167286214375175316441)
                    ·
                      refine ⟨480125464660781381487331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 640167286214375175316441 480125464660781381487331)
                      ·
                        rfl

theorem cell23_935041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 3, 3, 2, 2].length) (baseStart_935041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_935041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_935041 prefixEnd_935041 := by exact prefixLift 935041
  have htrace : WordTrace (prefixWord ++ tailWord_935041) baseStart_935041 baseEnd_935041 := by
    simpa [prefixWord, tailWord_935041, baseEnd_935041] using wordTrace_append hprefix tailTrace_935041
  have hstable : (prefixWord ++ tailWord_935041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935041).length < 2 ^ (prefixWord ++ tailWord_935041).sum := by decide
  have hdescent : baseEnd_935041 < baseStart_935041 := by decide
  rcases family_descends (prefixWord ++ tailWord_935041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935054 : List Nat := [4, 1, 1, 3, 2, 1, 3, 1, 1, 2, 4]
def baseStart_935054 : Nat := 118140960795 + 935054 * 2 ^ 59
def prefixEnd_935054 : Nat := 4983230072969 + 3 ^ 40 * 935054 * 2
def baseEnd_935054 : Nat := 480132139909289830624771

theorem tailTrace_935054 : CollatzResearch.WordTrace tailWord_935054 prefixEnd_935054 480132139909289830624771 := by
  unfold tailWord_935054
  simp only [CollatzResearch.WordTrace]
  refine ⟨4263027644308315919297527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22736147436311018236253477 4263027644308315919297527)
  ·
    refine ⟨6394541466462473878946291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4263027644308315919297527 6394541466462473878946291)
    ·
      refine ⟨9591812199693710818419437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6394541466462473878946291 9591812199693710818419437)
      ·
        refine ⟨3596929574885141556907289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9591812199693710818419437 3596929574885141556907289)
        ·
          refine ⟨2697697181163856167680467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3596929574885141556907289 2697697181163856167680467)
          ·
            refine ⟨4046545771745784251520701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2697697181163856167680467 4046545771745784251520701)
            ·
              refine ⟨1517454664404669094320263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4046545771745784251520701 1517454664404669094320263)
              ·
                refine ⟨2276181996607003641480395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1517454664404669094320263 2276181996607003641480395)
                ·
                  refine ⟨3414272994910505462220593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2276181996607003641480395 3414272994910505462220593)
                  ·
                    refine ⟨2560704746182879096665445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3414272994910505462220593 2560704746182879096665445)
                    ·
                      refine ⟨480132139909289830624771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2560704746182879096665445 480132139909289830624771)
                      ·
                        rfl

theorem cell23_935054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 3, 1, 1, 2, 4].length) (baseStart_935054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_935054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_935054 prefixEnd_935054 := by exact prefixLift 935054
  have htrace : WordTrace (prefixWord ++ tailWord_935054) baseStart_935054 baseEnd_935054 := by
    simpa [prefixWord, tailWord_935054, baseEnd_935054] using wordTrace_append hprefix tailTrace_935054
  have hstable : (prefixWord ++ tailWord_935054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935054).length < 2 ^ (prefixWord ++ tailWord_935054).sum := by decide
  have hdescent : baseEnd_935054 < baseStart_935054 := by decide
  rcases family_descends (prefixWord ++ tailWord_935054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935064 : List Nat := [2, 1, 2, 4, 2, 3, 2, 7]
def baseStart_935064 : Nat := 118140960795 + 935064 * 2 ^ 59
def prefixEnd_935064 : Nat := 4983230072969 + 3 ^ 40 * 935064 * 2
def baseEnd_935064 : Nat := 17782862026512399685175

theorem tailTrace_935064 : CollatzResearch.WordTrace tailWord_935064 prefixEnd_935064 17782862026512399685175 := by
  unfold tailWord_935064
  simp only [CollatzResearch.WordTrace]
  refine ⟨17052292942215149531122123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22736390589620199374829497 17052292942215149531122123)
  ·
    refine ⟨25578439413322724296683185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17052292942215149531122123 25578439413322724296683185)
    ·
      refine ⟨19183829559992043222512389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25578439413322724296683185 19183829559992043222512389)
      ·
        refine ⟨3596968042498508104221073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19183829559992043222512389 3596968042498508104221073)
        ·
          refine ⟨2697726031873881078165805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3596968042498508104221073 2697726031873881078165805)
          ·
            refine ⟨1011647261952705404312177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2697726031873881078165805 1011647261952705404312177)
            ·
              refine ⟨758735446464529053234133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1011647261952705404312177 758735446464529053234133)
              ·
                refine ⟨17782862026512399685175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 758735446464529053234133 17782862026512399685175)
                ·
                  rfl

theorem cell23_935064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 2, 7].length) (baseStart_935064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_935064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_935064 prefixEnd_935064 := by exact prefixLift 935064
  have htrace : WordTrace (prefixWord ++ tailWord_935064) baseStart_935064 baseEnd_935064 := by
    simpa [prefixWord, tailWord_935064, baseEnd_935064] using wordTrace_append hprefix tailTrace_935064
  have hstable : (prefixWord ++ tailWord_935064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935064).length < 2 ^ (prefixWord ++ tailWord_935064).sum := by decide
  have hdescent : baseEnd_935064 < baseStart_935064 := by decide
  rcases family_descends (prefixWord ++ tailWord_935064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935108 : List Nat := [2, 3, 3, 1, 3, 1, 1, 3, 2, 1, 3]
def baseStart_935108 : Nat := 118140960795 + 935108 * 2 ^ 59
def prefixEnd_935108 : Nat := 4983230072969 + 3 ^ 40 * 935108 * 2
def baseEnd_935108 : Nat := 480159867864632619349523

theorem tailTrace_935108 : CollatzResearch.WordTrace tailWord_935108 prefixEnd_935108 480159867864632619349523 := by
  unfold tailWord_935108
  simp only [CollatzResearch.WordTrace]
  refine ⟨17053095348135447288422989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22737460464180596384563985 17053095348135447288422989)
  ·
    refine ⟨6394910755550792733158621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17053095348135447288422989 6394910755550792733158621)
    ·
      refine ⟨2398091533331547274934483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6394910755550792733158621 2398091533331547274934483)
      ·
        refine ⟨3597137299997320912401725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2398091533331547274934483 3597137299997320912401725)
        ·
          refine ⟨1348926487498995342150647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3597137299997320912401725 1348926487498995342150647)
          ·
            refine ⟨2023389731248493013225971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1348926487498995342150647 2023389731248493013225971)
            ·
              refine ⟨3035084596872739519838957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2023389731248493013225971 3035084596872739519838957)
              ·
                refine ⟨1138156723827277319939609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3035084596872739519838957 1138156723827277319939609)
                ·
                  refine ⟨853617542870457989954707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1138156723827277319939609 853617542870457989954707)
                  ·
                    refine ⟨1280426314305686984932061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 853617542870457989954707 1280426314305686984932061)
                    ·
                      refine ⟨480159867864632619349523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1280426314305686984932061 480159867864632619349523)
                      ·
                        rfl

theorem cell23_935108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 3, 2, 1, 3].length) (baseStart_935108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_935108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_935108 prefixEnd_935108 := by exact prefixLift 935108
  have htrace : WordTrace (prefixWord ++ tailWord_935108) baseStart_935108 baseEnd_935108 := by
    simpa [prefixWord, tailWord_935108, baseEnd_935108] using wordTrace_append hprefix tailTrace_935108
  have hstable : (prefixWord ++ tailWord_935108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935108).length < 2 ^ (prefixWord ++ tailWord_935108).sum := by decide
  have hdescent : baseEnd_935108 < baseStart_935108 := by decide
  rcases family_descends (prefixWord ++ tailWord_935108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935148 : List Nat := [2, 2, 1, 1, 2, 5, 2, 2, 2, 2, 2]
def baseStart_935148 : Nat := 118140960795 + 935148 * 2 ^ 59
def prefixEnd_935148 : Nat := 4983230072969 + 3 ^ 40 * 935148 * 2
def baseEnd_935148 : Nat := 480180407090812462849339

theorem tailTrace_935148 : CollatzResearch.WordTrace tailWord_935148 prefixEnd_935148 480180407090812462849339 := by
  unfold tailWord_935148
  simp only [CollatzResearch.WordTrace]
  refine ⟨17053824808062990704151049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22738433077417320938868065 17053824808062990704151049)
  ·
    refine ⟨12790368606047243028113287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17053824808062990704151049 12790368606047243028113287)
    ·
      refine ⟨19185552909070864542169931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12790368606047243028113287 19185552909070864542169931)
      ·
        refine ⟨28778329363606296813254897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19185552909070864542169931 28778329363606296813254897)
        ·
          refine ⟨21583747022704722609941173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28778329363606296813254897 21583747022704722609941173)
          ·
            refine ⟨2023476283378567744681985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21583747022704722609941173 2023476283378567744681985)
            ·
              refine ⟨1517607212533925808511489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2023476283378567744681985 1517607212533925808511489)
              ·
                refine ⟨1138205409400444356383617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1517607212533925808511489 1138205409400444356383617)
                ·
                  refine ⟨853654057050333267287713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1138205409400444356383617 853654057050333267287713)
                  ·
                    refine ⟨640240542787749950465785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 853654057050333267287713 640240542787749950465785)
                    ·
                      refine ⟨480180407090812462849339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 640240542787749950465785 480180407090812462849339)
                      ·
                        rfl

theorem cell23_935148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 2, 2].length) (baseStart_935148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_935148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_935148 prefixEnd_935148 := by exact prefixLift 935148
  have htrace : WordTrace (prefixWord ++ tailWord_935148) baseStart_935148 baseEnd_935148 := by
    simpa [prefixWord, tailWord_935148, baseEnd_935148] using wordTrace_append hprefix tailTrace_935148
  have hstable : (prefixWord ++ tailWord_935148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935148).length < 2 ^ (prefixWord ++ tailWord_935148).sum := by decide
  have hdescent : baseEnd_935148 < baseStart_935148 := by decide
  rcases family_descends (prefixWord ++ tailWord_935148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935204 : List Nat := [2, 3, 1, 3, 1, 1, 2, 1, 4, 1, 4]
def baseStart_935204 : Nat := 118140960795 + 935204 * 2 ^ 59
def prefixEnd_935204 : Nat := 4983230072969 + 3 ^ 40 * 935204 * 2
def baseEnd_935204 : Nat := 480209162007464243749081

theorem tailTrace_935204 : CollatzResearch.WordTrace tailWord_935204 prefixEnd_935204 480209162007464243749081 := by
  unfold tailWord_935204
  simp only [CollatzResearch.WordTrace]
  refine ⟨17054846051961551486170333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22739794735948735314893777 17054846051961551486170333)
  ·
    refine ⟨6395567269485581807313875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17054846051961551486170333 6395567269485581807313875)
    ·
      refine ⟨9593350904228372710970813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6395567269485581807313875 9593350904228372710970813)
      ·
        refine ⟨3597506589085639766614055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9593350904228372710970813 3597506589085639766614055)
        ·
          refine ⟨5396259883628459649921083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3597506589085639766614055 5396259883628459649921083)
          ·
            refine ⟨8094389825442689474881625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5396259883628459649921083 8094389825442689474881625)
            ·
              refine ⟨6070792369082017106161219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8094389825442689474881625 6070792369082017106161219)
              ·
                refine ⟨9106188553623025659241829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6070792369082017106161219 9106188553623025659241829)
                ·
                  refine ⟨1707410353804317311107843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9106188553623025659241829 1707410353804317311107843)
                  ·
                    refine ⟨2561115530706475966661765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1707410353804317311107843 2561115530706475966661765)
                    ·
                      refine ⟨480209162007464243749081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2561115530706475966661765 480209162007464243749081)
                      ·
                        rfl

theorem cell23_935204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_935204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_935204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_935204 prefixEnd_935204 := by exact prefixLift 935204
  have htrace : WordTrace (prefixWord ++ tailWord_935204) baseStart_935204 baseEnd_935204 := by
    simpa [prefixWord, tailWord_935204, baseEnd_935204] using wordTrace_append hprefix tailTrace_935204
  have hstable : (prefixWord ++ tailWord_935204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935204).length < 2 ^ (prefixWord ++ tailWord_935204).sum := by decide
  have hdescent : baseEnd_935204 < baseStart_935204 := by decide
  rcases family_descends (prefixWord ++ tailWord_935204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935221 : List Nat := [1, 3, 3, 1, 2, 2, 2, 1, 2, 4, 2]
def baseStart_935221 : Nat := 118140960795 + 935221 * 2 ^ 59
def prefixEnd_935221 : Nat := 4983230072969 + 3 ^ 40 * 935221 * 2
def baseEnd_935221 : Nat := 480217891178590677236503

theorem tailTrace_935221 : CollatzResearch.WordTrace tailWord_935221 prefixEnd_935221 480217891178590677236503 := by
  unfold tailWord_935221
  simp only [CollatzResearch.WordTrace]
  refine ⟨34110312144861514875709517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22740208096574343250473011 34110312144861514875709517)
  ·
    refine ⟨12791367054323068078391069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34110312144861514875709517 12791367054323068078391069)
    ·
      refine ⟨4796762645371150529396651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12791367054323068078391069 4796762645371150529396651)
      ·
        refine ⟨7195143968056725794094977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4796762645371150529396651 7195143968056725794094977)
        ·
          refine ⟨5396357976042544345571233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7195143968056725794094977 5396357976042544345571233)
          ·
            refine ⟨4047268482031908259178425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5396357976042544345571233 4047268482031908259178425)
            ·
              refine ⟨3035451361523931194383819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4047268482031908259178425 3035451361523931194383819)
              ·
                refine ⟨4553177042285896791575729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3035451361523931194383819 4553177042285896791575729)
                ·
                  refine ⟨3414882781714422593681797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4553177042285896791575729 3414882781714422593681797)
                  ·
                    refine ⟨640290521571454236315337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3414882781714422593681797 640290521571454236315337)
                    ·
                      refine ⟨480217891178590677236503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 640290521571454236315337 480217891178590677236503)
                      ·
                        rfl

theorem cell23_935221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 1, 2, 4, 2].length) (baseStart_935221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_935221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_935221 prefixEnd_935221 := by exact prefixLift 935221
  have htrace : WordTrace (prefixWord ++ tailWord_935221) baseStart_935221 baseEnd_935221 := by
    simpa [prefixWord, tailWord_935221, baseEnd_935221] using wordTrace_append hprefix tailTrace_935221
  have hstable : (prefixWord ++ tailWord_935221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935221).length < 2 ^ (prefixWord ++ tailWord_935221).sum := by decide
  have hdescent : baseEnd_935221 < baseStart_935221 := by decide
  rcases family_descends (prefixWord ++ tailWord_935221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935278 : List Nat := [4, 1, 2, 4, 1, 1, 1, 3, 6]
def baseStart_935278 : Nat := 118140960795 + 935278 * 2 ^ 59
def prefixEnd_935278 : Nat := 4983230072969 + 3 ^ 40 * 935278 * 2
def baseEnd_935278 : Nat := 53360795508432994913749

theorem tailTrace_935278 : CollatzResearch.WordTrace tailWord_935278 prefixEnd_935278 53360795508432994913749 := by
  unfold tailWord_935278
  simp only [CollatzResearch.WordTrace]
  refine ⟨4264048888206876701316811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22741594070436675740356325 4264048888206876701316811)
  ·
    refine ⟨6396073332310315051975217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4264048888206876701316811 6396073332310315051975217)
    ·
      refine ⟨4797054999232736288981413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6396073332310315051975217 4797054999232736288981413)
      ·
        refine ⟨899447812356138054184015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4797054999232736288981413 899447812356138054184015)
        ·
          refine ⟨1349171718534207081276023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 899447812356138054184015 1349171718534207081276023)
          ·
            refine ⟨2023757577801310621914035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1349171718534207081276023 2023757577801310621914035)
            ·
              refine ⟨3035636366701965932871053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2023757577801310621914035 3035636366701965932871053)
              ·
                refine ⟨1138363637513237224826645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3035636366701965932871053 1138363637513237224826645)
                ·
                  refine ⟨53360795508432994913749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1138363637513237224826645 53360795508432994913749)
                  ·
                    rfl

theorem cell23_935278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 3, 6].length) (baseStart_935278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_935278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_935278 prefixEnd_935278 := by exact prefixLift 935278
  have htrace : WordTrace (prefixWord ++ tailWord_935278) baseStart_935278 baseEnd_935278 := by
    simpa [prefixWord, tailWord_935278, baseEnd_935278] using wordTrace_append hprefix tailTrace_935278
  have hstable : (prefixWord ++ tailWord_935278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935278).length < 2 ^ (prefixWord ++ tailWord_935278).sum := by decide
  have hdescent : baseEnd_935278 < baseStart_935278 := by decide
  rcases family_descends (prefixWord ++ tailWord_935278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935304 : List Nat := [2, 1, 3, 3, 1, 2, 1, 1, 3, 6]
def baseStart_935304 : Nat := 118140960795 + 935304 * 2 ^ 59
def prefixEnd_935304 : Nat := 4983230072969 + 3 ^ 40 * 935304 * 2
def baseEnd_935304 : Nat := 160086836690971284166207

theorem tailTrace_935304 : CollatzResearch.WordTrace tailWord_935304 prefixEnd_935304 160086836690971284166207 := by
  unfold tailWord_935304
  simp only [CollatzResearch.WordTrace]
  refine ⟨17056669701780410025490483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22742226269040546700653977 17056669701780410025490483)
  ·
    refine ⟨25585004552670615038235725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17056669701780410025490483 25585004552670615038235725)
    ·
      refine ⟨9594376707251480639338397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25585004552670615038235725 9594376707251480639338397)
      ·
        refine ⟨3597891265219305239751899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9594376707251480639338397 3597891265219305239751899)
        ·
          refine ⟨5396836897828957859627849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3597891265219305239751899 5396836897828957859627849)
          ·
            refine ⟨4047627673371718394720887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5396836897828957859627849 4047627673371718394720887)
            ·
              refine ⟨6071441510057577592081331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4047627673371718394720887 6071441510057577592081331)
              ·
                refine ⟨9107162265086366388121997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6071441510057577592081331 9107162265086366388121997)
                ·
                  refine ⟨3415185849407387395545749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9107162265086366388121997 3415185849407387395545749)
                  ·
                    refine ⟨160086836690971284166207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3415185849407387395545749 160086836690971284166207)
                    ·
                      rfl

theorem cell23_935304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 1, 3, 6].length) (baseStart_935304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_935304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_935304 prefixEnd_935304 := by exact prefixLift 935304
  have htrace : WordTrace (prefixWord ++ tailWord_935304) baseStart_935304 baseEnd_935304 := by
    simpa [prefixWord, tailWord_935304, baseEnd_935304] using wordTrace_append hprefix tailTrace_935304
  have hstable : (prefixWord ++ tailWord_935304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935304).length < 2 ^ (prefixWord ++ tailWord_935304).sum := by decide
  have hdescent : baseEnd_935304 < baseStart_935304 := by decide
  rcases family_descends (prefixWord ++ tailWord_935304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935321 : List Nat := [1, 2, 1, 2, 1, 5, 1, 4, 2, 4]
def baseStart_935321 : Nat := 118140960795 + 935321 * 2 ^ 59
def prefixEnd_935321 : Nat := 4983230072969 + 3 ^ 40 * 935321 * 2
def baseEnd_935321 : Nat := 160089746414680095328681

theorem tailTrace_935321 : CollatzResearch.WordTrace tailWord_935321 prefixEnd_935321 160089746414680095328681 := by
  unfold tailWord_935321
  simp only [CollatzResearch.WordTrace]
  refine ⟨34113959444499231954349817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22742639629666154636233211 34113959444499231954349817)
  ·
    refine ⟨25585469583374423965762363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34113959444499231954349817 25585469583374423965762363)
    ·
      refine ⟨38378204375061635948643545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25585469583374423965762363 38378204375061635948643545)
      ·
        refine ⟨28783653281296226961482659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38378204375061635948643545 28783653281296226961482659)
        ·
          refine ⟨43175479921944340442223989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28783653281296226961482659 43175479921944340442223989)
          ·
            refine ⟨4047701242682281916458499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43175479921944340442223989 4047701242682281916458499)
            ·
              refine ⟨6071551864023422874687749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4047701242682281916458499 6071551864023422874687749)
              ·
                refine ⟨1138415974504391789003953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6071551864023422874687749 1138415974504391789003953)
                ·
                  refine ⟨853811980878293841752965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1138415974504391789003953 853811980878293841752965)
                  ·
                    refine ⟨160089746414680095328681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 853811980878293841752965 160089746414680095328681)
                    ·
                      rfl

theorem cell23_935321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 4, 2, 4].length) (baseStart_935321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_935321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_935321 prefixEnd_935321 := by exact prefixLift 935321
  have htrace : WordTrace (prefixWord ++ tailWord_935321) baseStart_935321 baseEnd_935321 := by
    simpa [prefixWord, tailWord_935321, baseEnd_935321] using wordTrace_append hprefix tailTrace_935321
  have hstable : (prefixWord ++ tailWord_935321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935321).length < 2 ^ (prefixWord ++ tailWord_935321).sum := by decide
  have hdescent : baseEnd_935321 < baseStart_935321 := by decide
  rcases family_descends (prefixWord ++ tailWord_935321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935328 : List Nat := [2, 1, 1, 4, 1, 2, 2, 3, 3, 2, 2]
def baseStart_935328 : Nat := 118140960795 + 935328 * 2 ^ 59
def prefixEnd_935328 : Nat := 4983230072969 + 3 ^ 40 * 935328 * 2
def baseEnd_935328 : Nat := 480272833608621758598511

theorem tailTrace_935328 : CollatzResearch.WordTrace tailWord_935328 prefixEnd_935328 480272833608621758598511 := by
  unfold tailWord_935328
  simp only [CollatzResearch.WordTrace]
  refine ⟨17057107377736936074927319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22742809836982581433236425 17057107377736936074927319)
  ·
    refine ⟨25585661066605404112390979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17057107377736936074927319 25585661066605404112390979)
    ·
      refine ⟨38378491599908106168586469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25585661066605404112390979 38378491599908106168586469)
      ·
        refine ⟨7195967174982769906609963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38378491599908106168586469 7195967174982769906609963)
        ·
          refine ⟨10793950762474154859914945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7195967174982769906609963 10793950762474154859914945)
          ·
            refine ⟨8095463071855616144936209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10793950762474154859914945 8095463071855616144936209)
            ·
              refine ⟨6071597303891712108702157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8095463071855616144936209 6071597303891712108702157)
              ·
                refine ⟨2276848988959392040763309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6071597303891712108702157 2276848988959392040763309)
                ·
                  refine ⟨853818370859772015286241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2276848988959392040763309 853818370859772015286241)
                  ·
                    refine ⟨640363778144829011464681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 853818370859772015286241 640363778144829011464681)
                    ·
                      refine ⟨480272833608621758598511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 640363778144829011464681 480272833608621758598511)
                      ·
                        rfl

theorem cell23_935328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 3, 3, 2, 2].length) (baseStart_935328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_935328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_935328 prefixEnd_935328 := by exact prefixLift 935328
  have htrace : WordTrace (prefixWord ++ tailWord_935328) baseStart_935328 baseEnd_935328 := by
    simpa [prefixWord, tailWord_935328, baseEnd_935328] using wordTrace_append hprefix tailTrace_935328
  have hstable : (prefixWord ++ tailWord_935328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935328).length < 2 ^ (prefixWord ++ tailWord_935328).sum := by decide
  have hdescent : baseEnd_935328 < baseStart_935328 := by decide
  rcases family_descends (prefixWord ++ tailWord_935328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935384 : List Nat := [2, 1, 2, 2, 2, 1, 2, 1, 1, 5, 4]
def baseStart_935384 : Nat := 118140960795 + 935384 * 2 ^ 59
def prefixEnd_935384 : Nat := 4983230072969 + 3 ^ 40 * 935384 * 2
def baseEnd_935384 : Nat := 480301588525273539498253

theorem tailTrace_935384 : CollatzResearch.WordTrace tailWord_935384 prefixEnd_935384 480301588525273539498253 := by
  unfold tailWord_935384
  simp only [CollatzResearch.WordTrace]
  refine ⟨17058128621635496856946603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22744171495513995809262137 17058128621635496856946603)
  ·
    refine ⟨25587192932453245285419905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17058128621635496856946603 25587192932453245285419905)
    ·
      refine ⟨19190394699339933964064929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25587192932453245285419905 19190394699339933964064929)
      ·
        refine ⟨14392796024504950473048697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19190394699339933964064929 14392796024504950473048697)
        ·
          refine ⟨10794597018378712854786523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14392796024504950473048697 10794597018378712854786523)
          ·
            refine ⟨16191895527568069282179785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10794597018378712854786523 16191895527568069282179785)
            ·
              refine ⟨12143921645676051961634839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16191895527568069282179785 12143921645676051961634839)
              ·
                refine ⟨18215882468514077942452259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12143921645676051961634839 18215882468514077942452259)
                ·
                  refine ⟨27323823702771116913678389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18215882468514077942452259 27323823702771116913678389)
                  ·
                    refine ⟨2561608472134792210657349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27323823702771116913678389 2561608472134792210657349)
                    ·
                      refine ⟨480301588525273539498253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2561608472134792210657349 480301588525273539498253)
                      ·
                        rfl

theorem cell23_935384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 1, 5, 4].length) (baseStart_935384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_935384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_935384 prefixEnd_935384 := by exact prefixLift 935384
  have htrace : WordTrace (prefixWord ++ tailWord_935384) baseStart_935384 baseEnd_935384 := by
    simpa [prefixWord, tailWord_935384, baseEnd_935384] using wordTrace_append hprefix tailTrace_935384
  have hstable : (prefixWord ++ tailWord_935384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935384).length < 2 ^ (prefixWord ++ tailWord_935384).sum := by decide
  have hdescent : baseEnd_935384 < baseStart_935384 := by decide
  rcases family_descends (prefixWord ++ tailWord_935384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935418 : List Nat := [3, 1, 1, 1, 1, 2, 3, 1, 6, 2, 2]
def baseStart_935418 : Nat := 118140960795 + 935418 * 2 ^ 59
def prefixEnd_935418 : Nat := 4983230072969 + 3 ^ 40 * 935418 * 2
def baseEnd_935418 : Nat := 480319046867526406473097

theorem tailTrace_935418 : CollatzResearch.WordTrace tailWord_935418 prefixEnd_935418 480319046867526406473097 := by
  unfold tailWord_935418
  simp only [CollatzResearch.WordTrace]
  refine ⟨8529374331286954380157727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22744998216765211680420605 8529374331286954380157727)
  ·
    refine ⟨12794061496930431570236591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8529374331286954380157727 12794061496930431570236591)
    ·
      refine ⟨19191092245395647355354887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12794061496930431570236591 19191092245395647355354887)
      ·
        refine ⟨28786638368093471033032331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19191092245395647355354887 28786638368093471033032331)
        ·
          refine ⟨43179957552140206549548497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28786638368093471033032331 43179957552140206549548497)
          ·
            refine ⟨32384968164105154912161373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43179957552140206549548497 32384968164105154912161373)
            ·
              refine ⟨12144363061539433092060515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32384968164105154912161373 12144363061539433092060515)
              ·
                refine ⟨18216544592309149638090773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12144363061539433092060515 18216544592309149638090773)
                ·
                  refine ⟨853900527764491389285505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 18216544592309149638090773 853900527764491389285505)
                  ·
                    refine ⟨640425395823368541964129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 853900527764491389285505 640425395823368541964129)
                    ·
                      refine ⟨480319046867526406473097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 640425395823368541964129 480319046867526406473097)
                      ·
                        rfl

theorem cell23_935418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 6, 2, 2].length) (baseStart_935418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_935418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_935418 prefixEnd_935418 := by exact prefixLift 935418
  have htrace : WordTrace (prefixWord ++ tailWord_935418) baseStart_935418 baseEnd_935418 := by
    simpa [prefixWord, tailWord_935418, baseEnd_935418] using wordTrace_append hprefix tailTrace_935418
  have hstable : (prefixWord ++ tailWord_935418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935418).length < 2 ^ (prefixWord ++ tailWord_935418).sum := by decide
  have hdescent : baseEnd_935418 < baseStart_935418 := by decide
  rcases family_descends (prefixWord ++ tailWord_935418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935421 : List Nat := [1, 4, 1, 1, 1, 5, 1, 1, 2, 1, 5]
def baseStart_935421 : Nat := 118140960795 + 935421 * 2 ^ 59
def prefixEnd_935421 : Nat := 4983230072969 + 3 ^ 40 * 935421 * 2
def baseEnd_935421 : Nat := 480320587309489894735583

theorem tailTrace_935421 : CollatzResearch.WordTrace tailWord_935421 prefixEnd_935421 480320587309489894735583 := by
  unfold tailWord_935421
  simp only [CollatzResearch.WordTrace]
  refine ⟨34117606744136949032990117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22745071162757966021993411 34117606744136949032990117)
  ·
    refine ⟨6397051264525677943685647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34117606744136949032990117 6397051264525677943685647)
    ·
      refine ⟨9595576896788516915528471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6397051264525677943685647 9595576896788516915528471)
      ·
        refine ⟨14393365345182775373292707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9595576896788516915528471 14393365345182775373292707)
        ·
          refine ⟨21590048017774163059939061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14393365345182775373292707 21590048017774163059939061)
          ·
            refine ⟨2024067001666327786869287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21590048017774163059939061 2024067001666327786869287)
            ·
              refine ⟨3036100502499491680303931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2024067001666327786869287 3036100502499491680303931)
              ·
                refine ⟨4554150753749237520455897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3036100502499491680303931 4554150753749237520455897)
                ·
                  refine ⟨3415613065311928140341923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4554150753749237520455897 3415613065311928140341923)
                  ·
                    refine ⟨5123419597967892210512885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3415613065311928140341923 5123419597967892210512885)
                    ·
                      refine ⟨480320587309489894735583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5123419597967892210512885 480320587309489894735583)
                      ·
                        rfl

theorem cell23_935421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 1, 2, 1, 5].length) (baseStart_935421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_935421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_935421 prefixEnd_935421 := by exact prefixLift 935421
  have htrace : WordTrace (prefixWord ++ tailWord_935421) baseStart_935421 baseEnd_935421 := by
    simpa [prefixWord, tailWord_935421, baseEnd_935421] using wordTrace_append hprefix tailTrace_935421
  have hstable : (prefixWord ++ tailWord_935421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935421).length < 2 ^ (prefixWord ++ tailWord_935421).sum := by decide
  have hdescent : baseEnd_935421 < baseStart_935421 := by decide
  rcases family_descends (prefixWord ++ tailWord_935421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935430 : List Nat := [6, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2]
def baseStart_935430 : Nat := 118140960795 + 935430 * 2 ^ 59
def prefixEnd_935430 : Nat := 4983230072969 + 3 ^ 40 * 935430 * 2
def baseEnd_935430 : Nat := 480325208635380359523043

theorem tailTrace_935430 : CollatzResearch.WordTrace tailWord_935430 prefixEnd_935430 480325208635380359523043 := by
  unfold tailWord_935430
  simp only [CollatzResearch.WordTrace]
  refine ⟨1066185468784510736564617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 22745290000736229046711829 1066185468784510736564617)
  ·
    refine ⟨799639101588383052423463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1066185468784510736564617 799639101588383052423463)
    ·
      refine ⟨1199458652382574578635195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 799639101588383052423463 1199458652382574578635195)
      ·
        refine ⟨1799187978573861867952793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1199458652382574578635195 1799187978573861867952793)
        ·
          refine ⟨1349390983930396400964595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1799187978573861867952793 1349390983930396400964595)
          ·
            refine ⟨2024086475895594601446893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1349390983930396400964595 2024086475895594601446893)
            ·
              refine ⟨759032428460847975542585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2024086475895594601446893 759032428460847975542585)
              ·
                refine ⟨569274321345635981656939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 759032428460847975542585 569274321345635981656939)
                ·
                  refine ⟨853911482018453972485409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 569274321345635981656939 853911482018453972485409)
                  ·
                    refine ⟨640433611513840479364057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 853911482018453972485409 640433611513840479364057)
                    ·
                      refine ⟨480325208635380359523043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 640433611513840479364057 480325208635380359523043)
                      ·
                        rfl

theorem cell23_935430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2].length) (baseStart_935430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_935430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_935430 prefixEnd_935430 := by exact prefixLift 935430
  have htrace : WordTrace (prefixWord ++ tailWord_935430) baseStart_935430 baseEnd_935430 := by
    simpa [prefixWord, tailWord_935430, baseEnd_935430] using wordTrace_append hprefix tailTrace_935430
  have hstable : (prefixWord ++ tailWord_935430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935430).length < 2 ^ (prefixWord ++ tailWord_935430).sum := by decide
  have hdescent : baseEnd_935430 < baseStart_935430 := by decide
  rcases family_descends (prefixWord ++ tailWord_935430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935481 : List Nat := [1, 2, 1, 5, 1, 2, 1, 2, 1, 2, 5]
def baseStart_935481 : Nat := 118140960795 + 935481 * 2 ^ 59
def prefixEnd_935481 : Nat := 4983230072969 + 3 ^ 40 * 935481 * 2
def baseEnd_935481 : Nat := 480351396148759659985307

theorem tailTrace_935481 : CollatzResearch.WordTrace tailWord_935481 prefixEnd_935481 480351396148759659985307 := by
  unfold tailWord_935481
  simp only [CollatzResearch.WordTrace]
  refine ⟨34119795123919579280174297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22746530082613052853449531 34119795123919579280174297)
  ·
    refine ⟨25589846342939684460130723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34119795123919579280174297 25589846342939684460130723)
    ·
      refine ⟨38384769514409526690196085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25589846342939684460130723 38384769514409526690196085)
      ·
        refine ⟨3598572141975893127205883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38384769514409526690196085 3598572141975893127205883)
        ·
          refine ⟨5397858212963839690808825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3598572141975893127205883 5397858212963839690808825)
          ·
            refine ⟨4048393659722879768106619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5397858212963839690808825 4048393659722879768106619)
            ·
              refine ⟨6072590489584319652159929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4048393659722879768106619 6072590489584319652159929)
              ·
                refine ⟨4554442867188239739119947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6072590489584319652159929 4554442867188239739119947)
                ·
                  refine ⟨6831664300782359608679921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4554442867188239739119947 6831664300782359608679921)
                  ·
                    refine ⟨5123748225586769706509941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6831664300782359608679921 5123748225586769706509941)
                    ·
                      refine ⟨480351396148759659985307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5123748225586769706509941 480351396148759659985307)
                      ·
                        rfl

theorem cell23_935481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_935481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_935481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_935481 prefixEnd_935481 := by exact prefixLift 935481
  have htrace : WordTrace (prefixWord ++ tailWord_935481) baseStart_935481 baseEnd_935481 := by
    simpa [prefixWord, tailWord_935481, baseEnd_935481] using wordTrace_append hprefix tailTrace_935481
  have hstable : (prefixWord ++ tailWord_935481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935481).length < 2 ^ (prefixWord ++ tailWord_935481).sum := by decide
  have hdescent : baseEnd_935481 < baseStart_935481 := by decide
  rcases family_descends (prefixWord ++ tailWord_935481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935525 : List Nat := [1, 3, 1, 3, 3, 3, 1, 1, 2, 1, 4]
def baseStart_935525 : Nat := 118140960795 + 935525 * 2 ^ 59
def prefixEnd_935525 : Nat := 4983230072969 + 3 ^ 40 * 935525 * 2
def baseEnd_935525 : Nat := 480373989297557487835105

theorem tailTrace_935525 : CollatzResearch.WordTrace tailWord_935525 prefixEnd_935525 480373989297557487835105 := by
  unfold tailWord_935525
  simp only [CollatzResearch.WordTrace]
  refine ⟨34121399935760174794776029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22747599957173449863184019 34121399935760174794776029)
  ·
    refine ⟨12795524975910065548041011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34121399935760174794776029 12795524975910065548041011)
    ·
      refine ⟨19193287463865098322061517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12795524975910065548041011 19193287463865098322061517)
      ·
        refine ⟨7197482798949411870773069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19193287463865098322061517 7197482798949411870773069)
        ·
          refine ⟨2699056049606029451539901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7197482798949411870773069 2699056049606029451539901)
          ·
            refine ⟨1012146018602261044327463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2699056049606029451539901 1012146018602261044327463)
            ·
              refine ⟨1518219027903391566491195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1012146018602261044327463 1518219027903391566491195)
              ·
                refine ⟨2277328541855087349736793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1518219027903391566491195 2277328541855087349736793)
                ·
                  refine ⟨1707996406391315512302595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2277328541855087349736793 1707996406391315512302595)
                  ·
                    refine ⟨2561994609586973268453893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1707996406391315512302595 2561994609586973268453893)
                    ·
                      refine ⟨480373989297557487835105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2561994609586973268453893 480373989297557487835105)
                      ·
                        rfl

theorem cell23_935525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 1, 1, 2, 1, 4].length) (baseStart_935525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_935525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_935525 prefixEnd_935525 := by exact prefixLift 935525
  have htrace : WordTrace (prefixWord ++ tailWord_935525) baseStart_935525 baseEnd_935525 := by
    simpa [prefixWord, tailWord_935525, baseEnd_935525] using wordTrace_append hprefix tailTrace_935525
  have hstable : (prefixWord ++ tailWord_935525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935525).length < 2 ^ (prefixWord ++ tailWord_935525).sum := by decide
  have hdescent : baseEnd_935525 < baseStart_935525 := by decide
  rcases family_descends (prefixWord ++ tailWord_935525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935561 : List Nat := [1, 2, 1, 1, 4, 1, 2, 1, 5, 5]
def baseStart_935561 : Nat := 118140960795 + 935561 * 2 ^ 59
def prefixEnd_935561 : Nat := 4983230072969 + 3 ^ 40 * 935561 * 2
def baseEnd_935561 : Nat := 160130824867039782328313

theorem tailTrace_935561 : CollatzResearch.WordTrace tailWord_935561 prefixEnd_935561 160130824867039782328313 := by
  unfold tailWord_935561
  simp only [CollatzResearch.WordTrace]
  refine ⟨34122712963629752943086537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22748475309086501962057691 34122712963629752943086537)
  ·
    refine ⟨25592034722722314707314903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34122712963629752943086537 25592034722722314707314903)
    ·
      refine ⟨38388052084083472060972355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25592034722722314707314903 38388052084083472060972355)
      ·
        refine ⟨57582078126125208091458533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38388052084083472060972355 57582078126125208091458533)
        ·
          refine ⟨10796639648648476517148475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57582078126125208091458533 10796639648648476517148475)
          ·
            refine ⟨16194959472972714775722713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10796639648648476517148475 16194959472972714775722713)
            ·
              refine ⟨12146219604729536081792035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16194959472972714775722713 12146219604729536081792035)
              ·
                refine ⟨18219329407094304122688053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12146219604729536081792035 18219329407094304122688053)
                ·
                  refine ⟨1708062131915091011502005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18219329407094304122688053 1708062131915091011502005)
                  ·
                    refine ⟨160130824867039782328313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1708062131915091011502005 160130824867039782328313)
                    ·
                      rfl

theorem cell23_935561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 5, 5].length) (baseStart_935561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_935561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_935561 prefixEnd_935561 := by exact prefixLift 935561
  have htrace : WordTrace (prefixWord ++ tailWord_935561) baseStart_935561 baseEnd_935561 := by
    simpa [prefixWord, tailWord_935561, baseEnd_935561] using wordTrace_append hprefix tailTrace_935561
  have hstable : (prefixWord ++ tailWord_935561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935561).length < 2 ^ (prefixWord ++ tailWord_935561).sum := by decide
  have hdescent : baseEnd_935561 < baseStart_935561 := by decide
  rcases family_descends (prefixWord ++ tailWord_935561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935575 : List Nat := [1, 1, 3, 3, 2, 2, 2, 2, 3, 1, 3]
def baseStart_935575 : Nat := 118140960795 + 935575 * 2 ^ 59
def prefixEnd_935575 : Nat := 4983230072969 + 3 ^ 40 * 935575 * 2
def baseEnd_935575 : Nat := 480399663330282292209875

theorem tailTrace_935575 : CollatzResearch.WordTrace tailWord_935575 prefixEnd_935575 480399663330282292209875 := by
  unfold tailWord_935575
  simp only [CollatzResearch.WordTrace]
  refine ⟨34123223585579033334096179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22748815723719355556064119 34123223585579033334096179)
  ·
    refine ⟨51184835378368550001144269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34123223585579033334096179 51184835378368550001144269)
    ·
      refine ⟨19194313266888206250429101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51184835378368550001144269 19194313266888206250429101)
      ·
        refine ⟨7197867475083077343910913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19194313266888206250429101 7197867475083077343910913)
        ·
          refine ⟨5398400606312308007933185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7197867475083077343910913 5398400606312308007933185)
          ·
            refine ⟨4048800454734231005949889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5398400606312308007933185 4048800454734231005949889)
            ·
              refine ⟨3036600341050673254462417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4048800454734231005949889 3036600341050673254462417)
              ·
                refine ⟨2277450255788004940846813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3036600341050673254462417 2277450255788004940846813)
                ·
                  refine ⟨854043845920501852817555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2277450255788004940846813 854043845920501852817555)
                  ·
                    refine ⟨1281065768880752779226333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 854043845920501852817555 1281065768880752779226333)
                    ·
                      refine ⟨480399663330282292209875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1281065768880752779226333 480399663330282292209875)
                      ·
                        rfl

theorem cell23_935575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 2, 3, 1, 3].length) (baseStart_935575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_935575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_935575 prefixEnd_935575 := by exact prefixLift 935575
  have htrace : WordTrace (prefixWord ++ tailWord_935575) baseStart_935575 baseEnd_935575 := by
    simpa [prefixWord, tailWord_935575, baseEnd_935575] using wordTrace_append hprefix tailTrace_935575
  have hstable : (prefixWord ++ tailWord_935575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935575).length < 2 ^ (prefixWord ++ tailWord_935575).sum := by decide
  have hdescent : baseEnd_935575 < baseStart_935575 := by decide
  rcases family_descends (prefixWord ++ tailWord_935575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935585 : List Nat := [1, 2, 3, 3, 2, 1, 2, 1, 1, 5, 2]
def baseStart_935585 : Nat := 118140960795 + 935585 * 2 ^ 59
def prefixEnd_935585 : Nat := 4983230072969 + 3 ^ 40 * 935585 * 2
def baseEnd_935585 : Nat := 480404798136827253084829

theorem tailTrace_935585 : CollatzResearch.WordTrace tailWord_935585 prefixEnd_935585 480404798136827253084829 := by
  unfold tailWord_935585
  simp only [CollatzResearch.WordTrace]
  refine ⟨34123588315542805041960209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22749058877028536694640139 34123588315542805041960209)
  ·
    refine ⟨25592691236657103781470157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34123588315542805041960209 25592691236657103781470157)
    ·
      refine ⟨9597259213746413918051309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25592691236657103781470157 9597259213746413918051309)
      ·
        refine ⟨3598972205154905219269241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9597259213746413918051309 3598972205154905219269241)
        ·
          refine ⟨2699229153866178914451931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3598972205154905219269241 2699229153866178914451931)
          ·
            refine ⟨4048843730799268371677897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2699229153866178914451931 4048843730799268371677897)
            ·
              refine ⟨3036632798099451278758423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4048843730799268371677897 3036632798099451278758423)
              ·
                refine ⟨4554949197149176918137635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3036632798099451278758423 4554949197149176918137635)
                ·
                  refine ⟨6832423795723765377206453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4554949197149176918137635 6832423795723765377206453)
                  ·
                    refine ⟨640539730849103004113105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6832423795723765377206453 640539730849103004113105)
                    ·
                      refine ⟨480404798136827253084829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 640539730849103004113105 480404798136827253084829)
                      ·
                        rfl

theorem cell23_935585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 1, 1, 5, 2].length) (baseStart_935585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_935585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_935585 prefixEnd_935585 := by exact prefixLift 935585
  have htrace : WordTrace (prefixWord ++ tailWord_935585) baseStart_935585 baseEnd_935585 := by
    simpa [prefixWord, tailWord_935585, baseEnd_935585] using wordTrace_append hprefix tailTrace_935585
  have hstable : (prefixWord ++ tailWord_935585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935585).length < 2 ^ (prefixWord ++ tailWord_935585).sum := by decide
  have hdescent : baseEnd_935585 < baseStart_935585 := by decide
  rcases family_descends (prefixWord ++ tailWord_935585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935586 : List Nat := [3, 3, 1, 4, 1, 2, 1, 3, 1, 4]
def baseStart_935586 : Nat := 118140960795 + 935586 * 2 ^ 59
def prefixEnd_935586 : Nat := 4983230072969 + 3 ^ 40 * 935586 * 2
def baseEnd_935586 : Nat := 160135103872493916390775

theorem tailTrace_935586 : CollatzResearch.WordTrace tailWord_935586 prefixEnd_935586 160135103872493916390775 := by
  unfold tailWord_935586
  simp only [CollatzResearch.WordTrace]
  refine ⟨8530906197134795553186653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22749083192359454808497741 8530906197134795553186653)
  ·
    refine ⟨3199089823925548332444995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8530906197134795553186653 3199089823925548332444995)
    ·
      refine ⟨4798634735888322498667493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3199089823925548332444995 4798634735888322498667493)
      ·
        refine ⟨899744012979060468500155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4798634735888322498667493 899744012979060468500155)
        ·
          refine ⟨1349616019468590702750233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 899744012979060468500155 1349616019468590702750233)
          ·
            refine ⟨1012212014601443027062675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1349616019468590702750233 1012212014601443027062675)
            ·
              refine ⟨1518318021902164540594013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1012212014601443027062675 1518318021902164540594013)
              ·
                refine ⟨569369258213311702722755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1518318021902164540594013 569369258213311702722755)
                ·
                  refine ⟨854053887319967554084133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 569369258213311702722755 854053887319967554084133)
                  ·
                    refine ⟨160135103872493916390775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 854053887319967554084133 160135103872493916390775)
                    ·
                      rfl

theorem cell23_935586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 1, 3, 1, 4].length) (baseStart_935586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_935586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_935586 prefixEnd_935586 := by exact prefixLift 935586
  have htrace : WordTrace (prefixWord ++ tailWord_935586) baseStart_935586 baseEnd_935586 := by
    simpa [prefixWord, tailWord_935586, baseEnd_935586] using wordTrace_append hprefix tailTrace_935586
  have hstable : (prefixWord ++ tailWord_935586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935586).length < 2 ^ (prefixWord ++ tailWord_935586).sum := by decide
  have hdescent : baseEnd_935586 < baseStart_935586 := by decide
  rcases family_descends (prefixWord ++ tailWord_935586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935629 : List Nat := [1, 6, 2, 1, 1, 3, 1, 2, 1, 5]
def baseStart_935629 : Nat := 118140960795 + 935629 * 2 ^ 59
def prefixEnd_935629 : Nat := 4983230072969 + 3 ^ 40 * 935629 * 2
def baseEnd_935629 : Nat := 160142463761875026978209

theorem tailTrace_935629 : CollatzResearch.WordTrace tailWord_935629 prefixEnd_935629 160142463761875026978209 := by
  unfold tailWord_935629
  simp only [CollatzResearch.WordTrace]
  refine ⟨34125193127383400556561941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22750128751588933704374627 34125193127383400556561941)
  ·
    refine ⟨1599618427846096901088841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 34125193127383400556561941 1599618427846096901088841)
    ·
      refine ⟨1199713820884572675816631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1599618427846096901088841 1199713820884572675816631)
      ·
        refine ⟨1799570731326859013724947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1199713820884572675816631 1799570731326859013724947)
        ·
          refine ⟨2699356096990288520587421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1799570731326859013724947 2699356096990288520587421)
          ·
            refine ⟨1012258536371358195220283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2699356096990288520587421 1012258536371358195220283)
            ·
              refine ⟨1518387804557037292830425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1012258536371358195220283 1518387804557037292830425)
              ·
                refine ⟨1138790853417777969622819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1518387804557037292830425 1138790853417777969622819)
                ·
                  refine ⟨1708186280126666954434229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1138790853417777969622819 1708186280126666954434229)
                  ·
                    refine ⟨160142463761875026978209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1708186280126666954434229 160142463761875026978209)
                    ·
                      rfl

theorem cell23_935629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_935629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_935629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_935629 prefixEnd_935629 := by exact prefixLift 935629
  have htrace : WordTrace (prefixWord ++ tailWord_935629) baseStart_935629 baseEnd_935629 := by
    simpa [prefixWord, tailWord_935629, baseEnd_935629] using wordTrace_append hprefix tailTrace_935629
  have hstable : (prefixWord ++ tailWord_935629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935629).length < 2 ^ (prefixWord ++ tailWord_935629).sum := by decide
  have hdescent : baseEnd_935629 < baseStart_935629 := by decide
  rcases family_descends (prefixWord ++ tailWord_935629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935648 : List Nat := [2, 1, 1, 3, 1, 2, 3, 1, 3, 3, 3]
def baseStart_935648 : Nat := 118140960795 + 935648 * 2 ^ 59
def prefixEnd_935648 : Nat := 4983230072969 + 3 ^ 40 * 935648 * 2
def baseEnd_935648 : Nat := 480437147418060506597039

theorem tailTrace_935648 : CollatzResearch.WordTrace tailWord_935648 prefixEnd_935648 480437147418060506597039 := by
  unfold tailWord_935648
  simp only [CollatzResearch.WordTrace]
  refine ⟨17062943057157283400751799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22750590742876377867669065 17062943057157283400751799)
  ·
    refine ⟨25594414585735925101127699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17062943057157283400751799 25594414585735925101127699)
    ·
      refine ⟨38391621878603887651691549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25594414585735925101127699 38391621878603887651691549)
      ·
        refine ⟨14396858204476457869384331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38391621878603887651691549 14396858204476457869384331)
        ·
          refine ⟨21595287306714686804076497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14396858204476457869384331 21595287306714686804076497)
          ·
            refine ⟨16196465480036015103057373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21595287306714686804076497 16196465480036015103057373)
            ·
              refine ⟨6073674555013505663646515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16196465480036015103057373 6073674555013505663646515)
              ·
                refine ⟨9110511832520258495469773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6073674555013505663646515 9110511832520258495469773)
                ·
                  refine ⟨3416441937195096935801165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9110511832520258495469773 3416441937195096935801165)
                  ·
                    refine ⟨1281165726448161350925437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3416441937195096935801165 1281165726448161350925437)
                    ·
                      refine ⟨480437147418060506597039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1281165726448161350925437 480437147418060506597039)
                      ·
                        rfl

theorem cell23_935648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 1, 3, 3, 3].length) (baseStart_935648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_935648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_935648 prefixEnd_935648 := by exact prefixLift 935648
  have htrace : WordTrace (prefixWord ++ tailWord_935648) baseStart_935648 baseEnd_935648 := by
    simpa [prefixWord, tailWord_935648, baseEnd_935648] using wordTrace_append hprefix tailTrace_935648
  have hstable : (prefixWord ++ tailWord_935648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935648).length < 2 ^ (prefixWord ++ tailWord_935648).sum := by decide
  have hdescent : baseEnd_935648 < baseStart_935648 := by decide
  rcases family_descends (prefixWord ++ tailWord_935648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935652 : List Nat := [2, 3, 1, 1, 1, 3, 5, 1, 1, 2, 3]
def baseStart_935652 : Nat := 118140960795 + 935652 * 2 ^ 59
def prefixEnd_935652 : Nat := 4983230072969 + 3 ^ 40 * 935652 * 2
def baseEnd_935652 : Nat := 480439201340678490947021

theorem tailTrace_935652 : CollatzResearch.WordTrace tailWord_935652 prefixEnd_935652 480439201340678490947021 := by
  unfold tailWord_935652
  simp only [CollatzResearch.WordTrace]
  refine ⟨17063016003150037742324605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22750688004200050323099473 17063016003150037742324605)
  ·
    refine ⟨6398631001181264153371727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17063016003150037742324605 6398631001181264153371727)
    ·
      refine ⟨9597946501771896230057591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6398631001181264153371727 9597946501771896230057591)
      ·
        refine ⟨14396919752657844345086387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9597946501771896230057591 14396919752657844345086387)
        ·
          refine ⟨21595379628986766517629581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14396919752657844345086387 21595379628986766517629581)
          ·
            refine ⟨8098267360870037444111093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21595379628986766517629581 8098267360870037444111093)
            ·
              refine ⟨759212565081566010385415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8098267360870037444111093 759212565081566010385415)
              ·
                refine ⟨1138818847622349015578123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 759212565081566010385415 1138818847622349015578123)
                ·
                  refine ⟨1708228271433523523367185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1138818847622349015578123 1708228271433523523367185)
                  ·
                    refine ⟨1281171203575142642525389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1708228271433523523367185 1281171203575142642525389)
                    ·
                      refine ⟨480439201340678490947021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1281171203575142642525389 480439201340678490947021)
                      ·
                        rfl

theorem cell23_935652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 5, 1, 1, 2, 3].length) (baseStart_935652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_935652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_935652 prefixEnd_935652 := by exact prefixLift 935652
  have htrace : WordTrace (prefixWord ++ tailWord_935652) baseStart_935652 baseEnd_935652 := by
    simpa [prefixWord, tailWord_935652, baseEnd_935652] using wordTrace_append hprefix tailTrace_935652
  have hstable : (prefixWord ++ tailWord_935652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935652).length < 2 ^ (prefixWord ++ tailWord_935652).sum := by decide
  have hdescent : baseEnd_935652 < baseStart_935652 := by decide
  rcases family_descends (prefixWord ++ tailWord_935652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935655 : List Nat := [1, 1, 5, 4, 2, 10]
def baseStart_935655 : Nat := 118140960795 + 935655 * 2 ^ 59
def prefixEnd_935655 : Nat := 4983230072969 + 3 ^ 40 * 935655 * 2
def baseEnd_935655 : Nat := 1977122394167250943249

theorem tailTrace_935655 : CollatzResearch.WordTrace tailWord_935655 prefixEnd_935655 1977122394167250943249 := by
  unfold tailWord_935655
  simp only [CollatzResearch.WordTrace]
  refine ⟨34126141425289206997008419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22750760950192804664672279 34126141425289206997008419)
  ·
    refine ⟨51189212137933810495512629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34126141425289206997008419 51189212137933810495512629)
    ·
      refine ⟨4798988637931294733954309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51189212137933810495512629 4798988637931294733954309)
      ·
        refine ⟨899810369612117762616433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4798988637931294733954309 899810369612117762616433)
        ·
          refine ⟨674857777209088321962325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 899810369612117762616433 674857777209088321962325)
          ·
            refine ⟨1977122394167250943249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 674857777209088321962325 1977122394167250943249)
            ·
              rfl

theorem cell23_935655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 10].length) (baseStart_935655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_935655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_935655 prefixEnd_935655 := by exact prefixLift 935655
  have htrace : WordTrace (prefixWord ++ tailWord_935655) baseStart_935655 baseEnd_935655 := by
    simpa [prefixWord, tailWord_935655, baseEnd_935655] using wordTrace_append hprefix tailTrace_935655
  have hstable : (prefixWord ++ tailWord_935655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935655).length < 2 ^ (prefixWord ++ tailWord_935655).sum := by decide
  have hdescent : baseEnd_935655 < baseStart_935655 := by decide
  rcases family_descends (prefixWord ++ tailWord_935655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935682 : List Nat := [3, 4, 1, 1, 1, 1, 4, 1, 1, 3, 3]
def baseStart_935682 : Nat := 118140960795 + 935682 * 2 ^ 59
def prefixEnd_935682 : Nat := 4983230072969 + 3 ^ 40 * 935682 * 2
def baseEnd_935682 : Nat := 480454605760313373571883

theorem tailTrace_935682 : CollatzResearch.WordTrace tailWord_935682 prefixEnd_935682 480454605760313373571883 := by
  unfold tailWord_935682
  simp only [CollatzResearch.WordTrace]
  refine ⟨8531781549047847652060325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22751417464127593738827533 8531781549047847652060325)
  ·
    refine ⟨1599709040446471434761311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8531781549047847652060325 1599709040446471434761311)
    ·
      refine ⟨2399563560669707152141967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1599709040446471434761311 2399563560669707152141967)
      ·
        refine ⟨3599345341004560728212951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2399563560669707152141967 3599345341004560728212951)
        ·
          refine ⟨5399018011506841092319427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3599345341004560728212951 5399018011506841092319427)
          ·
            refine ⟨8098527017260261638479141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5399018011506841092319427 8098527017260261638479141)
            ·
              refine ⟨1518473815736299057214839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8098527017260261638479141 1518473815736299057214839)
              ·
                refine ⟨2277710723604448585822259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1518473815736299057214839 2277710723604448585822259)
                ·
                  refine ⟨3416566085406672878733389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2277710723604448585822259 3416566085406672878733389)
                  ·
                    refine ⟨1281212282027502329525021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3416566085406672878733389 1281212282027502329525021)
                    ·
                      refine ⟨480454605760313373571883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1281212282027502329525021 480454605760313373571883)
                      ·
                        rfl

theorem cell23_935682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 4, 1, 1, 3, 3].length) (baseStart_935682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_935682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_935682 prefixEnd_935682 := by exact prefixLift 935682
  have htrace : WordTrace (prefixWord ++ tailWord_935682) baseStart_935682 baseEnd_935682 := by
    simpa [prefixWord, tailWord_935682, baseEnd_935682] using wordTrace_append hprefix tailTrace_935682
  have hstable : (prefixWord ++ tailWord_935682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935682).length < 2 ^ (prefixWord ++ tailWord_935682).sum := by decide
  have hdescent : baseEnd_935682 < baseStart_935682 := by decide
  rcases family_descends (prefixWord ++ tailWord_935682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935688 : List Nat := [2, 1, 3, 2, 2, 1, 1, 2, 2, 3, 4]
def baseStart_935688 : Nat := 118140960795 + 935688 * 2 ^ 59
def prefixEnd_935688 : Nat := 4983230072969 + 3 ^ 40 * 935688 * 2
def baseEnd_935688 : Nat := 480457686644240350096855

theorem tailTrace_935688 : CollatzResearch.WordTrace tailWord_935688 prefixEnd_935688 480457686644240350096855 := by
  unfold tailWord_935688
  simp only [CollatzResearch.WordTrace]
  refine ⟨17063672517084826816479859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22751563356113102421973145 17063672517084826816479859)
  ·
    refine ⟨25595508775627240224719789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17063672517084826816479859 25595508775627240224719789)
    ·
      refine ⟨9598315790860215084269921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25595508775627240224719789 9598315790860215084269921)
      ·
        refine ⟨7198736843145161313202441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9598315790860215084269921 7198736843145161313202441)
        ·
          refine ⟨5399052632358870984901831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7198736843145161313202441 5399052632358870984901831)
          ·
            refine ⟨8098578948538306477352747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5399052632358870984901831 8098578948538306477352747)
            ·
              refine ⟨12147868422807459716029121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8098578948538306477352747 12147868422807459716029121)
              ·
                refine ⟨9110901317105594787021841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12147868422807459716029121 9110901317105594787021841)
                ·
                  refine ⟨6833175987829196090266381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9110901317105594787021841 6833175987829196090266381)
                  ·
                    refine ⟨2562440995435948533849893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6833175987829196090266381 2562440995435948533849893)
                    ·
                      refine ⟨480457686644240350096855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2562440995435948533849893 480457686644240350096855)
                      ·
                        rfl

theorem cell23_935688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 2, 2, 3, 4].length) (baseStart_935688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_935688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_935688 prefixEnd_935688 := by exact prefixLift 935688
  have htrace : WordTrace (prefixWord ++ tailWord_935688) baseStart_935688 baseEnd_935688 := by
    simpa [prefixWord, tailWord_935688, baseEnd_935688] using wordTrace_append hprefix tailTrace_935688
  have hstable : (prefixWord ++ tailWord_935688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935688).length < 2 ^ (prefixWord ++ tailWord_935688).sum := by decide
  have hdescent : baseEnd_935688 < baseStart_935688 := by decide
  rcases family_descends (prefixWord ++ tailWord_935688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935700 : List Nat := [2, 4, 4, 1, 2, 1, 2, 1, 1, 1, 4]
def baseStart_935700 : Nat := 118140960795 + 935700 * 2 ^ 59
def prefixEnd_935700 : Nat := 4983230072969 + 3 ^ 40 * 935700 * 2
def baseEnd_935700 : Nat := 480463848412094303146801

theorem tailTrace_935700 : CollatzResearch.WordTrace tailWord_935700 prefixEnd_935700 480463848412094303146801 := by
  unfold tailWord_935700
  simp only [CollatzResearch.WordTrace]
  refine ⟨17063891355063089841198277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22751855140084119788264369 17063891355063089841198277)
  ·
    refine ⟨3199479629074329345224677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17063891355063089841198277 3199479629074329345224677)
    ·
      refine ⟨599902430451436752229627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3199479629074329345224677 599902430451436752229627)
      ·
        refine ⟨899853645677155128344441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 599902430451436752229627 899853645677155128344441)
        ·
          refine ⟨674890234257866346258331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 899853645677155128344441 674890234257866346258331)
          ·
            refine ⟨1012335351386799519387497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 674890234257866346258331 1012335351386799519387497)
            ·
              refine ⟨759251513540099639540623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1012335351386799519387497 759251513540099639540623)
              ·
                refine ⟨1138877270310149459310935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 759251513540099639540623 1138877270310149459310935)
                ·
                  refine ⟨1708315905465224188966403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1138877270310149459310935 1708315905465224188966403)
                  ·
                    refine ⟨2562473858197836283449605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1708315905465224188966403 2562473858197836283449605)
                    ·
                      refine ⟨480463848412094303146801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2562473858197836283449605 480463848412094303146801)
                      ·
                        rfl

theorem cell23_935700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_935700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_935700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_935700 prefixEnd_935700 := by exact prefixLift 935700
  have htrace : WordTrace (prefixWord ++ tailWord_935700) baseStart_935700 baseEnd_935700 := by
    simpa [prefixWord, tailWord_935700, baseEnd_935700] using wordTrace_append hprefix tailTrace_935700
  have hstable : (prefixWord ++ tailWord_935700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935700).length < 2 ^ (prefixWord ++ tailWord_935700).sum := by decide
  have hdescent : baseEnd_935700 < baseStart_935700 := by decide
  rcases family_descends (prefixWord ++ tailWord_935700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935708 : List Nat := [2, 2, 3, 1, 1, 2, 2, 1, 1, 3, 5]
def baseStart_935708 : Nat := 118140960795 + 935708 * 2 ^ 59
def prefixEnd_935708 : Nat := 4983230072969 + 3 ^ 40 * 935708 * 2
def baseEnd_935708 : Nat := 480467956257330271846763

theorem tailTrace_935708 : CollatzResearch.WordTrace tailWord_935708 prefixEnd_935708 480467956257330271846763 := by
  unfold tailWord_935708
  simp only [CollatzResearch.WordTrace]
  refine ⟨17064037247048598524343889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22752049662731464699125185 17064037247048598524343889)
  ·
    refine ⟨12798027935286448893257917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17064037247048598524343889 12798027935286448893257917)
    ·
      refine ⟨4799260475732418334971719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12798027935286448893257917 4799260475732418334971719)
      ·
        refine ⟨7198890713598627502457579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4799260475732418334971719 7198890713598627502457579)
        ·
          refine ⟨10798336070397941253686369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7198890713598627502457579 10798336070397941253686369)
          ·
            refine ⟨8098752052798455940264777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10798336070397941253686369 8098752052798455940264777)
            ·
              refine ⟨6074064039598841955198583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8098752052798455940264777 6074064039598841955198583)
              ·
                refine ⟨9111096059398262932797875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6074064039598841955198583 9111096059398262932797875)
                ·
                  refine ⟨13666644089097394399196813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9111096059398262932797875 13666644089097394399196813)
                  ·
                    refine ⟨5124991533411522899698805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13666644089097394399196813 5124991533411522899698805)
                    ·
                      refine ⟨480467956257330271846763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5124991533411522899698805 480467956257330271846763)
                      ·
                        rfl

theorem cell23_935708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 1, 1, 3, 5].length) (baseStart_935708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_935708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_935708 prefixEnd_935708 := by exact prefixLift 935708
  have htrace : WordTrace (prefixWord ++ tailWord_935708) baseStart_935708 baseEnd_935708 := by
    simpa [prefixWord, tailWord_935708, baseEnd_935708] using wordTrace_append hprefix tailTrace_935708
  have hstable : (prefixWord ++ tailWord_935708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935708).length < 2 ^ (prefixWord ++ tailWord_935708).sum := by decide
  have hdescent : baseEnd_935708 < baseStart_935708 := by decide
  rcases family_descends (prefixWord ++ tailWord_935708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935762 : List Nat := [3, 2, 2, 1, 1, 3, 3, 3, 5]
def baseStart_935762 : Nat := 118140960795 + 935762 * 2 ^ 59
def prefixEnd_935762 : Nat := 4983230072969 + 3 ^ 40 * 935762 * 2
def baseEnd_935762 : Nat := 53388409356963673396835

theorem tailTrace_935762 : CollatzResearch.WordTrace tailWord_935762 prefixEnd_935762 53388409356963673396835 := by
  unfold tailWord_935762
  simp only [CollatzResearch.WordTrace]
  refine ⟨8532511008975391067788385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22753362690601042847435693 8532511008975391067788385)
  ·
    refine ⟨6399383256731543300841289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8532511008975391067788385 6399383256731543300841289)
    ·
      refine ⟨4799537442548657475630967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6399383256731543300841289 4799537442548657475630967)
      ·
        refine ⟨7199306163822986213446451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4799537442548657475630967 7199306163822986213446451)
        ·
          refine ⟨10798959245734479320169677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7199306163822986213446451 10798959245734479320169677)
          ·
            refine ⟨4049609717150429745063629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10798959245734479320169677 4049609717150429745063629)
            ·
              refine ⟨1518603643931411154398861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4049609717150429745063629 1518603643931411154398861)
              ·
                refine ⟨569476366474279182899573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1518603643931411154398861 569476366474279182899573)
                ·
                  refine ⟨53388409356963673396835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 569476366474279182899573 53388409356963673396835)
                  ·
                    rfl

theorem cell23_935762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 3, 3, 5].length) (baseStart_935762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_935762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_935762 prefixEnd_935762 := by exact prefixLift 935762
  have htrace : WordTrace (prefixWord ++ tailWord_935762) baseStart_935762 baseEnd_935762 := by
    simpa [prefixWord, tailWord_935762, baseEnd_935762] using wordTrace_append hprefix tailTrace_935762
  have hstable : (prefixWord ++ tailWord_935762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935762).length < 2 ^ (prefixWord ++ tailWord_935762).sum := by decide
  have hdescent : baseEnd_935762 < baseStart_935762 := by decide
  rcases family_descends (prefixWord ++ tailWord_935762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935775 : List Nat := [1, 1, 2, 3, 1, 5, 1, 2, 2, 5]
def baseStart_935775 : Nat := 118140960795 + 935775 * 2 ^ 59
def prefixEnd_935775 : Nat := 4983230072969 + 3 ^ 40 * 935775 * 2
def baseEnd_935775 : Nat := 160167453153727169902985

theorem tailTrace_935775 : CollatzResearch.WordTrace tailWord_935775 prefixEnd_935775 160167453153727169902985 := by
  unfold tailWord_935775
  simp only [CollatzResearch.WordTrace]
  refine ⟨34130518184854467491376779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22753678789902978327584519 34130518184854467491376779)
  ·
    refine ⟨51195777277281701237065169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34130518184854467491376779 51195777277281701237065169)
    ·
      refine ⟨38396832957961275927798877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51195777277281701237065169 38396832957961275927798877)
      ·
        refine ⟨14398812359235478472924579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38396832957961275927798877 14398812359235478472924579)
        ·
          refine ⟨21598218538853217709386869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14398812359235478472924579 21598218538853217709386869)
          ·
            refine ⟨2024832988017489160255019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21598218538853217709386869 2024832988017489160255019)
            ·
              refine ⟨3037249482026233740382529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2024832988017489160255019 3037249482026233740382529)
              ·
                refine ⟨2277937111519675305286897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3037249482026233740382529 2277937111519675305286897)
                ·
                  refine ⟨1708452833639756478965173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2277937111519675305286897 1708452833639756478965173)
                  ·
                    refine ⟨160167453153727169902985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1708452833639756478965173 160167453153727169902985)
                    ·
                      rfl

theorem cell23_935775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 2, 2, 5].length) (baseStart_935775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_935775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_935775 prefixEnd_935775 := by exact prefixLift 935775
  have htrace : WordTrace (prefixWord ++ tailWord_935775) baseStart_935775 baseEnd_935775 := by
    simpa [prefixWord, tailWord_935775, baseEnd_935775] using wordTrace_append hprefix tailTrace_935775
  have hstable : (prefixWord ++ tailWord_935775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935775).length < 2 ^ (prefixWord ++ tailWord_935775).sum := by decide
  have hdescent : baseEnd_935775 < baseStart_935775 := by decide
  rcases family_descends (prefixWord ++ tailWord_935775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935779 : List Nat := [1, 1, 1, 5, 4, 1, 3, 2, 5]
def baseStart_935779 : Nat := 118140960795 + 935779 * 2 ^ 59
def prefixEnd_935779 : Nat := 4983230072969 + 3 ^ 40 * 935779 * 2
def baseEnd_935779 : Nat := 53389379264866610450993

theorem tailTrace_935779 : CollatzResearch.WordTrace tailWord_935779 prefixEnd_935779 53389379264866610450993 := by
  unfold tailWord_935779
  simp only [CollatzResearch.WordTrace]
  refine ⟨34130664076839976174522391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22753776051226650783014927 34130664076839976174522391)
  ·
    refine ⟨51195996115259964261783587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34130664076839976174522391 51195996115259964261783587)
    ·
      refine ⟨76793994172889946392675381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51195996115259964261783587 76793994172889946392675381)
      ·
        refine ⟨7199436953708432474313317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 76793994172889946392675381 7199436953708432474313317)
        ·
          refine ⟨1349894428820331088933747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7199436953708432474313317 1349894428820331088933747)
          ·
            refine ⟨2024841643230496633400621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1349894428820331088933747 2024841643230496633400621)
            ·
              refine ⟨759315616211436237525233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2024841643230496633400621 759315616211436237525233)
              ·
                refine ⟨569486712158577178143925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 759315616211436237525233 569486712158577178143925)
                ·
                  refine ⟨53389379264866610450993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 569486712158577178143925 53389379264866610450993)
                  ·
                    rfl

theorem cell23_935779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 3, 2, 5].length) (baseStart_935779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_935779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_935779 prefixEnd_935779 := by exact prefixLift 935779
  have htrace : WordTrace (prefixWord ++ tailWord_935779) baseStart_935779 baseEnd_935779 := by
    simpa [prefixWord, tailWord_935779, baseEnd_935779] using wordTrace_append hprefix tailTrace_935779
  have hstable : (prefixWord ++ tailWord_935779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935779).length < 2 ^ (prefixWord ++ tailWord_935779).sum := by decide
  have hdescent : baseEnd_935779 < baseStart_935779 := by decide
  rcases family_descends (prefixWord ++ tailWord_935779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935795 : List Nat := [1, 1, 1, 2, 2, 1, 3, 3, 1, 6, 2]
def baseStart_935795 : Nat := 118140960795 + 935795 * 2 ^ 59
def prefixEnd_935795 : Nat := 4983230072969 + 3 ^ 40 * 935795 * 2
def baseEnd_935795 : Nat := 480512629074271431458863

theorem tailTrace_935795 : CollatzResearch.WordTrace tailWord_935795 prefixEnd_935795 480512629074271431458863 := by
  unfold tailWord_935795
  simp only [CollatzResearch.WordTrace]
  refine ⟨34131247644782010907104839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22754165096521340604736559 34131247644782010907104839)
  ·
    refine ⟨51196871467173016360657259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34131247644782010907104839 51196871467173016360657259)
    ·
      refine ⟨76795307200759524540985889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51196871467173016360657259 76795307200759524540985889)
      ·
        refine ⟨57596480400569643405739417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76795307200759524540985889 57596480400569643405739417)
        ·
          refine ⟨43197360300427232554304563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57596480400569643405739417 43197360300427232554304563)
          ·
            refine ⟨64796040450640848831456845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43197360300427232554304563 64796040450640848831456845)
            ·
              refine ⟨24298515168990318311796317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64796040450640848831456845 24298515168990318311796317)
              ·
                refine ⟨9111943188371369366923619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24298515168990318311796317 9111943188371369366923619)
                ·
                  refine ⟨13667914782557054050385429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9111943188371369366923619 13667914782557054050385429)
                  ·
                    refine ⟨640683505432361908611817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13667914782557054050385429 640683505432361908611817)
                    ·
                      refine ⟨480512629074271431458863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 640683505432361908611817 480512629074271431458863)
                      ·
                        rfl

theorem cell23_935795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 3, 1, 6, 2].length) (baseStart_935795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_935795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_935795 prefixEnd_935795 := by exact prefixLift 935795
  have htrace : WordTrace (prefixWord ++ tailWord_935795) baseStart_935795 baseEnd_935795 := by
    simpa [prefixWord, tailWord_935795, baseEnd_935795] using wordTrace_append hprefix tailTrace_935795
  have hstable : (prefixWord ++ tailWord_935795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935795).length < 2 ^ (prefixWord ++ tailWord_935795).sum := by decide
  have hdescent : baseEnd_935795 < baseStart_935795 := by decide
  rcases family_descends (prefixWord ++ tailWord_935795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935805 : List Nat := [1, 4, 1, 1, 2, 1, 1, 3, 5, 4]
def baseStart_935805 : Nat := 118140960795 + 935805 * 2 ^ 59
def prefixEnd_935805 : Nat := 4983230072969 + 3 ^ 40 * 935805 * 2
def baseEnd_935805 : Nat := 160172587960272130777939

theorem tailTrace_935805 : CollatzResearch.WordTrace tailWord_935805 prefixEnd_935805 160172587960272130777939 := by
  unfold tailWord_935805
  simp only [CollatzResearch.WordTrace]
  refine ⟨34131612374745782614968869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22754408249830521743312579 34131612374745782614968869)
  ·
    refine ⟨6399677320264834240306663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34131612374745782614968869 6399677320264834240306663)
    ·
      refine ⟨9599515980397251360459995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6399677320264834240306663 9599515980397251360459995)
      ·
        refine ⟨14399273970595877040689993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9599515980397251360459995 14399273970595877040689993)
        ·
          refine ⟨10799455477946907780517495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14399273970595877040689993 10799455477946907780517495)
          ·
            refine ⟨16199183216920361670776243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10799455477946907780517495 16199183216920361670776243)
            ·
              refine ⟨24298774825380542506164365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16199183216920361670776243 24298774825380542506164365)
              ·
                refine ⟨9112040559517703439811637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24298774825380542506164365 9112040559517703439811637)
                ·
                  refine ⟨854253802454784697482341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9112040559517703439811637 854253802454784697482341)
                  ·
                    refine ⟨160172587960272130777939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 854253802454784697482341 160172587960272130777939)
                    ·
                      rfl

theorem cell23_935805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 3, 5, 4].length) (baseStart_935805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_935805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_935805 prefixEnd_935805 := by exact prefixLift 935805
  have htrace : WordTrace (prefixWord ++ tailWord_935805) baseStart_935805 baseEnd_935805 := by
    simpa [prefixWord, tailWord_935805, baseEnd_935805] using wordTrace_append hprefix tailTrace_935805
  have hstable : (prefixWord ++ tailWord_935805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935805).length < 2 ^ (prefixWord ++ tailWord_935805).sum := by decide
  have hdescent : baseEnd_935805 < baseStart_935805 := by decide
  rcases family_descends (prefixWord ++ tailWord_935805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935809 : List Nat := [1, 2, 4, 4, 1, 1, 2, 1, 2, 5]
def baseStart_935809 : Nat := 118140960795 + 935809 * 2 ^ 59
def prefixEnd_935809 : Nat := 4983230072969 + 3 ^ 40 * 935809 * 2
def baseEnd_935809 : Nat := 160173272601144792227933

theorem tailTrace_935809 : CollatzResearch.WordTrace tailWord_935809 prefixEnd_935809 160173272601144792227933 := by
  unfold tailWord_935809
  simp only [CollatzResearch.WordTrace]
  refine ⟨34131758266731291298114481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22754505511154194198742987 34131758266731291298114481)
  ·
    refine ⟨25598818700048468473585861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34131758266731291298114481 25598818700048468473585861)
    ·
      refine ⟨4799778506259087838797349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25598818700048468473585861 4799778506259087838797349)
      ·
        refine ⟨899958469923578969774503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4799778506259087838797349 899958469923578969774503)
        ·
          refine ⟨1349937704885368454661755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 899958469923578969774503 1349937704885368454661755)
          ·
            refine ⟨2024906557328052681992633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1349937704885368454661755 2024906557328052681992633)
            ·
              refine ⟨1518679917996039511494475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2024906557328052681992633 1518679917996039511494475)
              ·
                refine ⟨2278019876994059267241713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1518679917996039511494475 2278019876994059267241713)
                ·
                  refine ⟨1708514907745544450431285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2278019876994059267241713 1708514907745544450431285)
                  ·
                    refine ⟨160173272601144792227933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1708514907745544450431285 160173272601144792227933)
                    ·
                      rfl

theorem cell23_935809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 2, 1, 2, 5].length) (baseStart_935809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_935809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_935809 prefixEnd_935809 := by exact prefixLift 935809
  have htrace : WordTrace (prefixWord ++ tailWord_935809) baseStart_935809 baseEnd_935809 := by
    simpa [prefixWord, tailWord_935809, baseEnd_935809] using wordTrace_append hprefix tailTrace_935809
  have hstable : (prefixWord ++ tailWord_935809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935809).length < 2 ^ (prefixWord ++ tailWord_935809).sum := by decide
  have hdescent : baseEnd_935809 < baseStart_935809 := by decide
  rcases family_descends (prefixWord ++ tailWord_935809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935830 : List Nat := [5, 3, 1, 1, 2, 2, 2, 2, 5]
def baseStart_935830 : Nat := 118140960795 + 935830 * 2 ^ 59
def prefixEnd_935830 : Nat := 4983230072969 + 3 ^ 40 * 935830 * 2
def baseEnd_935830 : Nat := 53392288988575421613467

theorem tailTrace_935830 : CollatzResearch.WordTrace tailWord_935830 prefixEnd_935830 53392288988575421613467 := by
  unfold tailWord_935830
  simp only [CollatzResearch.WordTrace]
  refine ⟨2133282762478450742789309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22755016133103474589752629 2133282762478450742789309)
  ·
    refine ⟨799981035929419028545991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2133282762478450742789309 799981035929419028545991)
    ·
      refine ⟨1199971553894128542818987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 799981035929419028545991 1199971553894128542818987)
      ·
        refine ⟨1799957330841192814228481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1199971553894128542818987 1799957330841192814228481)
        ·
          refine ⟨1349967998130894610671361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1799957330841192814228481 1349967998130894610671361)
          ·
            refine ⟨1012475998598170958003521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1349967998130894610671361 1012475998598170958003521)
            ·
              refine ⟨759356998948628218502641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1012475998598170958003521 759356998948628218502641)
              ·
                refine ⟨569517749211471163876981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 759356998948628218502641 569517749211471163876981)
                ·
                  refine ⟨53392288988575421613467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 569517749211471163876981 53392288988575421613467)
                  ·
                    rfl

theorem cell23_935830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 2, 2, 5].length) (baseStart_935830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_935830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_935830 prefixEnd_935830 := by exact prefixLift 935830
  have htrace : WordTrace (prefixWord ++ tailWord_935830) baseStart_935830 baseEnd_935830 := by
    simpa [prefixWord, tailWord_935830, baseEnd_935830] using wordTrace_append hprefix tailTrace_935830
  have hstable : (prefixWord ++ tailWord_935830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935830).length < 2 ^ (prefixWord ++ tailWord_935830).sum := by decide
  have hdescent : baseEnd_935830 < baseStart_935830 := by decide
  rcases family_descends (prefixWord ++ tailWord_935830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935865 : List Nat := [1, 2, 1, 4, 2, 1, 1, 3, 3, 5]
def baseStart_935865 : Nat := 118140960795 + 935865 * 2 ^ 59
def prefixEnd_935865 : Nat := 4983230072969 + 3 ^ 40 * 935865 * 2
def baseEnd_935865 : Nat := 160182857573362052527847

theorem tailTrace_935865 : CollatzResearch.WordTrace tailWord_935865 prefixEnd_935865 160182857573362052527847 := by
  unfold tailWord_935865
  simp only [CollatzResearch.WordTrace]
  refine ⟨34133800754528412862153049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22755867169685608574768699 34133800754528412862153049)
  ·
    refine ⟨25600350565896309646614787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34133800754528412862153049 25600350565896309646614787)
    ·
      refine ⟨38400525848844464469922181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25600350565896309646614787 38400525848844464469922181)
      ·
        refine ⟨7200098596658337088110409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38400525848844464469922181 7200098596658337088110409)
        ·
          refine ⟨5400073947493752816082807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7200098596658337088110409 5400073947493752816082807)
          ·
            refine ⟨8100110921240629224124211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5400073947493752816082807 8100110921240629224124211)
            ·
              refine ⟨12150166381860943836186317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8100110921240629224124211 12150166381860943836186317)
              ·
                refine ⟨4556312393197853938569869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12150166381860943836186317 4556312393197853938569869)
                ·
                  refine ⟨1708617147449195226963701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4556312393197853938569869 1708617147449195226963701)
                  ·
                    refine ⟨160182857573362052527847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1708617147449195226963701 160182857573362052527847)
                    ·
                      rfl

theorem cell23_935865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 3, 3, 5].length) (baseStart_935865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_935865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_935865 prefixEnd_935865 := by exact prefixLift 935865
  have htrace : WordTrace (prefixWord ++ tailWord_935865) baseStart_935865 baseEnd_935865 := by
    simpa [prefixWord, tailWord_935865, baseEnd_935865] using wordTrace_append hprefix tailTrace_935865
  have hstable : (prefixWord ++ tailWord_935865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935865).length < 2 ^ (prefixWord ++ tailWord_935865).sum := by decide
  have hdescent : baseEnd_935865 < baseStart_935865 := by decide
  rcases family_descends (prefixWord ++ tailWord_935865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935872 : List Nat := [2, 1, 1, 2, 3, 2, 3, 1, 1, 5, 2]
def baseStart_935872 : Nat := 118140960795 + 935872 * 2 ^ 59
def prefixEnd_935872 : Nat := 4983230072969 + 3 ^ 40 * 935872 * 2
def baseEnd_935872 : Nat := 480552167084667630196009

theorem tailTrace_935872 : CollatzResearch.WordTrace tailWord_935872 prefixEnd_935872 480552167084667630196009 := by
  unfold tailWord_935872
  simp only [CollatzResearch.WordTrace]
  refine ⟨17067028032751526528828935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22756037377002035371771913 17067028032751526528828935)
  ·
    refine ⟨25600542049127289793243403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17067028032751526528828935 25600542049127289793243403)
    ·
      refine ⟨38400813073690934689865105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25600542049127289793243403 38400813073690934689865105)
      ·
        refine ⟨28800609805268201017398829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38400813073690934689865105 28800609805268201017398829)
        ·
          refine ⟨10800228676975575381524561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28800609805268201017398829 10800228676975575381524561)
          ·
            refine ⟨8100171507731681536143421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10800228676975575381524561 8100171507731681536143421)
            ·
              refine ⟨3037564315399380576053783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8100171507731681536143421 3037564315399380576053783)
              ·
                refine ⟨4556346473099070864080675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3037564315399380576053783 4556346473099070864080675)
                ·
                  refine ⟨6834519709648606296121013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4556346473099070864080675 6834519709648606296121013)
                  ·
                    refine ⟨640736222779556840261345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6834519709648606296121013 640736222779556840261345)
                    ·
                      refine ⟨480552167084667630196009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 640736222779556840261345 480552167084667630196009)
                      ·
                        rfl

theorem cell23_935872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 1, 1, 5, 2].length) (baseStart_935872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_935872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_935872 prefixEnd_935872 := by exact prefixLift 935872
  have htrace : WordTrace (prefixWord ++ tailWord_935872) baseStart_935872 baseEnd_935872 := by
    simpa [prefixWord, tailWord_935872, baseEnd_935872] using wordTrace_append hprefix tailTrace_935872
  have hstable : (prefixWord ++ tailWord_935872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935872).length < 2 ^ (prefixWord ++ tailWord_935872).sum := by decide
  have hdescent : baseEnd_935872 < baseStart_935872 := by decide
  rcases family_descends (prefixWord ++ tailWord_935872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935905 : List Nat := [1, 2, 3, 1, 2, 1, 3, 1, 3, 1, 5]
def baseStart_935905 : Nat := 118140960795 + 935905 * 2 ^ 59
def prefixEnd_935905 : Nat := 4983230072969 + 3 ^ 40 * 935905 * 2
def baseEnd_935905 : Nat := 480569111946266001083357

theorem tailTrace_935905 : CollatzResearch.WordTrace tailWord_935905 prefixEnd_935905 480569111946266001083357 := by
  unfold tailWord_935905
  simp only [CollatzResearch.WordTrace]
  refine ⟨34135259674383499693609169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22756839782922333129072779 34135259674383499693609169)
  ·
    refine ⟨25601444755787624770206877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34135259674383499693609169 25601444755787624770206877)
    ·
      refine ⟨9600541783420359288827579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25601444755787624770206877 9600541783420359288827579)
      ·
        refine ⟨14400812675130538933241369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9600541783420359288827579 14400812675130538933241369)
        ·
          refine ⟨10800609506347904199931027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14400812675130538933241369 10800609506347904199931027)
          ·
            refine ⟨16200914259521856299896541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10800609506347904199931027 16200914259521856299896541)
            ·
              refine ⟨6075342847320696112461203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16200914259521856299896541 6075342847320696112461203)
              ·
                refine ⟨9113014270981044168691805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6075342847320696112461203 9113014270981044168691805)
                ·
                  refine ⟨3417380351617891563259427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9113014270981044168691805 3417380351617891563259427)
                  ·
                    refine ⟨5126070527426837344889141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3417380351617891563259427 5126070527426837344889141)
                    ·
                      refine ⟨480569111946266001083357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5126070527426837344889141 480569111946266001083357)
                      ·
                        rfl

theorem cell23_935905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 1, 3, 1, 5].length) (baseStart_935905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_935905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_935905 prefixEnd_935905 := by exact prefixLift 935905
  have htrace : WordTrace (prefixWord ++ tailWord_935905) baseStart_935905 baseEnd_935905 := by
    simpa [prefixWord, tailWord_935905, baseEnd_935905] using wordTrace_append hprefix tailTrace_935905
  have hstable : (prefixWord ++ tailWord_935905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935905).length < 2 ^ (prefixWord ++ tailWord_935905).sum := by decide
  have hdescent : baseEnd_935905 < baseStart_935905 := by decide
  rcases family_descends (prefixWord ++ tailWord_935905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935919 : List Nat := [1, 1, 2, 1, 4, 2, 1, 4, 3, 2, 2]
def baseStart_935919 : Nat := 118140960795 + 935919 * 2 ^ 59
def prefixEnd_935919 : Nat := 4983230072969 + 3 ^ 40 * 935919 * 2
def baseEnd_935919 : Nat := 480576300675428946308293

theorem tailTrace_935919 : CollatzResearch.WordTrace tailWord_935919 prefixEnd_935919 480576300675428946308293 := by
  unfold tailWord_935919
  simp only [CollatzResearch.WordTrace]
  refine ⟨34135770296332780084618811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22757180197555186723079207 34135770296332780084618811)
  ·
    refine ⟨51203655444499170126928217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34135770296332780084618811 51203655444499170126928217)
    ·
      refine ⟨38402741583374377595196163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51203655444499170126928217 38402741583374377595196163)
      ·
        refine ⟨57604112375061566392794245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38402741583374377595196163 57604112375061566392794245)
        ·
          refine ⟨10800771070324043698648921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57604112375061566392794245 10800771070324043698648921)
          ·
            refine ⟨8100578302743032773986691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10800771070324043698648921 8100578302743032773986691)
            ·
              refine ⟨12150867454114549160980037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8100578302743032773986691 12150867454114549160980037)
              ·
                refine ⟨2278287647646477967683757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12150867454114549160980037 2278287647646477967683757)
                ·
                  refine ⟨854357867867429237881409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2278287647646477967683757 854357867867429237881409)
                  ·
                    refine ⟨640768400900571928411057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 854357867867429237881409 640768400900571928411057)
                    ·
                      refine ⟨480576300675428946308293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 640768400900571928411057 480576300675428946308293)
                      ·
                        rfl

theorem cell23_935919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 4, 3, 2, 2].length) (baseStart_935919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_935919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_935919 prefixEnd_935919 := by exact prefixLift 935919
  have htrace : WordTrace (prefixWord ++ tailWord_935919) baseStart_935919 baseEnd_935919 := by
    simpa [prefixWord, tailWord_935919, baseEnd_935919] using wordTrace_append hprefix tailTrace_935919
  have hstable : (prefixWord ++ tailWord_935919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935919).length < 2 ^ (prefixWord ++ tailWord_935919).sum := by decide
  have hdescent : baseEnd_935919 < baseStart_935919 := by decide
  rcases family_descends (prefixWord ++ tailWord_935919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935936 : List Nat := [2, 1, 1, 2, 1, 1, 1, 9, 1, 2, 2]
def baseStart_935936 : Nat := 118140960795 + 935936 * 2 ^ 59
def prefixEnd_935936 : Nat := 4983230072969 + 3 ^ 40 * 935936 * 2
def baseEnd_935936 : Nat := 480585029846555379795715

theorem tailTrace_935936 : CollatzResearch.WordTrace tailWord_935936 prefixEnd_935936 480585029846555379795715 := by
  unfold tailWord_935936
  simp only [CollatzResearch.WordTrace]
  refine ⟨17068195168635595993993831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22757593558180794658658441 17068195168635595993993831)
  ·
    refine ⟨25602292752953393990990747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17068195168635595993993831 25602292752953393990990747)
    ·
      refine ⟨38403439129430090986486121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25602292752953393990990747 38403439129430090986486121)
      ·
        refine ⟨28802579347072568239864591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38403439129430090986486121 28802579347072568239864591)
        ·
          refine ⟨43203869020608852359796887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28802579347072568239864591 43203869020608852359796887)
          ·
            refine ⟨64805803530913278539695331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43203869020608852359796887 64805803530913278539695331)
            ·
              refine ⟨97208705296369917809542997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64805803530913278539695331 97208705296369917809542997)
              ·
                refine ⟨569582257595917487165291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 97208705296369917809542997 569582257595917487165291)
                ·
                  refine ⟨854373386393876230747937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 569582257595917487165291 854373386393876230747937)
                  ·
                    refine ⟨640780039795407173060953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 854373386393876230747937 640780039795407173060953)
                    ·
                      refine ⟨480585029846555379795715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 640780039795407173060953 480585029846555379795715)
                      ·
                        rfl

theorem cell23_935936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 9, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 9, 1, 2, 2].length) (baseStart_935936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_935936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_935936 prefixEnd_935936 := by exact prefixLift 935936
  have htrace : WordTrace (prefixWord ++ tailWord_935936) baseStart_935936 baseEnd_935936 := by
    simpa [prefixWord, tailWord_935936, baseEnd_935936] using wordTrace_append hprefix tailTrace_935936
  have hstable : (prefixWord ++ tailWord_935936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935936).length < 2 ^ (prefixWord ++ tailWord_935936).sum := by decide
  have hdescent : baseEnd_935936 < baseStart_935936 := by decide
  rcases family_descends (prefixWord ++ tailWord_935936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_935979 : List Nat := [1, 1, 1, 1, 2, 1, 4, 6, 1, 3, 2]
def baseStart_935979 : Nat := 118140960795 + 935979 * 2 ^ 59
def prefixEnd_935979 : Nat := 4983230072969 + 3 ^ 40 * 935979 * 2
def baseEnd_935979 : Nat := 480607109514698711558017

theorem tailTrace_935979 : CollatzResearch.WordTrace tailWord_935979 prefixEnd_935979 480607109514698711558017 := by
  unfold tailWord_935979
  simp only [CollatzResearch.WordTrace]
  refine ⟨34137958676115410331802991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22758639117410273554535327 34137958676115410331802991)
  ·
    refine ⟨51206938014173115497704487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34137958676115410331802991 51206938014173115497704487)
    ·
      refine ⟨76810407021259673246556731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51206938014173115497704487 76810407021259673246556731)
      ·
        refine ⟨115215610531889509869835097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76810407021259673246556731 115215610531889509869835097)
        ·
          refine ⟨86411707898917132402376323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115215610531889509869835097 86411707898917132402376323)
          ·
            refine ⟨129617561848375698603564485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86411707898917132402376323 129617561848375698603564485)
            ·
              refine ⟨24303292846570443488168341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 129617561848375698603564485 24303292846570443488168341)
              ·
                refine ⟨1139216852182989538507891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 24303292846570443488168341 1139216852182989538507891)
                ·
                  refine ⟨1708825278274484307761837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1139216852182989538507891 1708825278274484307761837)
                  ·
                    refine ⟨640809479352931615410689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1708825278274484307761837 640809479352931615410689)
                    ·
                      refine ⟨480607109514698711558017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 640809479352931615410689 480607109514698711558017)
                      ·
                        rfl

theorem cell23_935979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 6, 1, 3, 2].length) (baseStart_935979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_935979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_935979 prefixEnd_935979 := by exact prefixLift 935979
  have htrace : WordTrace (prefixWord ++ tailWord_935979) baseStart_935979 baseEnd_935979 := by
    simpa [prefixWord, tailWord_935979, baseEnd_935979] using wordTrace_append hprefix tailTrace_935979
  have hstable : (prefixWord ++ tailWord_935979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_935979).length < 2 ^ (prefixWord ++ tailWord_935979).sum := by decide
  have hdescent : baseEnd_935979 < baseStart_935979 := by decide
  rcases family_descends (prefixWord ++ tailWord_935979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936005 : List Nat := [1, 3, 1, 1, 1, 3, 1, 1, 2, 3, 6]
def baseStart_936005 : Nat := 118140960795 + 936005 * 2 ^ 59
def prefixEnd_936005 : Nat := 4983230072969 + 3 ^ 40 * 936005 * 2
def baseEnd_936005 : Nat := 480620460011715609832897

theorem tailTrace_936005 : CollatzResearch.WordTrace tailWord_936005 prefixEnd_936005 480620460011715609832897 := by
  unfold tailWord_936005
  simp only [CollatzResearch.WordTrace]
  refine ⟨34138906974021216772249469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22759271316014144514832979 34138906974021216772249469)
  ·
    refine ⟨12802090115257956289593551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34138906974021216772249469 12802090115257956289593551)
    ·
      refine ⟨19203135172886934434390327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12802090115257956289593551 19203135172886934434390327)
      ·
        refine ⟨28804702759330401651585491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19203135172886934434390327 28804702759330401651585491)
        ·
          refine ⟨43207054138995602477378237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28804702759330401651585491 43207054138995602477378237)
          ·
            refine ⟨16202645302123350929016839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43207054138995602477378237 16202645302123350929016839)
            ·
              refine ⟨24303967953185026393525259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16202645302123350929016839 24303967953185026393525259)
              ·
                refine ⟨36455951929777539590287889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24303967953185026393525259 36455951929777539590287889)
                ·
                  refine ⟨27341963947333154692715917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36455951929777539590287889 27341963947333154692715917)
                  ·
                    refine ⟨10253236480249933009768469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27341963947333154692715917 10253236480249933009768469)
                    ·
                      refine ⟨480620460011715609832897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10253236480249933009768469 480620460011715609832897)
                      ·
                        rfl

theorem cell23_936005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 3, 6].length) (baseStart_936005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_936005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_936005 prefixEnd_936005 := by exact prefixLift 936005
  have htrace : WordTrace (prefixWord ++ tailWord_936005) baseStart_936005 baseEnd_936005 := by
    simpa [prefixWord, tailWord_936005, baseEnd_936005] using wordTrace_append hprefix tailTrace_936005
  have hstable : (prefixWord ++ tailWord_936005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936005).length < 2 ^ (prefixWord ++ tailWord_936005).sum := by decide
  have hdescent : baseEnd_936005 < baseStart_936005 := by decide
  rcases family_descends (prefixWord ++ tailWord_936005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936012 : List Nat := [2, 2, 1, 3, 1, 1, 3, 1, 2, 4, 3]
def baseStart_936012 : Nat := 118140960795 + 936012 * 2 ^ 59
def prefixEnd_936012 : Nat := 4983230072969 + 3 ^ 40 * 936012 * 2
def baseEnd_936012 : Nat := 480624054376297082445365

theorem tailTrace_936012 : CollatzResearch.WordTrace tailWord_936012 prefixEnd_936012 480624054376297082445365 := by
  unfold tailWord_936012
  simp only [CollatzResearch.WordTrace]
  refine ⟨17069581142497928483877145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22759441523330571311836193 17069581142497928483877145)
  ·
    refine ⟨12802185856873446362907859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17069581142497928483877145 12802185856873446362907859)
    ·
      refine ⟨19203278785310169544361789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12802185856873446362907859 19203278785310169544361789)
      ·
        refine ⟨7201229544491313579135671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19203278785310169544361789 7201229544491313579135671)
        ·
          refine ⟨10801844316736970368703507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7201229544491313579135671 10801844316736970368703507)
          ·
            refine ⟨16202766475105455553055261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10801844316736970368703507 16202766475105455553055261)
            ·
              refine ⟨6076037428164545832395723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16202766475105455553055261 6076037428164545832395723)
              ·
                refine ⟨9114056142246818748593585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6076037428164545832395723 9114056142246818748593585)
                ·
                  refine ⟨6835542106685114061445189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9114056142246818748593585 6835542106685114061445189)
                  ·
                    refine ⟨1281664145003458886520973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6835542106685114061445189 1281664145003458886520973)
                    ·
                      refine ⟨480624054376297082445365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1281664145003458886520973 480624054376297082445365)
                      ·
                        rfl

theorem cell23_936012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 1, 2, 4, 3].length) (baseStart_936012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_936012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_936012 prefixEnd_936012 := by exact prefixLift 936012
  have htrace : WordTrace (prefixWord ++ tailWord_936012) baseStart_936012 baseEnd_936012 := by
    simpa [prefixWord, tailWord_936012, baseEnd_936012] using wordTrace_append hprefix tailTrace_936012
  have hstable : (prefixWord ++ tailWord_936012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936012).length < 2 ^ (prefixWord ++ tailWord_936012).sum := by decide
  have hdescent : baseEnd_936012 < baseStart_936012 := by decide
  rcases family_descends (prefixWord ++ tailWord_936012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936026 : List Nat := [3, 1, 1, 2, 1, 1, 3, 5, 2, 2, 2]
def baseStart_936026 : Nat := 118140960795 + 936026 * 2 ^ 59
def prefixEnd_936026 : Nat := 4983230072969 + 3 ^ 40 * 936026 * 2
def baseEnd_936026 : Nat := 480631243105460027670301

theorem tailTrace_936026 : CollatzResearch.WordTrace tailWord_936026 prefixEnd_936026 480631243105460027670301 := by
  unfold tailWord_936026
  simp only [CollatzResearch.WordTrace]
  refine ⟨8534918226736284339690983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22759781937963424905842621 8534918226736284339690983)
  ·
    refine ⟨12802377340104426509536475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8534918226736284339690983 12802377340104426509536475)
    ·
      refine ⟨19203566010156639764304713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12802377340104426509536475 19203566010156639764304713)
      ·
        refine ⟨14402674507617479823228535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19203566010156639764304713 14402674507617479823228535)
        ·
          refine ⟨21604011761426219734842803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14402674507617479823228535 21604011761426219734842803)
          ·
            refine ⟨32406017642139329602264205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21604011761426219734842803 32406017642139329602264205)
            ·
              refine ⟨12152256615802248600849077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32406017642139329602264205 12152256615802248600849077)
              ·
                refine ⟨1139274057731460806329601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12152256615802248600849077 1139274057731460806329601)
                ·
                  refine ⟨854455543298595604747201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1139274057731460806329601 854455543298595604747201)
                  ·
                    refine ⟨640841657473946703560401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 854455543298595604747201 640841657473946703560401)
                    ·
                      refine ⟨480631243105460027670301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 640841657473946703560401 480631243105460027670301)
                      ·
                        rfl

theorem cell23_936026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 5, 2, 2, 2].length) (baseStart_936026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_936026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_936026 prefixEnd_936026 := by exact prefixLift 936026
  have htrace : WordTrace (prefixWord ++ tailWord_936026) baseStart_936026 baseEnd_936026 := by
    simpa [prefixWord, tailWord_936026, baseEnd_936026] using wordTrace_append hprefix tailTrace_936026
  have hstable : (prefixWord ++ tailWord_936026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936026).length < 2 ^ (prefixWord ++ tailWord_936026).sum := by decide
  have hdescent : baseEnd_936026 < baseStart_936026 := by decide
  rcases family_descends (prefixWord ++ tailWord_936026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936032 : List Nat := [2, 1, 1, 3, 2, 4, 1, 2, 7]
def baseStart_936032 : Nat := 118140960795 + 936032 * 2 ^ 59
def prefixEnd_936032 : Nat := 4983230072969 + 3 ^ 40 * 936032 * 2
def baseEnd_936032 : Nat := 53403813776598556021697

theorem tailTrace_936032 : CollatzResearch.WordTrace tailWord_936032 prefixEnd_936032 53403813776598556021697 := by
  unfold tailWord_936032
  simp only [CollatzResearch.WordTrace]
  refine ⟨17069945872461700191741175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22759927829948933588988233 17069945872461700191741175)
  ·
    refine ⟨25604918808692550287611763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17069945872461700191741175 25604918808692550287611763)
    ·
      refine ⟨38407378213038825431417645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25604918808692550287611763 38407378213038825431417645)
      ·
        refine ⟨14402766829889559536781617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38407378213038825431417645 14402766829889559536781617)
        ·
          refine ⟨10802075122417169652586213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14402766829889559536781617 10802075122417169652586213)
          ·
            refine ⟨2025389085453219309859915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10802075122417169652586213 2025389085453219309859915)
            ·
              refine ⟨3038083628179828964789873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2025389085453219309859915 3038083628179828964789873)
              ·
                refine ⟨2278562721134871723592405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3038083628179828964789873 2278562721134871723592405)
                ·
                  refine ⟨53403813776598556021697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2278562721134871723592405 53403813776598556021697)
                  ·
                    rfl

theorem cell23_936032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 2, 7].length) (baseStart_936032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_936032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_936032 prefixEnd_936032 := by exact prefixLift 936032
  have htrace : WordTrace (prefixWord ++ tailWord_936032) baseStart_936032 baseEnd_936032 := by
    simpa [prefixWord, tailWord_936032, baseEnd_936032] using wordTrace_append hprefix tailTrace_936032
  have hstable : (prefixWord ++ tailWord_936032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936032).length < 2 ^ (prefixWord ++ tailWord_936032).sum := by decide
  have hdescent : baseEnd_936032 < baseStart_936032 := by decide
  rcases family_descends (prefixWord ++ tailWord_936032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936049 : List Nat := [1, 2, 2, 2, 1, 1, 6, 3, 5]
def baseStart_936049 : Nat := 118140960795 + 936049 * 2 ^ 59
def prefixEnd_936049 : Nat := 4983230072969 + 3 ^ 40 * 936049 * 2
def baseEnd_936049 : Nat := 53404783684501493075855

theorem tailTrace_936049 : CollatzResearch.WordTrace tailWord_936049 prefixEnd_936049 53404783684501493075855 := by
  unfold tailWord_936049
  simp only [CollatzResearch.WordTrace]
  refine ⟨34140511785861812286851201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22760341190574541524567467 34140511785861812286851201)
  ·
    refine ⟨25605383839396359215138401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34140511785861812286851201 25605383839396359215138401)
    ·
      refine ⟨19204037879547269411353801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25605383839396359215138401 19204037879547269411353801)
      ·
        refine ⟨14403028409660452058515351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19204037879547269411353801 14403028409660452058515351)
        ·
          refine ⟨21604542614490678087773027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14403028409660452058515351 21604542614490678087773027)
          ·
            refine ⟨32406813921736017131659541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21604542614490678087773027 32406813921736017131659541)
            ·
              refine ⟨1519069402581375803046541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 32406813921736017131659541 1519069402581375803046541)
              ·
                refine ⟨569651025968015926142453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1519069402581375803046541 569651025968015926142453)
                ·
                  refine ⟨53404783684501493075855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 569651025968015926142453 53404783684501493075855)
                  ·
                    rfl

theorem cell23_936049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 6, 3, 5].length) (baseStart_936049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_936049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_936049 prefixEnd_936049 := by exact prefixLift 936049
  have htrace : WordTrace (prefixWord ++ tailWord_936049) baseStart_936049 baseEnd_936049 := by
    simpa [prefixWord, tailWord_936049, baseEnd_936049] using wordTrace_append hprefix tailTrace_936049
  have hstable : (prefixWord ++ tailWord_936049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936049).length < 2 ^ (prefixWord ++ tailWord_936049).sum := by decide
  have hdescent : baseEnd_936049 < baseStart_936049 := by decide
  rcases family_descends (prefixWord ++ tailWord_936049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936092 : List Nat := [2, 2, 3, 2, 1, 1, 1, 1, 2, 8]
def baseStart_936092 : Nat := 118140960795 + 936092 * 2 ^ 59
def prefixEnd_936092 : Nat := 4983230072969 + 3 ^ 40 * 936092 * 2
def baseEnd_936092 : Nat := 160221710942885589814999

theorem tailTrace_936092 : CollatzResearch.WordTrace tailWord_936092 prefixEnd_936092 160221710942885589814999 := by
  unfold tailWord_936092
  simp only [CollatzResearch.WordTrace]
  refine ⟨17071040062353015315333265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22761386749804020420444353 17071040062353015315333265)
  ·
    refine ⟨12803280046764761486499949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17071040062353015315333265 12803280046764761486499949)
    ·
      refine ⟨4801230017536785557437481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12803280046764761486499949 4801230017536785557437481)
      ·
        refine ⟨3600922513152589168078111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4801230017536785557437481 3600922513152589168078111)
        ·
          refine ⟨5401383769728883752117167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3600922513152589168078111 5401383769728883752117167)
          ·
            refine ⟨8102075654593325628175751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5401383769728883752117167 8102075654593325628175751)
            ·
              refine ⟨12153113481889988442263627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8102075654593325628175751 12153113481889988442263627)
              ·
                refine ⟨18229670222834982663395441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12153113481889988442263627 18229670222834982663395441)
                ·
                  refine ⟨13672252667126236997546581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18229670222834982663395441 13672252667126236997546581)
                  ·
                    refine ⟨160221710942885589814999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 13672252667126236997546581 160221710942885589814999)
                    ·
                      rfl

theorem cell23_936092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 2, 8].length) (baseStart_936092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_936092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_936092 prefixEnd_936092 := by exact prefixLift 936092
  have htrace : WordTrace (prefixWord ++ tailWord_936092) baseStart_936092 baseEnd_936092 := by
    simpa [prefixWord, tailWord_936092, baseEnd_936092] using wordTrace_append hprefix tailTrace_936092
  have hstable : (prefixWord ++ tailWord_936092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936092).length < 2 ^ (prefixWord ++ tailWord_936092).sum := by decide
  have hdescent : baseEnd_936092 < baseStart_936092 := by decide
  rcases family_descends (prefixWord ++ tailWord_936092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936119 : List Nat := [1, 1, 3, 1, 4, 2, 1, 1, 4, 2, 3]
def baseStart_936119 : Nat := 118140960795 + 936119 * 2 ^ 59
def prefixEnd_936119 : Nat := 4983230072969 + 3 ^ 40 * 936119 * 2
def baseEnd_936119 : Nat := 480678996806328163807373

theorem tailTrace_936119 : CollatzResearch.WordTrace tailWord_936119 prefixEnd_936119 480678996806328163807373 := by
  unfold tailWord_936119
  simp only [CollatzResearch.WordTrace]
  refine ⟨34143064895608214241899411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22762043263738809494599607 34143064895608214241899411)
  ·
    refine ⟨51214597343412321362849117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34143064895608214241899411 51214597343412321362849117)
    ·
      refine ⟨19205474003779620511068419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51214597343412321362849117 19205474003779620511068419)
      ·
        refine ⟨28808211005669430766602629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19205474003779620511068419 28808211005669430766602629)
        ·
          refine ⟨5401539563563018268737993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28808211005669430766602629 5401539563563018268737993)
          ·
            refine ⟨4051154672672263701553495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5401539563563018268737993 4051154672672263701553495)
            ·
              refine ⟨6076732009008395552330243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4051154672672263701553495 6076732009008395552330243)
              ·
                refine ⟨9115098013512593328495365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6076732009008395552330243 9115098013512593328495365)
                ·
                  refine ⟨1709080877533611249092881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9115098013512593328495365 1709080877533611249092881)
                  ·
                    refine ⟨1281810658150208436819661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1709080877533611249092881 1281810658150208436819661)
                    ·
                      refine ⟨480678996806328163807373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1281810658150208436819661 480678996806328163807373)
                      ·
                        rfl

theorem cell23_936119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 1, 4, 2, 3].length) (baseStart_936119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_936119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_936119 prefixEnd_936119 := by exact prefixLift 936119
  have htrace : WordTrace (prefixWord ++ tailWord_936119) baseStart_936119 baseEnd_936119 := by
    simpa [prefixWord, tailWord_936119, baseEnd_936119] using wordTrace_append hprefix tailTrace_936119
  have hstable : (prefixWord ++ tailWord_936119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936119).length < 2 ^ (prefixWord ++ tailWord_936119).sum := by decide
  have hdescent : baseEnd_936119 < baseStart_936119 := by decide
  rcases family_descends (prefixWord ++ tailWord_936119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936122 : List Nat := [3, 1, 1, 1, 2, 2, 4, 1, 8]
def baseStart_936122 : Nat := 118140960795 + 936122 * 2 ^ 59
def prefixEnd_936122 : Nat := 4983230072969 + 3 ^ 40 * 936122 * 2
def baseEnd_936122 : Nat := 53408948583143516896651

theorem tailTrace_936122 : CollatzResearch.WordTrace tailWord_936122 prefixEnd_936122 53408948583143516896651 := by
  unfold tailWord_936122
  simp only [CollatzResearch.WordTrace]
  refine ⟨8535793578649336438564655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22762116209731563836172413 8535793578649336438564655)
  ·
    refine ⟨12803690367974004657846983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8535793578649336438564655 12803690367974004657846983)
    ·
      refine ⟨19205535551961006986770475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12803690367974004657846983 19205535551961006986770475)
      ·
        refine ⟨28808303327941510480155713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19205535551961006986770475 28808303327941510480155713)
        ·
          refine ⟨21606227495956132860116785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28808303327941510480155713 21606227495956132860116785)
          ·
            refine ⟨16204670621967099645087589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21606227495956132860116785 16204670621967099645087589)
            ·
              refine ⟨3038375741618831183453923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16204670621967099645087589 3038375741618831183453923)
              ·
                refine ⟨4557563612428246775180885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3038375741618831183453923 4557563612428246775180885)
                ·
                  refine ⟨53408948583143516896651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4557563612428246775180885 53408948583143516896651)
                  ·
                    rfl

theorem cell23_936122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 1, 8].length) (baseStart_936122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_936122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_936122 prefixEnd_936122 := by exact prefixLift 936122
  have htrace : WordTrace (prefixWord ++ tailWord_936122) baseStart_936122 baseEnd_936122 := by
    simpa [prefixWord, tailWord_936122, baseEnd_936122] using wordTrace_append hprefix tailTrace_936122
  have hstable : (prefixWord ++ tailWord_936122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936122).length < 2 ^ (prefixWord ++ tailWord_936122).sum := by decide
  have hdescent : baseEnd_936122 < baseStart_936122 := by decide
  rcases family_descends (prefixWord ++ tailWord_936122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936206 : List Nat := [4, 1, 1, 2, 1, 2, 2, 4, 1, 1, 4]
def baseStart_936206 : Nat := 118140960795 + 936206 * 2 ^ 59
def prefixEnd_936206 : Nat := 4983230072969 + 3 ^ 40 * 936206 * 2
def baseEnd_936206 : Nat := 480723669623269323419473

theorem tailTrace_936206 : CollatzResearch.WordTrace tailWord_936206 prefixEnd_936206 480723669623269323419473 := by
  unfold tailWord_936206
  simp only [CollatzResearch.WordTrace]
  refine ⟨4268279755786628512539559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22764158697528685400210981 4268279755786628512539559)
  ·
    refine ⟨6402419633679942768809339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4268279755786628512539559 6402419633679942768809339)
    ·
      refine ⟨9603629450519914153214009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6402419633679942768809339 9603629450519914153214009)
      ·
        refine ⟨7202722087889935614910507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9603629450519914153214009 7202722087889935614910507)
        ·
          refine ⟨10804083131834903422365761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7202722087889935614910507 10804083131834903422365761)
          ·
            refine ⟨8103062348876177566774321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10804083131834903422365761 8103062348876177566774321)
            ·
              refine ⟨6077296761657133175080741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8103062348876177566774321 6077296761657133175080741)
              ·
                refine ⟨1139493142810712470327639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6077296761657133175080741 1139493142810712470327639)
                ·
                  refine ⟨1709239714216068705491459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1139493142810712470327639 1709239714216068705491459)
                  ·
                    refine ⟨2563859571324103058237189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1709239714216068705491459 2563859571324103058237189)
                    ·
                      refine ⟨480723669623269323419473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2563859571324103058237189 480723669623269323419473)
                      ·
                        rfl

theorem cell23_936206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 4, 1, 1, 4].length) (baseStart_936206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_936206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_936206 prefixEnd_936206 := by exact prefixLift 936206
  have htrace : WordTrace (prefixWord ++ tailWord_936206) baseStart_936206 baseEnd_936206 := by
    simpa [prefixWord, tailWord_936206, baseEnd_936206] using wordTrace_append hprefix tailTrace_936206
  have hstable : (prefixWord ++ tailWord_936206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936206).length < 2 ^ (prefixWord ++ tailWord_936206).sum := by decide
  have hdescent : baseEnd_936206 < baseStart_936206 := by decide
  rcases family_descends (prefixWord ++ tailWord_936206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936219 : List Nat := [1, 1, 1, 1, 1, 1, 8, 2, 1, 2, 4]
def baseStart_936219 : Nat := 118140960795 + 936219 * 2 ^ 59
def prefixEnd_936219 : Nat := 4983230072969 + 3 ^ 40 * 936219 * 2
def baseEnd_936219 : Nat := 480730344871777772556913

theorem tailTrace_936219 : CollatzResearch.WordTrace tailWord_936219 prefixEnd_936219 480730344871777772556913 := by
  unfold tailWord_936219
  simp only [CollatzResearch.WordTrace]
  refine ⟨34146712195245931320539711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22764474796830620880359807 34146712195245931320539711)
  ·
    refine ⟨51220068292868896980809567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34146712195245931320539711 51220068292868896980809567)
    ·
      refine ⟨76830102439303345471214351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51220068292868896980809567 76830102439303345471214351)
      ·
        refine ⟨115245153658955018206821527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76830102439303345471214351 115245153658955018206821527)
        ·
          refine ⟨172867730488432527310232291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115245153658955018206821527 172867730488432527310232291)
          ·
            refine ⟨259301595732648790965348437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172867730488432527310232291 259301595732648790965348437)
            ·
              refine ⟨3038690574991978019125177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 259301595732648790965348437 3038690574991978019125177)
              ·
                refine ⟨2279017931243983514343883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3038690574991978019125177 2279017931243983514343883)
                ·
                  refine ⟨3418526896865975271515825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2279017931243983514343883 3418526896865975271515825)
                  ·
                    refine ⟨2563895172649481453636869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3418526896865975271515825 2563895172649481453636869)
                    ·
                      refine ⟨480730344871777772556913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2563895172649481453636869 480730344871777772556913)
                      ·
                        rfl

theorem cell23_936219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 2, 1, 2, 4].length) (baseStart_936219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_936219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_936219 prefixEnd_936219 := by exact prefixLift 936219
  have htrace : WordTrace (prefixWord ++ tailWord_936219) baseStart_936219 baseEnd_936219 := by
    simpa [prefixWord, tailWord_936219, baseEnd_936219] using wordTrace_append hprefix tailTrace_936219
  have hstable : (prefixWord ++ tailWord_936219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936219).length < 2 ^ (prefixWord ++ tailWord_936219).sum := by decide
  have hdescent : baseEnd_936219 < baseStart_936219 := by decide
  rcases family_descends (prefixWord ++ tailWord_936219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936223 : List Nat := [1, 1, 2, 4, 3, 1, 4, 1, 1, 1, 4]
def baseStart_936223 : Nat := 118140960795 + 936223 * 2 ^ 59
def prefixEnd_936223 : Nat := 4983230072969 + 3 ^ 40 * 936223 * 2
def baseEnd_936223 : Nat := 480732398794395756906895

theorem tailTrace_936223 : CollatzResearch.WordTrace tailWord_936223 prefixEnd_936223 480732398794395756906895 := by
  unfold tailWord_936223
  simp only [CollatzResearch.WordTrace]
  refine ⟨34146858087231440003685323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22764572058154293335790215 34146858087231440003685323)
  ·
    refine ⟨51220287130847160005527985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34146858087231440003685323 51220287130847160005527985)
    ·
      refine ⟨38415215348135370004145989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51220287130847160005527985 38415215348135370004145989)
      ·
        refine ⟨7202852877775381875777373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38415215348135370004145989 7202852877775381875777373)
        ·
          refine ⟨2701069829165768203416515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7202852877775381875777373 2701069829165768203416515)
          ·
            refine ⟨4051604743748652305124773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2701069829165768203416515 4051604743748652305124773)
            ·
              refine ⟨759675889452872307210895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4051604743748652305124773 759675889452872307210895)
              ·
                refine ⟨1139513834179308460816343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 759675889452872307210895 1139513834179308460816343)
                ·
                  refine ⟨1709270751268962691224515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1139513834179308460816343 1709270751268962691224515)
                  ·
                    refine ⟨2563906126903444036836773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1709270751268962691224515 2563906126903444036836773)
                    ·
                      refine ⟨480732398794395756906895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2563906126903444036836773 480732398794395756906895)
                      ·
                        rfl

theorem cell23_936223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 4, 1, 1, 1, 4].length) (baseStart_936223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_936223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_936223 prefixEnd_936223 := by exact prefixLift 936223
  have htrace : WordTrace (prefixWord ++ tailWord_936223) baseStart_936223 baseEnd_936223 := by
    simpa [prefixWord, tailWord_936223, baseEnd_936223] using wordTrace_append hprefix tailTrace_936223
  have hstable : (prefixWord ++ tailWord_936223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936223).length < 2 ^ (prefixWord ++ tailWord_936223).sum := by decide
  have hdescent : baseEnd_936223 < baseStart_936223 := by decide
  rcases family_descends (prefixWord ++ tailWord_936223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936229 : List Nat := [1, 3, 1, 2, 5, 1, 10]
def baseStart_936229 : Nat := 118140960795 + 936229 * 2 ^ 59
def prefixEnd_936229 : Nat := 4983230072969 + 3 ^ 40 * 936229 * 2
def baseEnd_936229 : Nat := 5935005921954601647307

theorem tailTrace_936229 : CollatzResearch.WordTrace tailWord_936229 prefixEnd_936229 5935005921954601647307 := by
  unfold tailWord_936229
  simp only [CollatzResearch.WordTrace]
  refine ⟨34147076925209703028403741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22764717950139802018935827 34147076925209703028403741)
  ·
    refine ⟨12805153846953638635651403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34147076925209703028403741 12805153846953638635651403)
    ·
      refine ⟨19207730770430457953477105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12805153846953638635651403 19207730770430457953477105)
      ·
        refine ⟨14405798077822843465107829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19207730770430457953477105 14405798077822843465107829)
        ·
          refine ⟨1350543569795891574853859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14405798077822843465107829 1350543569795891574853859)
          ·
            refine ⟨2025815354693837362280789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1350543569795891574853859 2025815354693837362280789)
            ·
              refine ⟨5935005921954601647307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2025815354693837362280789 5935005921954601647307)
              ·
                rfl

theorem cell23_936229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 10].length) (baseStart_936229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_936229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_936229 prefixEnd_936229 := by exact prefixLift 936229
  have htrace : WordTrace (prefixWord ++ tailWord_936229) baseStart_936229 baseEnd_936229 := by
    simpa [prefixWord, tailWord_936229, baseEnd_936229] using wordTrace_append hprefix tailTrace_936229
  have hstable : (prefixWord ++ tailWord_936229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936229).length < 2 ^ (prefixWord ++ tailWord_936229).sum := by decide
  have hdescent : baseEnd_936229 < baseStart_936229 := by decide
  rcases family_descends (prefixWord ++ tailWord_936229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936239 : List Nat := [1, 1, 2, 1, 2, 1, 4, 2, 3, 3, 3]
def baseStart_936239 : Nat := 118140960795 + 936239 * 2 ^ 59
def prefixEnd_936239 : Nat := 4983230072969 + 3 ^ 40 * 936239 * 2
def baseEnd_936239 : Nat := 480740614484867694306821

theorem tailTrace_936239 : CollatzResearch.WordTrace tailWord_936239 prefixEnd_936239 480740614484867694306821 := by
  unfold tailWord_936239
  simp only [CollatzResearch.WordTrace]
  refine ⟨34147441655173474736267771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22764961103448983157511847 34147441655173474736267771)
  ·
    refine ⟨51221162482760212104401657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34147441655173474736267771 51221162482760212104401657)
    ·
      refine ⟨38415871862070159078301243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51221162482760212104401657 38415871862070159078301243)
      ·
        refine ⟨57623807793105238617451865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38415871862070159078301243 57623807793105238617451865)
        ·
          refine ⟨43217855844828928963088899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57623807793105238617451865 43217855844828928963088899)
          ·
            refine ⟨64826783767243393444633349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43217855844828928963088899 64826783767243393444633349)
            ·
              refine ⟨12155021956358136270868753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64826783767243393444633349 12155021956358136270868753)
              ·
                refine ⟨9116266467268602203151565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12155021956358136270868753 9116266467268602203151565)
                ·
                  refine ⟨3418599925225725826181837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9116266467268602203151565 3418599925225725826181837)
                  ·
                    refine ⟨1281974971959647184818189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3418599925225725826181837 1281974971959647184818189)
                    ·
                      refine ⟨480740614484867694306821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1281974971959647184818189 480740614484867694306821)
                      ·
                        rfl

theorem cell23_936239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 2, 3, 3, 3].length) (baseStart_936239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_936239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_936239 prefixEnd_936239 := by exact prefixLift 936239
  have htrace : WordTrace (prefixWord ++ tailWord_936239) baseStart_936239 baseEnd_936239 := by
    simpa [prefixWord, tailWord_936239, baseEnd_936239] using wordTrace_append hprefix tailTrace_936239
  have hstable : (prefixWord ++ tailWord_936239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936239).length < 2 ^ (prefixWord ++ tailWord_936239).sum := by decide
  have hdescent : baseEnd_936239 < baseStart_936239 := by decide
  rcases family_descends (prefixWord ++ tailWord_936239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936299 : List Nat := [1, 1, 1, 1, 2, 2, 2, 3, 1, 6, 3]
def baseStart_936299 : Nat := 118140960795 + 936299 * 2 ^ 59
def prefixEnd_936299 : Nat := 4983230072969 + 3 ^ 40 * 936299 * 2
def baseEnd_936299 : Nat := 480771423324137459556545

theorem tailTrace_936299 : CollatzResearch.WordTrace tailWord_936299 prefixEnd_936299 480771423324137459556545 := by
  unfold tailWord_936299
  simp only [CollatzResearch.WordTrace]
  refine ⟨34149630034956104983451951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22766420023304069988967967 34149630034956104983451951)
  ·
    refine ⟨51224445052434157475177927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34149630034956104983451951 51224445052434157475177927)
    ·
      refine ⟨76836667578651236212766891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51224445052434157475177927 76836667578651236212766891)
      ·
        refine ⟨115255001367976854319150337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76836667578651236212766891 115255001367976854319150337)
        ·
          refine ⟨86441251025982640739362753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115255001367976854319150337 86441251025982640739362753)
          ·
            refine ⟨64830938269486980554522065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86441251025982640739362753 64830938269486980554522065)
            ·
              refine ⟨48623203702115235415891549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64830938269486980554522065 48623203702115235415891549)
              ·
                refine ⟨18233701388293213280959331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48623203702115235415891549 18233701388293213280959331)
                ·
                  refine ⟨27350552082439819921438997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18233701388293213280959331 27350552082439819921438997)
                  ·
                    refine ⟨1282057128864366558817453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27350552082439819921438997 1282057128864366558817453)
                    ·
                      refine ⟨480771423324137459556545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1282057128864366558817453 480771423324137459556545)
                      ·
                        rfl

theorem cell23_936299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 6, 3].length) (baseStart_936299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_936299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_936299 prefixEnd_936299 := by exact prefixLift 936299
  have htrace : WordTrace (prefixWord ++ tailWord_936299) baseStart_936299 baseEnd_936299 := by
    simpa [prefixWord, tailWord_936299, baseEnd_936299] using wordTrace_append hprefix tailTrace_936299
  have hstable : (prefixWord ++ tailWord_936299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936299).length < 2 ^ (prefixWord ++ tailWord_936299).sum := by decide
  have hdescent : baseEnd_936299 < baseStart_936299 := by decide
  rcases family_descends (prefixWord ++ tailWord_936299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936342 : List Nat := [5, 3, 1, 2, 2, 1, 2, 2, 1, 2, 2]
def baseStart_936342 : Nat := 118140960795 + 936342 * 2 ^ 59
def prefixEnd_936342 : Nat := 4983230072969 + 3 ^ 40 * 936342 * 2
def baseEnd_936342 : Nat := 480793502992280791318849

theorem tailTrace_936342 : CollatzResearch.WordTrace tailWord_936342 prefixEnd_936342 480793502992280791318849 := by
  unfold tailWord_936342
  simp only [CollatzResearch.WordTrace]
  refine ⟨2134449898362520207954205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22767465582533548884844853 2134449898362520207954205)
  ·
    refine ⟨800418711885945077982827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2134449898362520207954205 800418711885945077982827)
    ·
      refine ⟨1200628067828917616974241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 800418711885945077982827 1200628067828917616974241)
      ·
        refine ⟨900471050871688212730681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1200628067828917616974241 900471050871688212730681)
        ·
          refine ⟨675353288153766159548011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 900471050871688212730681 675353288153766159548011)
          ·
            refine ⟨1013029932230649239322017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 675353288153766159548011 1013029932230649239322017)
            ·
              refine ⟨759772449172986929491513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1013029932230649239322017 759772449172986929491513)
              ·
                refine ⟨569829336879740197118635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 759772449172986929491513 569829336879740197118635)
                ·
                  refine ⟨854744005319610295677953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 569829336879740197118635 854744005319610295677953)
                  ·
                    refine ⟨641058003989707721758465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 854744005319610295677953 641058003989707721758465)
                    ·
                      refine ⟨480793502992280791318849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 641058003989707721758465 480793502992280791318849)
                      ·
                        rfl

theorem cell23_936342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_936342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_936342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_936342 prefixEnd_936342 := by exact prefixLift 936342
  have htrace : WordTrace (prefixWord ++ tailWord_936342) baseStart_936342 baseEnd_936342 := by
    simpa [prefixWord, tailWord_936342, baseEnd_936342] using wordTrace_append hprefix tailTrace_936342
  have hstable : (prefixWord ++ tailWord_936342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936342).length < 2 ^ (prefixWord ++ tailWord_936342).sum := by decide
  have hdescent : baseEnd_936342 < baseStart_936342 := by decide
  rcases family_descends (prefixWord ++ tailWord_936342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936453 : List Nat := [1, 3, 1, 1, 2, 2, 2, 2, 5, 1, 3]
def baseStart_936453 : Nat := 118140960795 + 936453 * 2 ^ 59
def prefixEnd_936453 : Nat := 4983230072969 + 3 ^ 40 * 936453 * 2
def baseEnd_936453 : Nat := 480850499344929857030837

theorem tailTrace_936453 : CollatzResearch.WordTrace tailWord_936453 prefixEnd_936453 480850499344929857030837 := by
  unfold tailWord_936453
  simp only [CollatzResearch.WordTrace]
  refine ⟨34155246876398189284558013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22770164584265459523038675 34155246876398189284558013)
  ·
    refine ⟨12808217578649320981709255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34155246876398189284558013 12808217578649320981709255)
    ·
      refine ⟨19212326367973981472563883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12808217578649320981709255 19212326367973981472563883)
      ·
        refine ⟨28818489551960972208845825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19212326367973981472563883 28818489551960972208845825)
        ·
          refine ⟨21613867163970729156634369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28818489551960972208845825 21613867163970729156634369)
          ·
            refine ⟨16210400372978046867475777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21613867163970729156634369 16210400372978046867475777)
            ·
              refine ⟨12157800279733535150606833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16210400372978046867475777 12157800279733535150606833)
              ·
                refine ⟨9118350209800151362955125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12157800279733535150606833 9118350209800151362955125)
                ·
                  refine ⟨854845332168764190277043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9118350209800151362955125 854845332168764190277043)
                  ·
                    refine ⟨1282267998253146285415565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 854845332168764190277043 1282267998253146285415565)
                    ·
                      refine ⟨480850499344929857030837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1282267998253146285415565 480850499344929857030837)
                      ·
                        rfl

theorem cell23_936453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 2, 5, 1, 3].length) (baseStart_936453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_936453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_936453 prefixEnd_936453 := by exact prefixLift 936453
  have htrace : WordTrace (prefixWord ++ tailWord_936453) baseStart_936453 baseEnd_936453 := by
    simpa [prefixWord, tailWord_936453, baseEnd_936453] using wordTrace_append hprefix tailTrace_936453
  have hstable : (prefixWord ++ tailWord_936453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936453).length < 2 ^ (prefixWord ++ tailWord_936453).sum := by decide
  have hdescent : baseEnd_936453 < baseStart_936453 := by decide
  rcases family_descends (prefixWord ++ tailWord_936453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936454 : List Nat := [6, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4]
def baseStart_936454 : Nat := 118140960795 + 936454 * 2 ^ 59
def prefixEnd_936454 : Nat := 4983230072969 + 3 ^ 40 * 936454 * 2
def baseEnd_936454 : Nat := 480851012825584353118333

theorem tailTrace_936454 : CollatzResearch.WordTrace tailWord_936454 prefixEnd_936454 480851012825584353118333 := by
  unfold tailWord_936454
  simp only [CollatzResearch.WordTrace]
  refine ⟨1067352604668580201729513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 22770188899596377636896277 1067352604668580201729513)
  ·
    refine ⟨800514453501435151297135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1067352604668580201729513 800514453501435151297135)
    ·
      refine ⟨1200771680252152726945703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 800514453501435151297135 1200771680252152726945703)
      ·
        refine ⟨1801157520378229090418555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1200771680252152726945703 1801157520378229090418555)
        ·
          refine ⟨2701736280567343635627833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1801157520378229090418555 2701736280567343635627833)
          ·
            refine ⟨2026302210425507726720875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2701736280567343635627833 2026302210425507726720875)
            ·
              refine ⟨3039453315638261590081313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2026302210425507726720875 3039453315638261590081313)
              ·
                refine ⟨2279589986728696192560985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3039453315638261590081313 2279589986728696192560985)
                ·
                  refine ⟨1709692490046522144420739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2279589986728696192560985 1709692490046522144420739)
                  ·
                    refine ⟨2564538735069783216631109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1709692490046522144420739 2564538735069783216631109)
                    ·
                      refine ⟨480851012825584353118333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2564538735069783216631109 480851012825584353118333)
                      ·
                        rfl

theorem cell23_936454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_936454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_936454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_936454 prefixEnd_936454 := by exact prefixLift 936454
  have htrace : WordTrace (prefixWord ++ tailWord_936454) baseStart_936454 baseEnd_936454 := by
    simpa [prefixWord, tailWord_936454, baseEnd_936454] using wordTrace_append hprefix tailTrace_936454
  have hstable : (prefixWord ++ tailWord_936454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936454).length < 2 ^ (prefixWord ++ tailWord_936454).sum := by decide
  have hdescent : baseEnd_936454 < baseStart_936454 := by decide
  rcases family_descends (prefixWord ++ tailWord_936454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936456 : List Nat := [2, 1, 3, 2, 1, 1, 1, 2, 5, 5]
def baseStart_936456 : Nat := 118140960795 + 936456 * 2 ^ 59
def prefixEnd_936456 : Nat := 4983230072969 + 3 ^ 40 * 936456 * 2
def baseEnd_936456 : Nat := 160284013262297781764441

theorem tailTrace_936456 : CollatzResearch.WordTrace tailWord_936456 prefixEnd_936456 160284013262297781764441 := by
  unfold tailWord_936456
  simp only [CollatzResearch.WordTrace]
  refine ⟨17077678147693660398458611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22770237530258213864611481 17077678147693660398458611)
  ·
    refine ⟨25616517221540490597687917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17077678147693660398458611 25616517221540490597687917)
    ·
      refine ⟨9606193958077683974132969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25616517221540490597687917 9606193958077683974132969)
      ·
        refine ⟨7204645468558262980599727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9606193958077683974132969 7204645468558262980599727)
        ·
          refine ⟨10806968202837394470899591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7204645468558262980599727 10806968202837394470899591)
          ·
            refine ⟨16210452304256091706349387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10806968202837394470899591 16210452304256091706349387)
            ·
              refine ⟨24315678456384137559524081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16210452304256091706349387 24315678456384137559524081)
              ·
                refine ⟨18236758842288103169643061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24315678456384137559524081 18236758842288103169643061)
                ·
                  refine ⟨1709696141464509672154037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18236758842288103169643061 1709696141464509672154037)
                  ·
                    refine ⟨160284013262297781764441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1709696141464509672154037 160284013262297781764441)
                    ·
                      rfl

theorem cell23_936456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 5, 5].length) (baseStart_936456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_936456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_936456 prefixEnd_936456 := by exact prefixLift 936456
  have htrace : WordTrace (prefixWord ++ tailWord_936456) baseStart_936456 baseEnd_936456 := by
    simpa [prefixWord, tailWord_936456, baseEnd_936456] using wordTrace_append hprefix tailTrace_936456
  have hstable : (prefixWord ++ tailWord_936456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936456).length < 2 ^ (prefixWord ++ tailWord_936456).sum := by decide
  have hdescent : baseEnd_936456 < baseStart_936456 := by decide
  rcases family_descends (prefixWord ++ tailWord_936456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936463 : List Nat := [1, 1, 2, 1, 1, 1, 2, 5, 4, 3, 2]
def baseStart_936463 : Nat := 118140960795 + 936463 * 2 ^ 59
def prefixEnd_936463 : Nat := 4983230072969 + 3 ^ 40 * 936463 * 2
def baseEnd_936463 : Nat := 480855634151474817905791

theorem tailTrace_936463 : CollatzResearch.WordTrace tailWord_936463 prefixEnd_936463 480855634151474817905791 := by
  unfold tailWord_936463
  simp only [CollatzResearch.WordTrace]
  refine ⟨34155611606361960992422043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22770407737574640661614695 34155611606361960992422043)
  ·
    refine ⟨51233417409542941488633065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34155611606361960992422043 51233417409542941488633065)
    ·
      refine ⟨38425063057157206116474799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51233417409542941488633065 38425063057157206116474799)
      ·
        refine ⟨57637594585735809174712199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38425063057157206116474799 57637594585735809174712199)
        ·
          refine ⟨86456391878603713762068299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57637594585735809174712199 86456391878603713762068299)
          ·
            refine ⟨129684587817905570643102449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86456391878603713762068299 129684587817905570643102449)
            ·
              refine ⟨97263440863429177982326837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129684587817905570643102449 97263440863429177982326837)
              ·
                refine ⟨9118447580946485435843141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 97263440863429177982326837 9118447580946485435843141)
                ·
                  refine ⟨1709708921427466019220589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9118447580946485435843141 1709708921427466019220589)
                  ·
                    refine ⟨641140845535299757207721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1709708921427466019220589 641140845535299757207721)
                    ·
                      refine ⟨480855634151474817905791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 641140845535299757207721 480855634151474817905791)
                      ·
                        rfl

theorem cell23_936463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 5, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 5, 4, 3, 2].length) (baseStart_936463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_936463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_936463 prefixEnd_936463 := by exact prefixLift 936463
  have htrace : WordTrace (prefixWord ++ tailWord_936463) baseStart_936463 baseEnd_936463 := by
    simpa [prefixWord, tailWord_936463, baseEnd_936463] using wordTrace_append hprefix tailTrace_936463
  have hstable : (prefixWord ++ tailWord_936463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936463).length < 2 ^ (prefixWord ++ tailWord_936463).sum := by decide
  have hdescent : baseEnd_936463 < baseStart_936463 := by decide
  rcases family_descends (prefixWord ++ tailWord_936463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936490 : List Nat := [3, 1, 4, 1, 1, 2, 3, 2, 1, 5]
def baseStart_936490 : Nat := 118140960795 + 936490 * 2 ^ 59
def prefixEnd_936490 : Nat := 4983230072969 + 3 ^ 40 * 936490 * 2
def baseEnd_936490 : Nat := 160289832709715404089389

theorem tailTrace_936490 : CollatzResearch.WordTrace tailWord_936490 prefixEnd_936490 160289832709715404089389 := by
  unfold tailWord_936490
  simp only [CollatzResearch.WordTrace]
  refine ⟨8539149094316036150913731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22771064251509429735769949 8539149094316036150913731)
  ·
    refine ⟨12808723641474054226370597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8539149094316036150913731 12808723641474054226370597)
    ·
      refine ⟨2401635682776385167444487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12808723641474054226370597 2401635682776385167444487)
      ·
        refine ⟨3602453524164577751166731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2401635682776385167444487 3602453524164577751166731)
        ·
          refine ⟨5403680286246866626750097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3602453524164577751166731 5403680286246866626750097)
          ·
            refine ⟨4052760214685149970062573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5403680286246866626750097 4052760214685149970062573)
            ·
              refine ⟨1519785080506931238773465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4052760214685149970062573 1519785080506931238773465)
              ·
                refine ⟨1139838810380198429080099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1519785080506931238773465 1139838810380198429080099)
                ·
                  refine ⟨1709758215570297643620149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1139838810380198429080099 1709758215570297643620149)
                  ·
                    refine ⟨160289832709715404089389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1709758215570297643620149 160289832709715404089389)
                    ·
                      rfl

theorem cell23_936490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 3, 2, 1, 5].length) (baseStart_936490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_936490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_936490 prefixEnd_936490 := by exact prefixLift 936490
  have htrace : WordTrace (prefixWord ++ tailWord_936490) baseStart_936490 baseEnd_936490 := by
    simpa [prefixWord, tailWord_936490, baseEnd_936490] using wordTrace_append hprefix tailTrace_936490
  have hstable : (prefixWord ++ tailWord_936490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936490).length < 2 ^ (prefixWord ++ tailWord_936490).sum := by decide
  have hdescent : baseEnd_936490 < baseStart_936490 := by decide
  rcases family_descends (prefixWord ++ tailWord_936490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936496 : List Nat := [2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 5]
def baseStart_936496 : Nat := 118140960795 + 936496 * 2 ^ 59
def prefixEnd_936496 : Nat := 4983230072969 + 3 ^ 40 * 936496 * 2
def baseEnd_936496 : Nat := 480872579013073188793139

theorem tailTrace_936496 : CollatzResearch.WordTrace tailWord_936496 prefixEnd_936496 480872579013073188793139 := by
  unfold tailWord_936496
  simp only [CollatzResearch.WordTrace]
  refine ⟨17078407607621203814186671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22771210143494938418915561 17078407607621203814186671)
  ·
    refine ⟨25617611411431805721280007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17078407607621203814186671 25617611411431805721280007)
    ·
      refine ⟨38426417117147708581920011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25617611411431805721280007 38426417117147708581920011)
      ·
        refine ⟨57639625675721562872880017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38426417117147708581920011 57639625675721562872880017)
        ·
          refine ⟨43229719256791172154660013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57639625675721562872880017 43229719256791172154660013)
          ·
            refine ⟨16211144721296689557997505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43229719256791172154660013 16211144721296689557997505)
            ·
              refine ⟨12158358540972517168498129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16211144721296689557997505 12158358540972517168498129)
              ·
                refine ⟨9118768905729387876373597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12158358540972517168498129 9118768905729387876373597)
                ·
                  refine ⟨3419538339648520453640099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9118768905729387876373597 3419538339648520453640099)
                  ·
                    refine ⟨5129307509472780680460149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3419538339648520453640099 5129307509472780680460149)
                    ·
                      refine ⟨480872579013073188793139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5129307509472780680460149 480872579013073188793139)
                      ·
                        rfl

theorem cell23_936496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 5].length) (baseStart_936496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_936496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_936496 prefixEnd_936496 := by exact prefixLift 936496
  have htrace : WordTrace (prefixWord ++ tailWord_936496) baseStart_936496 baseEnd_936496 := by
    simpa [prefixWord, tailWord_936496, baseEnd_936496] using wordTrace_append hprefix tailTrace_936496
  have hstable : (prefixWord ++ tailWord_936496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936496).length < 2 ^ (prefixWord ++ tailWord_936496).sum := by decide
  have hdescent : baseEnd_936496 < baseStart_936496 := by decide
  rcases family_descends (prefixWord ++ tailWord_936496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936536 : List Nat := [2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 6]
def baseStart_936536 : Nat := 118140960795 + 936536 * 2 ^ 59
def prefixEnd_936536 : Nat := 4983230072969 + 3 ^ 40 * 936536 * 2
def baseEnd_936536 : Nat := 480893118239253032292955

theorem tailTrace_936536 : CollatzResearch.WordTrace tailWord_936536 prefixEnd_936536 480893118239253032292955 := by
  unfold tailWord_936536
  simp only [CollatzResearch.WordTrace]
  refine ⟨17079137067548747229914731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22772182756731662973219641 17079137067548747229914731)
  ·
    refine ⟨25618705601323120844872097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17079137067548747229914731 25618705601323120844872097)
    ·
      refine ⟨19214029200992340633654073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25618705601323120844872097 19214029200992340633654073)
      ·
        refine ⟨14410521900744255475240555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19214029200992340633654073 14410521900744255475240555)
        ·
          refine ⟨21615782851116383212860833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14410521900744255475240555 21615782851116383212860833)
          ·
            refine ⟨16211837138337287409645625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21615782851116383212860833 16211837138337287409645625)
            ·
              refine ⟨12158877853752965557234219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16211837138337287409645625 12158877853752965557234219)
              ·
                refine ⟨18238316780629448335851329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12158877853752965557234219 18238316780629448335851329)
                ·
                  refine ⟨13678737585472086251888497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18238316780629448335851329 13678737585472086251888497)
                  ·
                    refine ⟨10259053189104064688916373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13678737585472086251888497 10259053189104064688916373)
                    ·
                      refine ⟨480893118239253032292955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10259053189104064688916373 480893118239253032292955)
                      ·
                        rfl

theorem cell23_936536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 6].length) (baseStart_936536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_936536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_936536 prefixEnd_936536 := by exact prefixLift 936536
  have htrace : WordTrace (prefixWord ++ tailWord_936536) baseStart_936536 baseEnd_936536 := by
    simpa [prefixWord, tailWord_936536, baseEnd_936536] using wordTrace_append hprefix tailTrace_936536
  have hstable : (prefixWord ++ tailWord_936536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936536).length < 2 ^ (prefixWord ++ tailWord_936536).sum := by decide
  have hdescent : baseEnd_936536 < baseStart_936536 := by decide
  rcases family_descends (prefixWord ++ tailWord_936536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936604 : List Nat := [2, 2, 3, 2, 2, 2, 2, 2, 1, 3, 2]
def baseStart_936604 : Nat := 118140960795 + 936604 * 2 ^ 59
def prefixEnd_936604 : Nat := 4983230072969 + 3 ^ 40 * 936604 * 2
def baseEnd_936604 : Nat := 480928034923758766242643

theorem tailTrace_936604 : CollatzResearch.WordTrace tailWord_936604 prefixEnd_936604 480928034923758766242643 := by
  unfold tailWord_936604
  simp only [CollatzResearch.WordTrace]
  refine ⟨17080377149425571036652433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22773836199234094715536577 17080377149425571036652433)
  ·
    refine ⟨12810282862069178277489325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17080377149425571036652433 12810282862069178277489325)
    ·
      refine ⟨4803856073275941854058497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12810282862069178277489325 4803856073275941854058497)
      ·
        refine ⟨3602892054956956390543873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4803856073275941854058497 3602892054956956390543873)
        ·
          refine ⟨2702169041217717292907905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3602892054956956390543873 2702169041217717292907905)
          ·
            refine ⟨2026626780913287969680929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2702169041217717292907905 2026626780913287969680929)
            ·
              refine ⟨1519970085684965977260697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2026626780913287969680929 1519970085684965977260697)
              ·
                refine ⟨1139977564263724482945523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1519970085684965977260697 1139977564263724482945523)
                ·
                  refine ⟨1709966346395586724418285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1139977564263724482945523 1709966346395586724418285)
                  ·
                    refine ⟨641237379898345021656857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1709966346395586724418285 641237379898345021656857)
                    ·
                      refine ⟨480928034923758766242643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 641237379898345021656857 480928034923758766242643)
                      ·
                        rfl

theorem cell23_936604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 2, 2, 1, 3, 2].length) (baseStart_936604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_936604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_936604 prefixEnd_936604 := by exact prefixLift 936604
  have htrace : WordTrace (prefixWord ++ tailWord_936604) baseStart_936604 baseEnd_936604 := by
    simpa [prefixWord, tailWord_936604, baseEnd_936604] using wordTrace_append hprefix tailTrace_936604
  have hstable : (prefixWord ++ tailWord_936604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936604).length < 2 ^ (prefixWord ++ tailWord_936604).sum := by decide
  have hdescent : baseEnd_936604 < baseStart_936604 := by decide
  rcases family_descends (prefixWord ++ tailWord_936604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936640 : List Nat := [2, 1, 1, 2, 4, 4, 1, 1, 7]
def baseStart_936640 : Nat := 118140960795 + 936640 * 2 ^ 59
def prefixEnd_936640 : Nat := 4983230072969 + 3 ^ 40 * 936640 * 2
def baseEnd_936640 : Nat := 53438502247480069488053

theorem tailTrace_936640 : CollatzResearch.WordTrace tailWord_936640 prefixEnd_936640 53438502247480069488053 := by
  unfold tailWord_936640
  simp only [CollatzResearch.WordTrace]
  refine ⟨17081033663360360110807687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22774711551147146814410249 17081033663360360110807687)
  ·
    refine ⟨25621550495040540166211531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17081033663360360110807687 25621550495040540166211531)
    ·
      refine ⟨38432325742560810249317297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25621550495040540166211531 38432325742560810249317297)
      ·
        refine ⟨28824244306920607686987973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38432325742560810249317297 28824244306920607686987973)
        ·
          refine ⟨5404545807547613941310245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28824244306920607686987973 5404545807547613941310245)
          ·
            refine ⟨1013352338915177613995671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5404545807547613941310245 1013352338915177613995671)
            ·
              refine ⟨1520028508372766420993507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1013352338915177613995671 1520028508372766420993507)
              ·
                refine ⟨2280042762559149631490261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1520028508372766420993507 2280042762559149631490261)
                ·
                  refine ⟨53438502247480069488053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2280042762559149631490261 53438502247480069488053)
                  ·
                    rfl

theorem cell23_936640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 1, 1, 7].length) (baseStart_936640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_936640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_936640 prefixEnd_936640 := by exact prefixLift 936640
  have htrace : WordTrace (prefixWord ++ tailWord_936640) baseStart_936640 baseEnd_936640 := by
    simpa [prefixWord, tailWord_936640, baseEnd_936640] using wordTrace_append hprefix tailTrace_936640
  have hstable : (prefixWord ++ tailWord_936640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936640).length < 2 ^ (prefixWord ++ tailWord_936640).sum := by decide
  have hdescent : baseEnd_936640 < baseStart_936640 := by decide
  rcases family_descends (prefixWord ++ tailWord_936640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936703 : List Nat := [1, 1, 2, 2, 1, 3, 1, 2, 2, 4, 4]
def baseStart_936703 : Nat := 118140960795 + 936703 * 2 ^ 59
def prefixEnd_936703 : Nat := 4983230072969 + 3 ^ 40 * 936703 * 2
def baseEnd_936703 : Nat := 480978869508553878904687

theorem tailTrace_936703 : CollatzResearch.WordTrace tailWord_936703 prefixEnd_936703 480978869508553878904687 := by
  unfold tailWord_936703
  simp only [CollatzResearch.WordTrace]
  refine ⟨34164365125492481981158763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22776243416994987987439175 34164365125492481981158763)
  ·
    refine ⟨51246547688238722971738145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34164365125492481981158763 51246547688238722971738145)
    ·
      refine ⟨38434910766179042228803609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51246547688238722971738145 38434910766179042228803609)
      ·
        refine ⟨28826183074634281671602707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38434910766179042228803609 28826183074634281671602707)
        ·
          refine ⟨43239274611951422507404061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28826183074634281671602707 43239274611951422507404061)
          ·
            refine ⟨16214727979481783440276523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43239274611951422507404061 16214727979481783440276523)
            ·
              refine ⟨24322091969222675160414785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16214727979481783440276523 24322091969222675160414785)
              ·
                refine ⟨18241568976917006370311089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24322091969222675160414785 18241568976917006370311089)
                ·
                  refine ⟨13681176732687754777733317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18241568976917006370311089 13681176732687754777733317)
                  ·
                    refine ⟨2565220637378954020824997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13681176732687754777733317 2565220637378954020824997)
                    ·
                      refine ⟨480978869508553878904687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2565220637378954020824997 480978869508553878904687)
                      ·
                        rfl

theorem cell23_936703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 2, 4, 4].length) (baseStart_936703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_936703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_936703 prefixEnd_936703 := by exact prefixLift 936703
  have htrace : WordTrace (prefixWord ++ tailWord_936703) baseStart_936703 baseEnd_936703 := by
    simpa [prefixWord, tailWord_936703, baseEnd_936703] using wordTrace_append hprefix tailTrace_936703
  have hstable : (prefixWord ++ tailWord_936703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936703).length < 2 ^ (prefixWord ++ tailWord_936703).sum := by decide
  have hdescent : baseEnd_936703 < baseStart_936703 := by decide
  rcases family_descends (prefixWord ++ tailWord_936703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936727 : List Nat := [1, 1, 3, 4, 3, 1, 1, 1, 1, 4, 3]
def baseStart_936727 : Nat := 118140960795 + 936727 * 2 ^ 59
def prefixEnd_936727 : Nat := 4983230072969 + 3 ^ 40 * 936727 * 2
def baseEnd_936727 : Nat := 480991193044261785004577

theorem tailTrace_936727 : CollatzResearch.WordTrace tailWord_936727 prefixEnd_936727 480991193044261785004577 := by
  unfold tailWord_936727
  simp only [CollatzResearch.WordTrace]
  refine ⟨34165240477405534080032435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22776826984937022720021623 34165240477405534080032435)
  ·
    refine ⟨51247860716108301120048653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34165240477405534080032435 51247860716108301120048653)
    ·
      refine ⟨19217947768540612920018245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51247860716108301120048653 19217947768540612920018245)
      ·
        refine ⟨3603365206601364922503421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19217947768540612920018245 3603365206601364922503421)
        ·
          refine ⟨1351261952475511845938783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3603365206601364922503421 1351261952475511845938783)
          ·
            refine ⟨2026892928713267768908175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1351261952475511845938783 2026892928713267768908175)
            ·
              refine ⟨3040339393069901653362263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2026892928713267768908175 3040339393069901653362263)
              ·
                refine ⟨4560509089604852480043395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3040339393069901653362263 4560509089604852480043395)
                ·
                  refine ⟨6840763634407278720065093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4560509089604852480043395 6840763634407278720065093)
                  ·
                    refine ⟨1282643181451364760012205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6840763634407278720065093 1282643181451364760012205)
                    ·
                      refine ⟨480991193044261785004577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1282643181451364760012205 480991193044261785004577)
                      ·
                        rfl

theorem cell23_936727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 1, 1, 4, 3].length) (baseStart_936727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_936727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_936727 prefixEnd_936727 := by exact prefixLift 936727
  have htrace : WordTrace (prefixWord ++ tailWord_936727) baseStart_936727 baseEnd_936727 := by
    simpa [prefixWord, tailWord_936727, baseEnd_936727] using wordTrace_append hprefix tailTrace_936727
  have hstable : (prefixWord ++ tailWord_936727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936727).length < 2 ^ (prefixWord ++ tailWord_936727).sum := by decide
  have hdescent : baseEnd_936727 < baseStart_936727 := by decide
  rcases family_descends (prefixWord ++ tailWord_936727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936767 : List Nat := [1, 1, 2, 2, 5, 1, 1, 2, 1, 5, 2]
def baseStart_936767 : Nat := 118140960795 + 936767 * 2 ^ 59
def prefixEnd_936767 : Nat := 4983230072969 + 3 ^ 40 * 936767 * 2
def baseEnd_936767 : Nat := 481011732270441628504393

theorem tailTrace_936767 : CollatzResearch.WordTrace tailWord_936767 prefixEnd_936767 481011732270441628504393 := by
  unfold tailWord_936767
  simp only [CollatzResearch.WordTrace]
  refine ⟨34166699397260620911488555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22777799598173747274325703 34166699397260620911488555)
  ·
    refine ⟨51250049095890931367232833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34166699397260620911488555 51250049095890931367232833)
    ·
      refine ⟨38437536821918198525424625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51250049095890931367232833 38437536821918198525424625)
      ·
        refine ⟨28828152616438648894068469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38437536821918198525424625 28828152616438648894068469)
        ·
          refine ⟨2702639307791123333818919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28828152616438648894068469 2702639307791123333818919)
          ·
            refine ⟨4053958961686685000728379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2702639307791123333818919 4053958961686685000728379)
            ·
              refine ⟨6080938442530027501092569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4053958961686685000728379 6080938442530027501092569)
              ·
                refine ⟨4560703831897520625819427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6080938442530027501092569 4560703831897520625819427)
                ·
                  refine ⟨6841055747846280938729141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4560703831897520625819427 6841055747846280938729141)
                  ·
                    refine ⟨641348976360588838005857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6841055747846280938729141 641348976360588838005857)
                    ·
                      refine ⟨481011732270441628504393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 641348976360588838005857 481011732270441628504393)
                      ·
                        rfl

theorem cell23_936767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 2, 1, 5, 2].length) (baseStart_936767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_936767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_936767 prefixEnd_936767 := by exact prefixLift 936767
  have htrace : WordTrace (prefixWord ++ tailWord_936767) baseStart_936767 baseEnd_936767 := by
    simpa [prefixWord, tailWord_936767, baseEnd_936767] using wordTrace_append hprefix tailTrace_936767
  have hstable : (prefixWord ++ tailWord_936767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936767).length < 2 ^ (prefixWord ++ tailWord_936767).sum := by decide
  have hdescent : baseEnd_936767 < baseStart_936767 := by decide
  rcases family_descends (prefixWord ++ tailWord_936767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936777 : List Nat := [1, 2, 1, 1, 2, 6, 2, 2, 1, 5]
def baseStart_936777 : Nat := 118140960795 + 936777 * 2 ^ 59
def prefixEnd_936777 : Nat := 4983230072969 + 3 ^ 40 * 936777 * 2
def baseEnd_936777 : Nat := 160338955692328863126449

theorem tailTrace_936777 : CollatzResearch.WordTrace tailWord_936777 prefixEnd_936777 160338955692328863126449 := by
  unfold tailWord_936777
  simp only [CollatzResearch.WordTrace]
  refine ⟨34167064127224392619352585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22778042751482928412901723 34167064127224392619352585)
  ·
    refine ⟨25625298095418294464514439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34167064127224392619352585 25625298095418294464514439)
    ·
      refine ⟨38437947143127441696771659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25625298095418294464514439 38437947143127441696771659)
      ·
        refine ⟨57656920714691162545157489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38437947143127441696771659 57656920714691162545157489)
        ·
          refine ⟨43242690536018371908868117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57656920714691162545157489 43242690536018371908868117)
          ·
            refine ⟨2027001118875861183228193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 43242690536018371908868117 2027001118875861183228193)
            ·
              refine ⟨1520250839156895887421145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2027001118875861183228193 1520250839156895887421145)
              ·
                refine ⟨1140188129367671915565859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1520250839156895887421145 1140188129367671915565859)
                ·
                  refine ⟨1710282194051507873348789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1140188129367671915565859 1710282194051507873348789)
                  ·
                    refine ⟨160338955692328863126449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1710282194051507873348789 160338955692328863126449)
                    ·
                      rfl

theorem cell23_936777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 2, 2, 1, 5].length) (baseStart_936777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_936777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_936777 prefixEnd_936777 := by exact prefixLift 936777
  have htrace : WordTrace (prefixWord ++ tailWord_936777) baseStart_936777 baseEnd_936777 := by
    simpa [prefixWord, tailWord_936777, baseEnd_936777] using wordTrace_append hprefix tailTrace_936777
  have hstable : (prefixWord ++ tailWord_936777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936777).length < 2 ^ (prefixWord ++ tailWord_936777).sum := by decide
  have hdescent : baseEnd_936777 < baseStart_936777 := by decide
  rcases family_descends (prefixWord ++ tailWord_936777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936791 : List Nat := [1, 1, 3, 2, 4, 1, 3, 3, 1, 1, 3]
def baseStart_936791 : Nat := 118140960795 + 936791 * 2 ^ 59
def prefixEnd_936791 : Nat := 4983230072969 + 3 ^ 40 * 936791 * 2
def baseEnd_936791 : Nat := 481024055806149534604283

theorem tailTrace_936791 : CollatzResearch.WordTrace tailWord_936791 prefixEnd_936791 481024055806149534604283 := by
  unfold tailWord_936791
  simp only [CollatzResearch.WordTrace]
  refine ⟨34167574749173673010362227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22778383166115782006908151 34167574749173673010362227)
  ·
    refine ⟨51251362123760509515543341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34167574749173673010362227 51251362123760509515543341)
    ·
      refine ⟨19219260796410191068328753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51251362123760509515543341 19219260796410191068328753)
      ·
        refine ⟨14414445597307643301246565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19219260796410191068328753 14414445597307643301246565)
        ·
          refine ⟨2702708549495183118983731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14414445597307643301246565 2702708549495183118983731)
          ·
            refine ⟨4054062824242774678475597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2702708549495183118983731 4054062824242774678475597)
            ·
              refine ⟨1520273559091040504428349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4054062824242774678475597 1520273559091040504428349)
              ·
                refine ⟨570102584659140189160631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1520273559091040504428349 570102584659140189160631)
                ·
                  refine ⟨855153876988710283740947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 570102584659140189160631 855153876988710283740947)
                  ·
                    refine ⟨1282730815483065425611421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 855153876988710283740947 1282730815483065425611421)
                    ·
                      refine ⟨481024055806149534604283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1282730815483065425611421 481024055806149534604283)
                      ·
                        rfl

theorem cell23_936791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 3, 3, 1, 1, 3].length) (baseStart_936791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_936791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_936791 prefixEnd_936791 := by exact prefixLift 936791
  have htrace : WordTrace (prefixWord ++ tailWord_936791) baseStart_936791 baseEnd_936791 := by
    simpa [prefixWord, tailWord_936791, baseEnd_936791] using wordTrace_append hprefix tailTrace_936791
  have hstable : (prefixWord ++ tailWord_936791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936791).length < 2 ^ (prefixWord ++ tailWord_936791).sum := by decide
  have hdescent : baseEnd_936791 < baseStart_936791 := by decide
  rcases family_descends (prefixWord ++ tailWord_936791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936807 : List Nat := [1, 1, 5, 1, 2, 2, 2, 1, 4, 4]
def baseStart_936807 : Nat := 118140960795 + 936807 * 2 ^ 59
def prefixEnd_936807 : Nat := 4983230072969 + 3 ^ 40 * 936807 * 2
def baseEnd_936807 : Nat := 160344090498873824001403

theorem tailTrace_936807 : CollatzResearch.WordTrace tailWord_936807 prefixEnd_936807 160344090498873824001403 := by
  unfold tailWord_936807
  simp only [CollatzResearch.WordTrace]
  refine ⟨34168158317115707742944675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22778772211410471828629783 34168158317115707742944675)
  ·
    refine ⟨51252237475673561614417013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34168158317115707742944675 51252237475673561614417013)
    ·
      refine ⟨4804897263344396401351595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51252237475673561614417013 4804897263344396401351595)
      ·
        refine ⟨7207345895016594602027393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4804897263344396401351595 7207345895016594602027393)
        ·
          refine ⟨5405509421262445951520545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7207345895016594602027393 5405509421262445951520545)
          ·
            refine ⟨4054132065946834463640409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5405509421262445951520545 4054132065946834463640409)
            ·
              refine ⟨3040599049460125847730307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4054132065946834463640409 3040599049460125847730307)
              ·
                refine ⟨4560898574190188771595461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3040599049460125847730307 4560898574190188771595461)
                ·
                  refine ⟨855168482660660394674149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4560898574190188771595461 855168482660660394674149)
                  ·
                    refine ⟨160344090498873824001403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 855168482660660394674149 160344090498873824001403)
                    ·
                      rfl

theorem cell23_936807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 1, 4, 4].length) (baseStart_936807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_936807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_936807 prefixEnd_936807 := by exact prefixLift 936807
  have htrace : WordTrace (prefixWord ++ tailWord_936807) baseStart_936807 baseEnd_936807 := by
    simpa [prefixWord, tailWord_936807, baseEnd_936807] using wordTrace_append hprefix tailTrace_936807
  have hstable : (prefixWord ++ tailWord_936807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936807).length < 2 ^ (prefixWord ++ tailWord_936807).sum := by decide
  have hdescent : baseEnd_936807 < baseStart_936807 := by decide
  rcases family_descends (prefixWord ++ tailWord_936807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936808 : List Nat := [2, 1, 4, 2, 1, 3, 3, 2, 1, 1, 3]
def baseStart_936808 : Nat := 118140960795 + 936808 * 2 ^ 59
def prefixEnd_936808 : Nat := 4983230072969 + 3 ^ 40 * 936808 * 2
def baseEnd_936808 : Nat := 481032784977275968091705

theorem tailTrace_936808 : CollatzResearch.WordTrace tailWord_936808 prefixEnd_936808 481032784977275968091705 := by
  unfold tailWord_936808
  simp only [CollatzResearch.WordTrace]
  refine ⟨17084097395056042456865539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22778796526741389942487385 17084097395056042456865539)
  ·
    refine ⟨25626146092584063685298309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17084097395056042456865539 25626146092584063685298309)
    ·
      refine ⟨4804902392359511940993433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25626146092584063685298309 4804902392359511940993433)
      ·
        refine ⟨3603676794269633955745075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4804902392359511940993433 3603676794269633955745075)
        ·
          refine ⟨5405515191404450933617613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3603676794269633955745075 5405515191404450933617613)
          ·
            refine ⟨2027068196776669100106605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5405515191404450933617613 2027068196776669100106605)
            ·
              refine ⟨760150573791250912539977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2027068196776669100106605 760150573791250912539977)
              ·
                refine ⟨570112930343438184404983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 760150573791250912539977 570112930343438184404983)
                ·
                  refine ⟨855169395515157276607475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 570112930343438184404983 855169395515157276607475)
                  ·
                    refine ⟨1282754093272735914911213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 855169395515157276607475 1282754093272735914911213)
                    ·
                      refine ⟨481032784977275968091705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1282754093272735914911213 481032784977275968091705)
                      ·
                        rfl

theorem cell23_936808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 3, 2, 1, 1, 3].length) (baseStart_936808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_936808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_936808 prefixEnd_936808 := by exact prefixLift 936808
  have htrace : WordTrace (prefixWord ++ tailWord_936808) baseStart_936808 baseEnd_936808 := by
    simpa [prefixWord, tailWord_936808, baseEnd_936808] using wordTrace_append hprefix tailTrace_936808
  have hstable : (prefixWord ++ tailWord_936808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936808).length < 2 ^ (prefixWord ++ tailWord_936808).sum := by decide
  have hdescent : baseEnd_936808 < baseStart_936808 := by decide
  rcases family_descends (prefixWord ++ tailWord_936808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936854 : List Nat := [5, 3, 1, 1, 1, 12]
def baseStart_936854 : Nat := 118140960795 + 936854 * 2 ^ 59
def prefixEnd_936854 : Nat := 4983230072969 + 3 ^ 40 * 936854 * 2
def baseEnd_936854 : Nat := 1979655988013920938751

theorem tailTrace_936854 : CollatzResearch.WordTrace tailWord_936854 prefixEnd_936854 1979655988013920938751 := by
  unfold tailWord_936854
  simp only [CollatzResearch.WordTrace]
  refine ⟨2135617034246589673119101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22779915031963623179937077 2135617034246589673119101)
  ·
    refine ⟨800856387842471127419663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2135617034246589673119101 800856387842471127419663)
    ·
      refine ⟨1201284581763706691129495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 800856387842471127419663 1201284581763706691129495)
      ·
        refine ⟨1801926872645560036694243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1201284581763706691129495 1801926872645560036694243)
        ·
          refine ⟨2702890308968340055041365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1801926872645560036694243 2702890308968340055041365)
          ·
            refine ⟨1979655988013920938751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 2702890308968340055041365 1979655988013920938751)
            ·
              rfl

theorem cell23_936854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 12].length) (baseStart_936854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_936854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_936854 prefixEnd_936854 := by exact prefixLift 936854
  have htrace : WordTrace (prefixWord ++ tailWord_936854) baseStart_936854 baseEnd_936854 := by
    simpa [prefixWord, tailWord_936854, baseEnd_936854] using wordTrace_append hprefix tailTrace_936854
  have hstable : (prefixWord ++ tailWord_936854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936854).length < 2 ^ (prefixWord ++ tailWord_936854).sum := by decide
  have hdescent : baseEnd_936854 < baseStart_936854 := by decide
  rcases family_descends (prefixWord ++ tailWord_936854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936864 : List Nat := [2, 1, 1, 4, 1, 1, 3, 4, 2, 1, 3]
def baseStart_936864 : Nat := 118140960795 + 936864 * 2 ^ 59
def prefixEnd_936864 : Nat := 4983230072969 + 3 ^ 40 * 936864 * 2
def baseEnd_936864 : Nat := 481061539893927748991447

theorem tailTrace_936864 : CollatzResearch.WordTrace tailWord_936864 prefixEnd_936864 481061539893927748991447 := by
  unfold tailWord_936864
  simp only [CollatzResearch.WordTrace]
  refine ⟨17085118638954603238884823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22780158185272804318513097 17085118638954603238884823)
  ·
    refine ⟨25627677958431904858327235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17085118638954603238884823 25627677958431904858327235)
    ·
      refine ⟨38441516937647857287490853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25627677958431904858327235 38441516937647857287490853)
      ·
        refine ⟨7207784425808973241404535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38441516937647857287490853 7207784425808973241404535)
        ·
          refine ⟨10811676638713459862106803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7207784425808973241404535 10811676638713459862106803)
          ·
            refine ⟨16217514958070189793160205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10811676638713459862106803 16217514958070189793160205)
            ·
              refine ⟨6081568109276321172435077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16217514958070189793160205 6081568109276321172435077)
              ·
                refine ⟨1140294020489310219831577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6081568109276321172435077 1140294020489310219831577)
                ·
                  refine ⟨855220515366982664873683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1140294020489310219831577 855220515366982664873683)
                  ·
                    refine ⟨1282830773050473997310525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 855220515366982664873683 1282830773050473997310525)
                    ·
                      refine ⟨481061539893927748991447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1282830773050473997310525 481061539893927748991447)
                      ·
                        rfl

theorem cell23_936864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 4, 2, 1, 3].length) (baseStart_936864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_936864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_936864 prefixEnd_936864 := by exact prefixLift 936864
  have htrace : WordTrace (prefixWord ++ tailWord_936864) baseStart_936864 baseEnd_936864 := by
    simpa [prefixWord, tailWord_936864, baseEnd_936864] using wordTrace_append hprefix tailTrace_936864
  have hstable : (prefixWord ++ tailWord_936864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936864).length < 2 ^ (prefixWord ++ tailWord_936864).sum := by decide
  have hdescent : baseEnd_936864 < baseStart_936864 := by decide
  rcases family_descends (prefixWord ++ tailWord_936864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936865 : List Nat := [1, 2, 3, 4, 1, 1, 4, 2, 1, 2, 2]
def baseStart_936865 : Nat := 118140960795 + 936865 * 2 ^ 59
def prefixEnd_936865 : Nat := 4983230072969 + 3 ^ 40 * 936865 * 2
def baseEnd_936865 : Nat := 481062053374582245078943

theorem tailTrace_936865 : CollatzResearch.WordTrace tailWord_936865 prefixEnd_936865 481062053374582245078943 := by
  unfold tailWord_936865
  simp only [CollatzResearch.WordTrace]
  refine ⟨34170273750905583648556049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22780182500603722432370699 34170273750905583648556049)
  ·
    refine ⟨25627705313179187736417037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34170273750905583648556049 25627705313179187736417037)
    ·
      refine ⟨9610389492442195401156389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25627705313179187736417037 9610389492442195401156389)
      ·
        refine ⟨1801948029832911637716823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9610389492442195401156389 1801948029832911637716823)
        ·
          refine ⟨2702922044749367456575235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1801948029832911637716823 2702922044749367456575235)
          ·
            refine ⟨4054383067124051184862853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2702922044749367456575235 4054383067124051184862853)
            ·
              refine ⟨760196825085759597161785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4054383067124051184862853 760196825085759597161785)
              ·
                refine ⟨570147618814319697871339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 760196825085759597161785 570147618814319697871339)
                ·
                  refine ⟨855221428221479546807009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 570147618814319697871339 855221428221479546807009)
                  ·
                    refine ⟨641416071166109660105257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 855221428221479546807009 641416071166109660105257)
                    ·
                      refine ⟨481062053374582245078943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 641416071166109660105257 481062053374582245078943)
                      ·
                        rfl

theorem cell23_936865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 4, 2, 1, 2, 2].length) (baseStart_936865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_936865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_936865 prefixEnd_936865 := by exact prefixLift 936865
  have htrace : WordTrace (prefixWord ++ tailWord_936865) baseStart_936865 baseEnd_936865 := by
    simpa [prefixWord, tailWord_936865, baseEnd_936865] using wordTrace_append hprefix tailTrace_936865
  have hstable : (prefixWord ++ tailWord_936865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936865).length < 2 ^ (prefixWord ++ tailWord_936865).sum := by decide
  have hdescent : baseEnd_936865 < baseStart_936865 := by decide
  rcases family_descends (prefixWord ++ tailWord_936865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936902 : List Nat := [6, 1, 3, 1, 1, 1, 1, 3, 1, 2, 3]
def baseStart_936902 : Nat := 118140960795 + 936902 * 2 ^ 59
def prefixEnd_936902 : Nat := 4983230072969 + 3 ^ 40 * 936902 * 2
def baseEnd_936902 : Nat := 481081052158798600316273

theorem tailTrace_936902 : CollatzResearch.WordTrace tailWord_936902 prefixEnd_936902 481081052158798600316273 := by
  unfold tailWord_936902
  simp only [CollatzResearch.WordTrace]
  refine ⟨1067863226617860592739155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 22781082167847692645101973 1067863226617860592739155)
  ·
    refine ⟨1601794839926790889108733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1067863226617860592739155 1601794839926790889108733)
    ·
      refine ⟨600673064972546583415775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1601794839926790889108733 600673064972546583415775)
      ·
        refine ⟨901009597458819875123663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 600673064972546583415775 901009597458819875123663)
        ·
          refine ⟨1351514396188229812685495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 901009597458819875123663 1351514396188229812685495)
          ·
            refine ⟨2027271594282344719028243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1351514396188229812685495 2027271594282344719028243)
            ·
              refine ⟨3040907391423517078542365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2027271594282344719028243 3040907391423517078542365)
              ·
                refine ⟨1140340271783818904453387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3040907391423517078542365 1140340271783818904453387)
                ·
                  refine ⟨1710510407675728356680081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1140340271783818904453387 1710510407675728356680081)
                  ·
                    refine ⟨1282882805756796267510061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1710510407675728356680081 1282882805756796267510061)
                    ·
                      refine ⟨481081052158798600316273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1282882805756796267510061 481081052158798600316273)
                      ·
                        rfl

theorem cell23_936902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_936902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_936902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_936902 prefixEnd_936902 := by exact prefixLift 936902
  have htrace : WordTrace (prefixWord ++ tailWord_936902) baseStart_936902 baseEnd_936902 := by
    simpa [prefixWord, tailWord_936902, baseEnd_936902] using wordTrace_append hprefix tailTrace_936902
  have hstable : (prefixWord ++ tailWord_936902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936902).length < 2 ^ (prefixWord ++ tailWord_936902).sum := by decide
  have hdescent : baseEnd_936902 < baseStart_936902 := by decide
  rcases family_descends (prefixWord ++ tailWord_936902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936921 : List Nat := [1, 2, 1, 2, 5, 2, 1, 1, 4, 2, 2]
def baseStart_936921 : Nat := 118140960795 + 936921 * 2 ^ 59
def prefixEnd_936921 : Nat := 4983230072969 + 3 ^ 40 * 936921 * 2
def baseEnd_936921 : Nat := 481090808291234025978685

theorem tailTrace_936921 : CollatzResearch.WordTrace tailWord_936921 prefixEnd_936921 481090808291234025978685 := by
  unfold tailWord_936921
  simp only [CollatzResearch.WordTrace]
  refine ⟨34172316238702705212594617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22781544159135136808396411 34172316238702705212594617)
  ·
    refine ⟨25629237179027028909445963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34172316238702705212594617 25629237179027028909445963)
    ·
      refine ⟨38443855768540543364168945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25629237179027028909445963 38443855768540543364168945)
      ·
        refine ⟨28832891826405407523126709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38443855768540543364168945 28832891826405407523126709)
        ·
          refine ⟨2703083608725506955293129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28832891826405407523126709 2703083608725506955293129)
          ·
            refine ⟨2027312706544130216469847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2703083608725506955293129 2027312706544130216469847)
            ·
              refine ⟨3040969059816195324704771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2027312706544130216469847 3040969059816195324704771)
              ·
                refine ⟨4561453589724292987057157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3040969059816195324704771 4561453589724292987057157)
                ·
                  refine ⟨855272548073304935073217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4561453589724292987057157 855272548073304935073217)
                  ·
                    refine ⟨641454411054978701304913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 855272548073304935073217 641454411054978701304913)
                    ·
                      refine ⟨481090808291234025978685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 641454411054978701304913 481090808291234025978685)
                      ·
                        rfl

theorem cell23_936921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 1, 4, 2, 2].length) (baseStart_936921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_936921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_936921 prefixEnd_936921 := by exact prefixLift 936921
  have htrace : WordTrace (prefixWord ++ tailWord_936921) baseStart_936921 baseEnd_936921 := by
    simpa [prefixWord, tailWord_936921, baseEnd_936921] using wordTrace_append hprefix tailTrace_936921
  have hstable : (prefixWord ++ tailWord_936921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936921).length < 2 ^ (prefixWord ++ tailWord_936921).sum := by decide
  have hdescent : baseEnd_936921 < baseStart_936921 := by decide
  rcases family_descends (prefixWord ++ tailWord_936921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936957 : List Nat := [1, 4, 1, 1, 1, 2, 1, 5, 2, 5]
def baseStart_936957 : Nat := 118140960795 + 936957 * 2 ^ 59
def prefixEnd_936957 : Nat := 4983230072969 + 3 ^ 40 * 936957 * 2
def baseEnd_936957 : Nat := 160369764531598628376173

theorem tailTrace_936957 : CollatzResearch.WordTrace tailWord_936957 prefixEnd_936957 160369764531598628376173 := by
  unfold tailWord_936957
  simp only [CollatzResearch.WordTrace]
  refine ⟨34173629266572283360905125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22782419511048188907270083 34173629266572283360905125)
  ·
    refine ⟨6407555487482303130169711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34173629266572283360905125 6407555487482303130169711)
    ·
      refine ⟨9611333231223454695254567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6407555487482303130169711 9611333231223454695254567)
      ·
        refine ⟨14416999846835182042881851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9611333231223454695254567 14416999846835182042881851)
        ·
          refine ⟨21625499770252773064322777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14416999846835182042881851 21625499770252773064322777)
          ·
            refine ⟨16219124827689579798242083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21625499770252773064322777 16219124827689579798242083)
            ·
              refine ⟨24328687241534369697363125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16219124827689579798242083 24328687241534369697363125)
              ·
                refine ⟨2280814428893847159127793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24328687241534369697363125 2280814428893847159127793)
                ·
                  refine ⟨1710610821670385369345845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2280814428893847159127793 1710610821670385369345845)
                  ·
                    refine ⟨160369764531598628376173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1710610821670385369345845 160369764531598628376173)
                    ·
                      rfl

theorem cell23_936957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 5, 2, 5].length) (baseStart_936957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_936957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_936957 prefixEnd_936957 := by exact prefixLift 936957
  have htrace : WordTrace (prefixWord ++ tailWord_936957) baseStart_936957 baseEnd_936957 := by
    simpa [prefixWord, tailWord_936957, baseEnd_936957] using wordTrace_append hprefix tailTrace_936957
  have hstable : (prefixWord ++ tailWord_936957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936957).length < 2 ^ (prefixWord ++ tailWord_936957).sum := by decide
  have hdescent : baseEnd_936957 < baseStart_936957 := by decide
  rcases family_descends (prefixWord ++ tailWord_936957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936960 : List Nat := [2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 8]
def baseStart_936960 : Nat := 118140960795 + 936960 * 2 ^ 59
def prefixEnd_936960 : Nat := 4983230072969 + 3 ^ 40 * 936960 * 2
def baseEnd_936960 : Nat := 481110834036759373391005

theorem tailTrace_936960 : CollatzResearch.WordTrace tailWord_936960 prefixEnd_936960 481110834036759373391005 := by
  unfold tailWord_936960
  simp only [CollatzResearch.WordTrace]
  refine ⟨17086869342780707436632167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22782492457040943248842889 17086869342780707436632167)
  ·
    refine ⟨25630304014171061154948251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17086869342780707436632167 25630304014171061154948251)
    ·
      refine ⟨38445456021256591732422377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25630304014171061154948251 38445456021256591732422377)
      ·
        refine ⟨28834092015942443799316783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38445456021256591732422377 28834092015942443799316783)
        ·
          refine ⟨43251138023913665698975175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28834092015942443799316783 43251138023913665698975175)
          ·
            refine ⟨64876707035870498548462763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43251138023913665698975175 64876707035870498548462763)
            ·
              refine ⟨97315060553805747822694145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64876707035870498548462763 97315060553805747822694145)
              ·
                refine ⟨72986295415354310867020609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97315060553805747822694145 72986295415354310867020609)
                ·
                  refine ⟨54739721561515733150265457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72986295415354310867020609 54739721561515733150265457)
                  ·
                    refine ⟨41054791171136799862699093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54739721561515733150265457 41054791171136799862699093)
                    ·
                      refine ⟨481110834036759373391005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 41054791171136799862699093 481110834036759373391005)
                      ·
                        rfl

theorem cell23_936960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 8].length) (baseStart_936960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_936960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_936960 prefixEnd_936960 := by exact prefixLift 936960
  have htrace : WordTrace (prefixWord ++ tailWord_936960) baseStart_936960 baseEnd_936960 := by
    simpa [prefixWord, tailWord_936960, baseEnd_936960] using wordTrace_append hprefix tailTrace_936960
  have hstable : (prefixWord ++ tailWord_936960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936960).length < 2 ^ (prefixWord ++ tailWord_936960).sum := by decide
  have hdescent : baseEnd_936960 < baseStart_936960 := by decide
  rcases family_descends (prefixWord ++ tailWord_936960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936961 : List Nat := [1, 2, 4, 1, 2, 4, 1, 3, 5]
def baseStart_936961 : Nat := 118140960795 + 936961 * 2 ^ 59
def prefixEnd_936961 : Nat := 4983230072969 + 3 ^ 40 * 936961 * 2
def baseEnd_936961 : Nat := 53456816390823763275389

theorem tailTrace_936961 : CollatzResearch.WordTrace tailWord_936961 prefixEnd_936961 53456816390823763275389 := by
  unfold tailWord_936961
  simp only [CollatzResearch.WordTrace]
  refine ⟨34173775158557792044050737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22782516772371861362700491 34173775158557792044050737)
  ·
    refine ⟨25630331368918344033038053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34173775158557792044050737 25630331368918344033038053)
    ·
      refine ⟨4805687131672189506194635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25630331368918344033038053 4805687131672189506194635)
      ·
        refine ⟨7208530697508284259291953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4805687131672189506194635 7208530697508284259291953)
        ·
          refine ⟨5406398023131213194468965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7208530697508284259291953 5406398023131213194468965)
          ·
            refine ⟨1013699629337102473962931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5406398023131213194468965 1013699629337102473962931)
            ·
              refine ⟨1520549444005653710944397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1013699629337102473962931 1520549444005653710944397)
              ·
                refine ⟨570206041502120141604149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1520549444005653710944397 570206041502120141604149)
                ·
                  refine ⟨53456816390823763275389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 570206041502120141604149 53456816390823763275389)
                  ·
                    rfl

theorem cell23_936961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 1, 3, 5].length) (baseStart_936961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_936961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_936961 prefixEnd_936961 := by exact prefixLift 936961
  have htrace : WordTrace (prefixWord ++ tailWord_936961) baseStart_936961 baseEnd_936961 := by
    simpa [prefixWord, tailWord_936961, baseEnd_936961] using wordTrace_append hprefix tailTrace_936961
  have hstable : (prefixWord ++ tailWord_936961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936961).length < 2 ^ (prefixWord ++ tailWord_936961).sum := by decide
  have hdescent : baseEnd_936961 < baseStart_936961 := by decide
  rcases family_descends (prefixWord ++ tailWord_936961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936967 : List Nat := [1, 1, 4, 3, 1, 1, 2, 2, 1, 2, 5]
def baseStart_936967 : Nat := 118140960795 + 936967 * 2 ^ 59
def prefixEnd_936967 : Nat := 4983230072969 + 3 ^ 40 * 936967 * 2
def baseEnd_936967 : Nat := 481114428401340846003473

theorem tailTrace_936967 : CollatzResearch.WordTrace tailWord_936967 prefixEnd_936967 481114428401340846003473 := by
  unfold tailWord_936967
  simp only [CollatzResearch.WordTrace]
  refine ⟨34173993996536055068769155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22782662664357370045846103 34173993996536055068769155)
  ·
    refine ⟨51260990994804082603153733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34173993996536055068769155 51260990994804082603153733)
    ·
      refine ⟨9611435811525765488091325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51260990994804082603153733 9611435811525765488091325)
      ·
        refine ⟨3604288429322162058034247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9611435811525765488091325 3604288429322162058034247)
        ·
          refine ⟨5406432643983243087051371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3604288429322162058034247 5406432643983243087051371)
          ·
            refine ⟨8109648965974864630577057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5406432643983243087051371 8109648965974864630577057)
            ·
              refine ⟨6082236724481148472932793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8109648965974864630577057 6082236724481148472932793)
              ·
                refine ⟨4561677543360861354699595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6082236724481148472932793 4561677543360861354699595)
                ·
                  refine ⟨6842516315041292032049393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4561677543360861354699595 6842516315041292032049393)
                  ·
                    refine ⟨5131887236280969024037045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6842516315041292032049393 5131887236280969024037045)
                    ·
                      refine ⟨481114428401340846003473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5131887236280969024037045 481114428401340846003473)
                      ·
                        rfl

theorem cell23_936967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_936967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_936967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_936967 prefixEnd_936967 := by exact prefixLift 936967
  have htrace : WordTrace (prefixWord ++ tailWord_936967) baseStart_936967 baseEnd_936967 := by
    simpa [prefixWord, tailWord_936967, baseEnd_936967] using wordTrace_append hprefix tailTrace_936967
  have hstable : (prefixWord ++ tailWord_936967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936967).length < 2 ^ (prefixWord ++ tailWord_936967).sum := by decide
  have hdescent : baseEnd_936967 < baseStart_936967 := by decide
  rcases family_descends (prefixWord ++ tailWord_936967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_936974 : List Nat := [4, 1, 1, 2, 2, 3, 1, 2, 2, 5]
def baseStart_936974 : Nat := 118140960795 + 936974 * 2 ^ 59
def prefixEnd_936974 : Nat := 4983230072969 + 3 ^ 40 * 936974 * 2
def baseEnd_936974 : Nat := 160372674255307439538647

theorem tailTrace_936974 : CollatzResearch.WordTrace tailWord_936974 prefixEnd_936974 160372674255307439538647 := by
  unfold tailWord_936974
  simp only [CollatzResearch.WordTrace]
  refine ⟨4271781163438836908034247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22782832871673796842849317 4271781163438836908034247)
  ·
    refine ⟨6407671745158255362051371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4271781163438836908034247 6407671745158255362051371)
    ·
      refine ⟨9611507617737383043077057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6407671745158255362051371 9611507617737383043077057)
      ·
        refine ⟨7208630713303037282307793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9611507617737383043077057 7208630713303037282307793)
        ·
          refine ⟨5406473034977277961730845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7208630713303037282307793 5406473034977277961730845)
          ·
            refine ⟨2027427388116479235649067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5406473034977277961730845 2027427388116479235649067)
            ·
              refine ⟨3041141082174718853473601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2027427388116479235649067 3041141082174718853473601)
              ·
                refine ⟨2280855811631039140105201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3041141082174718853473601 2280855811631039140105201)
                ·
                  refine ⟨1710641858723279355078901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2280855811631039140105201 1710641858723279355078901)
                  ·
                    refine ⟨160372674255307439538647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1710641858723279355078901 160372674255307439538647)
                    ·
                      rfl

theorem cell23_936974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 2, 2, 5].length) (baseStart_936974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_936974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_936974 prefixEnd_936974 := by exact prefixLift 936974
  have htrace : WordTrace (prefixWord ++ tailWord_936974) baseStart_936974 baseEnd_936974 := by
    simpa [prefixWord, tailWord_936974, baseEnd_936974] using wordTrace_append hprefix tailTrace_936974
  have hstable : (prefixWord ++ tailWord_936974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_936974).length < 2 ^ (prefixWord ++ tailWord_936974).sum := by decide
  have hdescent : baseEnd_936974 < baseStart_936974 := by decide
  rcases family_descends (prefixWord ++ tailWord_936974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937061 : List Nat := [1, 3, 1, 3, 2, 1, 3, 2, 3, 1, 3]
def baseStart_937061 : Nat := 118140960795 + 937061 * 2 ^ 59
def prefixEnd_937061 : Nat := 4983230072969 + 3 ^ 40 * 937061 * 2
def baseEnd_937061 : Nat := 481162695582863478228041

theorem tailTrace_937061 : CollatzResearch.WordTrace tailWord_937061 prefixEnd_937061 481162695582863478228041 := by
  unfold tailWord_937061
  simp only [CollatzResearch.WordTrace]
  refine ⟨34177422458195509122691037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22784948305463672748460691 34177422458195509122691037)
  ·
    refine ⟨12816533421823315921009139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34177422458195509122691037 12816533421823315921009139)
    ·
      refine ⟨19224800132734973881513709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12816533421823315921009139 19224800132734973881513709)
      ·
        refine ⟨7209300049775615205567641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19224800132734973881513709 7209300049775615205567641)
        ·
          refine ⟨5406975037331711404175731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7209300049775615205567641 5406975037331711404175731)
          ·
            refine ⟨8110462555997567106263597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5406975037331711404175731 8110462555997567106263597)
            ·
              refine ⟨3041423458499087664848849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8110462555997567106263597 3041423458499087664848849)
              ·
                refine ⟨2281067593874315748636637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3041423458499087664848849 2281067593874315748636637)
                ·
                  refine ⟨855400347702868405738739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2281067593874315748636637 855400347702868405738739)
                  ·
                    refine ⟨1283100521554302608608109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 855400347702868405738739 1283100521554302608608109)
                    ·
                      refine ⟨481162695582863478228041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1283100521554302608608109 481162695582863478228041)
                      ·
                        rfl

theorem cell23_937061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 2, 3, 1, 3].length) (baseStart_937061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_937061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_937061 prefixEnd_937061 := by exact prefixLift 937061
  have htrace : WordTrace (prefixWord ++ tailWord_937061) baseStart_937061 baseEnd_937061 := by
    simpa [prefixWord, tailWord_937061, baseEnd_937061] using wordTrace_append hprefix tailTrace_937061
  have hstable : (prefixWord ++ tailWord_937061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937061).length < 2 ^ (prefixWord ++ tailWord_937061).sum := by decide
  have hdescent : baseEnd_937061 < baseStart_937061 := by decide
  rcases family_descends (prefixWord ++ tailWord_937061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937081 : List Nat := [1, 2, 1, 3, 5, 1, 1, 3, 1, 5]
def baseStart_937081 : Nat := 118140960795 + 937081 * 2 ^ 59
def prefixEnd_937081 : Nat := 4983230072969 + 3 ^ 40 * 937081 * 2
def baseEnd_937081 : Nat := 160390988398651133325983

theorem tailTrace_937081 : CollatzResearch.WordTrace tailWord_937081 prefixEnd_937081 160390988398651133325983 := by
  unfold tailWord_937081
  simp only [CollatzResearch.WordTrace]
  refine ⟨34178151918123052538419097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22785434612082035025612731 34178151918123052538419097)
  ·
    refine ⟨25633613938592289403814323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34178151918123052538419097 25633613938592289403814323)
    ·
      refine ⟨38450420907888434105721485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25633613938592289403814323 38450420907888434105721485)
      ·
        refine ⟨14418907840458162789645557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38450420907888434105721485 14418907840458162789645557)
        ·
          refine ⟨1351772610042952761529271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14418907840458162789645557 1351772610042952761529271)
          ·
            refine ⟨2027658915064429142293907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1351772610042952761529271 2027658915064429142293907)
            ·
              refine ⟨3041488372596643713440861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2027658915064429142293907 3041488372596643713440861)
              ·
                refine ⟨1140558139723741392540323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3041488372596643713440861 1140558139723741392540323)
                ·
                  refine ⟨1710837209585612088810485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1140558139723741392540323 1710837209585612088810485)
                  ·
                    refine ⟨160390988398651133325983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1710837209585612088810485 160390988398651133325983)
                    ·
                      rfl

theorem cell23_937081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 3, 1, 5].length) (baseStart_937081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_937081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_937081 prefixEnd_937081 := by exact prefixLift 937081
  have htrace : WordTrace (prefixWord ++ tailWord_937081) baseStart_937081 baseEnd_937081 := by
    simpa [prefixWord, tailWord_937081, baseEnd_937081] using wordTrace_append hprefix tailTrace_937081
  have hstable : (prefixWord ++ tailWord_937081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937081).length < 2 ^ (prefixWord ++ tailWord_937081).sum := by decide
  have hdescent : baseEnd_937081 < baseStart_937081 := by decide
  rcases family_descends (prefixWord ++ tailWord_937081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937087 : List Nat := [1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 5]
def baseStart_937087 : Nat := 118140960795 + 937087 * 2 ^ 59
def prefixEnd_937087 : Nat := 4983230072969 + 3 ^ 40 * 937087 * 2
def baseEnd_937087 : Nat := 481176046079880376502921

theorem tailTrace_937087 : CollatzResearch.WordTrace tailWord_937087 prefixEnd_937087 481176046079880376502921 := by
  unfold tailWord_937087
  simp only [CollatzResearch.WordTrace]
  refine ⟨34178370756101315563137515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22785580504067543708758343 34178370756101315563137515)
  ·
    refine ⟨51267556134151973344706273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34178370756101315563137515 51267556134151973344706273)
    ·
      refine ⟨38450667100613980008529705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51267556134151973344706273 38450667100613980008529705)
      ·
        refine ⟨28838000325460485006397279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38450667100613980008529705 28838000325460485006397279)
        ·
          refine ⟨43257000488190727509595919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28838000325460485006397279 43257000488190727509595919)
          ·
            refine ⟨64885500732286091264393879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43257000488190727509595919 64885500732286091264393879)
            ·
              refine ⟨97328251098429136896590819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64885500732286091264393879 97328251098429136896590819)
              ·
                refine ⟨145992376647643705344886229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97328251098429136896590819 145992376647643705344886229)
                ·
                  refine ⟨3421696327679149344020771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 145992376647643705344886229 3421696327679149344020771)
                  ·
                    refine ⟨5132544491518724016031157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3421696327679149344020771 5132544491518724016031157)
                    ·
                      refine ⟨481176046079880376502921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5132544491518724016031157 481176046079880376502921)
                      ·
                        rfl

theorem cell23_937087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 5].length) (baseStart_937087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_937087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_937087 prefixEnd_937087 := by exact prefixLift 937087
  have htrace : WordTrace (prefixWord ++ tailWord_937087) baseStart_937087 baseEnd_937087 := by
    simpa [prefixWord, tailWord_937087, baseEnd_937087] using wordTrace_append hprefix tailTrace_937087
  have hstable : (prefixWord ++ tailWord_937087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937087).length < 2 ^ (prefixWord ++ tailWord_937087).sum := by decide
  have hdescent : baseEnd_937087 < baseStart_937087 := by decide
  rcases family_descends (prefixWord ++ tailWord_937087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937104 : List Nat := [2, 1, 1, 1, 1, 1, 4, 4, 3, 2, 3]
def baseStart_937104 : Nat := 118140960795 + 937104 * 2 ^ 59
def prefixEnd_937104 : Nat := 4983230072969 + 3 ^ 40 * 937104 * 2
def baseEnd_937104 : Nat := 481184775251006809990343

theorem tailTrace_937104 : CollatzResearch.WordTrace tailWord_937104 prefixEnd_937104 481184775251006809990343 := by
  unfold tailWord_937104
  simp only [CollatzResearch.WordTrace]
  refine ⟨17089495398519863733253183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22785993864693151644337577 17089495398519863733253183)
  ·
    refine ⟨25634243097779795599879775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17089495398519863733253183 25634243097779795599879775)
    ·
      refine ⟨38451364646669693399819663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25634243097779795599879775 38451364646669693399819663)
      ·
        refine ⟨57677046970004540099729495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38451364646669693399819663 57677046970004540099729495)
        ·
          refine ⟨86515570455006810149594243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57677046970004540099729495 86515570455006810149594243)
          ·
            refine ⟨129773355682510215224391365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86515570455006810149594243 129773355682510215224391365)
            ·
              refine ⟨24332504190470665354573381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 129773355682510215224391365 24332504190470665354573381)
              ·
                refine ⟨4562344535713249753982509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24332504190470665354573381 4562344535713249753982509)
                ·
                  refine ⟨1710879200892468657743441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4562344535713249753982509 1710879200892468657743441)
                  ·
                    refine ⟨1283159400669351493307581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1710879200892468657743441 1283159400669351493307581)
                    ·
                      refine ⟨481184775251006809990343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1283159400669351493307581 481184775251006809990343)
                      ·
                        rfl

theorem cell23_937104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 4, 3, 2, 3].length) (baseStart_937104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_937104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_937104 prefixEnd_937104 := by exact prefixLift 937104
  have htrace : WordTrace (prefixWord ++ tailWord_937104) baseStart_937104 baseEnd_937104 := by
    simpa [prefixWord, tailWord_937104, baseEnd_937104] using wordTrace_append hprefix tailTrace_937104
  have hstable : (prefixWord ++ tailWord_937104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937104).length < 2 ^ (prefixWord ++ tailWord_937104).sum := by decide
  have hdescent : baseEnd_937104 < baseStart_937104 := by decide
  rcases family_descends (prefixWord ++ tailWord_937104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937111 : List Nat := [1, 1, 3, 3, 3, 3, 1, 1, 1, 6]
def baseStart_937111 : Nat := 118140960795 + 937111 * 2 ^ 59
def prefixEnd_937111 : Nat := 4983230072969 + 3 ^ 40 * 937111 * 2
def baseEnd_937111 : Nat := 160396123205196094200937

theorem tailTrace_937111 : CollatzResearch.WordTrace tailWord_937111 prefixEnd_937111 160396123205196094200937 := by
  unfold tailWord_937111
  simp only [CollatzResearch.WordTrace]
  refine ⟨34179246108014367662011187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22786164072009578441340791 34179246108014367662011187)
  ·
    refine ⟨51268869162021551493016781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34179246108014367662011187 51268869162021551493016781)
    ·
      refine ⟨19225825935758081809881293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51268869162021551493016781 19225825935758081809881293)
      ·
        refine ⟨7209684725909280678705485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19225825935758081809881293 7209684725909280678705485)
        ·
          refine ⟨2703631772215980254514557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7209684725909280678705485 2703631772215980254514557)
          ·
            refine ⟨1013861914580992595442959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2703631772215980254514557 1013861914580992595442959)
            ·
              refine ⟨1520792871871488893164439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1013861914580992595442959 1520792871871488893164439)
              ·
                refine ⟨2281189307807233339746659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1520792871871488893164439 2281189307807233339746659)
                ·
                  refine ⟨3421783961710850009619989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2281189307807233339746659 3421783961710850009619989)
                  ·
                    refine ⟨160396123205196094200937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3421783961710850009619989 160396123205196094200937)
                    ·
                      rfl

theorem cell23_937111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 1, 1, 1, 6].length) (baseStart_937111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_937111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_937111 prefixEnd_937111 := by exact prefixLift 937111
  have htrace : WordTrace (prefixWord ++ tailWord_937111) baseStart_937111 baseEnd_937111 := by
    simpa [prefixWord, tailWord_937111, baseEnd_937111] using wordTrace_append hprefix tailTrace_937111
  have hstable : (prefixWord ++ tailWord_937111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937111).length < 2 ^ (prefixWord ++ tailWord_937111).sum := by decide
  have hdescent : baseEnd_937111 < baseStart_937111 := by decide
  rcases family_descends (prefixWord ++ tailWord_937111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937118 : List Nat := [4, 3, 1, 1, 2, 1, 1, 4, 1, 1, 4]
def baseStart_937118 : Nat := 118140960795 + 937118 * 2 ^ 59
def prefixEnd_937118 : Nat := 4983230072969 + 3 ^ 40 * 937118 * 2
def baseEnd_937118 : Nat := 481191963980169755215279

theorem tailTrace_937118 : CollatzResearch.WordTrace tailWord_937118 prefixEnd_937118 481191963980169755215279 := by
  unfold tailWord_937118
  simp only [CollatzResearch.WordTrace]
  refine ⟨4272437677373625982189501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22786334279326005238344005 4272437677373625982189501)
  ·
    refine ⟨1602164129015109743321063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4272437677373625982189501 1602164129015109743321063)
    ·
      refine ⟨2403246193522664614981595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1602164129015109743321063 2403246193522664614981595)
      ·
        refine ⟨3604869290283996922472393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2403246193522664614981595 3604869290283996922472393)
        ·
          refine ⟨2703651967712997691854295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3604869290283996922472393 2703651967712997691854295)
          ·
            refine ⟨4055477951569496537781443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2703651967712997691854295 4055477951569496537781443)
            ·
              refine ⟨6083216927354244806672165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4055477951569496537781443 6083216927354244806672165)
              ·
                refine ⟨1140603173878920901251031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6083216927354244806672165 1140603173878920901251031)
                ·
                  refine ⟨1710904760818381351876547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1140603173878920901251031 1710904760818381351876547)
                  ·
                    refine ⟨2566357141227572027814821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1710904760818381351876547 2566357141227572027814821)
                    ·
                      refine ⟨481191963980169755215279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2566357141227572027814821 481191963980169755215279)
                      ·
                        rfl

theorem cell23_937118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 4, 1, 1, 4].length) (baseStart_937118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_937118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_937118 prefixEnd_937118 := by exact prefixLift 937118
  have htrace : WordTrace (prefixWord ++ tailWord_937118) baseStart_937118 baseEnd_937118 := by
    simpa [prefixWord, tailWord_937118, baseEnd_937118] using wordTrace_append hprefix tailTrace_937118
  have hstable : (prefixWord ++ tailWord_937118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937118).length < 2 ^ (prefixWord ++ tailWord_937118).sum := by decide
  have hdescent : baseEnd_937118 < baseStart_937118 := by decide
  rcases family_descends (prefixWord ++ tailWord_937118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937124 : List Nat := [2, 3, 1, 2, 3, 2, 1, 9]
def baseStart_937124 : Nat := 118140960795 + 937124 * 2 ^ 59
def prefixEnd_937124 : Nat := 4983230072969 + 3 ^ 40 * 937124 * 2
def baseEnd_937124 : Nat := 17822038698670249323713

theorem tailTrace_937124 : CollatzResearch.WordTrace tailWord_937124 prefixEnd_937124 17822038698670249323713 := by
  unfold tailWord_937124
  simp only [CollatzResearch.WordTrace]
  refine ⟨17089860128483635441117213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22786480171311513921489617 17089860128483635441117213)
  ·
    refine ⟨6408697548181363290418955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17089860128483635441117213 6408697548181363290418955)
    ·
      refine ⟨9613046322272044935628433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6408697548181363290418955 9613046322272044935628433)
      ·
        refine ⟨7209784741704033701721325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9613046322272044935628433 7209784741704033701721325)
        ·
          refine ⟨2703669278139012638145497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7209784741704033701721325 2703669278139012638145497)
          ·
            refine ⟨2027751958604259478609123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2703669278139012638145497 2027751958604259478609123)
            ·
              refine ⟨3041627937906389217913685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2027751958604259478609123 3041627937906389217913685)
              ·
                refine ⟨17822038698670249323713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3041627937906389217913685 17822038698670249323713)
                ·
                  rfl

theorem cell23_937124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 9].length) (baseStart_937124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_937124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_937124 prefixEnd_937124 := by exact prefixLift 937124
  have htrace : WordTrace (prefixWord ++ tailWord_937124) baseStart_937124 baseEnd_937124 := by
    simpa [prefixWord, tailWord_937124, baseEnd_937124] using wordTrace_append hprefix tailTrace_937124
  have hstable : (prefixWord ++ tailWord_937124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937124).length < 2 ^ (prefixWord ++ tailWord_937124).sum := by decide
  have hdescent : baseEnd_937124 < baseStart_937124 := by decide
  rcases family_descends (prefixWord ++ tailWord_937124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937135 : List Nat := [1, 1, 2, 1, 2, 3, 5, 3, 1, 2, 2]
def baseStart_937135 : Nat := 118140960795 + 937135 * 2 ^ 59
def prefixEnd_937135 : Nat := 4983230072969 + 3 ^ 40 * 937135 * 2
def baseEnd_937135 : Nat := 481200693151296188702701

theorem tailTrace_937135 : CollatzResearch.WordTrace tailWord_937135 prefixEnd_937135 481200693151296188702701 := by
  unfold tailWord_937135
  simp only [CollatzResearch.WordTrace]
  refine ⟨34180121459927419760884859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22786747639951613173923239 34180121459927419760884859)
  ·
    refine ⟨51270182189891129641327289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34180121459927419760884859 51270182189891129641327289)
    ·
      refine ⟨38452636642418347230995467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51270182189891129641327289 38452636642418347230995467)
      ·
        refine ⟨57678954963627520846493201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38452636642418347230995467 57678954963627520846493201)
        ·
          refine ⟨43259216222720640634869901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57678954963627520846493201 43259216222720640634869901)
          ·
            refine ⟨16222206083520240238076213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43259216222720640634869901 16222206083520240238076213)
            ·
              refine ⟨1520831820330022522319645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16222206083520240238076213 1520831820330022522319645)
              ·
                refine ⟨570311932623758445869867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1520831820330022522319645 570311932623758445869867)
                ·
                  refine ⟨855467898935637668804801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 570311932623758445869867 855467898935637668804801)
                  ·
                    refine ⟨641600924201728251603601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 855467898935637668804801 641600924201728251603601)
                    ·
                      refine ⟨481200693151296188702701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 641600924201728251603601 481200693151296188702701)
                      ·
                        rfl

theorem cell23_937135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 5, 3, 1, 2, 2].length) (baseStart_937135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_937135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_937135 prefixEnd_937135 := by exact prefixLift 937135
  have htrace : WordTrace (prefixWord ++ tailWord_937135) baseStart_937135 baseEnd_937135 := by
    simpa [prefixWord, tailWord_937135, baseEnd_937135] using wordTrace_append hprefix tailTrace_937135
  have hstable : (prefixWord ++ tailWord_937135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937135).length < 2 ^ (prefixWord ++ tailWord_937135).sum := by decide
  have hdescent : baseEnd_937135 < baseStart_937135 := by decide
  rcases family_descends (prefixWord ++ tailWord_937135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937151 : List Nat := [1, 1, 2, 2, 2, 2, 4, 1, 4, 1, 3]
def baseStart_937151 : Nat := 118140960795 + 937151 * 2 ^ 59
def prefixEnd_937151 : Nat := 4983230072969 + 3 ^ 40 * 937151 * 2
def baseEnd_937151 : Nat := 481208908841768126102627

theorem tailTrace_937151 : CollatzResearch.WordTrace tailWord_937151 prefixEnd_937151 481208908841768126102627 := by
  unfold tailWord_937151
  simp only [CollatzResearch.WordTrace]
  refine ⟨34180705027869454493467307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22787136685246302995644871 34180705027869454493467307)
  ·
    refine ⟨51271057541804181740200961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34180705027869454493467307 51271057541804181740200961)
    ·
      refine ⟨38453293156353136305150721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51271057541804181740200961 38453293156353136305150721)
      ·
        refine ⟨28839969867264852228863041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38453293156353136305150721 28839969867264852228863041)
        ·
          refine ⟨21629977400448639171647281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28839969867264852228863041 21629977400448639171647281)
          ·
            refine ⟨16222483050336479378735461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21629977400448639171647281 16222483050336479378735461)
            ·
              refine ⟨3041715571938089883512899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16222483050336479378735461 3041715571938089883512899)
              ·
                refine ⟨4562573357907134825269349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3041715571938089883512899 4562573357907134825269349)
                ·
                  refine ⟨855482504607587779738003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4562573357907134825269349 855482504607587779738003)
                  ·
                    refine ⟨1283223756911381669607005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 855482504607587779738003 1283223756911381669607005)
                    ·
                      refine ⟨481208908841768126102627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1283223756911381669607005 481208908841768126102627)
                      ·
                        rfl

theorem cell23_937151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 1, 4, 1, 3].length) (baseStart_937151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_937151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_937151 prefixEnd_937151 := by exact prefixLift 937151
  have htrace : WordTrace (prefixWord ++ tailWord_937151) baseStart_937151 baseEnd_937151 := by
    simpa [prefixWord, tailWord_937151, baseEnd_937151] using wordTrace_append hprefix tailTrace_937151
  have hstable : (prefixWord ++ tailWord_937151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937151).length < 2 ^ (prefixWord ++ tailWord_937151).sum := by decide
  have hdescent : baseEnd_937151 < baseStart_937151 := by decide
  rcases family_descends (prefixWord ++ tailWord_937151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937152 : List Nat := [2, 1, 1, 2, 7, 1, 1, 1, 3, 2, 2]
def baseStart_937152 : Nat := 118140960795 + 937152 * 2 ^ 59
def prefixEnd_937152 : Nat := 4983230072969 + 3 ^ 40 * 937152 * 2
def baseEnd_937152 : Nat := 481209422322422622190123

theorem tailTrace_937152 : CollatzResearch.WordTrace tailWord_937152 prefixEnd_937152 481209422322422622190123 := by
  unfold tailWord_937152
  simp only [CollatzResearch.WordTrace]
  refine ⟨17090370750432915832126855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22787161000577221109502473 17090370750432915832126855)
  ·
    refine ⟨25635556125649373748190283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17090370750432915832126855 25635556125649373748190283)
    ·
      refine ⟨38453334188474060622285425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25635556125649373748190283 38453334188474060622285425)
      ·
        refine ⟨28840000641355545466714069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38453334188474060622285425 28840000641355545466714069)
        ·
          refine ⟨675937515031770596876111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 28840000641355545466714069 675937515031770596876111)
          ·
            refine ⟨1013906272547655895314167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 675937515031770596876111 1013906272547655895314167)
            ·
              refine ⟨1520859408821483842971251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1013906272547655895314167 1520859408821483842971251)
              ·
                refine ⟨2281289113232225764456877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1520859408821483842971251 2281289113232225764456877)
                ·
                  refine ⟨855483417462084661671329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2281289113232225764456877 855483417462084661671329)
                  ·
                    refine ⟨641612563096563496253497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 855483417462084661671329 641612563096563496253497)
                    ·
                      refine ⟨481209422322422622190123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 641612563096563496253497 481209422322422622190123)
                      ·
                        rfl

theorem cell23_937152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 1, 1, 3, 2, 2].length) (baseStart_937152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_937152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_937152 prefixEnd_937152 := by exact prefixLift 937152
  have htrace : WordTrace (prefixWord ++ tailWord_937152) baseStart_937152 baseEnd_937152 := by
    simpa [prefixWord, tailWord_937152, baseEnd_937152] using wordTrace_append hprefix tailTrace_937152
  have hstable : (prefixWord ++ tailWord_937152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937152).length < 2 ^ (prefixWord ++ tailWord_937152).sum := by decide
  have hdescent : baseEnd_937152 < baseStart_937152 := by decide
  rcases family_descends (prefixWord ++ tailWord_937152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937172 : List Nat := [2, 4, 1, 4, 1, 2, 1, 2, 1, 2, 3]
def baseStart_937172 : Nat := 118140960795 + 937172 * 2 ^ 59
def prefixEnd_937172 : Nat := 4983230072969 + 3 ^ 40 * 937172 * 2
def baseEnd_937172 : Nat := 481219691935512543940031

theorem tailTrace_937172 : CollatzResearch.WordTrace tailWord_937172 prefixEnd_937172 481219691935512543940031 := by
  unfold tailWord_937172
  simp only [CollatzResearch.WordTrace]
  refine ⟨17090735480396687539990885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22787647307195583386654513 17090735480396687539990885)
  ·
    refine ⟨3204512902574378913748291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17090735480396687539990885 3204512902574378913748291)
    ·
      refine ⟨4806769353861568370622437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3204512902574378913748291 4806769353861568370622437)
      ·
        refine ⟨901269253849044069491707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4806769353861568370622437 901269253849044069491707)
        ·
          refine ⟨1351903880773566104237561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 901269253849044069491707 1351903880773566104237561)
          ·
            refine ⟨1013927910580174578178171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1351903880773566104237561 1013927910580174578178171)
            ·
              refine ⟨1520891865870261867267257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1013927910580174578178171 1520891865870261867267257)
              ·
                refine ⟨1140668899402696400450443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1520891865870261867267257 1140668899402696400450443)
                ·
                  refine ⟨1711003349104044600675665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1140668899402696400450443 1711003349104044600675665)
                  ·
                    refine ⟨1283252511828033450506749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1711003349104044600675665 1283252511828033450506749)
                    ·
                      refine ⟨481219691935512543940031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1283252511828033450506749 481219691935512543940031)
                      ·
                        rfl

theorem cell23_937172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_937172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_937172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_937172 prefixEnd_937172 := by exact prefixLift 937172
  have htrace : WordTrace (prefixWord ++ tailWord_937172) baseStart_937172 baseEnd_937172 := by
    simpa [prefixWord, tailWord_937172, baseEnd_937172] using wordTrace_append hprefix tailTrace_937172
  have hstable : (prefixWord ++ tailWord_937172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937172).length < 2 ^ (prefixWord ++ tailWord_937172).sum := by decide
  have hdescent : baseEnd_937172 < baseStart_937172 := by decide
  rcases family_descends (prefixWord ++ tailWord_937172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937195 : List Nat := [1, 1, 1, 1, 2, 7, 3, 1, 1, 3, 2]
def baseStart_937195 : Nat := 118140960795 + 937195 * 2 ^ 59
def prefixEnd_937195 : Nat := 4983230072969 + 3 ^ 40 * 937195 * 2
def baseEnd_937195 : Nat := 481231501990565953952425

theorem tailTrace_937195 : CollatzResearch.WordTrace tailWord_937195 prefixEnd_937195 481231501990565953952425 := by
  unfold tailWord_937195
  simp only [CollatzResearch.WordTrace]
  refine ⟨34182309839710050008069039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22788206559806700005379359 34182309839710050008069039)
  ·
    refine ⟨51273464759565075012103559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34182309839710050008069039 51273464759565075012103559)
    ·
      refine ⟨76910197139347612518155339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51273464759565075012103559 76910197139347612518155339)
      ·
        refine ⟨115365295709021418777233009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76910197139347612518155339 115365295709021418777233009)
        ·
          refine ⟨86523971781766064082924757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115365295709021418777233009 86523971781766064082924757)
          ·
            refine ⟨2027905588635142126943549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 86523971781766064082924757 2027905588635142126943549)
            ·
              refine ⟨760464595738178297603831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2027905588635142126943549 760464595738178297603831)
              ·
                refine ⟨1140696893607267446405747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 760464595738178297603831 1140696893607267446405747)
                ·
                  refine ⟨1711045340410901169608621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1140696893607267446405747 1711045340410901169608621)
                  ·
                    refine ⟨641642002654087938603233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1711045340410901169608621 641642002654087938603233)
                    ·
                      refine ⟨481231501990565953952425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 641642002654087938603233 481231501990565953952425)
                      ·
                        rfl

theorem cell23_937195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 3, 1, 1, 3, 2].length) (baseStart_937195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_937195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_937195 prefixEnd_937195 := by exact prefixLift 937195
  have htrace : WordTrace (prefixWord ++ tailWord_937195) baseStart_937195 baseEnd_937195 := by
    simpa [prefixWord, tailWord_937195, baseEnd_937195] using wordTrace_append hprefix tailTrace_937195
  have hstable : (prefixWord ++ tailWord_937195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937195).length < 2 ^ (prefixWord ++ tailWord_937195).sum := by decide
  have hdescent : baseEnd_937195 < baseStart_937195 := by decide
  rcases family_descends (prefixWord ++ tailWord_937195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937218 : List Nat := [3, 4, 1, 1, 3, 1, 1, 1, 2, 6]
def baseStart_937218 : Nat := 118140960795 + 937218 * 2 ^ 59
def prefixEnd_937218 : Nat := 4983230072969 + 3 ^ 40 * 937218 * 2
def baseEnd_937218 : Nat := 160414437348539787988273

theorem tailTrace_937218 : CollatzResearch.WordTrace tailWord_937218 prefixEnd_937218 160414437348539787988273 := by
  unfold tailWord_937218
  simp only [CollatzResearch.WordTrace]
  refine ⟨8545787179656681234039077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22788765812417816624104205 8545787179656681234039077)
  ·
    refine ⟨1602335096185627731382327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8545787179656681234039077 1602335096185627731382327)
    ·
      refine ⟨2403502644278441597073491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1602335096185627731382327 2403502644278441597073491)
      ·
        refine ⟨3605253966417662395610237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2403502644278441597073491 3605253966417662395610237)
        ·
          refine ⟨1351970237406623398353839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3605253966417662395610237 1351970237406623398353839)
          ·
            refine ⟨2027955356109935097530759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1351970237406623398353839 2027955356109935097530759)
            ·
              refine ⟨3041933034164902646296139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2027955356109935097530759 3041933034164902646296139)
              ·
                refine ⟨4562899551247353969444209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3041933034164902646296139 4562899551247353969444209)
                ·
                  refine ⟨3422174663435515477083157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4562899551247353969444209 3422174663435515477083157)
                  ·
                    refine ⟨160414437348539787988273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3422174663435515477083157 160414437348539787988273)
                    ·
                      rfl

theorem cell23_937218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 1, 2, 6].length) (baseStart_937218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_937218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_937218 prefixEnd_937218 := by exact prefixLift 937218
  have htrace : WordTrace (prefixWord ++ tailWord_937218) baseStart_937218 baseEnd_937218 := by
    simpa [prefixWord, tailWord_937218, baseEnd_937218] using wordTrace_append hprefix tailTrace_937218
  have hstable : (prefixWord ++ tailWord_937218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937218).length < 2 ^ (prefixWord ++ tailWord_937218).sum := by decide
  have hdescent : baseEnd_937218 < baseStart_937218 := by decide
  rcases family_descends (prefixWord ++ tailWord_937218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937246 : List Nat := [4, 3, 2, 1, 2, 2, 2, 1, 1, 3, 2]
def baseStart_937246 : Nat := 118140960795 + 937246 * 2 ^ 59
def prefixEnd_937246 : Nat := 4983230072969 + 3 ^ 40 * 937246 * 2
def baseEnd_937246 : Nat := 481257689503945254414691

theorem tailTrace_937246 : CollatzResearch.WordTrace tailWord_937246 prefixEnd_937246 481257689503945254414691 := by
  unfold tailWord_937246
  simp only [CollatzResearch.WordTrace]
  refine ⟨4273021245315660714771949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22789446641683523812117061 4273021245315660714771949)
  ·
    refine ⟨1602382966993372768039481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4273021245315660714771949 1602382966993372768039481)
    ·
      refine ⟨1201787225245029576029611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1602382966993372768039481 1201787225245029576029611)
      ·
        refine ⟨1802680837867544364044417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1201787225245029576029611 1802680837867544364044417)
        ·
          refine ⟨1352010628400658273033313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1802680837867544364044417 1352010628400658273033313)
          ·
            refine ⟨1014007971300493704774985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1352010628400658273033313 1014007971300493704774985)
            ·
              refine ⟨760505978475370278581239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1014007971300493704774985 760505978475370278581239)
              ·
                refine ⟨1140758967713055417871859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 760505978475370278581239 1140758967713055417871859)
                ·
                  refine ⟨1711138451569583126807789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1140758967713055417871859 1711138451569583126807789)
                  ·
                    refine ⟨641676919338593672552921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1711138451569583126807789 641676919338593672552921)
                    ·
                      refine ⟨481257689503945254414691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 641676919338593672552921 481257689503945254414691)
                      ·
                        rfl

theorem cell23_937246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 2, 1, 1, 3, 2].length) (baseStart_937246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_937246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_937246 prefixEnd_937246 := by exact prefixLift 937246
  have htrace : WordTrace (prefixWord ++ tailWord_937246) baseStart_937246 baseEnd_937246 := by
    simpa [prefixWord, tailWord_937246, baseEnd_937246] using wordTrace_append hprefix tailTrace_937246
  have hstable : (prefixWord ++ tailWord_937246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937246).length < 2 ^ (prefixWord ++ tailWord_937246).sum := by decide
  have hdescent : baseEnd_937246 < baseStart_937246 := by decide
  rcases family_descends (prefixWord ++ tailWord_937246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937258 : List Nat := [3, 1, 4, 2, 1, 1, 1, 2, 2, 3, 3]
def baseStart_937258 : Nat := 118140960795 + 937258 * 2 ^ 59
def prefixEnd_937258 : Nat := 4983230072969 + 3 ^ 40 * 937258 * 2
def baseEnd_937258 : Nat := 481263851271799207464635

theorem tailTrace_937258 : CollatzResearch.WordTrace tailWord_937258 prefixEnd_937258 481263851271799207464635 := by
  unfold tailWord_937258
  simp only [CollatzResearch.WordTrace]
  refine ⟨8546151909620452941903107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22789738425654541178408285 8546151909620452941903107)
  ·
    refine ⟨12819227864430679412854661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8546151909620452941903107 12819227864430679412854661)
    ·
      refine ⟨2403605224580752389910249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12819227864430679412854661 2403605224580752389910249)
      ·
        refine ⟨1802703918435564292432687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2403605224580752389910249 1802703918435564292432687)
        ·
          refine ⟨2704055877653346438649031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1802703918435564292432687 2704055877653346438649031)
          ·
            refine ⟨4056083816480019657973547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2704055877653346438649031 4056083816480019657973547)
            ·
              refine ⟨6084125724720029486960321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4056083816480019657973547 6084125724720029486960321)
              ·
                refine ⟨4563094293540022115220241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6084125724720029486960321 4563094293540022115220241)
                ·
                  refine ⟨3422320720155016586415181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4563094293540022115220241 3422320720155016586415181)
                  ·
                    refine ⟨1283370270058131219905693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3422320720155016586415181 1283370270058131219905693)
                    ·
                      refine ⟨481263851271799207464635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1283370270058131219905693 481263851271799207464635)
                      ·
                        rfl

theorem cell23_937258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_937258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_937258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_937258 prefixEnd_937258 := by exact prefixLift 937258
  have htrace : WordTrace (prefixWord ++ tailWord_937258) baseStart_937258 baseEnd_937258 := by
    simpa [prefixWord, tailWord_937258, baseEnd_937258] using wordTrace_append hprefix tailTrace_937258
  have hstable : (prefixWord ++ tailWord_937258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937258).length < 2 ^ (prefixWord ++ tailWord_937258).sum := by decide
  have hdescent : baseEnd_937258 < baseStart_937258 := by decide
  rcases family_descends (prefixWord ++ tailWord_937258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937304 : List Nat := [2, 1, 2, 2, 1, 1, 3, 1, 10]
def baseStart_937304 : Nat := 118140960795 + 937304 * 2 ^ 59
def prefixEnd_937304 : Nat := 4983230072969 + 3 ^ 40 * 937304 * 2
def baseEnd_937304 : Nat := 53476385709100669721047

theorem tailTrace_937304 : CollatzResearch.WordTrace tailWord_937304 prefixEnd_937304 53476385709100669721047 := by
  unfold tailWord_937304
  simp only [CollatzResearch.WordTrace]
  refine ⟨17093142698157580811893483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22790856930876774415857977 17093142698157580811893483)
  ·
    refine ⟨25639714047236371217840225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17093142698157580811893483 25639714047236371217840225)
    ·
      refine ⟨19229785535427278413380169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25639714047236371217840225 19229785535427278413380169)
      ·
        refine ⟨14422339151570458810035127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19229785535427278413380169 14422339151570458810035127)
        ·
          refine ⟨21633508727355688215052691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14422339151570458810035127 21633508727355688215052691)
          ·
            refine ⟨32450263091033532322579037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21633508727355688215052691 32450263091033532322579037)
            ·
              refine ⟨12168848659137574620967139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32450263091033532322579037 12168848659137574620967139)
              ·
                refine ⟨18253272988706361931450709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12168848659137574620967139 18253272988706361931450709)
                ·
                  refine ⟨53476385709100669721047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 18253272988706361931450709 53476385709100669721047)
                  ·
                    rfl

theorem cell23_937304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 10].length) (baseStart_937304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_937304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_937304 prefixEnd_937304 := by exact prefixLift 937304
  have htrace : WordTrace (prefixWord ++ tailWord_937304) baseStart_937304 baseEnd_937304 := by
    simpa [prefixWord, tailWord_937304, baseEnd_937304] using wordTrace_append hprefix tailTrace_937304
  have hstable : (prefixWord ++ tailWord_937304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937304).length < 2 ^ (prefixWord ++ tailWord_937304).sum := by decide
  have hdescent : baseEnd_937304 < baseStart_937304 := by decide
  rcases family_descends (prefixWord ++ tailWord_937304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937325 : List Nat := [1, 5, 1, 1, 1, 5, 1, 1, 3, 4]
def baseStart_937325 : Nat := 118140960795 + 937325 * 2 ^ 59
def prefixEnd_937325 : Nat := 4983230072969 + 3 ^ 40 * 937325 * 2
def baseEnd_937325 : Nat := 160432751491883481775609

theorem tailTrace_937325 : CollatzResearch.WordTrace tailWord_937325 prefixEnd_937325 160432751491883481775609 := by
  unfold tailWord_937325
  simp only [CollatzResearch.WordTrace]
  refine ⟨34187051329239082210301429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22791367552826054806867619 34187051329239082210301429)
  ·
    refine ⟨3205036062116163957215759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34187051329239082210301429 3205036062116163957215759)
    ·
      refine ⟨4807554093174245935823639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3205036062116163957215759 4807554093174245935823639)
      ·
        refine ⟨7211331139761368903735459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4807554093174245935823639 7211331139761368903735459)
        ·
          refine ⟨10816996709642053355603189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7211331139761368903735459 10816996709642053355603189)
          ·
            refine ⟨1014093441528942502087799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10816996709642053355603189 1014093441528942502087799)
            ·
              refine ⟨1521140162293413753131699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1014093441528942502087799 1521140162293413753131699)
              ·
                refine ⟨2281710243440120629697549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1521140162293413753131699 2281710243440120629697549)
                ·
                  refine ⟨855641341290045236136581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2281710243440120629697549 855641341290045236136581)
                  ·
                    refine ⟨160432751491883481775609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 855641341290045236136581 160432751491883481775609)
                    ·
                      rfl

theorem cell23_937325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 1, 1, 3, 4].length) (baseStart_937325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_937325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_937325 prefixEnd_937325 := by exact prefixLift 937325
  have htrace : WordTrace (prefixWord ++ tailWord_937325) baseStart_937325 baseEnd_937325 := by
    simpa [prefixWord, tailWord_937325, baseEnd_937325] using wordTrace_append hprefix tailTrace_937325
  have hstable : (prefixWord ++ tailWord_937325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937325).length < 2 ^ (prefixWord ++ tailWord_937325).sum := by decide
  have hdescent : baseEnd_937325 < baseStart_937325 := by decide
  rcases family_descends (prefixWord ++ tailWord_937325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937375 : List Nat := [1, 1, 2, 5, 1, 2, 2, 2, 2, 3, 2]
def baseStart_937375 : Nat := 118140960795 + 937375 * 2 ^ 59
def prefixEnd_937375 : Nat := 4983230072969 + 3 ^ 40 * 937375 * 2
def baseEnd_937375 : Nat := 481323928508375249701597

theorem tailTrace_937375 : CollatzResearch.WordTrace tailWord_937375 prefixEnd_937375 481323928508375249701597 := by
  unfold tailWord_937375
  simp only [CollatzResearch.WordTrace]
  refine ⟨34188874979057940749621579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22792583319371960499747719 34188874979057940749621579)
  ·
    refine ⟨51283312468586911124432369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34188874979057940749621579 51283312468586911124432369)
    ·
      refine ⟨38462484351440183343324277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51283312468586911124432369 38462484351440183343324277)
      ·
        refine ⟨3605857907947517188436651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38462484351440183343324277 3605857907947517188436651)
        ·
          refine ⟨5408786861921275782654977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3605857907947517188436651 5408786861921275782654977)
          ·
            refine ⟨4056590146440956836991233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5408786861921275782654977 4056590146440956836991233)
            ·
              refine ⟨3042442609830717627743425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4056590146440956836991233 3042442609830717627743425)
              ·
                refine ⟨2281831957373038220807569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3042442609830717627743425 2281831957373038220807569)
                ·
                  refine ⟨1711373968029778665605677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2281831957373038220807569 1711373968029778665605677)
                  ·
                    refine ⟨641765238011166999602129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1711373968029778665605677 641765238011166999602129)
                    ·
                      refine ⟨481323928508375249701597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 641765238011166999602129 481323928508375249701597)
                      ·
                        rfl

theorem cell23_937375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 2, 2, 3, 2].length) (baseStart_937375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_937375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_937375 prefixEnd_937375 := by exact prefixLift 937375
  have htrace : WordTrace (prefixWord ++ tailWord_937375) baseStart_937375 baseEnd_937375 := by
    simpa [prefixWord, tailWord_937375, baseEnd_937375] using wordTrace_append hprefix tailTrace_937375
  have hstable : (prefixWord ++ tailWord_937375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937375).length < 2 ^ (prefixWord ++ tailWord_937375).sum := by decide
  have hdescent : baseEnd_937375 < baseStart_937375 := by decide
  rcases family_descends (prefixWord ++ tailWord_937375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937391 : List Nat := [1, 1, 2, 1, 2, 2, 1, 6, 1, 1, 5]
def baseStart_937391 : Nat := 118140960795 + 937391 * 2 ^ 59
def prefixEnd_937391 : Nat := 4983230072969 + 3 ^ 40 * 937391 * 2
def baseEnd_937391 : Nat := 481332144198847187101523

theorem tailTrace_937391 : CollatzResearch.WordTrace tailWord_937391 prefixEnd_937391 481332144198847187101523 := by
  unfold tailWord_937391
  simp only [CollatzResearch.WordTrace]
  refine ⟨34189458546999975482204027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22792972364666650321469351 34189458546999975482204027)
  ·
    refine ⟨51284187820499963223306041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34189458546999975482204027 51284187820499963223306041)
    ·
      refine ⟨38463140865374972417479531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51284187820499963223306041 38463140865374972417479531)
      ·
        refine ⟨57694711298062458626219297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38463140865374972417479531 57694711298062458626219297)
        ·
          refine ⟨43271033473546843969664473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57694711298062458626219297 43271033473546843969664473)
          ·
            refine ⟨32453275105160132977248355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43271033473546843969664473 32453275105160132977248355)
            ·
              refine ⟨48679912657740199465872533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32453275105160132977248355 48679912657740199465872533)
              ·
                refine ⟨2281870905831571849962775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 48679912657740199465872533 2281870905831571849962775)
                ·
                  refine ⟨3422806358747357774944163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2281870905831571849962775 3422806358747357774944163)
                  ·
                    refine ⟨5134209538121036662416245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3422806358747357774944163 5134209538121036662416245)
                    ·
                      refine ⟨481332144198847187101523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5134209538121036662416245 481332144198847187101523)
                      ·
                        rfl

theorem cell23_937391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 6, 1, 1, 5].length) (baseStart_937391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_937391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_937391 prefixEnd_937391 := by exact prefixLift 937391
  have htrace : WordTrace (prefixWord ++ tailWord_937391) baseStart_937391 baseEnd_937391 := by
    simpa [prefixWord, tailWord_937391, baseEnd_937391] using wordTrace_append hprefix tailTrace_937391
  have hstable : (prefixWord ++ tailWord_937391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937391).length < 2 ^ (prefixWord ++ tailWord_937391).sum := by decide
  have hdescent : baseEnd_937391 < baseStart_937391 := by decide
  rcases family_descends (prefixWord ++ tailWord_937391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937408 : List Nat := [2, 1, 1, 2, 3, 1, 4, 1, 3, 2, 3]
def baseStart_937408 : Nat := 118140960795 + 937408 * 2 ^ 59
def prefixEnd_937408 : Nat := 4983230072969 + 3 ^ 40 * 937408 * 2
def baseEnd_937408 : Nat := 481340873369973620588945

theorem tailTrace_937408 : CollatzResearch.WordTrace tailWord_937408 prefixEnd_937408 481340873369973620588945 := by
  unfold tailWord_937408
  simp only [CollatzResearch.WordTrace]
  refine ⟨17095039293969193692786439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22793385725292258257048585 17095039293969193692786439)
  ·
    refine ⟨25642558940953790539179659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17095039293969193692786439 25642558940953790539179659)
    ·
      refine ⟨38463838411430685808769489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25642558940953790539179659 38463838411430685808769489)
      ·
        refine ⟨28847878808573014356577117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38463838411430685808769489 28847878808573014356577117)
        ·
          refine ⟨10817954553214880383716419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28847878808573014356577117 10817954553214880383716419)
          ·
            refine ⟨16226931829822320575574629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10817954553214880383716419 16226931829822320575574629)
            ·
              refine ⟨3042549718091685107920243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16226931829822320575574629 3042549718091685107920243)
              ·
                refine ⟨4563824577137527661880365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3042549718091685107920243 4563824577137527661880365)
                ·
                  refine ⟨1711434216426572873205137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4563824577137527661880365 1711434216426572873205137)
                  ·
                    refine ⟨1283575662319929654903853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1711434216426572873205137 1283575662319929654903853)
                    ·
                      refine ⟨481340873369973620588945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1283575662319929654903853 481340873369973620588945)
                      ·
                        rfl

theorem cell23_937408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 1, 3, 2, 3].length) (baseStart_937408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_937408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_937408 prefixEnd_937408 := by exact prefixLift 937408
  have htrace : WordTrace (prefixWord ++ tailWord_937408) baseStart_937408 baseEnd_937408 := by
    simpa [prefixWord, tailWord_937408, baseEnd_937408] using wordTrace_append hprefix tailTrace_937408
  have hstable : (prefixWord ++ tailWord_937408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937408).length < 2 ^ (prefixWord ++ tailWord_937408).sum := by decide
  have hdescent : baseEnd_937408 < baseStart_937408 := by decide
  rcases family_descends (prefixWord ++ tailWord_937408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937418 : List Nat := [3, 1, 2, 1, 2, 3, 2, 2, 1, 2, 4]
def baseStart_937418 : Nat := 118140960795 + 937418 * 2 ^ 59
def prefixEnd_937418 : Nat := 4983230072969 + 3 ^ 40 * 937418 * 2
def baseEnd_937418 : Nat := 481346008176518581463899

theorem tailTrace_937418 : CollatzResearch.WordTrace tailWord_937418 prefixEnd_937418 481346008176518581463899 := by
  unfold tailWord_937418
  simp only [CollatzResearch.WordTrace]
  refine ⟨8547610829475539773359227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22793628878601439395624605 8547610829475539773359227)
  ·
    refine ⟨12821416244213309660038841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8547610829475539773359227 12821416244213309660038841)
    ·
      refine ⟨9616062183159982245029131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12821416244213309660038841 9616062183159982245029131)
      ·
        refine ⟨14424093274739973367543697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9616062183159982245029131 14424093274739973367543697)
        ·
          refine ⟨10818069956054980025657773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14424093274739973367543697 10818069956054980025657773)
          ·
            refine ⟨4056776233520617509621665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10818069956054980025657773 4056776233520617509621665)
            ·
              refine ⟨3042582175140463132216249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4056776233520617509621665 3042582175140463132216249)
              ·
                refine ⟨2281936631355347349162187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3042582175140463132216249 2281936631355347349162187)
                ·
                  refine ⟨3422904947033021023743281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2281936631355347349162187 3422904947033021023743281)
                  ·
                    refine ⟨2567178710274765767807461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3422904947033021023743281 2567178710274765767807461)
                    ·
                      refine ⟨481346008176518581463899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2567178710274765767807461 481346008176518581463899)
                      ·
                        rfl

theorem cell23_937418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 2, 1, 2, 4].length) (baseStart_937418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_937418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_937418 prefixEnd_937418 := by exact prefixLift 937418
  have htrace : WordTrace (prefixWord ++ tailWord_937418) baseStart_937418 baseEnd_937418 := by
    simpa [prefixWord, tailWord_937418, baseEnd_937418] using wordTrace_append hprefix tailTrace_937418
  have hstable : (prefixWord ++ tailWord_937418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937418).length < 2 ^ (prefixWord ++ tailWord_937418).sum := by decide
  have hdescent : baseEnd_937418 < baseStart_937418 := by decide
  rcases family_descends (prefixWord ++ tailWord_937418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937428 : List Nat := [2, 4, 1, 2, 3, 1, 10]
def baseStart_937428 : Nat := 118140960795 + 937428 * 2 ^ 59
def prefixEnd_937428 : Nat := 4983230072969 + 3 ^ 40 * 937428 * 2
def baseEnd_937428 : Nat := 5942606703494611633813

theorem tailTrace_937428 : CollatzResearch.WordTrace tailWord_937428 prefixEnd_937428 5942606703494611633813 := by
  unfold tailWord_937428
  simp only [CollatzResearch.WordTrace]
  refine ⟨17095404023932965400650469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22793872031910620534200625 17095404023932965400650469)
  ·
    refine ⟨3205388254487431012621963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17095404023932965400650469 3205388254487431012621963)
    ·
      refine ⟨4808082381731146518932945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3205388254487431012621963 4808082381731146518932945)
      ·
        refine ⟨3606061786298359889199709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4808082381731146518932945 3606061786298359889199709)
        ·
          refine ⟨1352273169861884958449891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3606061786298359889199709 1352273169861884958449891)
          ·
            refine ⟨2028409754792827437674837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1352273169861884958449891 2028409754792827437674837)
            ·
              refine ⟨5942606703494611633813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2028409754792827437674837 5942606703494611633813)
              ·
                rfl

theorem cell23_937428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 10].length) (baseStart_937428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_937428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_937428 prefixEnd_937428 := by exact prefixLift 937428
  have htrace : WordTrace (prefixWord ++ tailWord_937428) baseStart_937428 baseEnd_937428 := by
    simpa [prefixWord, tailWord_937428, baseEnd_937428] using wordTrace_append hprefix tailTrace_937428
  have hstable : (prefixWord ++ tailWord_937428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937428).length < 2 ^ (prefixWord ++ tailWord_937428).sum := by decide
  have hdescent : baseEnd_937428 < baseStart_937428 := by decide
  rcases family_descends (prefixWord ++ tailWord_937428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937455 : List Nat := [1, 1, 2, 1, 4, 1, 2, 5, 2, 1, 3]
def baseStart_937455 : Nat := 118140960795 + 937455 * 2 ^ 59
def prefixEnd_937455 : Nat := 4983230072969 + 3 ^ 40 * 937455 * 2
def baseEnd_937455 : Nat := 481365006960734936701229

theorem tailTrace_937455 : CollatzResearch.WordTrace tailWord_937455 prefixEnd_937455 481365006960734936701229 := by
  unfold tailWord_937455
  simp only [CollatzResearch.WordTrace]
  refine ⟨34191792818768114412533819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22794528545845409608355879 34191792818768114412533819)
  ·
    refine ⟨51287689228152171618800729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34191792818768114412533819 51287689228152171618800729)
    ·
      refine ⟨38465766921114128714100547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51287689228152171618800729 38465766921114128714100547)
      ·
        refine ⟨57698650381671193071150821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38465766921114128714100547 57698650381671193071150821)
        ·
          refine ⟨10818496946563348700840779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57698650381671193071150821 10818496946563348700840779)
          ·
            refine ⟨16227745419845023051261169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10818496946563348700840779 16227745419845023051261169)
            ·
              refine ⟨12170809064883767288445877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16227745419845023051261169 12170809064883767288445877)
              ·
                refine ⟨1141013349832853183291801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12170809064883767288445877 1141013349832853183291801)
                ·
                  refine ⟨855760012374639887468851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1141013349832853183291801 855760012374639887468851)
                  ·
                    refine ⟨1283640018561959831203277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 855760012374639887468851 1283640018561959831203277)
                    ·
                      refine ⟨481365006960734936701229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1283640018561959831203277 481365006960734936701229)
                      ·
                        rfl

theorem cell23_937455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 5, 2, 1, 3].length) (baseStart_937455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_937455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_937455 prefixEnd_937455 := by exact prefixLift 937455
  have htrace : WordTrace (prefixWord ++ tailWord_937455) baseStart_937455 baseEnd_937455 := by
    simpa [prefixWord, tailWord_937455, baseEnd_937455] using wordTrace_append hprefix tailTrace_937455
  have hstable : (prefixWord ++ tailWord_937455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937455).length < 2 ^ (prefixWord ++ tailWord_937455).sum := by decide
  have hdescent : baseEnd_937455 < baseStart_937455 := by decide
  rcases family_descends (prefixWord ++ tailWord_937455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937471 : List Nat := [1, 1, 2, 2, 1, 2, 2, 2, 4, 6]
def baseStart_937471 : Nat := 118140960795 + 937471 * 2 ^ 59
def prefixEnd_937471 : Nat := 4983230072969 + 3 ^ 40 * 937471 * 2
def baseEnd_937471 : Nat := 160457740883735624700385

theorem tailTrace_937471 : CollatzResearch.WordTrace tailWord_937471 prefixEnd_937471 160457740883735624700385 := by
  unfold tailWord_937471
  simp only [CollatzResearch.WordTrace]
  refine ⟨34192376386710149145116267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22794917591140099430077511 34192376386710149145116267)
  ·
    refine ⟨51288564580065223717674401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34192376386710149145116267 51288564580065223717674401)
    ·
      refine ⟨38466423435048917788255801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51288564580065223717674401 38466423435048917788255801)
      ·
        refine ⟨28849817576286688341191851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38466423435048917788255801 28849817576286688341191851)
        ·
          refine ⟨43274726364430032511787777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28849817576286688341191851 43274726364430032511787777)
          ·
            refine ⟨32456044773322524383840833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43274726364430032511787777 32456044773322524383840833)
            ·
              refine ⟨24342033579991893287880625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32456044773322524383840833 24342033579991893287880625)
              ·
                refine ⟨18256525184993919965910469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24342033579991893287880625 18256525184993919965910469)
                ·
                  refine ⟨3423098472186359993608213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18256525184993919965910469 3423098472186359993608213)
                  ·
                    refine ⟨160457740883735624700385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3423098472186359993608213 160457740883735624700385)
                    ·
                      rfl

theorem cell23_937471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 4, 6].length) (baseStart_937471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_937471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_937471 prefixEnd_937471 := by exact prefixLift 937471
  have htrace : WordTrace (prefixWord ++ tailWord_937471) baseStart_937471 baseEnd_937471 := by
    simpa [prefixWord, tailWord_937471, baseEnd_937471] using wordTrace_append hprefix tailTrace_937471
  have hstable : (prefixWord ++ tailWord_937471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937471).length < 2 ^ (prefixWord ++ tailWord_937471).sum := by decide
  have hdescent : baseEnd_937471 < baseStart_937471 := by decide
  rcases family_descends (prefixWord ++ tailWord_937471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937473 : List Nat := [1, 2, 4, 1, 5, 1, 1, 3, 1, 2, 2]
def baseStart_937473 : Nat := 118140960795 + 937473 * 2 ^ 59
def prefixEnd_937473 : Nat := 4983230072969 + 3 ^ 40 * 937473 * 2
def baseEnd_937473 : Nat := 481374249612515866276147

theorem tailTrace_937473 : CollatzResearch.WordTrace tailWord_937473 prefixEnd_937473 481374249612515866276147 := by
  unfold tailWord_937473
  simp only [CollatzResearch.WordTrace]
  refine ⟨34192449332702903486689073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22794966221801935657792715 34192449332702903486689073)
  ·
    refine ⟨25644336999527177615016805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34192449332702903486689073 25644336999527177615016805)
    ·
      refine ⟨4808313187411345802815651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25644336999527177615016805 4808313187411345802815651)
      ·
        refine ⟨7212469781117018704223477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4808313187411345802815651 7212469781117018704223477)
        ·
          refine ⟨676169041979720503520951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7212469781117018704223477 676169041979720503520951)
          ·
            refine ⟨1014253562969580755281427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 676169041979720503520951 1014253562969580755281427)
            ·
              refine ⟨1521380344454371132922141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1014253562969580755281427 1521380344454371132922141)
              ·
                refine ⟨570517629170389174845803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1521380344454371132922141 570517629170389174845803)
                ·
                  refine ⟨855776443755583762268705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 570517629170389174845803 855776443755583762268705)
                  ·
                    refine ⟨641832332816687821701529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 855776443755583762268705 641832332816687821701529)
                    ·
                      refine ⟨481374249612515866276147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 641832332816687821701529 481374249612515866276147)
                      ·
                        rfl

theorem cell23_937473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 1, 3, 1, 2, 2].length) (baseStart_937473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_937473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_937473 prefixEnd_937473 := by exact prefixLift 937473
  have htrace : WordTrace (prefixWord ++ tailWord_937473) baseStart_937473 baseEnd_937473 := by
    simpa [prefixWord, tailWord_937473, baseEnd_937473] using wordTrace_append hprefix tailTrace_937473
  have hstable : (prefixWord ++ tailWord_937473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937473).length < 2 ^ (prefixWord ++ tailWord_937473).sum := by decide
  have hdescent : baseEnd_937473 < baseStart_937473 := by decide
  rcases family_descends (prefixWord ++ tailWord_937473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937482 : List Nat := [3, 1, 2, 2, 2, 2, 2, 3, 1, 3, 2]
def baseStart_937482 : Nat := 118140960795 + 937482 * 2 ^ 59
def prefixEnd_937482 : Nat := 4983230072969 + 3 ^ 40 * 937482 * 2
def baseEnd_937482 : Nat := 481378870938406331063605

theorem tailTrace_937482 : CollatzResearch.WordTrace tailWord_937482 prefixEnd_937482 481378870938406331063605 := by
  unfold tailWord_937482
  simp only [CollatzResearch.WordTrace]
  refine ⟨8548194397417574505941675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22795185059780198682511133 8548194397417574505941675)
  ·
    refine ⟨12822291596126361758912513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8548194397417574505941675 12822291596126361758912513)
    ·
      refine ⟨9616718697094771319184385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12822291596126361758912513 9616718697094771319184385)
      ·
        refine ⟨7212539022821078489388289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9616718697094771319184385 7212539022821078489388289)
        ·
          refine ⟨5409404267115808867041217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7212539022821078489388289 5409404267115808867041217)
          ·
            refine ⟨4057053200336856650280913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5409404267115808867041217 4057053200336856650280913)
            ·
              refine ⟨3042789900252642487710685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4057053200336856650280913 3042789900252642487710685)
              ·
                refine ⟨1141046212594740932891507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3042789900252642487710685 1141046212594740932891507)
                ·
                  refine ⟨1711569318892111399337261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1141046212594740932891507 1711569318892111399337261)
                  ·
                    refine ⟨641838494584541774751473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1711569318892111399337261 641838494584541774751473)
                    ·
                      refine ⟨481378870938406331063605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 641838494584541774751473 481378870938406331063605)
                      ·
                        rfl

theorem cell23_937482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 3, 1, 3, 2].length) (baseStart_937482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_937482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_937482 prefixEnd_937482 := by exact prefixLift 937482
  have htrace : WordTrace (prefixWord ++ tailWord_937482) baseStart_937482 baseEnd_937482 := by
    simpa [prefixWord, tailWord_937482, baseEnd_937482] using wordTrace_append hprefix tailTrace_937482
  have hstable : (prefixWord ++ tailWord_937482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937482).length < 2 ^ (prefixWord ++ tailWord_937482).sum := by decide
  have hdescent : baseEnd_937482 < baseStart_937482 := by decide
  rcases family_descends (prefixWord ++ tailWord_937482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937498 : List Nat := [3, 1, 1, 3, 1, 1, 1, 3, 2, 4, 3]
def baseStart_937498 : Nat := 118140960795 + 937498 * 2 ^ 59
def prefixEnd_937498 : Nat := 4983230072969 + 3 ^ 40 * 937498 * 2
def baseEnd_937498 : Nat := 481387086628878268463531

theorem tailTrace_937498 : CollatzResearch.WordTrace tailWord_937498 prefixEnd_937498 481387086628878268463531 := by
  unfold tailWord_937498
  simp only [CollatzResearch.WordTrace]
  refine ⟨8548340289403083189087287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22795574105074888504232765 8548340289403083189087287)
  ·
    refine ⟨12822510434104624783630931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8548340289403083189087287 12822510434104624783630931)
    ·
      refine ⟨19233765651156937175446397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12822510434104624783630931 19233765651156937175446397)
      ·
        refine ⟨7212662119183851440792399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19233765651156937175446397 7212662119183851440792399)
        ·
          refine ⟨10818993178775777161188599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7212662119183851440792399 10818993178775777161188599)
          ·
            refine ⟨16228489768163665741782899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10818993178775777161188599 16228489768163665741782899)
            ·
              refine ⟨24342734652245498612674349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16228489768163665741782899 24342734652245498612674349)
              ·
                refine ⟨9128525494592061979752881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24342734652245498612674349 9128525494592061979752881)
                ·
                  refine ⟨6846394120944046484814661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9128525494592061979752881 6846394120944046484814661)
                  ·
                    refine ⟨1283698897677008715902749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6846394120944046484814661 1283698897677008715902749)
                    ·
                      refine ⟨481387086628878268463531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1283698897677008715902749 481387086628878268463531)
                      ·
                        rfl

theorem cell23_937498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 3, 2, 4, 3].length) (baseStart_937498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_937498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_937498 prefixEnd_937498 := by exact prefixLift 937498
  have htrace : WordTrace (prefixWord ++ tailWord_937498) baseStart_937498 baseEnd_937498 := by
    simpa [prefixWord, tailWord_937498, baseEnd_937498] using wordTrace_append hprefix tailTrace_937498
  have hstable : (prefixWord ++ tailWord_937498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937498).length < 2 ^ (prefixWord ++ tailWord_937498).sum := by decide
  have hdescent : baseEnd_937498 < baseStart_937498 := by decide
  rcases family_descends (prefixWord ++ tailWord_937498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937568 : List Nat := [2, 1, 1, 3, 2, 1, 1, 4, 1, 3, 4]
def baseStart_937568 : Nat := 118140960795 + 937568 * 2 ^ 59
def prefixEnd_937568 : Nat := 4983230072969 + 3 ^ 40 * 937568 * 2
def baseEnd_937568 : Nat := 481423030274692994588209

theorem tailTrace_937568 : CollatzResearch.WordTrace tailWord_937568 prefixEnd_937568 481423030274692994588209 := by
  unfold tailWord_937568
  simp only [CollatzResearch.WordTrace]
  refine ⟨17097957133679367355698679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22797276178239156474264905 17097957133679367355698679)
  ·
    refine ⟨25646935700519051033548019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17097957133679367355698679 25646935700519051033548019)
    ·
      refine ⟨38470403550778576550322029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25646935700519051033548019 38470403550778576550322029)
      ·
        refine ⟨14426401331541966206370761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38470403550778576550322029 14426401331541966206370761)
        ·
          refine ⟨10819800998656474654778071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14426401331541966206370761 10819800998656474654778071)
          ·
            refine ⟨16229701497984711982167107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10819800998656474654778071 16229701497984711982167107)
            ·
              refine ⟨24344552246977067973250661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16229701497984711982167107 24344552246977067973250661)
              ·
                refine ⟨4564603546308200244984499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24344552246977067973250661 4564603546308200244984499)
                ·
                  refine ⟨6846905319462300367476749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4564603546308200244984499 6846905319462300367476749)
                  ·
                    refine ⟨2567589494798362637803781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6846905319462300367476749 2567589494798362637803781)
                    ·
                      refine ⟨481423030274692994588209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2567589494798362637803781 481423030274692994588209)
                      ·
                        rfl

theorem cell23_937568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 4, 1, 3, 4].length) (baseStart_937568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_937568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_937568 prefixEnd_937568 := by exact prefixLift 937568
  have htrace : WordTrace (prefixWord ++ tailWord_937568) baseStart_937568 baseEnd_937568 := by
    simpa [prefixWord, tailWord_937568, baseEnd_937568] using wordTrace_append hprefix tailTrace_937568
  have hstable : (prefixWord ++ tailWord_937568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937568).length < 2 ^ (prefixWord ++ tailWord_937568).sum := by decide
  have hdescent : baseEnd_937568 < baseStart_937568 := by decide
  rcases family_descends (prefixWord ++ tailWord_937568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937605 : List Nat := [1, 3, 1, 1, 4, 1, 2, 1, 4, 2, 3]
def baseStart_937605 : Nat := 118140960795 + 937605 * 2 ^ 59
def prefixEnd_937605 : Nat := 4983230072969 + 3 ^ 40 * 937605 * 2
def baseEnd_937605 : Nat := 481442029058909349825539

theorem tailTrace_937605 : CollatzResearch.WordTrace tailWord_937605 prefixEnd_937605 481442029058909349825539 := by
  unfold tailWord_937605
  simp only [CollatzResearch.WordTrace]
  refine ⟨34197263768224690030494269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22798175845483126686996179 34197263768224690030494269)
  ·
    refine ⟨12823973913084258761435351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34197263768224690030494269 12823973913084258761435351)
    ·
      refine ⟨19235960869626388142153027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12823973913084258761435351 19235960869626388142153027)
      ·
        refine ⟨28853941304439582213229541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19235960869626388142153027 28853941304439582213229541)
        ·
          refine ⟨5410113994582421664980539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28853941304439582213229541 5410113994582421664980539)
          ·
            refine ⟨8115170991873632497470809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5410113994582421664980539 8115170991873632497470809)
            ·
              refine ⟨6086378243905224373103107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8115170991873632497470809 6086378243905224373103107)
              ·
                refine ⟨9129567365857836559654661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6086378243905224373103107 9129567365857836559654661)
                ·
                  refine ⟨1711793881098344354935249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9129567365857836559654661 1711793881098344354935249)
                  ·
                    refine ⟨1283845410823758266201437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1711793881098344354935249 1283845410823758266201437)
                    ·
                      refine ⟨481442029058909349825539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1283845410823758266201437 481442029058909349825539)
                      ·
                        rfl

theorem cell23_937605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 1, 4, 2, 3].length) (baseStart_937605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_937605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_937605 prefixEnd_937605 := by exact prefixLift 937605
  have htrace : WordTrace (prefixWord ++ tailWord_937605) baseStart_937605 baseEnd_937605 := by
    simpa [prefixWord, tailWord_937605, baseEnd_937605] using wordTrace_append hprefix tailTrace_937605
  have hstable : (prefixWord ++ tailWord_937605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937605).length < 2 ^ (prefixWord ++ tailWord_937605).sum := by decide
  have hdescent : baseEnd_937605 < baseStart_937605 := by decide
  rcases family_descends (prefixWord ++ tailWord_937605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937612 : List Nat := [2, 2, 1, 2, 1, 1, 3, 6, 1, 4]
def baseStart_937612 : Nat := 118140960795 + 937612 * 2 ^ 59
def prefixEnd_937612 : Nat := 4983230072969 + 3 ^ 40 * 937612 * 2
def baseEnd_937612 : Nat := 160481874474496940812669

theorem tailTrace_937612 : CollatzResearch.WordTrace tailWord_937612 prefixEnd_937612 160481874474496940812669 := by
  unfold tailWord_937612
  simp only [CollatzResearch.WordTrace]
  refine ⟨17098759539599665112999545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22798346052799553483999393 17098759539599665112999545)
  ·
    refine ⟨12824069654699748834749659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17098759539599665112999545 12824069654699748834749659)
    ·
      refine ⟨19236104482049623252124489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12824069654699748834749659 19236104482049623252124489)
      ·
        refine ⟨14427078361537217439093367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19236104482049623252124489 14427078361537217439093367)
        ·
          refine ⟨21640617542305826158640051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14427078361537217439093367 21640617542305826158640051)
          ·
            refine ⟨32460926313458739237960077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21640617542305826158640051 32460926313458739237960077)
            ·
              refine ⟨12172847367547027214235029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32460926313458739237960077 12172847367547027214235029)
              ·
                refine ⟨570602220353766900667267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12172847367547027214235029 570602220353766900667267)
                ·
                  refine ⟨855903330530650351000901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 570602220353766900667267 855903330530650351000901)
                  ·
                    refine ⟨160481874474496940812669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 855903330530650351000901 160481874474496940812669)
                    ·
                      rfl

theorem cell23_937612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 6, 1, 4].length) (baseStart_937612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_937612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_937612 prefixEnd_937612 := by exact prefixLift 937612
  have htrace : WordTrace (prefixWord ++ tailWord_937612) baseStart_937612 baseEnd_937612 := by
    simpa [prefixWord, tailWord_937612, baseEnd_937612] using wordTrace_append hprefix tailTrace_937612
  have hstable : (prefixWord ++ tailWord_937612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937612).length < 2 ^ (prefixWord ++ tailWord_937612).sum := by decide
  have hdescent : baseEnd_937612 < baseStart_937612 := by decide
  rcases family_descends (prefixWord ++ tailWord_937612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937676 : List Nat := [2, 2, 1, 5, 3, 1, 2, 1, 6]
def baseStart_937676 : Nat := 118140960795 + 937676 * 2 ^ 59
def prefixEnd_937676 : Nat := 4983230072969 + 3 ^ 40 * 937676 * 2
def baseEnd_937676 : Nat := 53497609576153174670857

theorem tailTrace_937676 : CollatzResearch.WordTrace tailWord_937676 prefixEnd_937676 53497609576153174670857 := by
  unfold tailWord_937676
  simp only [CollatzResearch.WordTrace]
  refine ⟨17099926675483734578164441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22799902233978312770885921 17099926675483734578164441)
  ·
    refine ⟨12824945006612800933623331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17099926675483734578164441 12824945006612800933623331)
    ·
      refine ⟨19237417509919201400434997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12824945006612800933623331 19237417509919201400434997)
      ·
        refine ⟨1803507891554925131290781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19237417509919201400434997 1803507891554925131290781)
        ·
          refine ⟨676315459333096924234043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1803507891554925131290781 676315459333096924234043)
          ·
            refine ⟨1014473188999645386351065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 676315459333096924234043 1014473188999645386351065)
            ·
              refine ⟨760854891749734039763299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1014473188999645386351065 760854891749734039763299)
              ·
                refine ⟨1141282337624601059644949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 760854891749734039763299 1141282337624601059644949)
                ·
                  refine ⟨53497609576153174670857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1141282337624601059644949 53497609576153174670857)
                  ·
                    rfl

theorem cell23_937676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 2, 1, 6].length) (baseStart_937676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_937676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_937676 prefixEnd_937676 := by exact prefixLift 937676
  have htrace : WordTrace (prefixWord ++ tailWord_937676) baseStart_937676 baseEnd_937676 := by
    simpa [prefixWord, tailWord_937676, baseEnd_937676] using wordTrace_append hprefix tailTrace_937676
  have hstable : (prefixWord ++ tailWord_937676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937676).length < 2 ^ (prefixWord ++ tailWord_937676).sum := by decide
  have hdescent : baseEnd_937676 < baseStart_937676 := by decide
  rcases family_descends (prefixWord ++ tailWord_937676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937732 : List Nat := [2, 3, 2, 2, 1, 4, 1, 8]
def baseStart_937732 : Nat := 118140960795 + 937732 * 2 ^ 59
def prefixEnd_937732 : Nat := 4983230072969 + 3 ^ 40 * 937732 * 2
def baseEnd_937732 : Nat := 17833601522297420479165

theorem tailTrace_937732 : CollatzResearch.WordTrace tailWord_937732 prefixEnd_937732 17833601522297420479165 := by
  unfold tailWord_937732
  simp only [CollatzResearch.WordTrace]
  refine ⟨17100947919382295360183725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22801263892509727146911633 17100947919382295360183725)
  ·
    refine ⟨6412855469768360760068897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17100947919382295360183725 6412855469768360760068897)
    ·
      refine ⟨4809641602326270570051673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6412855469768360760068897 4809641602326270570051673)
      ·
        refine ⟨3607231201744702927538755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4809641602326270570051673 3607231201744702927538755)
        ·
          refine ⟨5410846802617054391308133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3607231201744702927538755 5410846802617054391308133)
          ·
            refine ⟨1014533775490697698370275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5410846802617054391308133 1014533775490697698370275)
            ·
              refine ⟨1521800663236046547555413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1014533775490697698370275 1521800663236046547555413)
              ·
                refine ⟨17833601522297420479165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1521800663236046547555413 17833601522297420479165)
                ·
                  rfl

theorem cell23_937732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 1, 8].length) (baseStart_937732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_937732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_937732 prefixEnd_937732 := by exact prefixLift 937732
  have htrace : WordTrace (prefixWord ++ tailWord_937732) baseStart_937732 baseEnd_937732 := by
    simpa [prefixWord, tailWord_937732, baseEnd_937732] using wordTrace_append hprefix tailTrace_937732
  have hstable : (prefixWord ++ tailWord_937732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937732).length < 2 ^ (prefixWord ++ tailWord_937732).sum := by decide
  have hdescent : baseEnd_937732 < baseStart_937732 := by decide
  rcases family_descends (prefixWord ++ tailWord_937732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937742 : List Nat := [4, 1, 1, 2, 1, 1, 3, 3, 1, 3, 3]
def baseStart_937742 : Nat := 118140960795 + 937742 * 2 ^ 59
def prefixEnd_937742 : Nat := 4983230072969 + 3 ^ 40 * 937742 * 2
def baseEnd_937742 : Nat := 481512375908575313812409

theorem tailTrace_937742 : CollatzResearch.WordTrace tailWord_937742 prefixEnd_937742 481512375908575313812409 := by
  unfold tailWord_937742
  simp only [CollatzResearch.WordTrace]
  refine ⟨4275282571091045303528935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22801507045818908285487653 4275282571091045303528935)
  ·
    refine ⟨6412923856636567955293403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4275282571091045303528935 6412923856636567955293403)
    ·
      refine ⟨9619385784954851932940105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6412923856636567955293403 9619385784954851932940105)
      ·
        refine ⟨7214539338716138949705079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9619385784954851932940105 7214539338716138949705079)
        ·
          refine ⟨10821809008074208424557619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7214539338716138949705079 10821809008074208424557619)
          ·
            refine ⟨16232713512111312636836429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10821809008074208424557619 16232713512111312636836429)
            ·
              refine ⟨6087267567041742238813661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16232713512111312636836429 6087267567041742238813661)
              ·
                refine ⟨2282725337640653339555123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6087267567041742238813661 2282725337640653339555123)
                ·
                  refine ⟨3424088006460980009332685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2282725337640653339555123 3424088006460980009332685)
                  ·
                    refine ⟨1284033002422867503499757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3424088006460980009332685 1284033002422867503499757)
                    ·
                      refine ⟨481512375908575313812409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1284033002422867503499757 481512375908575313812409)
                      ·
                        rfl

theorem cell23_937742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 3, 1, 3, 3].length) (baseStart_937742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_937742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_937742 prefixEnd_937742 := by exact prefixLift 937742
  have htrace : WordTrace (prefixWord ++ tailWord_937742) baseStart_937742 baseEnd_937742 := by
    simpa [prefixWord, tailWord_937742, baseEnd_937742] using wordTrace_append hprefix tailTrace_937742
  have hstable : (prefixWord ++ tailWord_937742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937742).length < 2 ^ (prefixWord ++ tailWord_937742).sum := by decide
  have hdescent : baseEnd_937742 < baseStart_937742 := by decide
  rcases family_descends (prefixWord ++ tailWord_937742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937799 : List Nat := [1, 1, 4, 1, 2, 1, 5, 1, 1, 4, 2]
def baseStart_937799 : Nat := 118140960795 + 937799 * 2 ^ 59
def prefixEnd_937799 : Nat := 4983230072969 + 3 ^ 40 * 937799 * 2
def baseEnd_937799 : Nat := 481541644305881590799647

theorem tailTrace_937799 : CollatzResearch.WordTrace tailWord_937799 prefixEnd_937799 481541644305881590799647 := by
  unfold tailWord_937799
  simp only [CollatzResearch.WordTrace]
  refine ⟨34204339529521861163056451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22802893019681240775370967 34204339529521861163056451)
  ·
    refine ⟨51306509294282791744584677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34204339529521861163056451 51306509294282791744584677)
    ·
      refine ⟨9619970492678023452109627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51306509294282791744584677 9619970492678023452109627)
      ·
        refine ⟨14429955739017035178164441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9619970492678023452109627 14429955739017035178164441)
        ·
          refine ⟨10822466804262776383623331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14429955739017035178164441 10822466804262776383623331)
          ·
            refine ⟨16233700206394164575434997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10822466804262776383623331 16233700206394164575434997)
            ·
              refine ⟨1521909394349452928947031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16233700206394164575434997 1521909394349452928947031)
              ·
                refine ⟨2282864091524179393420547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1521909394349452928947031 2282864091524179393420547)
                ·
                  refine ⟨3424296137286269090130821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2282864091524179393420547 3424296137286269090130821)
                  ·
                    refine ⟨642055525741175454399529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3424296137286269090130821 642055525741175454399529)
                    ·
                      refine ⟨481541644305881590799647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 642055525741175454399529 481541644305881590799647)
                      ·
                        rfl

theorem cell23_937799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 5, 1, 1, 4, 2].length) (baseStart_937799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_937799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_937799 prefixEnd_937799 := by exact prefixLift 937799
  have htrace : WordTrace (prefixWord ++ tailWord_937799) baseStart_937799 baseEnd_937799 := by
    simpa [prefixWord, tailWord_937799, baseEnd_937799] using wordTrace_append hprefix tailTrace_937799
  have hstable : (prefixWord ++ tailWord_937799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937799).length < 2 ^ (prefixWord ++ tailWord_937799).sum := by decide
  have hdescent : baseEnd_937799 < baseStart_937799 := by decide
  rcases family_descends (prefixWord ++ tailWord_937799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937872 : List Nat := [2, 1, 1, 1, 1, 1, 2, 7, 2, 1, 4]
def baseStart_937872 : Nat := 118140960795 + 937872 * 2 ^ 59
def prefixEnd_937872 : Nat := 4983230072969 + 3 ^ 40 * 937872 * 2
def baseEnd_937872 : Nat := 481579128393659805186811

theorem tailTrace_937872 : CollatzResearch.WordTrace tailWord_937872 prefixEnd_937872 481579128393659805186811 := by
  unfold tailWord_937872
  simp only [CollatzResearch.WordTrace]
  refine ⟨17103501029128697315231935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22804668038838263086975913 17103501029128697315231935)
  ·
    refine ⟨25655251543693045972847903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17103501029128697315231935 25655251543693045972847903)
    ·
      refine ⟨38482877315539568959271855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25655251543693045972847903 38482877315539568959271855)
      ·
        refine ⟨57724315973309353438907783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38482877315539568959271855 57724315973309353438907783)
        ·
          refine ⟨86586473959964030158361675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57724315973309353438907783 86586473959964030158361675)
          ·
            refine ⟨129879710939946045237542513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86586473959964030158361675 129879710939946045237542513)
            ·
              refine ⟨97409783204959533928156885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129879710939946045237542513 97409783204959533928156885)
              ·
                refine ⟨2283041793866239076441177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 97409783204959533928156885 2283041793866239076441177)
                ·
                  refine ⟨1712281345399679307330883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2283041793866239076441177 1712281345399679307330883)
                  ·
                    refine ⟨2568422018099518960996325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1712281345399679307330883 2568422018099518960996325)
                    ·
                      refine ⟨481579128393659805186811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2568422018099518960996325 481579128393659805186811)
                      ·
                        rfl

theorem cell23_937872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 7, 2, 1, 4].length) (baseStart_937872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_937872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_937872 prefixEnd_937872 := by exact prefixLift 937872
  have htrace : WordTrace (prefixWord ++ tailWord_937872) baseStart_937872 baseEnd_937872 := by
    simpa [prefixWord, tailWord_937872, baseEnd_937872] using wordTrace_append hprefix tailTrace_937872
  have hstable : (prefixWord ++ tailWord_937872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937872).length < 2 ^ (prefixWord ++ tailWord_937872).sum := by decide
  have hdescent : baseEnd_937872 < baseStart_937872 := by decide
  rcases family_descends (prefixWord ++ tailWord_937872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937890 : List Nat := [3, 3, 1, 2, 4, 1, 2, 2, 5]
def baseStart_937890 : Nat := 118140960795 + 937890 * 2 ^ 59
def prefixEnd_937890 : Nat := 4983230072969 + 3 ^ 40 * 937890 * 2
def baseEnd_937890 : Nat := 53509819005048970529081

theorem tailTrace_937890 : CollatzResearch.WordTrace tailWord_937890 prefixEnd_937890 53509819005048970529081 := by
  unfold tailWord_937890
  simp only [CollatzResearch.WordTrace]
  refine ⟨8551914643048045926154781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22805105714794789136412749 8551914643048045926154781)
  ·
    refine ⟨3206967991143017222308043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8551914643048045926154781 3206967991143017222308043)
    ·
      refine ⟨4810451986714525833462065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3206967991143017222308043 4810451986714525833462065)
      ·
        refine ⟨3607838990035894375096549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4810451986714525833462065 3607838990035894375096549)
        ·
          refine ⟨676469810631730195330603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3607838990035894375096549 676469810631730195330603)
          ·
            refine ⟨1014704715947595292995905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 676469810631730195330603 1014704715947595292995905)
            ·
              refine ⟨761028536960696469746929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1014704715947595292995905 761028536960696469746929)
              ·
                refine ⟨570771402720522352310197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 761028536960696469746929 570771402720522352310197)
                ·
                  refine ⟨53509819005048970529081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 570771402720522352310197 53509819005048970529081)
                  ·
                    rfl

theorem cell23_937890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 2, 2, 5].length) (baseStart_937890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_937890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_937890 prefixEnd_937890 := by exact prefixLift 937890
  have htrace : WordTrace (prefixWord ++ tailWord_937890) baseStart_937890 baseEnd_937890 := by
    simpa [prefixWord, tailWord_937890, baseEnd_937890] using wordTrace_append hprefix tailTrace_937890
  have hstable : (prefixWord ++ tailWord_937890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937890).length < 2 ^ (prefixWord ++ tailWord_937890).sum := by decide
  have hdescent : baseEnd_937890 < baseStart_937890 := by decide
  rcases family_descends (prefixWord ++ tailWord_937890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937912 : List Nat := [2, 1, 2, 1, 2, 3, 1, 5, 6]
def baseStart_937912 : Nat := 118140960795 + 937912 * 2 ^ 59
def prefixEnd_937912 : Nat := 4983230072969 + 3 ^ 40 * 937912 * 2
def baseEnd_937912 : Nat := 53511074179982183187403

theorem tailTrace_937912 : CollatzResearch.WordTrace tailWord_937912 prefixEnd_937912 53511074179982183187403 := by
  unfold tailWord_937912
  simp only [CollatzResearch.WordTrace]
  refine ⟨17104230489056240730959995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22805640652074987641279993 17104230489056240730959995)
  ·
    refine ⟨25656345733584361096439993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17104230489056240730959995 25656345733584361096439993)
    ·
      refine ⟨19242259300188270822329995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25656345733584361096439993 19242259300188270822329995)
      ·
        refine ⟨28863388950282406233494993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19242259300188270822329995 28863388950282406233494993)
        ·
          refine ⟨21647541712711804675121245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28863388950282406233494993 21647541712711804675121245)
          ·
            refine ⟨8117828142266926753170467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21647541712711804675121245 8117828142266926753170467)
            ·
              refine ⟨12176742213400390129755701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8117828142266926753170467 12176742213400390129755701)
              ·
                refine ⟨1141569582506286574664597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12176742213400390129755701 1141569582506286574664597)
                ·
                  refine ⟨53511074179982183187403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1141569582506286574664597 53511074179982183187403)
                  ·
                    rfl

theorem cell23_937912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 5, 6].length) (baseStart_937912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_937912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_937912 prefixEnd_937912 := by exact prefixLift 937912
  have htrace : WordTrace (prefixWord ++ tailWord_937912) baseStart_937912 baseEnd_937912 := by
    simpa [prefixWord, tailWord_937912, baseEnd_937912] using wordTrace_append hprefix tailTrace_937912
  have hstable : (prefixWord ++ tailWord_937912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937912).length < 2 ^ (prefixWord ++ tailWord_937912).sum := by decide
  have hdescent : baseEnd_937912 < baseStart_937912 := by decide
  rcases family_descends (prefixWord ++ tailWord_937912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937946 : List Nat := [3, 1, 1, 2, 5, 2, 1, 2, 6]
def baseStart_937946 : Nat := 118140960795 + 937946 * 2 ^ 59
def prefixEnd_937946 : Nat := 4983230072969 + 3 ^ 40 * 937946 * 2
def baseEnd_937946 : Nat := 53513013995788057295719

theorem tailTrace_937946 : CollatzResearch.WordTrace tailWord_937946 prefixEnd_937946 53513013995788057295719 := by
  unfold tailWord_937946
  simp only [CollatzResearch.WordTrace]
  refine ⟨8552425264997326317164423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22806467373326203512438461 8552425264997326317164423)
  ·
    refine ⟨12828637897495989475746635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8552425264997326317164423 12828637897495989475746635)
    ·
      refine ⟨19242956846243984213619953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12828637897495989475746635 19242956846243984213619953)
      ·
        refine ⟨14432217634682988160214965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19242956846243984213619953 14432217634682988160214965)
        ·
          refine ⟨1353020403251530140020153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14432217634682988160214965 1353020403251530140020153)
          ·
            refine ⟨1014765302438647605015115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1353020403251530140020153 1014765302438647605015115)
            ·
              refine ⟨1522147953657971407522673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1014765302438647605015115 1522147953657971407522673)
              ·
                refine ⟨1141610965243478555642005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1522147953657971407522673 1141610965243478555642005)
                ·
                  refine ⟨53513013995788057295719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1141610965243478555642005 53513013995788057295719)
                  ·
                    rfl

theorem cell23_937946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 1, 2, 6].length) (baseStart_937946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_937946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_937946 prefixEnd_937946 := by exact prefixLift 937946
  have htrace : WordTrace (prefixWord ++ tailWord_937946) baseStart_937946 baseEnd_937946 := by
    simpa [prefixWord, tailWord_937946, baseEnd_937946] using wordTrace_append hprefix tailTrace_937946
  have hstable : (prefixWord ++ tailWord_937946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937946).length < 2 ^ (prefixWord ++ tailWord_937946).sum := by decide
  have hdescent : baseEnd_937946 < baseStart_937946 := by decide
  rcases family_descends (prefixWord ++ tailWord_937946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937956 : List Nat := [2, 3, 1, 1, 1, 1, 6, 1, 3, 1, 3]
def baseStart_937956 : Nat := 118140960795 + 937956 * 2 ^ 59
def prefixEnd_937956 : Nat := 4983230072969 + 3 ^ 40 * 937956 * 2
def baseEnd_937956 : Nat := 481622260768637476536425

theorem tailTrace_937956 : CollatzResearch.WordTrace tailWord_937956 prefixEnd_937956 481622260768637476536425 := by
  unfold tailWord_937956
  simp only [CollatzResearch.WordTrace]
  refine ⟨17105032894976538488260861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22806710526635384651014481 17105032894976538488260861)
  ·
    refine ⟨6414387335616201933097823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17105032894976538488260861 6414387335616201933097823)
    ·
      refine ⟨9621581003424302899646735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6414387335616201933097823 9621581003424302899646735)
      ·
        refine ⟨14432371505136454349470103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9621581003424302899646735 14432371505136454349470103)
        ·
          refine ⟨21648557257704681524205155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14432371505136454349470103 21648557257704681524205155)
          ·
            refine ⟨32472835886557022286307733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21648557257704681524205155 32472835886557022286307733)
            ·
              refine ⟨1522164182182360419670675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 32472835886557022286307733 1522164182182360419670675)
              ·
                refine ⟨2283246273273540629506013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1522164182182360419670675 2283246273273540629506013)
                ·
                  refine ⟨856217352477577736064755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2283246273273540629506013 856217352477577736064755)
                  ·
                    refine ⟨1284326028716366604097133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 856217352477577736064755 1284326028716366604097133)
                    ·
                      refine ⟨481622260768637476536425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1284326028716366604097133 481622260768637476536425)
                      ·
                        rfl

theorem cell23_937956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 6, 1, 3, 1, 3].length) (baseStart_937956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_937956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_937956 prefixEnd_937956 := by exact prefixLift 937956
  have htrace : WordTrace (prefixWord ++ tailWord_937956) baseStart_937956 baseEnd_937956 := by
    simpa [prefixWord, tailWord_937956, baseEnd_937956] using wordTrace_append hprefix tailTrace_937956
  have hstable : (prefixWord ++ tailWord_937956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937956).length < 2 ^ (prefixWord ++ tailWord_937956).sum := by decide
  have hdescent : baseEnd_937956 < baseStart_937956 := by decide
  rcases family_descends (prefixWord ++ tailWord_937956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937966 : List Nat := [4, 1, 2, 1, 3, 1, 1, 2, 1, 5, 2]
def baseStart_937966 : Nat := 118140960795 + 937966 * 2 ^ 59
def prefixEnd_937966 : Nat := 4983230072969 + 3 ^ 40 * 937966 * 2
def baseEnd_937966 : Nat := 481627395575182437411379

theorem tailTrace_937966 : CollatzResearch.WordTrace tailWord_937966 prefixEnd_937966 481627395575182437411379 := by
  unfold tailWord_937966
  simp only [CollatzResearch.WordTrace]
  refine ⟨4276303814989606085548219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22806953679944565789590501 4276303814989606085548219)
  ·
    refine ⟨6414455722484409128322329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4276303814989606085548219 6414455722484409128322329)
    ·
      refine ⟨4810841791863306846241747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6414455722484409128322329 4810841791863306846241747)
      ·
        refine ⟨7216262687794960269362621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4810841791863306846241747 7216262687794960269362621)
        ·
          refine ⟨2706098507923110101010983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7216262687794960269362621 2706098507923110101010983)
          ·
            refine ⟨4059147761884665151516475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2706098507923110101010983 4059147761884665151516475)
            ·
              refine ⟨6088721642826997727274713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4059147761884665151516475 6088721642826997727274713)
              ·
                refine ⟨4566541232120248295456035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6088721642826997727274713 4566541232120248295456035)
                ·
                  refine ⟨6849811848180372443184053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4566541232120248295456035 6849811848180372443184053)
                  ·
                    refine ⟨642169860766909916548505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6849811848180372443184053 642169860766909916548505)
                    ·
                      refine ⟨481627395575182437411379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 642169860766909916548505 481627395575182437411379)
                      ·
                        rfl

theorem cell23_937966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 2, 1, 5, 2].length) (baseStart_937966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_937966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_937966 prefixEnd_937966 := by exact prefixLift 937966
  have htrace : WordTrace (prefixWord ++ tailWord_937966) baseStart_937966 baseEnd_937966 := by
    simpa [prefixWord, tailWord_937966, baseEnd_937966] using wordTrace_append hprefix tailTrace_937966
  have hstable : (prefixWord ++ tailWord_937966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937966).length < 2 ^ (prefixWord ++ tailWord_937966).sum := by decide
  have hdescent : baseEnd_937966 < baseStart_937966 := by decide
  rcases family_descends (prefixWord ++ tailWord_937966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937979 : List Nat := [1, 1, 1, 1, 1, 3, 5, 4, 1, 1, 4]
def baseStart_937979 : Nat := 118140960795 + 937979 * 2 ^ 59
def prefixEnd_937979 : Nat := 4983230072969 + 3 ^ 40 * 937979 * 2
def baseEnd_937979 : Nat := 481634070823690886548819

theorem tailTrace_937979 : CollatzResearch.WordTrace tailWord_937979 prefixEnd_937979 481634070823690886548819 := by
  unfold tailWord_937979
  simp only [CollatzResearch.WordTrace]
  refine ⟨34210904668869751904608991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22807269779246501269739327 34210904668869751904608991)
  ·
    refine ⟨51316357003304627856913487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34210904668869751904608991 51316357003304627856913487)
    ·
      refine ⟨76974535504956941785370231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51316357003304627856913487 76974535504956941785370231)
      ·
        refine ⟨115461803257435412678055347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76974535504956941785370231 115461803257435412678055347)
        ·
          refine ⟨173192704886153119017083021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115461803257435412678055347 173192704886153119017083021)
          ·
            refine ⟨64947264332307419631406133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 173192704886153119017083021 64947264332307419631406133)
            ·
              refine ⟨6088806031153820590444325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64947264332307419631406133 6088806031153820590444325)
              ·
                refine ⟨1141651130841341360708311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6088806031153820590444325 1141651130841341360708311)
                ·
                  refine ⟨1712476696262012041062467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1141651130841341360708311 1712476696262012041062467)
                  ·
                    refine ⟨2568715044393018061593701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1712476696262012041062467 2568715044393018061593701)
                    ·
                      refine ⟨481634070823690886548819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2568715044393018061593701 481634070823690886548819)
                      ·
                        rfl

theorem cell23_937979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 4, 1, 1, 4].length) (baseStart_937979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_937979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_937979 prefixEnd_937979 := by exact prefixLift 937979
  have htrace : WordTrace (prefixWord ++ tailWord_937979) baseStart_937979 baseEnd_937979 := by
    simpa [prefixWord, tailWord_937979, baseEnd_937979] using wordTrace_append hprefix tailTrace_937979
  have hstable : (prefixWord ++ tailWord_937979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937979).length < 2 ^ (prefixWord ++ tailWord_937979).sum := by decide
  have hdescent : baseEnd_937979 < baseStart_937979 := by decide
  rcases family_descends (prefixWord ++ tailWord_937979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937989 : List Nat := [1, 3, 1, 1, 2, 4, 1, 2, 4, 4]
def baseStart_937989 : Nat := 118140960795 + 937989 * 2 ^ 59
def prefixEnd_937989 : Nat := 4983230072969 + 3 ^ 40 * 937989 * 2
def baseEnd_937989 : Nat := 160546401876745282474591

theorem tailTrace_937989 : CollatzResearch.WordTrace tailWord_937989 prefixEnd_937989 160546401876745282474591 := by
  unfold tailWord_937989
  simp only [CollatzResearch.WordTrace]
  refine ⟨34211269398833523612473021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22807512932555682408315347 34211269398833523612473021)
  ·
    refine ⟨12829226024562571354677383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34211269398833523612473021 12829226024562571354677383)
    ·
      refine ⟨19243839036843857032016075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12829226024562571354677383 19243839036843857032016075)
      ·
        refine ⟨28865758555265785548024113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19243839036843857032016075 28865758555265785548024113)
        ·
          refine ⟨21649318916449339161018085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28865758555265785548024113 21649318916449339161018085)
          ·
            refine ⟨4059247296834251092690891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21649318916449339161018085 4059247296834251092690891)
            ·
              refine ⟨6088870945251376639036337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4059247296834251092690891 6088870945251376639036337)
              ·
                refine ⟨4566653208938532479277253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6088870945251376639036337 4566653208938532479277253)
                ·
                  refine ⟨856247476675974839864485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4566653208938532479277253 856247476675974839864485)
                  ·
                    refine ⟨160546401876745282474591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 856247476675974839864485 160546401876745282474591)
                    ·
                      rfl

theorem cell23_937989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 2, 4, 4].length) (baseStart_937989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_937989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_937989 prefixEnd_937989 := by exact prefixLift 937989
  have htrace : WordTrace (prefixWord ++ tailWord_937989) baseStart_937989 baseEnd_937989 := by
    simpa [prefixWord, tailWord_937989, baseEnd_937989] using wordTrace_append hprefix tailTrace_937989
  have hstable : (prefixWord ++ tailWord_937989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937989).length < 2 ^ (prefixWord ++ tailWord_937989).sum := by decide
  have hdescent : baseEnd_937989 < baseStart_937989 := by decide
  rcases family_descends (prefixWord ++ tailWord_937989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938007 : List Nat := [1, 1, 3, 5, 2, 1, 3, 2, 1, 1, 3]
def baseStart_938007 : Nat := 118140960795 + 938007 * 2 ^ 59
def prefixEnd_938007 : Nat := 4983230072969 + 3 ^ 40 * 938007 * 2
def baseEnd_938007 : Nat := 481648448282016776998691

theorem tailTrace_938007 : CollatzResearch.WordTrace tailWord_938007 prefixEnd_938007 481648448282016776998691 := by
  unfold tailWord_938007
  simp only [CollatzResearch.WordTrace]
  refine ⟨34211925912768312686628275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22807950608512208457752183 34211925912768312686628275)
  ·
    refine ⟨51317888869152469029942413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34211925912768312686628275 51317888869152469029942413)
    ·
      refine ⟨19244208325932175886228405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51317888869152469029942413 19244208325932175886228405)
      ·
        refine ⟨1804144530556141489333913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19244208325932175886228405 1804144530556141489333913)
        ·
          refine ⟨1353108397917106117000435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1804144530556141489333913 1353108397917106117000435)
          ·
            refine ⟨2029662596875659175500653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1353108397917106117000435 2029662596875659175500653)
            ·
              refine ⟨761123473828372190812745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2029662596875659175500653 761123473828372190812745)
              ·
                refine ⟨570842605371279143109559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 761123473828372190812745 570842605371279143109559)
                ·
                  refine ⟨856263908056918714664339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 570842605371279143109559 856263908056918714664339)
                  ·
                    refine ⟨1284395862085378071996509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 856263908056918714664339 1284395862085378071996509)
                    ·
                      refine ⟨481648448282016776998691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1284395862085378071996509 481648448282016776998691)
                      ·
                        rfl

theorem cell23_938007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 3, 2, 1, 1, 3].length) (baseStart_938007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_938007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_938007 prefixEnd_938007 := by exact prefixLift 938007
  have htrace : WordTrace (prefixWord ++ tailWord_938007) baseStart_938007 baseEnd_938007 := by
    simpa [prefixWord, tailWord_938007, baseEnd_938007] using wordTrace_append hprefix tailTrace_938007
  have hstable : (prefixWord ++ tailWord_938007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938007).length < 2 ^ (prefixWord ++ tailWord_938007).sum := by decide
  have hdescent : baseEnd_938007 < baseStart_938007 := by decide
  rcases family_descends (prefixWord ++ tailWord_938007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938033 : List Nat := [1, 2, 2, 3, 1, 5, 1, 2, 1, 2, 3]
def baseStart_938033 : Nat := 118140960795 + 938033 * 2 ^ 59
def prefixEnd_938033 : Nat := 4983230072969 + 3 ^ 40 * 938033 * 2
def baseEnd_938033 : Nat := 481661798779033675273571

theorem tailTrace_938033 : CollatzResearch.WordTrace tailWord_938033 prefixEnd_938033 481661798779033675273571 := by
  unfold tailWord_938033
  simp only [CollatzResearch.WordTrace]
  refine ⟨34212874210674119127074753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22808582807116079418049835 34212874210674119127074753)
  ·
    refine ⟨25659655658005589345306065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34212874210674119127074753 25659655658005589345306065)
    ·
      refine ⟨19244741743504192008979549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25659655658005589345306065 19244741743504192008979549)
      ·
        refine ⟨7216778153814072003367331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19244741743504192008979549 7216778153814072003367331)
        ·
          refine ⟨10825167230721108005050997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7216778153814072003367331 10825167230721108005050997)
          ·
            refine ⟨1014859427880103875473531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10825167230721108005050997 1014859427880103875473531)
            ·
              refine ⟨1522289141820155813210297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1014859427880103875473531 1522289141820155813210297)
              ·
                refine ⟨1141716856365116859907723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1522289141820155813210297 1141716856365116859907723)
                ·
                  refine ⟨1712575284547675289861585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1141716856365116859907723 1712575284547675289861585)
                  ·
                    refine ⟨1284431463410756467396189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1712575284547675289861585 1284431463410756467396189)
                    ·
                      refine ⟨481661798779033675273571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1284431463410756467396189 481661798779033675273571)
                      ·
                        rfl

theorem cell23_938033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 1, 2, 1, 2, 3].length) (baseStart_938033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_938033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_938033 prefixEnd_938033 := by exact prefixLift 938033
  have htrace : WordTrace (prefixWord ++ tailWord_938033) baseStart_938033 baseEnd_938033 := by
    simpa [prefixWord, tailWord_938033, baseEnd_938033] using wordTrace_append hprefix tailTrace_938033
  have hstable : (prefixWord ++ tailWord_938033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938033).length < 2 ^ (prefixWord ++ tailWord_938033).sum := by decide
  have hdescent : baseEnd_938033 < baseStart_938033 := by decide
  rcases family_descends (prefixWord ++ tailWord_938033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938069 : List Nat := [1, 3, 2, 2, 1, 3, 1, 1, 2, 3, 4]
def baseStart_938069 : Nat := 118140960795 + 938069 * 2 ^ 59
def prefixEnd_938069 : Nat := 4983230072969 + 3 ^ 40 * 938069 * 2
def baseEnd_938069 : Nat := 481680284082595534423405

theorem tailTrace_938069 : CollatzResearch.WordTrace tailWord_938069 prefixEnd_938069 481680284082595534423405 := by
  unfold tailWord_938069
  simp only [CollatzResearch.WordTrace]
  refine ⟨34214187238543697275385261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22809458159029131516923507 34214187238543697275385261)
  ·
    refine ⟨12830320214453886478269473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34214187238543697275385261 12830320214453886478269473)
    ·
      refine ⟨9622740160840414858702105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12830320214453886478269473 9622740160840414858702105)
      ·
        refine ⟨7217055120630311144026579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9622740160840414858702105 7217055120630311144026579)
        ·
          refine ⟨10825582680945466716039869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7217055120630311144026579 10825582680945466716039869)
          ·
            refine ⟨4059593505354550018514951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10825582680945466716039869 4059593505354550018514951)
            ·
              refine ⟨6089390258031825027772427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4059593505354550018514951 6089390258031825027772427)
              ·
                refine ⟨9134085387047737541658641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6089390258031825027772427 9134085387047737541658641)
                ·
                  refine ⟨6850564040285803156243981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9134085387047737541658641 6850564040285803156243981)
                  ·
                    refine ⟨2568961515107176183591493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6850564040285803156243981 2568961515107176183591493)
                    ·
                      refine ⟨481680284082595534423405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2568961515107176183591493 481680284082595534423405)
                      ·
                        rfl

theorem cell23_938069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 1, 2, 3, 4].length) (baseStart_938069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_938069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_938069 prefixEnd_938069 := by exact prefixLift 938069
  have htrace : WordTrace (prefixWord ++ tailWord_938069) baseStart_938069 baseEnd_938069 := by
    simpa [prefixWord, tailWord_938069, baseEnd_938069] using wordTrace_append hprefix tailTrace_938069
  have hstable : (prefixWord ++ tailWord_938069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938069).length < 2 ^ (prefixWord ++ tailWord_938069).sum := by decide
  have hdescent : baseEnd_938069 < baseStart_938069 := by decide
  rcases family_descends (prefixWord ++ tailWord_938069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938089 : List Nat := [1, 2, 1, 1, 1, 5, 1, 2, 2, 4, 3]
def baseStart_938089 : Nat := 118140960795 + 938089 * 2 ^ 59
def prefixEnd_938089 : Nat := 4983230072969 + 3 ^ 40 * 938089 * 2
def baseEnd_938089 : Nat := 481690553695685456173313

theorem tailTrace_938089 : CollatzResearch.WordTrace tailWord_938089 prefixEnd_938089 481690553695685456173313 := by
  unfold tailWord_938089
  simp only [CollatzResearch.WordTrace]
  refine ⟨34214916698471240691113321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22809944465647493794075547 34214916698471240691113321)
  ·
    refine ⟨25661187523853430518334991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34214916698471240691113321 25661187523853430518334991)
    ·
      refine ⟨38491781285780145777502487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25661187523853430518334991 38491781285780145777502487)
      ·
        refine ⟨57737671928670218666253731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38491781285780145777502487 57737671928670218666253731)
        ·
          refine ⟨86606507893005327999380597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57737671928670218666253731 86606507893005327999380597)
          ·
            refine ⟨8119360114969249499941931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 86606507893005327999380597 8119360114969249499941931)
            ·
              refine ⟨12179040172453874249912897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8119360114969249499941931 12179040172453874249912897)
              ·
                refine ⟨9134280129340405687434673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12179040172453874249912897 9134280129340405687434673)
                ·
                  refine ⟨6850710097005304265576005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9134280129340405687434673 6850710097005304265576005)
                  ·
                    refine ⟨1284508143188494549795501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6850710097005304265576005 1284508143188494549795501)
                    ·
                      refine ⟨481690553695685456173313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1284508143188494549795501 481690553695685456173313)
                      ·
                        rfl

theorem cell23_938089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 2, 2, 4, 3].length) (baseStart_938089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_938089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_938089 prefixEnd_938089 := by exact prefixLift 938089
  have htrace : WordTrace (prefixWord ++ tailWord_938089) baseStart_938089 baseEnd_938089 := by
    simpa [prefixWord, tailWord_938089, baseEnd_938089] using wordTrace_append hprefix tailTrace_938089
  have hstable : (prefixWord ++ tailWord_938089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938089).length < 2 ^ (prefixWord ++ tailWord_938089).sum := by decide
  have hdescent : baseEnd_938089 < baseStart_938089 := by decide
  rcases family_descends (prefixWord ++ tailWord_938089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938120 : List Nat := [2, 1, 3, 4, 1, 2, 1, 1, 4, 2, 2]
def baseStart_938120 : Nat := 118140960795 + 938120 * 2 ^ 59
def prefixEnd_938120 : Nat := 4983230072969 + 3 ^ 40 * 938120 * 2
def baseEnd_938120 : Nat := 481706471595974834885671

theorem tailTrace_938120 : CollatzResearch.WordTrace tailWord_938120 prefixEnd_938120 481706471595974834885671 := by
  unfold tailWord_938120
  simp only [CollatzResearch.WordTrace]
  refine ⟨17108023680679466492745907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22810698240905955323661209 17108023680679466492745907)
  ·
    refine ⟨25662035521019199739118861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17108023680679466492745907 25662035521019199739118861)
    ·
      refine ⟨9623263320382199902169573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25662035521019199739118861 9623263320382199902169573)
      ·
        refine ⟨1804361872571662481656795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9623263320382199902169573 1804361872571662481656795)
        ·
          refine ⟨2706542808857493722485193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1804361872571662481656795 2706542808857493722485193)
          ·
            refine ⟨2029907106643120291863895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2706542808857493722485193 2029907106643120291863895)
            ·
              refine ⟨3044860659964680437795843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2029907106643120291863895 3044860659964680437795843)
              ·
                refine ⟨4567290989947020656693765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3044860659964680437795843 4567290989947020656693765)
                ·
                  refine ⟨856367060615066373130081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4567290989947020656693765 856367060615066373130081)
                  ·
                    refine ⟨642275295461299779847561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 856367060615066373130081 642275295461299779847561)
                    ·
                      refine ⟨481706471595974834885671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 642275295461299779847561 481706471595974834885671)
                      ·
                        rfl

theorem cell23_938120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 1, 4, 2, 2].length) (baseStart_938120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_938120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_938120 prefixEnd_938120 := by exact prefixLift 938120
  have htrace : WordTrace (prefixWord ++ tailWord_938120) baseStart_938120 baseEnd_938120 := by
    simpa [prefixWord, tailWord_938120, baseEnd_938120] using wordTrace_append hprefix tailTrace_938120
  have hstable : (prefixWord ++ tailWord_938120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938120).length < 2 ^ (prefixWord ++ tailWord_938120).sum := by decide
  have hdescent : baseEnd_938120 < baseStart_938120 := by decide
  rcases family_descends (prefixWord ++ tailWord_938120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938176 : List Nat := [2, 1, 1, 2, 5, 1, 1, 1, 4, 1, 4]
def baseStart_938176 : Nat := 118140960795 + 938176 * 2 ^ 59
def prefixEnd_938176 : Nat := 4983230072969 + 3 ^ 40 * 938176 * 2
def baseEnd_938176 : Nat := 481735226512626615785413

theorem tailTrace_938176 : CollatzResearch.WordTrace tailWord_938176 prefixEnd_938176 481735226512626615785413 := by
  unfold tailWord_938176
  simp only [CollatzResearch.WordTrace]
  refine ⟨17109044924578027274765191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22812059899437369699686921 17109044924578027274765191)
  ·
    refine ⟨25663567386867040912147787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17109044924578027274765191 25663567386867040912147787)
    ·
      refine ⟨38495351080300561368221681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25663567386867040912147787 38495351080300561368221681)
      ·
        refine ⟨28871513310225421026166261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38495351080300561368221681 28871513310225421026166261)
        ·
          refine ⟨2706704372833633221203087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28871513310225421026166261 2706704372833633221203087)
          ·
            refine ⟨4060056559250449831804631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2706704372833633221203087 4060056559250449831804631)
            ·
              refine ⟨6090084838875674747706947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4060056559250449831804631 6090084838875674747706947)
              ·
                refine ⟨9135127258313512121560421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6090084838875674747706947 9135127258313512121560421)
                ·
                  refine ⟨1712836360933783522792579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9135127258313512121560421 1712836360933783522792579)
                  ·
                    refine ⟨2569254541400675284188869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1712836360933783522792579 2569254541400675284188869)
                    ·
                      refine ⟨481735226512626615785413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2569254541400675284188869 481735226512626615785413)
                      ·
                        rfl

theorem cell23_938176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 1, 4, 1, 4].length) (baseStart_938176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_938176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_938176 prefixEnd_938176 := by exact prefixLift 938176
  have htrace : WordTrace (prefixWord ++ tailWord_938176) baseStart_938176 baseEnd_938176 := by
    simpa [prefixWord, tailWord_938176, baseEnd_938176] using wordTrace_append hprefix tailTrace_938176
  have hstable : (prefixWord ++ tailWord_938176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938176).length < 2 ^ (prefixWord ++ tailWord_938176).sum := by decide
  have hdescent : baseEnd_938176 < baseStart_938176 := by decide
  rcases family_descends (prefixWord ++ tailWord_938176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938177 : List Nat := [1, 2, 6, 1, 2, 1, 3, 2, 5]
def baseStart_938177 : Nat := 118140960795 + 938177 * 2 ^ 59
def prefixEnd_938177 : Nat := 4983230072969 + 3 ^ 40 * 938177 * 2
def baseEnd_938177 : Nat := 53526193332586790208101

theorem tailTrace_938177 : CollatzResearch.WordTrace tailWord_938177 prefixEnd_938177 53526193332586790208101 := by
  unfold tailWord_938177
  simp only [CollatzResearch.WordTrace]
  refine ⟨34218126322152431720316785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22812084214768287813544523 34218126322152431720316785)
  ·
    refine ⟨25663594741614323790237589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34218126322152431720316785 25663594741614323790237589)
    ·
      refine ⟨1202981003513171427667387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 25663594741614323790237589 1202981003513171427667387)
      ·
        refine ⟨1804471505269757141501081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1202981003513171427667387 1804471505269757141501081)
        ·
          refine ⟨1353353628952317856125811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1804471505269757141501081 1353353628952317856125811)
          ·
            refine ⟨2030030443428476784188717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1353353628952317856125811 2030030443428476784188717)
            ·
              refine ⟨761261416285678794070769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2030030443428476784188717 761261416285678794070769)
              ·
                refine ⟨570946062214259095553077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 761261416285678794070769 570946062214259095553077)
                ·
                  refine ⟨53526193332586790208101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 570946062214259095553077 53526193332586790208101)
                  ·
                    rfl

theorem cell23_938177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 3, 2, 5].length) (baseStart_938177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_938177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_938177 prefixEnd_938177 := by exact prefixLift 938177
  have htrace : WordTrace (prefixWord ++ tailWord_938177) baseStart_938177 baseEnd_938177 := by
    simpa [prefixWord, tailWord_938177, baseEnd_938177] using wordTrace_append hprefix tailTrace_938177
  have hstable : (prefixWord ++ tailWord_938177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938177).length < 2 ^ (prefixWord ++ tailWord_938177).sum := by decide
  have hdescent : baseEnd_938177 < baseStart_938177 := by decide
  rcases family_descends (prefixWord ++ tailWord_938177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938213 : List Nat := [1, 3, 1, 4, 2, 1, 1, 3, 2, 2, 3]
def baseStart_938213 : Nat := 118140960795 + 938213 * 2 ^ 59
def prefixEnd_938213 : Nat := 4983230072969 + 3 ^ 40 * 938213 * 2
def baseEnd_938213 : Nat := 481754225296842971022743

theorem tailTrace_938213 : CollatzResearch.WordTrace tailWord_938213 prefixEnd_938213 481754225296842971022743 := by
  unfold tailWord_938213
  simp only [CollatzResearch.WordTrace]
  refine ⟨34219439350022009868627293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22812959566681339912418195 34219439350022009868627293)
  ·
    refine ⟨12832289756258253700735235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34219439350022009868627293 12832289756258253700735235)
    ·
      refine ⟨19248434634387380551102853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12832289756258253700735235 19248434634387380551102853)
      ·
        refine ⟨3609081493947633853331785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19248434634387380551102853 3609081493947633853331785)
        ·
          refine ⟨2706811120460725389998839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3609081493947633853331785 2706811120460725389998839)
          ·
            refine ⟨4060216680691088084998259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2706811120460725389998839 4060216680691088084998259)
            ·
              refine ⟨6090325021036632127497389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4060216680691088084998259 6090325021036632127497389)
              ·
                refine ⟨2283871882888737047811521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6090325021036632127497389 2283871882888737047811521)
                ·
                  refine ⟨1712903912166552785858641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2283871882888737047811521 1712903912166552785858641)
                  ·
                    refine ⟨1284677934124914589393981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1712903912166552785858641 1284677934124914589393981)
                    ·
                      refine ⟨481754225296842971022743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1284677934124914589393981 481754225296842971022743)
                      ·
                        rfl

theorem cell23_938213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 3, 2, 2, 3].length) (baseStart_938213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_938213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_938213 prefixEnd_938213 := by exact prefixLift 938213
  have htrace : WordTrace (prefixWord ++ tailWord_938213) baseStart_938213 baseEnd_938213 := by
    simpa [prefixWord, tailWord_938213, baseEnd_938213] using wordTrace_append hprefix tailTrace_938213
  have hstable : (prefixWord ++ tailWord_938213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938213).length < 2 ^ (prefixWord ++ tailWord_938213).sum := by decide
  have hdescent : baseEnd_938213 < baseStart_938213 := by decide
  rcases family_descends (prefixWord ++ tailWord_938213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938243 : List Nat := [1, 1, 1, 3, 2, 3, 2, 3, 3, 1, 3]
def baseStart_938243 : Nat := 118140960795 + 938243 * 2 ^ 59
def prefixEnd_938243 : Nat := 4983230072969 + 3 ^ 40 * 938243 * 2
def baseEnd_938243 : Nat := 481769629716477853647605

theorem tailTrace_938243 : CollatzResearch.WordTrace tailWord_938243 prefixEnd_938243 481769629716477853647605 := by
  unfold tailWord_938243
  simp only [CollatzResearch.WordTrace]
  refine ⟨34220533539913324992219383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22813689026608883328146255 34220533539913324992219383)
  ·
    refine ⟨51330800309869987488329075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34220533539913324992219383 51330800309869987488329075)
    ·
      refine ⟨76996200464804981232493613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51330800309869987488329075 76996200464804981232493613)
      ·
        refine ⟨28873575174301867962185105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76996200464804981232493613 28873575174301867962185105)
        ·
          refine ⟨21655181380726400971638829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28873575174301867962185105 21655181380726400971638829)
          ·
            refine ⟨8120693017772400364364561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21655181380726400971638829 8120693017772400364364561)
            ·
              refine ⟨6090519763329300273273421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8120693017772400364364561 6090519763329300273273421)
              ·
                refine ⟨2283944911248487602477533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6090519763329300273273421 2283944911248487602477533)
                ·
                  refine ⟨856479341718182850929075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2283944911248487602477533 856479341718182850929075)
                  ·
                    refine ⟨1284719012577274276393613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 856479341718182850929075 1284719012577274276393613)
                    ·
                      refine ⟨481769629716477853647605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1284719012577274276393613 481769629716477853647605)
                      ·
                        rfl

theorem cell23_938243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 3, 3, 1, 3].length) (baseStart_938243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_938243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_938243 prefixEnd_938243 := by exact prefixLift 938243
  have htrace : WordTrace (prefixWord ++ tailWord_938243) baseStart_938243 baseEnd_938243 := by
    simpa [prefixWord, tailWord_938243, baseEnd_938243] using wordTrace_append hprefix tailTrace_938243
  have hstable : (prefixWord ++ tailWord_938243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938243).length < 2 ^ (prefixWord ++ tailWord_938243).sum := by decide
  have hdescent : baseEnd_938243 < baseStart_938243 := by decide
  rcases family_descends (prefixWord ++ tailWord_938243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938280 : List Nat := [2, 1, 5, 1, 3, 1, 1, 3, 1, 5]
def baseStart_938280 : Nat := 118140960795 + 938280 * 2 ^ 59
def prefixEnd_938280 : Nat := 4983230072969 + 3 ^ 40 * 938280 * 2
def baseEnd_938280 : Nat := 160596209500231402961645

theorem tailTrace_938280 : CollatzResearch.WordTrace tailWord_938280 prefixEnd_938280 160596209500231402961645 := by
  unfold tailWord_938280
  simp only [CollatzResearch.WordTrace]
  refine ⟨17110941520389640155658147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22814588693852853540877529 17110941520389640155658147)
  ·
    refine ⟨25666412280584460233487221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17110941520389640155658147 25666412280584460233487221)
    ·
      refine ⟨2406226151304793146889427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25666412280584460233487221 2406226151304793146889427)
      ·
        refine ⟨3609339226957189720334141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2406226151304793146889427 3609339226957189720334141)
        ·
          refine ⟨1353502210108946145125303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3609339226957189720334141 1353502210108946145125303)
          ·
            refine ⟨2030253315163419217687955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1353502210108946145125303 2030253315163419217687955)
            ·
              refine ⟨3045379972745128826531933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2030253315163419217687955 3045379972745128826531933)
              ·
                refine ⟨1142017489779423309949475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3045379972745128826531933 1142017489779423309949475)
                ·
                  refine ⟨1713026234669134964924213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1142017489779423309949475 1713026234669134964924213)
                  ·
                    refine ⟨160596209500231402961645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1713026234669134964924213 160596209500231402961645)
                    ·
                      rfl

theorem cell23_938280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 3, 1, 5].length) (baseStart_938280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_938280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_938280 prefixEnd_938280 := by exact prefixLift 938280
  have htrace : WordTrace (prefixWord ++ tailWord_938280) baseStart_938280 baseEnd_938280 := by
    simpa [prefixWord, tailWord_938280, baseEnd_938280] using wordTrace_append hprefix tailTrace_938280
  have hstable : (prefixWord ++ tailWord_938280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938280).length < 2 ^ (prefixWord ++ tailWord_938280).sum := by decide
  have hdescent : baseEnd_938280 < baseStart_938280 := by decide
  rcases family_descends (prefixWord ++ tailWord_938280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938293 : List Nat := [1, 3, 3, 1, 2, 1, 3, 1, 4, 4]
def baseStart_938293 : Nat := 118140960795 + 938293 * 2 ^ 59
def prefixEnd_938293 : Nat := 4983230072969 + 3 ^ 40 * 938293 * 2
def baseEnd_938293 : Nat := 160598434583067552674125

theorem tailTrace_938293 : CollatzResearch.WordTrace tailWord_938293 prefixEnd_938293 160598434583067552674125 := by
  unfold tailWord_938293
  simp only [CollatzResearch.WordTrace]
  refine ⟨34222357189732183531539533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22814904793154789021026355 34222357189732183531539533)
  ·
    refine ⟨12833383946149568824327325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34222357189732183531539533 12833383946149568824327325)
    ·
      refine ⟨4812518979806088309122747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12833383946149568824327325 4812518979806088309122747)
      ·
        refine ⟨7218778469709132463684121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4812518979806088309122747 7218778469709132463684121)
        ·
          refine ⟨5414083852281849347763091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7218778469709132463684121 5414083852281849347763091)
          ·
            refine ⟨8121125778422774021644637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5414083852281849347763091 8121125778422774021644637)
            ·
              refine ⟨3045422166908540258116739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8121125778422774021644637 3045422166908540258116739)
              ·
                refine ⟨4568133250362810387175109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3045422166908540258116739 4568133250362810387175109)
                ·
                  refine ⟨856524984443026947595333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4568133250362810387175109 856524984443026947595333)
                  ·
                    refine ⟨160598434583067552674125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 856524984443026947595333 160598434583067552674125)
                    ·
                      rfl

theorem cell23_938293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 1, 4, 4].length) (baseStart_938293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_938293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_938293 prefixEnd_938293 := by exact prefixLift 938293
  have htrace : WordTrace (prefixWord ++ tailWord_938293) baseStart_938293 baseEnd_938293 := by
    simpa [prefixWord, tailWord_938293, baseEnd_938293] using wordTrace_append hprefix tailTrace_938293
  have hstable : (prefixWord ++ tailWord_938293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938293).length < 2 ^ (prefixWord ++ tailWord_938293).sum := by decide
  have hdescent : baseEnd_938293 < baseStart_938293 := by decide
  rcases family_descends (prefixWord ++ tailWord_938293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938296 : List Nat := [2, 1, 2, 1, 3, 1, 2, 2, 3, 2, 4]
def baseStart_938296 : Nat := 118140960795 + 938296 * 2 ^ 59
def prefixEnd_938296 : Nat := 4983230072969 + 3 ^ 40 * 938296 * 2
def baseEnd_938296 : Nat := 481796844191166146284861

theorem tailTrace_938296 : CollatzResearch.WordTrace tailWord_938296 prefixEnd_938296 481796844191166146284861 := by
  unfold tailWord_938296
  simp only [CollatzResearch.WordTrace]
  refine ⟨17111233304360657521949371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22814977739147543362599161 17111233304360657521949371)
  ·
    refine ⟨25666849956540986282924057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17111233304360657521949371 25666849956540986282924057)
    ·
      refine ⟨19250137467405739712193043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25666849956540986282924057 19250137467405739712193043)
      ·
        refine ⟨28875206201108609568289565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19250137467405739712193043 28875206201108609568289565)
        ·
          refine ⟨10828202325415728588108587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28875206201108609568289565 10828202325415728588108587)
          ·
            refine ⟨16242303488123592882162881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10828202325415728588108587 16242303488123592882162881)
            ·
              refine ⟨12181727616092694661622161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16242303488123592882162881 12181727616092694661622161)
              ·
                refine ⟨9136295712069520996216621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12181727616092694661622161 9136295712069520996216621)
                ·
                  refine ⟨3426110892026070373581233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9136295712069520996216621 3426110892026070373581233)
                  ·
                    refine ⟨2569583169019552780185925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3426110892026070373581233 2569583169019552780185925)
                    ·
                      refine ⟨481796844191166146284861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2569583169019552780185925 481796844191166146284861)
                      ·
                        rfl

theorem cell23_938296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 2, 3, 2, 4].length) (baseStart_938296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_938296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_938296 prefixEnd_938296 := by exact prefixLift 938296
  have htrace : WordTrace (prefixWord ++ tailWord_938296) baseStart_938296 baseEnd_938296 := by
    simpa [prefixWord, tailWord_938296, baseEnd_938296] using wordTrace_append hprefix tailTrace_938296
  have hstable : (prefixWord ++ tailWord_938296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938296).length < 2 ^ (prefixWord ++ tailWord_938296).sum := by decide
  have hdescent : baseEnd_938296 < baseStart_938296 := by decide
  rcases family_descends (prefixWord ++ tailWord_938296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938320 : List Nat := [2, 1, 1, 1, 1, 7, 2, 2, 1, 2, 3]
def baseStart_938320 : Nat := 118140960795 + 938320 * 2 ^ 59
def prefixEnd_938320 : Nat := 4983230072969 + 3 ^ 40 * 938320 * 2
def baseEnd_938320 : Nat := 481809167726874052384751

theorem tailTrace_938320 : CollatzResearch.WordTrace tailWord_938320 prefixEnd_938320 481809167726874052384751 := by
  unfold tailWord_938320
  simp only [CollatzResearch.WordTrace]
  refine ⟨17111670980317183571386207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22815561307089578095181609 17111670980317183571386207)
  ·
    refine ⟨25667506470475775357079311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17111670980317183571386207 25667506470475775357079311)
    ·
      refine ⟨38501259705713663035618967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25667506470475775357079311 38501259705713663035618967)
      ·
        refine ⟨57751889558570494553428451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38501259705713663035618967 57751889558570494553428451)
        ·
          refine ⟨86627834337855741830142677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57751889558570494553428451 86627834337855741830142677)
          ·
            refine ⟨2030339867293493949143969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 86627834337855741830142677 2030339867293493949143969)
            ·
              refine ⟨1522754900470120461857977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2030339867293493949143969 1522754900470120461857977)
              ·
                refine ⟨1142066175352590346393483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1522754900470120461857977 1142066175352590346393483)
                ·
                  refine ⟨1713099263028885519590225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1142066175352590346393483 1713099263028885519590225)
                  ·
                    refine ⟨1284824447271664139692669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1713099263028885519590225 1284824447271664139692669)
                    ·
                      refine ⟨481809167726874052384751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1284824447271664139692669 481809167726874052384751)
                      ·
                        rfl

theorem cell23_938320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 2, 2, 1, 2, 3].length) (baseStart_938320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_938320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_938320 prefixEnd_938320 := by exact prefixLift 938320
  have htrace : WordTrace (prefixWord ++ tailWord_938320) baseStart_938320 baseEnd_938320 := by
    simpa [prefixWord, tailWord_938320, baseEnd_938320] using wordTrace_append hprefix tailTrace_938320
  have hstable : (prefixWord ++ tailWord_938320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938320).length < 2 ^ (prefixWord ++ tailWord_938320).sum := by decide
  have hdescent : baseEnd_938320 < baseStart_938320 := by decide
  rcases family_descends (prefixWord ++ tailWord_938320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938377 : List Nat := [1, 2, 1, 1, 6, 1, 3, 2, 1, 3, 2]
def baseStart_938377 : Nat := 118140960795 + 938377 * 2 ^ 59
def prefixEnd_938377 : Nat := 4983230072969 + 3 ^ 40 * 938377 * 2
def baseEnd_938377 : Nat := 481838436124180329371989

theorem tailTrace_938377 : CollatzResearch.WordTrace tailWord_938377 prefixEnd_938377 481838436124180329371989 := by
  unfold tailWord_938377
  simp only [CollatzResearch.WordTrace]
  refine ⟨34225420921427865877597385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22816947280951910585064923 34225420921427865877597385)
  ·
    refine ⟨25669065691070899408198039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34225420921427865877597385 25669065691070899408198039)
    ·
      refine ⟨38503598536606349112297059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25669065691070899408198039 38503598536606349112297059)
      ·
        refine ⟨57755397804909523668445589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38503598536606349112297059 57755397804909523668445589)
        ·
          refine ⟨2707284272105133921958387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 57755397804909523668445589 2707284272105133921958387)
          ·
            refine ⟨4060926408157700882937581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2707284272105133921958387 4060926408157700882937581)
            ·
              refine ⟨1522847403059137831101593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4060926408157700882937581 1522847403059137831101593)
              ·
                refine ⟨1142135552294353373326195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1522847403059137831101593 1142135552294353373326195)
                ·
                  refine ⟨1713203328441530059989293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1142135552294353373326195 1713203328441530059989293)
                  ·
                    refine ⟨642451248165573772495985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1713203328441530059989293 642451248165573772495985)
                    ·
                      refine ⟨481838436124180329371989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 642451248165573772495985 481838436124180329371989)
                      ·
                        rfl

theorem cell23_938377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 3, 2, 1, 3, 2].length) (baseStart_938377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_938377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_938377 prefixEnd_938377 := by exact prefixLift 938377
  have htrace : WordTrace (prefixWord ++ tailWord_938377) baseStart_938377 baseEnd_938377 := by
    simpa [prefixWord, tailWord_938377, baseEnd_938377] using wordTrace_append hprefix tailTrace_938377
  have hstable : (prefixWord ++ tailWord_938377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938377).length < 2 ^ (prefixWord ++ tailWord_938377).sum := by decide
  have hdescent : baseEnd_938377 < baseStart_938377 := by decide
  rcases family_descends (prefixWord ++ tailWord_938377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938394 : List Nat := [3, 1, 1, 4, 1, 3, 3, 1, 1, 3, 2]
def baseStart_938394 : Nat := 118140960795 + 938394 * 2 ^ 59
def prefixEnd_938394 : Nat := 4983230072969 + 3 ^ 40 * 938394 * 2
def baseEnd_938394 : Nat := 481847165295306762859411

theorem tailTrace_938394 : CollatzResearch.WordTrace tailWord_938394 prefixEnd_938394 481847165295306762859411 := by
  unfold tailWord_938394
  simp only [CollatzResearch.WordTrace]
  refine ⟨8556510240591569445241559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22817360641577518520644157 8556510240591569445241559)
  ·
    refine ⟨12834765360887354167862339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8556510240591569445241559 12834765360887354167862339)
    ·
      refine ⟨19252148041331031251793509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12834765360887354167862339 19252148041331031251793509)
      ·
        refine ⟨3609777757749568359711283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19252148041331031251793509 3609777757749568359711283)
        ·
          refine ⟨5414666636624352539566925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3609777757749568359711283 5414666636624352539566925)
          ·
            refine ⟨2030499988734132202337597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5414666636624352539566925 2030499988734132202337597)
            ·
              refine ⟨761437495775299575876599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2030499988734132202337597 761437495775299575876599)
              ·
                refine ⟨1142156243662949363814899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 761437495775299575876599 1142156243662949363814899)
                ·
                  refine ⟨1713234365494424045722349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1142156243662949363814899 1713234365494424045722349)
                  ·
                    refine ⟨642462887060409017145881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1713234365494424045722349 642462887060409017145881)
                    ·
                      refine ⟨481847165295306762859411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 642462887060409017145881 481847165295306762859411)
                      ·
                        rfl

theorem cell23_938394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 3, 1, 1, 3, 2].length) (baseStart_938394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_938394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_938394 prefixEnd_938394 := by exact prefixLift 938394
  have htrace : WordTrace (prefixWord ++ tailWord_938394) baseStart_938394 baseEnd_938394 := by
    simpa [prefixWord, tailWord_938394, baseEnd_938394] using wordTrace_append hprefix tailTrace_938394
  have hstable : (prefixWord ++ tailWord_938394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938394).length < 2 ^ (prefixWord ++ tailWord_938394).sum := by decide
  have hdescent : baseEnd_938394 < baseStart_938394 := by decide
  rcases family_descends (prefixWord ++ tailWord_938394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938423 : List Nat := [1, 1, 3, 1, 3, 3, 1, 1, 1, 5, 3]
def baseStart_938423 : Nat := 118140960795 + 938423 * 2 ^ 59
def prefixEnd_938423 : Nat := 4983230072969 + 3 ^ 40 * 938423 * 2
def baseEnd_938423 : Nat := 481862056234287149396777

theorem tailTrace_938423 : CollatzResearch.WordTrace tailWord_938423 prefixEnd_938423 481862056234287149396777 := by
  unfold tailWord_938423
  simp only [CollatzResearch.WordTrace]
  refine ⟨34227098679261215733771923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22818065786174143822514615 34227098679261215733771923)
  ·
    refine ⟨51340648018891823600657885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34227098679261215733771923 51340648018891823600657885)
    ·
      refine ⟨19252743007084433850246707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51340648018891823600657885 19252743007084433850246707)
      ·
        refine ⟨28879114510626650775370061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19252743007084433850246707 28879114510626650775370061)
        ·
          refine ⟨10829667941484994040763773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28879114510626650775370061 10829667941484994040763773)
          ·
            refine ⟨4061125478056872765286415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10829667941484994040763773 4061125478056872765286415)
            ·
              refine ⟨6091688217085309147929623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4061125478056872765286415 6091688217085309147929623)
              ·
                refine ⟨9137532325627963721894435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6091688217085309147929623 9137532325627963721894435)
                ·
                  refine ⟨13706298488441945582841653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9137532325627963721894435 13706298488441945582841653)
                  ·
                    refine ⟨1284965483291432398391405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13706298488441945582841653 1284965483291432398391405)
                    ·
                      refine ⟨481862056234287149396777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1284965483291432398391405 481862056234287149396777)
                      ·
                        rfl

theorem cell23_938423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 1, 1, 5, 3].length) (baseStart_938423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_938423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_938423 prefixEnd_938423 := by exact prefixLift 938423
  have htrace : WordTrace (prefixWord ++ tailWord_938423) baseStart_938423 baseEnd_938423 := by
    simpa [prefixWord, tailWord_938423, baseEnd_938423] using wordTrace_append hprefix tailTrace_938423
  have hstable : (prefixWord ++ tailWord_938423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938423).length < 2 ^ (prefixWord ++ tailWord_938423).sum := by decide
  have hdescent : baseEnd_938423 < baseStart_938423 := by decide
  rcases family_descends (prefixWord ++ tailWord_938423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938480 : List Nat := [2, 1, 1, 1, 3, 3, 1, 3, 2, 4, 2]
def baseStart_938480 : Nat := 118140960795 + 938480 * 2 ^ 59
def prefixEnd_938480 : Nat := 4983230072969 + 3 ^ 40 * 938480 * 2
def baseEnd_938480 : Nat := 481891324631593426384015

theorem tailTrace_938480 : CollatzResearch.WordTrace tailWord_938480 prefixEnd_938480 481891324631593426384015 := by
  unfold tailWord_938480
  simp only [CollatzResearch.WordTrace]
  refine ⟨17114588820027357234298447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22819451760036476312397929 17114588820027357234298447)
  ·
    refine ⟨25671883230041035851447671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17114588820027357234298447 25671883230041035851447671)
    ·
      refine ⟨38507824845061553777171507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25671883230041035851447671 38507824845061553777171507)
      ·
        refine ⟨57761737267592330665757261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38507824845061553777171507 57761737267592330665757261)
        ·
          refine ⟨21660651475347123999658973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57761737267592330665757261 21660651475347123999658973)
          ·
            refine ⟨8122744303255171499872115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21660651475347123999658973 8122744303255171499872115)
            ·
              refine ⟨12184116454882757249808173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8122744303255171499872115 12184116454882757249808173)
              ·
                refine ⟨4569043670581033968678065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12184116454882757249808173 4569043670581033968678065)
                ·
                  refine ⟨3426782752935775476508549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4569043670581033968678065 3426782752935775476508549)
                  ·
                    refine ⟨642521766175457901845353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3426782752935775476508549 642521766175457901845353)
                    ·
                      refine ⟨481891324631593426384015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 642521766175457901845353 481891324631593426384015)
                      ·
                        rfl

theorem cell23_938480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 3, 2, 4, 2].length) (baseStart_938480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_938480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_938480 prefixEnd_938480 := by exact prefixLift 938480
  have htrace : WordTrace (prefixWord ++ tailWord_938480) baseStart_938480 baseEnd_938480 := by
    simpa [prefixWord, tailWord_938480, baseEnd_938480] using wordTrace_append hprefix tailTrace_938480
  have hstable : (prefixWord ++ tailWord_938480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938480).length < 2 ^ (prefixWord ++ tailWord_938480).sum := by decide
  have hdescent : baseEnd_938480 < baseStart_938480 := by decide
  rcases family_descends (prefixWord ++ tailWord_938480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938483 : List Nat := [1, 1, 1, 2, 2, 2, 3, 1, 3, 4, 3]
def baseStart_938483 : Nat := 118140960795 + 938483 * 2 ^ 59
def prefixEnd_938483 : Nat := 4983230072969 + 3 ^ 40 * 938483 * 2
def baseEnd_938483 : Nat := 481892865073556914646501

theorem tailTrace_938483 : CollatzResearch.WordTrace tailWord_938483 prefixEnd_938483 481892865073556914646501 := by
  unfold tailWord_938483
  simp only [CollatzResearch.WordTrace]
  refine ⟨34229287059043845980956103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22819524706029230653970735 34229287059043845980956103)
  ·
    refine ⟨51343930588565768971434155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34229287059043845980956103 51343930588565768971434155)
    ·
      refine ⟨77015895882848653457151233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51343930588565768971434155 77015895882848653457151233)
      ·
        refine ⟨57761921912136490092863425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77015895882848653457151233 57761921912136490092863425)
        ·
          refine ⟨43321441434102367569647569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57761921912136490092863425 43321441434102367569647569)
          ·
            refine ⟨32491081075576775677235677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43321441434102367569647569 32491081075576775677235677)
            ·
              refine ⟨12184155403341290878963379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32491081075576775677235677 12184155403341290878963379)
              ·
                refine ⟨18276233105011936318445069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12184155403341290878963379 18276233105011936318445069)
                ·
                  refine ⟨6853587414379476119416901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18276233105011936318445069 6853587414379476119416901)
                  ·
                    refine ⟨1285047640196151772390669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6853587414379476119416901 1285047640196151772390669)
                    ·
                      refine ⟨481892865073556914646501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1285047640196151772390669 481892865073556914646501)
                      ·
                        rfl

theorem cell23_938483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 3, 4, 3].length) (baseStart_938483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_938483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_938483 prefixEnd_938483 := by exact prefixLift 938483
  have htrace : WordTrace (prefixWord ++ tailWord_938483) baseStart_938483 baseEnd_938483 := by
    simpa [prefixWord, tailWord_938483, baseEnd_938483] using wordTrace_append hprefix tailTrace_938483
  have hstable : (prefixWord ++ tailWord_938483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938483).length < 2 ^ (prefixWord ++ tailWord_938483).sum := by decide
  have hdescent : baseEnd_938483 < baseStart_938483 := by decide
  rcases family_descends (prefixWord ++ tailWord_938483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938493 : List Nat := [1, 4, 1, 1, 1, 3, 1, 1, 2, 4, 4]
def baseStart_938493 : Nat := 118140960795 + 938493 * 2 ^ 59
def prefixEnd_938493 : Nat := 4983230072969 + 3 ^ 40 * 938493 * 2
def baseEnd_938493 : Nat := 481897999880101875521455

theorem tailTrace_938493 : CollatzResearch.WordTrace tailWord_938493 prefixEnd_938493 481897999880101875521455 := by
  unfold tailWord_938493
  simp only [CollatzResearch.WordTrace]
  refine ⟨34229651789007617688820133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22819767859338411792546755 34229651789007617688820133)
  ·
    refine ⟨6418059710438928316653775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34229651789007617688820133 6418059710438928316653775)
    ·
      refine ⟨9627089565658392474980663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6418059710438928316653775 9627089565658392474980663)
      ·
        refine ⟨14440634348487588712470995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9627089565658392474980663 14440634348487588712470995)
        ·
          refine ⟨21660951522731383068706493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14440634348487588712470995 21660951522731383068706493)
          ·
            refine ⟨8122856821024268650764935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21660951522731383068706493 8122856821024268650764935)
            ·
              refine ⟨12184285231536402976147403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8122856821024268650764935 12184285231536402976147403)
              ·
                refine ⟨18276427847304604464221105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12184285231536402976147403 18276427847304604464221105)
                ·
                  refine ⟨13707320885478453348165829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18276427847304604464221105 13707320885478453348165829)
                  ·
                    refine ⟨2570122666027210002781093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13707320885478453348165829 2570122666027210002781093)
                    ·
                      refine ⟨481897999880101875521455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2570122666027210002781093 481897999880101875521455)
                      ·
                        rfl

theorem cell23_938493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 2, 4, 4].length) (baseStart_938493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_938493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_938493 prefixEnd_938493 := by exact prefixLift 938493
  have htrace : WordTrace (prefixWord ++ tailWord_938493) baseStart_938493 baseEnd_938493 := by
    simpa [prefixWord, tailWord_938493, baseEnd_938493] using wordTrace_append hprefix tailTrace_938493
  have hstable : (prefixWord ++ tailWord_938493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938493).length < 2 ^ (prefixWord ++ tailWord_938493).sum := by decide
  have hdescent : baseEnd_938493 < baseStart_938493 := by decide
  rcases family_descends (prefixWord ++ tailWord_938493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938540 : List Nat := [2, 2, 1, 1, 1, 2, 1, 3, 3, 5, 2]
def baseStart_938540 : Nat := 118140960795 + 938540 * 2 ^ 59
def prefixEnd_938540 : Nat := 4983230072969 + 3 ^ 40 * 938540 * 2
def baseEnd_938540 : Nat := 481922133470863191633739

theorem tailTrace_938540 : CollatzResearch.WordTrace tailWord_938540 prefixEnd_938540 481922133470863191633739 := by
  unfold tailWord_938540
  simp only [CollatzResearch.WordTrace]
  refine ⟨17115683009918672357890537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22820910679891563143854049 17115683009918672357890537)
  ·
    refine ⟨12836762257439004268417903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17115683009918672357890537 12836762257439004268417903)
    ·
      refine ⟨19255143386158506402626855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12836762257439004268417903 19255143386158506402626855)
      ·
        refine ⟨28882715079237759603940283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19255143386158506402626855 28882715079237759603940283)
        ·
          refine ⟨43324072618856639405910425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28882715079237759603940283 43324072618856639405910425)
          ·
            refine ⟨32493054464142479554432819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43324072618856639405910425 32493054464142479554432819)
            ·
              refine ⟨48739581696213719331649229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32493054464142479554432819 48739581696213719331649229)
              ·
                refine ⟨18277343136080144749368461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48739581696213719331649229 18277343136080144749368461)
                ·
                  refine ⟨6854003676030054281013173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18277343136080144749368461 6854003676030054281013173)
                  ·
                    refine ⟨642562844627817588844985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6854003676030054281013173 642562844627817588844985)
                    ·
                      refine ⟨481922133470863191633739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 642562844627817588844985 481922133470863191633739)
                      ·
                        rfl

theorem cell23_938540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 5, 2].length) (baseStart_938540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_938540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_938540 prefixEnd_938540 := by exact prefixLift 938540
  have htrace : WordTrace (prefixWord ++ tailWord_938540) baseStart_938540 baseEnd_938540 := by
    simpa [prefixWord, tailWord_938540, baseEnd_938540] using wordTrace_append hprefix tailTrace_938540
  have hstable : (prefixWord ++ tailWord_938540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938540).length < 2 ^ (prefixWord ++ tailWord_938540).sum := by decide
  have hdescent : baseEnd_938540 < baseStart_938540 := by decide
  rcases family_descends (prefixWord ++ tailWord_938540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938581 : List Nat := [1, 3, 2, 2, 1, 1, 6, 2, 1, 1, 3]
def baseStart_938581 : Nat := 118140960795 + 938581 * 2 ^ 59
def prefixEnd_938581 : Nat := 4983230072969 + 3 ^ 40 * 938581 * 2
def baseEnd_938581 : Nat := 481943186177697531221051

theorem tailTrace_938581 : CollatzResearch.WordTrace tailWord_938581 prefixEnd_938581 481943186177697531221051 := by
  unfold tailWord_938581
  simp only [CollatzResearch.WordTrace]
  refine ⟨34232861412688808718023597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22821907608459205812015731 34232861412688808718023597)
  ·
    refine ⟨12837323029758303269258849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34232861412688808718023597 12837323029758303269258849)
    ·
      refine ⟨9627992272318727451944137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12837323029758303269258849 9627992272318727451944137)
      ·
        refine ⟨7220994204239045588958103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9627992272318727451944137 7220994204239045588958103)
        ·
          refine ⟨10831491306358568383437155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7220994204239045588958103 10831491306358568383437155)
          ·
            refine ⟨16247236959537852575155733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10831491306358568383437155 16247236959537852575155733)
            ·
              refine ⟨761589232478336839460425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 16247236959537852575155733 761589232478336839460425)
              ·
                refine ⟨571191924358752629595319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 761589232478336839460425 571191924358752629595319)
                ·
                  refine ⟨856787886538128944392979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 571191924358752629595319 856787886538128944392979)
                  ·
                    refine ⟨1285181829807193416589469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 856787886538128944392979 1285181829807193416589469)
                    ·
                      refine ⟨481943186177697531221051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1285181829807193416589469 481943186177697531221051)
                      ·
                        rfl

theorem cell23_938581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 6, 2, 1, 1, 3].length) (baseStart_938581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_938581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_938581 prefixEnd_938581 := by exact prefixLift 938581
  have htrace : WordTrace (prefixWord ++ tailWord_938581) baseStart_938581 baseEnd_938581 := by
    simpa [prefixWord, tailWord_938581, baseEnd_938581] using wordTrace_append hprefix tailTrace_938581
  have hstable : (prefixWord ++ tailWord_938581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938581).length < 2 ^ (prefixWord ++ tailWord_938581).sum := by decide
  have hdescent : baseEnd_938581 < baseStart_938581 := by decide
  rcases family_descends (prefixWord ++ tailWord_938581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938597 : List Nat := [1, 3, 1, 3, 4, 1, 2, 1, 1, 6]
def baseStart_938597 : Nat := 118140960795 + 938597 * 2 ^ 59
def prefixEnd_938597 : Nat := 4983230072969 + 3 ^ 40 * 938597 * 2
def baseEnd_938597 : Nat := 160650467289389822873659

theorem tailTrace_938597 : CollatzResearch.WordTrace tailWord_938597 prefixEnd_938597 160650467289389822873659 := by
  unfold tailWord_938597
  simp only [CollatzResearch.WordTrace]
  refine ⟨34233444980630843450606045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22822296653753895633737363 34233444980630843450606045)
  ·
    refine ⟨12837541867736566293977267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34233444980630843450606045 12837541867736566293977267)
    ·
      refine ⟨19256312801604849440965901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12837541867736566293977267 19256312801604849440965901)
      ·
        refine ⟨7221117300601818540362213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19256312801604849440965901 7221117300601818540362213)
        ·
          refine ⟨1353959493862840976317915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7221117300601818540362213 1353959493862840976317915)
          ·
            refine ⟨2030939240794261464476873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1353959493862840976317915 2030939240794261464476873)
            ·
              refine ⟨1523204430595696098357655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2030939240794261464476873 1523204430595696098357655)
              ·
                refine ⟨2284806645893544147536483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1523204430595696098357655 2284806645893544147536483)
                ·
                  refine ⟨3427209968840316221304725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2284806645893544147536483 3427209968840316221304725)
                  ·
                    refine ⟨160650467289389822873659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3427209968840316221304725 160650467289389822873659)
                    ·
                      rfl

theorem cell23_938597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 2, 1, 1, 6].length) (baseStart_938597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_938597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_938597 prefixEnd_938597 := by exact prefixLift 938597
  have htrace : WordTrace (prefixWord ++ tailWord_938597) baseStart_938597 baseEnd_938597 := by
    simpa [prefixWord, tailWord_938597, baseEnd_938597] using wordTrace_append hprefix tailTrace_938597
  have hstable : (prefixWord ++ tailWord_938597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938597).length < 2 ^ (prefixWord ++ tailWord_938597).sum := by decide
  have hdescent : baseEnd_938597 < baseStart_938597 := by decide
  rcases family_descends (prefixWord ++ tailWord_938597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938621 : List Nat := [1, 4, 1, 1, 5, 2, 2, 1, 1, 1, 4]
def baseStart_938621 : Nat := 118140960795 + 938621 * 2 ^ 59
def prefixEnd_938621 : Nat := 4983230072969 + 3 ^ 40 * 938621 * 2
def baseEnd_938621 : Nat := 481963725403877374720867

theorem tailTrace_938621 : CollatzResearch.WordTrace tailWord_938621 prefixEnd_938621 481963725403877374720867 := by
  unfold tailWord_938621
  simp only [CollatzResearch.WordTrace]
  refine ⟨34234320332543895549479717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22822880221695930366319811 34234320332543895549479717)
  ·
    refine ⟨6418935062351980415527447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34234320332543895549479717 6418935062351980415527447)
    ·
      refine ⟨9628402593527970623291171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6418935062351980415527447 9628402593527970623291171)
      ·
        refine ⟨14442603890291955934936757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9628402593527970623291171 14442603890291955934936757)
        ·
          refine ⟨1353994114714870868900321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14442603890291955934936757 1353994114714870868900321)
          ·
            refine ⟨1015495586036153151675241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1353994114714870868900321 1015495586036153151675241)
            ·
              refine ⟨761621689527114863756431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1015495586036153151675241 761621689527114863756431)
              ·
                refine ⟨1142432534290672295634647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 761621689527114863756431 1142432534290672295634647)
                ·
                  refine ⟨1713648801436008443451971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1142432534290672295634647 1713648801436008443451971)
                  ·
                    refine ⟨2570473202154012665177957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1713648801436008443451971 2570473202154012665177957)
                    ·
                      refine ⟨481963725403877374720867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2570473202154012665177957 481963725403877374720867)
                      ·
                        rfl

theorem cell23_938621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 2, 1, 1, 1, 4].length) (baseStart_938621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_938621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_938621 prefixEnd_938621 := by exact prefixLift 938621
  have htrace : WordTrace (prefixWord ++ tailWord_938621) baseStart_938621 baseEnd_938621 := by
    simpa [prefixWord, tailWord_938621, baseEnd_938621] using wordTrace_append hprefix tailTrace_938621
  have hstable : (prefixWord ++ tailWord_938621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938621).length < 2 ^ (prefixWord ++ tailWord_938621).sum := by decide
  have hdescent : baseEnd_938621 < baseStart_938621 := by decide
  rcases family_descends (prefixWord ++ tailWord_938621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938623 : List Nat := [1, 1, 2, 2, 1, 1, 1, 4, 1, 9]
def baseStart_938623 : Nat := 118140960795 + 938623 * 2 ^ 59
def prefixEnd_938623 : Nat := 4983230072969 + 3 ^ 40 * 938623 * 2
def baseEnd_938623 : Nat := 160654917455062122298619

theorem tailTrace_938623 : CollatzResearch.WordTrace tailWord_938623 prefixEnd_938623 160654917455062122298619 := by
  unfold tailWord_938623
  simp only [CollatzResearch.WordTrace]
  refine ⟨34234393278536649891052523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22822928852357766594035015 34234393278536649891052523)
  ·
    refine ⟨51351589917804974836578785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34234393278536649891052523 51351589917804974836578785)
    ·
      refine ⟨38513692438353731127434089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51351589917804974836578785 38513692438353731127434089)
      ·
        refine ⟨28885269328765298345575567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38513692438353731127434089 28885269328765298345575567)
        ·
          refine ⟨43327903993147947518363351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28885269328765298345575567 43327903993147947518363351)
          ·
            refine ⟨64991855989721921277545027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43327903993147947518363351 64991855989721921277545027)
            ·
              refine ⟨97487783984582881916317541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64991855989721921277545027 97487783984582881916317541)
              ·
                refine ⟨18278959497109290359309539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 97487783984582881916317541 18278959497109290359309539)
                ·
                  refine ⟨27418439245663935538964309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18278959497109290359309539 27418439245663935538964309)
                  ·
                    refine ⟨160654917455062122298619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 27418439245663935538964309 160654917455062122298619)
                    ·
                      rfl

theorem cell23_938623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 9].length) (baseStart_938623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_938623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_938623 prefixEnd_938623 := by exact prefixLift 938623
  have htrace : WordTrace (prefixWord ++ tailWord_938623) baseStart_938623 baseEnd_938623 := by
    simpa [prefixWord, tailWord_938623, baseEnd_938623] using wordTrace_append hprefix tailTrace_938623
  have hstable : (prefixWord ++ tailWord_938623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938623).length < 2 ^ (prefixWord ++ tailWord_938623).sum := by decide
  have hdescent : baseEnd_938623 < baseStart_938623 := by decide
  rcases family_descends (prefixWord ++ tailWord_938623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938624 : List Nat := [2, 1, 1, 2, 1, 5, 4, 1, 1, 2, 3]
def baseStart_938624 : Nat := 118140960795 + 938624 * 2 ^ 59
def prefixEnd_938624 : Nat := 4983230072969 + 3 ^ 40 * 938624 * 2
def baseEnd_938624 : Nat := 481965265845840862983353

theorem tailTrace_938624 : CollatzResearch.WordTrace tailWord_938624 prefixEnd_938624 481965265845840862983353 := by
  unfold tailWord_938624
  simp only [CollatzResearch.WordTrace]
  refine ⟨17117214875766513530919463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22822953167688684707892617 17117214875766513530919463)
  ·
    refine ⟨25675822313649770296379195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17117214875766513530919463 25675822313649770296379195)
    ·
      refine ⟨38513733470474655444568793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25675822313649770296379195 38513733470474655444568793)
      ·
        refine ⟨28885300102855991583426595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38513733470474655444568793 28885300102855991583426595)
        ·
          refine ⟨43327950154283987375139893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28885300102855991583426595 43327950154283987375139893)
          ·
            refine ⟨4061995326964123816419365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43327950154283987375139893 4061995326964123816419365)
            ·
              refine ⟨761624123805773215578631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4061995326964123816419365 761624123805773215578631)
              ·
                refine ⟨1142436185708659823367947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 761624123805773215578631 1142436185708659823367947)
                ·
                  refine ⟨1713654278562989735051921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1142436185708659823367947 1713654278562989735051921)
                  ·
                    refine ⟨1285240708922242301288941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1713654278562989735051921 1285240708922242301288941)
                    ·
                      refine ⟨481965265845840862983353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1285240708922242301288941 481965265845840862983353)
                      ·
                        rfl

theorem cell23_938624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 4, 1, 1, 2, 3].length) (baseStart_938624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_938624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_938624 prefixEnd_938624 := by exact prefixLift 938624
  have htrace : WordTrace (prefixWord ++ tailWord_938624) baseStart_938624 baseEnd_938624 := by
    simpa [prefixWord, tailWord_938624, baseEnd_938624] using wordTrace_append hprefix tailTrace_938624
  have hstable : (prefixWord ++ tailWord_938624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938624).length < 2 ^ (prefixWord ++ tailWord_938624).sum := by decide
  have hdescent : baseEnd_938624 < baseStart_938624 := by decide
  rcases family_descends (prefixWord ++ tailWord_938624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938680 : List Nat := [2, 1, 2, 1, 2, 1, 1, 1, 3, 6, 3]
def baseStart_938680 : Nat := 118140960795 + 938680 * 2 ^ 59
def prefixEnd_938680 : Nat := 4983230072969 + 3 ^ 40 * 938680 * 2
def baseEnd_938680 : Nat := 481994020762492643883095

theorem tailTrace_938680 : CollatzResearch.WordTrace tailWord_938680 prefixEnd_938680 481994020762492643883095 := by
  unfold tailWord_938680
  simp only [CollatzResearch.WordTrace]
  refine ⟨17118236119665074312938747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22824314826220099083918329 17118236119665074312938747)
  ·
    refine ⟨25677354179497611469408121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17118236119665074312938747 25677354179497611469408121)
    ·
      refine ⟨19258015634623208602056091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25677354179497611469408121 19258015634623208602056091)
      ·
        refine ⟨28887023451934812903084137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19258015634623208602056091 28887023451934812903084137)
        ·
          refine ⟨21665267588951109677313103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28887023451934812903084137 21665267588951109677313103)
          ·
            refine ⟨32497901383426664515969655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21665267588951109677313103 32497901383426664515969655)
            ·
              refine ⟨48746852075139996773954483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32497901383426664515969655 48746852075139996773954483)
              ·
                refine ⟨73120278112709995160931725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48746852075139996773954483 73120278112709995160931725)
                ·
                  refine ⟨27420104292266248185349397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73120278112709995160931725 27420104292266248185349397)
                  ·
                    refine ⟨1285317388699980383688253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27420104292266248185349397 1285317388699980383688253)
                    ·
                      refine ⟨481994020762492643883095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1285317388699980383688253 481994020762492643883095)
                      ·
                        rfl

theorem cell23_938680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 3, 6, 3].length) (baseStart_938680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_938680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_938680 prefixEnd_938680 := by exact prefixLift 938680
  have htrace : WordTrace (prefixWord ++ tailWord_938680) baseStart_938680 baseEnd_938680 := by
    simpa [prefixWord, tailWord_938680, baseEnd_938680] using wordTrace_append hprefix tailTrace_938680
  have hstable : (prefixWord ++ tailWord_938680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938680).length < 2 ^ (prefixWord ++ tailWord_938680).sum := by decide
  have hdescent : baseEnd_938680 < baseStart_938680 := by decide
  rcases family_descends (prefixWord ++ tailWord_938680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938711 : List Nat := [1, 1, 3, 2, 1, 5, 1, 3, 2, 2, 2]
def baseStart_938711 : Nat := 118140960795 + 938711 * 2 ^ 59
def prefixEnd_938711 : Nat := 4983230072969 + 3 ^ 40 * 938711 * 2
def baseEnd_938711 : Nat := 482009938662782022595453

theorem tailTrace_938711 : CollatzResearch.WordTrace tailWord_938711 prefixEnd_938711 482009938662782022595453 := by
  unfold tailWord_938711
  simp only [CollatzResearch.WordTrace]
  refine ⟨34237602902217840920255987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22825068601478560613503991 34237602902217840920255987)
  ·
    refine ⟨51356404353326761380383981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34237602902217840920255987 51356404353326761380383981)
    ·
      refine ⟨19258651632497535517643993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51356404353326761380383981 19258651632497535517643993)
      ·
        refine ⟨14443988724373151638232995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19258651632497535517643993 14443988724373151638232995)
        ·
          refine ⟨21665983086559727457349493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14443988724373151638232995 21665983086559727457349493)
          ·
            refine ⟨2031185914364974449126515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21665983086559727457349493 2031185914364974449126515)
            ·
              refine ⟨3046778871547461673689773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2031185914364974449126515 3046778871547461673689773)
              ·
                refine ⟨1142542076830298127633665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3046778871547461673689773 1142542076830298127633665)
                ·
                  refine ⟨856906557622723595725249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1142542076830298127633665 856906557622723595725249)
                  ·
                    refine ⟨642679918217042696793937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 856906557622723595725249 642679918217042696793937)
                    ·
                      refine ⟨482009938662782022595453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 642679918217042696793937 482009938662782022595453)
                      ·
                        rfl

theorem cell23_938711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 3, 2, 2, 2].length) (baseStart_938711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_938711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_938711 prefixEnd_938711 := by exact prefixLift 938711
  have htrace : WordTrace (prefixWord ++ tailWord_938711) baseStart_938711 baseEnd_938711 := by
    simpa [prefixWord, tailWord_938711, baseEnd_938711] using wordTrace_append hprefix tailTrace_938711
  have hstable : (prefixWord ++ tailWord_938711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938711).length < 2 ^ (prefixWord ++ tailWord_938711).sum := by decide
  have hdescent : baseEnd_938711 < baseStart_938711 := by decide
  rcases family_descends (prefixWord ++ tailWord_938711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938784 : List Nat := [2, 1, 1, 5, 1, 2, 3, 1, 2, 1, 4]
def baseStart_938784 : Nat := 118140960795 + 938784 * 2 ^ 59
def prefixEnd_938784 : Nat := 4983230072969 + 3 ^ 40 * 938784 * 2
def baseEnd_938784 : Nat := 482047422750560236982617

theorem tailTrace_938784 : CollatzResearch.WordTrace tailWord_938784 prefixEnd_938784 482047422750560236982617 := by
  unfold tailWord_938784
  simp only [CollatzResearch.WordTrace]
  refine ⟨17120132715476687193831703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22826843620635582925108937 17120132715476687193831703)
  ·
    refine ⟨25680199073215030790747555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17120132715476687193831703 25680199073215030790747555)
    ·
      refine ⟨38520298609822546186121333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25680199073215030790747555 38520298609822546186121333)
      ·
        refine ⟨3611277994670863704948875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38520298609822546186121333 3611277994670863704948875)
        ·
          refine ⟨5416916992006295557423313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3611277994670863704948875 5416916992006295557423313)
          ·
            refine ⟨4062687744004721668067485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5416916992006295557423313 4062687744004721668067485)
            ·
              refine ⟨1523507904001770625525307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4062687744004721668067485 1523507904001770625525307)
              ·
                refine ⟨2285261856002655938287961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1523507904001770625525307 2285261856002655938287961)
                ·
                  refine ⟨1713946392001991953715971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2285261856002655938287961 1713946392001991953715971)
                  ·
                    refine ⟨2570919588002987930573957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1713946392001991953715971 2570919588002987930573957)
                    ·
                      refine ⟨482047422750560236982617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2570919588002987930573957 482047422750560236982617)
                      ·
                        rfl

theorem cell23_938784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 3, 1, 2, 1, 4].length) (baseStart_938784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_938784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_938784 prefixEnd_938784 := by exact prefixLift 938784
  have htrace : WordTrace (prefixWord ++ tailWord_938784) baseStart_938784 baseEnd_938784 := by
    simpa [prefixWord, tailWord_938784, baseEnd_938784] using wordTrace_append hprefix tailTrace_938784
  have hstable : (prefixWord ++ tailWord_938784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938784).length < 2 ^ (prefixWord ++ tailWord_938784).sum := by decide
  have hdescent : baseEnd_938784 < baseStart_938784 := by decide
  rcases family_descends (prefixWord ++ tailWord_938784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938824 : List Nat := [2, 1, 3, 1, 1, 3, 5, 1, 6]
def baseStart_938824 : Nat := 118140960795 + 938824 * 2 ^ 59
def prefixEnd_938824 : Nat := 4983230072969 + 3 ^ 40 * 938824 * 2
def baseEnd_938824 : Nat := 53563106886304453386937

theorem tailTrace_938824 : CollatzResearch.WordTrace tailWord_938824 prefixEnd_938824 53563106886304453386937 := by
  unfold tailWord_938824
  simp only [CollatzResearch.WordTrace]
  refine ⟨17120862175404230609559763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22827816233872307479413017 17120862175404230609559763)
  ·
    refine ⟨25681293263106345914339645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17120862175404230609559763 25681293263106345914339645)
    ·
      refine ⟨9630484973664879717877367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25681293263106345914339645 9630484973664879717877367)
      ·
        refine ⟨14445727460497319576816051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9630484973664879717877367 14445727460497319576816051)
        ·
          refine ⟨21668591190745979365224077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14445727460497319576816051 21668591190745979365224077)
          ·
            refine ⟨8125721696529742261959029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21668591190745979365224077 8125721696529742261959029)
            ·
              refine ⟨761786409049663337058659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8125721696529742261959029 761786409049663337058659)
              ·
                refine ⟨1142679613574495005587989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 761786409049663337058659 1142679613574495005587989)
                ·
                  refine ⟨53563106886304453386937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1142679613574495005587989 53563106886304453386937)
                  ·
                    rfl

theorem cell23_938824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 5, 1, 6].length) (baseStart_938824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_938824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_938824 prefixEnd_938824 := by exact prefixLift 938824
  have htrace : WordTrace (prefixWord ++ tailWord_938824) baseStart_938824 baseEnd_938824 := by
    simpa [prefixWord, tailWord_938824, baseEnd_938824] using wordTrace_append hprefix tailTrace_938824
  have hstable : (prefixWord ++ tailWord_938824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938824).length < 2 ^ (prefixWord ++ tailWord_938824).sum := by decide
  have hdescent : baseEnd_938824 < baseStart_938824 := by decide
  rcases family_descends (prefixWord ++ tailWord_938824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938857 : List Nat := [1, 2, 1, 1, 1, 3, 1, 1, 7, 1, 4]
def baseStart_938857 : Nat := 118140960795 + 938857 * 2 ^ 59
def prefixEnd_938857 : Nat := 4983230072969 + 3 ^ 40 * 938857 * 2
def baseEnd_938857 : Nat := 482084906838338451369781

theorem tailTrace_938857 : CollatzResearch.WordTrace tailWord_938857 prefixEnd_938857 482084906838338451369781 := by
  unfold tailWord_938857
  simp only [CollatzResearch.WordTrace]
  refine ⟨34242927959688907855070825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22828618639792605236713883 34242927959688907855070825)
  ·
    refine ⟨25682195969766680891303119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34242927959688907855070825 25682195969766680891303119)
    ·
      refine ⟨38523293954650021336954679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25682195969766680891303119 38523293954650021336954679)
      ·
        refine ⟨57784940931975032005432019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38523293954650021336954679 57784940931975032005432019)
        ·
          refine ⟨86677411397962548008148029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57784940931975032005432019 86677411397962548008148029)
          ·
            refine ⟨32504029274235955503055511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86677411397962548008148029 32504029274235955503055511)
            ·
              refine ⟨48756043911353933254583267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32504029274235955503055511 48756043911353933254583267)
              ·
                refine ⟨73134065867030899881874901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48756043911353933254583267 73134065867030899881874901)
                ·
                  refine ⟨1714079668758536715981443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 73134065867030899881874901 1714079668758536715981443)
                  ·
                    refine ⟨2571119503137805073972165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1714079668758536715981443 2571119503137805073972165)
                    ·
                      refine ⟨482084906838338451369781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2571119503137805073972165 482084906838338451369781)
                      ·
                        rfl

theorem cell23_938857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 7, 1, 4].length) (baseStart_938857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_938857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_938857 prefixEnd_938857 := by exact prefixLift 938857
  have htrace : WordTrace (prefixWord ++ tailWord_938857) baseStart_938857 baseEnd_938857 := by
    simpa [prefixWord, tailWord_938857, baseEnd_938857] using wordTrace_append hprefix tailTrace_938857
  have hstable : (prefixWord ++ tailWord_938857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938857).length < 2 ^ (prefixWord ++ tailWord_938857).sum := by decide
  have hdescent : baseEnd_938857 < baseStart_938857 := by decide
  rcases family_descends (prefixWord ++ tailWord_938857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938891 : List Nat := [1, 1, 1, 1, 4, 2, 2, 4, 3, 2, 2]
def baseStart_938891 : Nat := 118140960795 + 938891 * 2 ^ 59
def prefixEnd_938891 : Nat := 4983230072969 + 3 ^ 40 * 938891 * 2
def baseEnd_938891 : Nat := 482102365180591318344625

theorem tailTrace_938891 : CollatzResearch.WordTrace tailWord_938891 prefixEnd_938891 482102365180591318344625 := by
  unfold tailWord_938891
  simp only [CollatzResearch.WordTrace]
  refine ⟨34244168041565731661808527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22829445361043821107872351 34244168041565731661808527)
  ·
    refine ⟨51366252062348597492712791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34244168041565731661808527 51366252062348597492712791)
    ·
      refine ⟨77049378093522896239069187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51366252062348597492712791 77049378093522896239069187)
      ·
        refine ⟨115574067140284344358603781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77049378093522896239069187 115574067140284344358603781)
        ·
          refine ⟨21670137588803314567238209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115574067140284344358603781 21670137588803314567238209)
          ·
            refine ⟨16252603191602485925428657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21670137588803314567238209 16252603191602485925428657)
            ·
              refine ⟨12189452393701864444071493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16252603191602485925428657 12189452393701864444071493)
              ·
                refine ⟨2285522323819099583263405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12189452393701864444071493 2285522323819099583263405)
                ·
                  refine ⟨857070871432162343723777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2285522323819099583263405 857070871432162343723777)
                  ·
                    refine ⟨642803153574121757792833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 857070871432162343723777 642803153574121757792833)
                    ·
                      refine ⟨482102365180591318344625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 642803153574121757792833 482102365180591318344625)
                      ·
                        rfl

theorem cell23_938891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 4, 3, 2, 2].length) (baseStart_938891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_938891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_938891 prefixEnd_938891 := by exact prefixLift 938891
  have htrace : WordTrace (prefixWord ++ tailWord_938891) baseStart_938891 baseEnd_938891 := by
    simpa [prefixWord, tailWord_938891, baseEnd_938891] using wordTrace_append hprefix tailTrace_938891
  have hstable : (prefixWord ++ tailWord_938891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938891).length < 2 ^ (prefixWord ++ tailWord_938891).sum := by decide
  have hdescent : baseEnd_938891 < baseStart_938891 := by decide
  rcases family_descends (prefixWord ++ tailWord_938891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938911 : List Nat := [1, 1, 2, 5, 2, 3, 1, 1, 1, 1, 5]
def baseStart_938911 : Nat := 118140960795 + 938911 * 2 ^ 59
def prefixEnd_938911 : Nat := 4983230072969 + 3 ^ 40 * 938911 * 2
def baseEnd_938911 : Nat := 482112634793681240094533

theorem tailTrace_938911 : CollatzResearch.WordTrace tailWord_938911 prefixEnd_938911 482112634793681240094533 := by
  unfold tailWord_938911
  simp only [CollatzResearch.WordTrace]
  refine ⟨34244897501493275077536587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22829931667662183385024391 34244897501493275077536587)
  ·
    refine ⟨51367346252239912616304881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34244897501493275077536587 51367346252239912616304881)
    ·
      refine ⟨38525509689179934462228661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51367346252239912616304881 38525509689179934462228661)
      ·
        refine ⟨3611766533360618855833937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38525509689179934462228661 3611766533360618855833937)
        ·
          refine ⟨2708824900020464141875453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3611766533360618855833937 2708824900020464141875453)
          ·
            refine ⟨1015809337507674053203295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2708824900020464141875453 1015809337507674053203295)
            ·
              refine ⟨1523714006261511079804943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1015809337507674053203295 1523714006261511079804943)
              ·
                refine ⟨2285571009392266619707415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1523714006261511079804943 2285571009392266619707415)
                ·
                  refine ⟨3428356514088399929561123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2285571009392266619707415 3428356514088399929561123)
                  ·
                    refine ⟨5142534771132599894341685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3428356514088399929561123 5142534771132599894341685)
                    ·
                      refine ⟨482112634793681240094533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5142534771132599894341685 482112634793681240094533)
                      ·
                        rfl

theorem cell23_938911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 1, 1, 1, 1, 5].length) (baseStart_938911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_938911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_938911 prefixEnd_938911 := by exact prefixLift 938911
  have htrace : WordTrace (prefixWord ++ tailWord_938911) baseStart_938911 baseEnd_938911 := by
    simpa [prefixWord, tailWord_938911, baseEnd_938911] using wordTrace_append hprefix tailTrace_938911
  have hstable : (prefixWord ++ tailWord_938911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938911).length < 2 ^ (prefixWord ++ tailWord_938911).sum := by decide
  have hdescent : baseEnd_938911 < baseStart_938911 := by decide
  rcases family_descends (prefixWord ++ tailWord_938911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938919 : List Nat := [1, 1, 6, 1, 4, 1, 2, 2, 1, 1, 3]
def baseStart_938919 : Nat := 118140960795 + 938919 * 2 ^ 59
def prefixEnd_938919 : Nat := 4983230072969 + 3 ^ 40 * 938919 * 2
def baseEnd_938919 : Nat := 482116742638917208794497

theorem tailTrace_938919 : CollatzResearch.WordTrace tailWord_938919 prefixEnd_938919 482116742638917208794497 := by
  unfold tailWord_938919
  simp only [CollatzResearch.WordTrace]
  refine ⟨34245189285464292443827811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22830126190309528295885207 34245189285464292443827811)
  ·
    refine ⟨51367783928196438665741717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34245189285464292443827811 51367783928196438665741717)
    ·
      refine ⟨2407864871634208062456643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 51367783928196438665741717 2407864871634208062456643)
      ·
        refine ⟨3611797307451312093684965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2407864871634208062456643 3611797307451312093684965)
        ·
          refine ⟨677211995147121017565931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3611797307451312093684965 677211995147121017565931)
          ·
            refine ⟨1015817992720681526348897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 677211995147121017565931 1015817992720681526348897)
            ·
              refine ⟨761863494540511144761673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1015817992720681526348897 761863494540511144761673)
              ·
                refine ⟨571397620905383358571255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 761863494540511144761673 571397620905383358571255)
                ·
                  refine ⟨857096431358075037856883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 571397620905383358571255 857096431358075037856883)
                  ·
                    refine ⟨1285644647037112556785325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 857096431358075037856883 1285644647037112556785325)
                    ·
                      refine ⟨482116742638917208794497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1285644647037112556785325 482116742638917208794497)
                      ·
                        rfl

theorem cell23_938919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 2, 2, 1, 1, 3].length) (baseStart_938919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_938919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_938919 prefixEnd_938919 := by exact prefixLift 938919
  have htrace : WordTrace (prefixWord ++ tailWord_938919) baseStart_938919 baseEnd_938919 := by
    simpa [prefixWord, tailWord_938919, baseEnd_938919] using wordTrace_append hprefix tailTrace_938919
  have hstable : (prefixWord ++ tailWord_938919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938919).length < 2 ^ (prefixWord ++ tailWord_938919).sum := by decide
  have hdescent : baseEnd_938919 < baseStart_938919 := by decide
  rcases family_descends (prefixWord ++ tailWord_938919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938948 : List Nat := [2, 3, 3, 3, 1, 1, 3, 7]
def baseStart_938948 : Nat := 118140960795 + 938948 * 2 ^ 59
def prefixEnd_938948 : Nat := 4983230072969 + 3 ^ 40 * 938948 * 2
def baseEnd_938948 : Nat := 17856727169551762790069

theorem tailTrace_938948 : CollatzResearch.WordTrace tailWord_938948 prefixEnd_938948 17856727169551762790069 := by
  unfold tailWord_938948
  simp only [CollatzResearch.WordTrace]
  refine ⟨17123123501179615198316749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22830831334906153597755665 17123123501179615198316749)
  ·
    refine ⟨6421171312942355699368781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17123123501179615198316749 6421171312942355699368781)
    ·
      refine ⟨2407939242353383387263293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6421171312942355699368781 2407939242353383387263293)
      ·
        refine ⟨902977215882518770223735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2407939242353383387263293 902977215882518770223735)
        ·
          refine ⟨1354465823823778155335603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 902977215882518770223735 1354465823823778155335603)
          ·
            refine ⟨2031698735735667233003405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1354465823823778155335603 2031698735735667233003405)
            ·
              refine ⟨761887025900875212376277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2031698735735667233003405 761887025900875212376277)
              ·
                refine ⟨17856727169551762790069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 761887025900875212376277 17856727169551762790069)
                ·
                  rfl

theorem cell23_938948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 3, 7].length) (baseStart_938948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_938948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_938948 prefixEnd_938948 := by exact prefixLift 938948
  have htrace : WordTrace (prefixWord ++ tailWord_938948) baseStart_938948 baseEnd_938948 := by
    simpa [prefixWord, tailWord_938948, baseEnd_938948] using wordTrace_append hprefix tailTrace_938948
  have hstable : (prefixWord ++ tailWord_938948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938948).length < 2 ^ (prefixWord ++ tailWord_938948).sum := by decide
  have hdescent : baseEnd_938948 < baseStart_938948 := by decide
  rcases family_descends (prefixWord ++ tailWord_938948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938951 : List Nat := [1, 1, 4, 1, 1, 2, 4, 1, 3, 3, 2]
def baseStart_938951 : Nat := 118140960795 + 938951 * 2 ^ 59
def prefixEnd_938951 : Nat := 4983230072969 + 3 ^ 40 * 938951 * 2
def baseEnd_938951 : Nat := 482133174019861083594349

theorem tailTrace_938951 : CollatzResearch.WordTrace tailWord_938951 prefixEnd_938951 482133174019861083594349 := by
  unfold tailWord_938951
  simp only [CollatzResearch.WordTrace]
  refine ⟨34246356421348361908992707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22830904280898907939328471 34246356421348361908992707)
  ·
    refine ⟨51369534632022542863489061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34246356421348361908992707 51369534632022542863489061)
    ·
      refine ⟨9631787743504226786904199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51369534632022542863489061 9631787743504226786904199)
      ·
        refine ⟨14447681615256340180356299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9631787743504226786904199 14447681615256340180356299)
        ·
          refine ⟨21671522422884510270534449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14447681615256340180356299 21671522422884510270534449)
          ·
            refine ⟨16253641817163382702900837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21671522422884510270534449 16253641817163382702900837)
            ·
              refine ⟨3047557840718134256793907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16253641817163382702900837 3047557840718134256793907)
              ·
                refine ⟨4571336761077201385190861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3047557840718134256793907 4571336761077201385190861)
                ·
                  refine ⟨1714251285403950519446573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4571336761077201385190861 1714251285403950519446573)
                  ·
                    refine ⟨642844232026481444792465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1714251285403950519446573 642844232026481444792465)
                    ·
                      refine ⟨482133174019861083594349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 642844232026481444792465 482133174019861083594349)
                      ·
                        rfl

theorem cell23_938951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 1, 3, 3, 2].length) (baseStart_938951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_938951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_938951 prefixEnd_938951 := by exact prefixLift 938951
  have htrace : WordTrace (prefixWord ++ tailWord_938951) baseStart_938951 baseEnd_938951 := by
    simpa [prefixWord, tailWord_938951, baseEnd_938951] using wordTrace_append hprefix tailTrace_938951
  have hstable : (prefixWord ++ tailWord_938951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938951).length < 2 ^ (prefixWord ++ tailWord_938951).sum := by decide
  have hdescent : baseEnd_938951 < baseStart_938951 := by decide
  rcases family_descends (prefixWord ++ tailWord_938951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938968 : List Nat := [2, 1, 2, 2, 2, 4, 1, 3, 1, 3, 2]
def baseStart_938968 : Nat := 118140960795 + 938968 * 2 ^ 59
def prefixEnd_938968 : Nat := 4983230072969 + 3 ^ 40 * 938968 * 2
def baseEnd_938968 : Nat := 482141903190987517081771

theorem tailTrace_938968 : CollatzResearch.WordTrace tailWord_938968 prefixEnd_938968 482141903190987517081771 := by
  unfold tailWord_938968
  simp only [CollatzResearch.WordTrace]
  refine ⟨17123488231143386906180779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22831317641524515874907705 17123488231143386906180779)
  ·
    refine ⟨25685232346715080359271169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17123488231143386906180779 25685232346715080359271169)
    ·
      refine ⟨19263924260036310269453377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25685232346715080359271169 19263924260036310269453377)
      ·
        refine ⟨14447943195027232702090033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19263924260036310269453377 14447943195027232702090033)
        ·
          refine ⟨10835957396270424526567525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14447943195027232702090033 10835957396270424526567525)
          ·
            refine ⟨2031742011800704598731411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10835957396270424526567525 2031742011800704598731411)
            ·
              refine ⟨3047613017701056898097117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2031742011800704598731411 3047613017701056898097117)
              ·
                refine ⟨1142854881637896336786419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3047613017701056898097117 1142854881637896336786419)
                ·
                  refine ⟨1714282322456844505179629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1142854881637896336786419 1714282322456844505179629)
                  ·
                    refine ⟨642855870921316689442361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1714282322456844505179629 642855870921316689442361)
                    ·
                      refine ⟨482141903190987517081771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 642855870921316689442361 482141903190987517081771)
                      ·
                        rfl

theorem cell23_938968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 3, 1, 3, 2].length) (baseStart_938968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_938968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_938968 prefixEnd_938968 := by exact prefixLift 938968
  have htrace : WordTrace (prefixWord ++ tailWord_938968) baseStart_938968 baseEnd_938968 := by
    simpa [prefixWord, tailWord_938968, baseEnd_938968] using wordTrace_append hprefix tailTrace_938968
  have hstable : (prefixWord ++ tailWord_938968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938968).length < 2 ^ (prefixWord ++ tailWord_938968).sum := by decide
  have hdescent : baseEnd_938968 < baseStart_938968 := by decide
  rcases family_descends (prefixWord ++ tailWord_938968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938975 : List Nat := [1, 1, 2, 3, 5, 2, 1, 2, 2, 1, 3]
def baseStart_938975 : Nat := 118140960795 + 938975 * 2 ^ 59
def prefixEnd_938975 : Nat := 4983230072969 + 3 ^ 40 * 938975 * 2
def baseEnd_938975 : Nat := 482145497555568989694239

theorem tailTrace_938975 : CollatzResearch.WordTrace tailWord_938975 prefixEnd_938975 482145497555568989694239 := by
  unfold tailWord_938975
  simp only [CollatzResearch.WordTrace]
  refine ⟨34247231773261414007866379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22831487848840942671910919 34247231773261414007866379)
  ·
    refine ⟨51370847659892121011799569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34247231773261414007866379 51370847659892121011799569)
    ·
      refine ⟨38528135744919090758849677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51370847659892121011799569 38528135744919090758849677)
      ·
        refine ⟨14448050904344659034568629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38528135744919090758849677 14448050904344659034568629)
        ·
          refine ⟨1354504772282311784490809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14448050904344659034568629 1354504772282311784490809)
          ·
            refine ⟨1015878579211733838368107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1354504772282311784490809 1015878579211733838368107)
            ·
              refine ⟨1523817868817600757552161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1015878579211733838368107 1523817868817600757552161)
              ·
                refine ⟨1142863401613200568164121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1523817868817600757552161 1142863401613200568164121)
                ·
                  refine ⟨857147551209900426123091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1142863401613200568164121 857147551209900426123091)
                  ·
                    refine ⟨1285721326814850639184637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 857147551209900426123091 1285721326814850639184637)
                    ·
                      refine ⟨482145497555568989694239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1285721326814850639184637 482145497555568989694239)
                      ·
                        rfl

theorem cell23_938975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 1, 2, 2, 1, 3].length) (baseStart_938975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_938975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_938975 prefixEnd_938975 := by exact prefixLift 938975
  have htrace : WordTrace (prefixWord ++ tailWord_938975) baseStart_938975 baseEnd_938975 := by
    simpa [prefixWord, tailWord_938975, baseEnd_938975] using wordTrace_append hprefix tailTrace_938975
  have hstable : (prefixWord ++ tailWord_938975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938975).length < 2 ^ (prefixWord ++ tailWord_938975).sum := by decide
  have hdescent : baseEnd_938975 < baseStart_938975 := by decide
  rcases family_descends (prefixWord ++ tailWord_938975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938984 : List Nat := [2, 1, 4, 1, 1, 1, 2, 1, 1, 6, 3]
def baseStart_938984 : Nat := 118140960795 + 938984 * 2 ^ 59
def prefixEnd_938984 : Nat := 4983230072969 + 3 ^ 40 * 938984 * 2
def baseEnd_938984 : Nat := 482150118881459454481697

theorem tailTrace_938984 : CollatzResearch.WordTrace tailWord_938984 prefixEnd_938984 482150118881459454481697 := by
  unfold tailWord_938984
  simp only [CollatzResearch.WordTrace]
  refine ⟨17123780015114404272472003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22831706686819205696629337 17123780015114404272472003)
  ·
    refine ⟨25685670022671606408708005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17123780015114404272472003 25685670022671606408708005)
    ·
      refine ⟨4816063129250926201632751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25685670022671606408708005 4816063129250926201632751)
      ·
        refine ⟨7224094693876389302449127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4816063129250926201632751 7224094693876389302449127)
        ·
          refine ⟨10836142040814583953673691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7224094693876389302449127 10836142040814583953673691)
          ·
            refine ⟨16254213061221875930510537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10836142040814583953673691 16254213061221875930510537)
            ·
              refine ⟨12190659795916406947882903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16254213061221875930510537 12190659795916406947882903)
              ·
                refine ⟨18285989693874610421824355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12190659795916406947882903 18285989693874610421824355)
                ·
                  refine ⟨27428984540811915632736533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18285989693874610421824355 27428984540811915632736533)
                  ·
                    refine ⟨1285733650350558545284525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27428984540811915632736533 1285733650350558545284525)
                    ·
                      refine ⟨482150118881459454481697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1285733650350558545284525 482150118881459454481697)
                      ·
                        rfl

theorem cell23_938984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 1, 6, 3].length) (baseStart_938984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_938984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_938984 prefixEnd_938984 := by exact prefixLift 938984
  have htrace : WordTrace (prefixWord ++ tailWord_938984) baseStart_938984 baseEnd_938984 := by
    simpa [prefixWord, tailWord_938984, baseEnd_938984] using wordTrace_append hprefix tailTrace_938984
  have hstable : (prefixWord ++ tailWord_938984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938984).length < 2 ^ (prefixWord ++ tailWord_938984).sum := by decide
  have hdescent : baseEnd_938984 < baseStart_938984 := by decide
  rcases family_descends (prefixWord ++ tailWord_938984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939004 : List Nat := [2, 2, 2, 1, 2, 3, 2, 2, 7]
def baseStart_939004 : Nat := 118140960795 + 939004 * 2 ^ 59
def prefixEnd_939004 : Nat := 4983230072969 + 3 ^ 40 * 939004 * 2
def baseEnd_939004 : Nat := 53573376499394375136845

theorem tailTrace_939004 : CollatzResearch.WordTrace tailWord_939004 prefixEnd_939004 53573376499394375136845 := by
  unfold tailWord_939004
  simp only [CollatzResearch.WordTrace]
  refine ⟨17124144745078175980336033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22832192993437567973781377 17124144745078175980336033)
  ·
    refine ⟨12843108558808631985252025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17124144745078175980336033 12843108558808631985252025)
    ·
      refine ⟨9632331419106473988939019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12843108558808631985252025 9632331419106473988939019)
      ·
        refine ⟨14448497128659710983408529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9632331419106473988939019 14448497128659710983408529)
        ·
          refine ⟨10836372846494783237556397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14448497128659710983408529 10836372846494783237556397)
          ·
            refine ⟨4063639817435543714083649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10836372846494783237556397 4063639817435543714083649)
            ·
              refine ⟨3047729863076657785562737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4063639817435543714083649 3047729863076657785562737)
              ·
                refine ⟨2285797397307493339172053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3047729863076657785562737 2285797397307493339172053)
                ·
                  refine ⟨53573376499394375136845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2285797397307493339172053 53573376499394375136845)
                  ·
                    rfl

theorem cell23_939004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 2, 7].length) (baseStart_939004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_939004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_939004 prefixEnd_939004 := by exact prefixLift 939004
  have htrace : WordTrace (prefixWord ++ tailWord_939004) baseStart_939004 baseEnd_939004 := by
    simpa [prefixWord, tailWord_939004, baseEnd_939004] using wordTrace_append hprefix tailTrace_939004
  have hstable : (prefixWord ++ tailWord_939004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939004).length < 2 ^ (prefixWord ++ tailWord_939004).sum := by decide
  have hdescent : baseEnd_939004 < baseStart_939004 := by decide
  rcases family_descends (prefixWord ++ tailWord_939004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939071 : List Nat := [1, 1, 2, 2, 3, 1, 1, 2, 4, 4, 2]
def baseStart_939071 : Nat := 118140960795 + 939071 * 2 ^ 59
def prefixEnd_939071 : Nat := 4983230072969 + 3 ^ 40 * 939071 * 2
def baseEnd_939071 : Nat := 482194791698400614093797

theorem tailTrace_939071 : CollatzResearch.WordTrace tailWord_939071 prefixEnd_939071 482194791698400614093797 := by
  unfold tailWord_939071
  simp only [CollatzResearch.WordTrace]
  refine ⟨34250733180913622403361067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22833822120609081602240711 34250733180913622403361067)
  ·
    refine ⟨51376099771370433605041601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34250733180913622403361067 51376099771370433605041601)
    ·
      refine ⟨38532074828527825203781201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51376099771370433605041601 38532074828527825203781201)
      ·
        refine ⟨28899056121395868902835901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38532074828527825203781201 28899056121395868902835901)
        ·
          refine ⟨10837146045523450838563463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28899056121395868902835901 10837146045523450838563463)
          ·
            refine ⟨16255719068285176257845195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10837146045523450838563463 16255719068285176257845195)
            ·
              refine ⟨24383578602427764386767793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16255719068285176257845195 24383578602427764386767793)
              ·
                refine ⟨18287683951820823290075845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24383578602427764386767793 18287683951820823290075845)
                ·
                  refine ⟨3428940740966404366889221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18287683951820823290075845 3428940740966404366889221)
                  ·
                    refine ⟨642926388931200818791729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3428940740966404366889221 642926388931200818791729)
                    ·
                      refine ⟨482194791698400614093797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 642926388931200818791729 482194791698400614093797)
                      ·
                        rfl

theorem cell23_939071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 4, 4, 2].length) (baseStart_939071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_939071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_939071 prefixEnd_939071 := by exact prefixLift 939071
  have htrace : WordTrace (prefixWord ++ tailWord_939071) baseStart_939071 baseEnd_939071 := by
    simpa [prefixWord, tailWord_939071, baseEnd_939071] using wordTrace_append hprefix tailTrace_939071
  have hstable : (prefixWord ++ tailWord_939071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939071).length < 2 ^ (prefixWord ++ tailWord_939071).sum := by decide
  have hdescent : baseEnd_939071 < baseStart_939071 := by decide
  rcases family_descends (prefixWord ++ tailWord_939071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939078 : List Nat := [6, 1, 1, 1, 1, 2, 1, 2, 1, 2, 5]
def baseStart_939078 : Nat := 118140960795 + 939078 * 2 ^ 59
def prefixEnd_939078 : Nat := 4983230072969 + 3 ^ 40 * 939078 * 2
def baseEnd_939078 : Nat := 482198386062982086706265

theorem tailTrace_939078 : CollatzResearch.WordTrace tailWord_939078 prefixEnd_939078 482198386062982086706265 := by
  unfold tailWord_939078
  simp only [CollatzResearch.WordTrace]
  refine ⟨1070343390371508206214559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 22833992327925508399243925 1070343390371508206214559)
  ·
    refine ⟨1605515085557262309321839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1070343390371508206214559 1605515085557262309321839)
    ·
      refine ⟨2408272628335893463982759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1605515085557262309321839 2408272628335893463982759)
      ·
        refine ⟨3612408942503840195974139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2408272628335893463982759 3612408942503840195974139)
        ·
          refine ⟨5418613413755760293961209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3612408942503840195974139 5418613413755760293961209)
          ·
            refine ⟨4063960060316820220470907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5418613413755760293961209 4063960060316820220470907)
            ·
              refine ⟨6095940090475230330706361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4063960060316820220470907 6095940090475230330706361)
              ·
                refine ⟨4571955067856422748029771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6095940090475230330706361 4571955067856422748029771)
                ·
                  refine ⟨6857932601784634122044657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4571955067856422748029771 6857932601784634122044657)
                  ·
                    refine ⟨5143449451338475591533493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6857932601784634122044657 5143449451338475591533493)
                    ·
                      refine ⟨482198386062982086706265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5143449451338475591533493 482198386062982086706265)
                      ·
                        rfl

theorem cell23_939078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_939078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_939078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_939078 prefixEnd_939078 := by exact prefixLift 939078
  have htrace : WordTrace (prefixWord ++ tailWord_939078) baseStart_939078 baseEnd_939078 := by
    simpa [prefixWord, tailWord_939078, baseEnd_939078] using wordTrace_append hprefix tailTrace_939078
  have hstable : (prefixWord ++ tailWord_939078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939078).length < 2 ^ (prefixWord ++ tailWord_939078).sum := by decide
  have hdescent : baseEnd_939078 < baseStart_939078 := by decide
  rcases family_descends (prefixWord ++ tailWord_939078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939084 : List Nat := [2, 2, 1, 3, 1, 1, 1, 3, 2, 1, 6]
def baseStart_939084 : Nat := 118140960795 + 939084 * 2 ^ 59
def prefixEnd_939084 : Nat := 4983230072969 + 3 ^ 40 * 939084 * 2
def baseEnd_939084 : Nat := 482201466946909063231237

theorem tailTrace_939084 : CollatzResearch.WordTrace tailWord_939084 prefixEnd_939084 482201466946909063231237 := by
  unfold tailWord_939084
  simp only [CollatzResearch.WordTrace]
  refine ⟨17125603664933262811792153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22834138219911017082389537 17125603664933262811792153)
  ·
    refine ⟨12844202748699947108844115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17125603664933262811792153 12844202748699947108844115)
    ·
      refine ⟨19266304123049920663266173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12844202748699947108844115 19266304123049920663266173)
      ·
        refine ⟨7224864046143720248724815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19266304123049920663266173 7224864046143720248724815)
        ·
          refine ⟨10837296069215580373087223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7224864046143720248724815 10837296069215580373087223)
          ·
            refine ⟨16255944103823370559630835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10837296069215580373087223 16255944103823370559630835)
            ·
              refine ⟨24383916155735055839446253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16255944103823370559630835 24383916155735055839446253)
              ·
                refine ⟨9143968558400645939792345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24383916155735055839446253 9143968558400645939792345)
                ·
                  refine ⟨6857976418800484454844259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9143968558400645939792345 6857976418800484454844259)
                  ·
                    refine ⟨10286964628200726682266389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6857976418800484454844259 10286964628200726682266389)
                    ·
                      refine ⟨482201466946909063231237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10286964628200726682266389 482201466946909063231237)
                      ·
                        rfl

theorem cell23_939084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 3, 2, 1, 6].length) (baseStart_939084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_939084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_939084 prefixEnd_939084 := by exact prefixLift 939084
  have htrace : WordTrace (prefixWord ++ tailWord_939084) baseStart_939084 baseEnd_939084 := by
    simpa [prefixWord, tailWord_939084, baseEnd_939084] using wordTrace_append hprefix tailTrace_939084
  have hstable : (prefixWord ++ tailWord_939084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939084).length < 2 ^ (prefixWord ++ tailWord_939084).sum := by decide
  have hdescent : baseEnd_939084 < baseStart_939084 := by decide
  rcases family_descends (prefixWord ++ tailWord_939084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939111 : List Nat := [1, 1, 5, 1, 1, 3, 2, 3, 6]
def baseStart_939111 : Nat := 118140960795 + 939111 * 2 ^ 59
def prefixEnd_939111 : Nat := 4983230072969 + 3 ^ 40 * 939111 * 2
def baseEnd_939111 : Nat := 53579481213842273065957

theorem tailTrace_939111 : CollatzResearch.WordTrace tailWord_939111 prefixEnd_939111 53579481213842273065957 := by
  unfold tailWord_939111
  simp only [CollatzResearch.WordTrace]
  refine ⟨34252192100768709234817187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22834794733845806156544791 34252192100768709234817187)
  ·
    refine ⟨51378288151153063852225781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34252192100768709234817187 51378288151153063852225781)
    ·
      refine ⟨4816714514170599736146167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51378288151153063852225781 4816714514170599736146167)
      ·
        refine ⟨7225071771255899604219251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4816714514170599736146167 7225071771255899604219251)
        ·
          refine ⟨10837607656883849406328877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7225071771255899604219251 10837607656883849406328877)
          ·
            refine ⟨4064102871331443527373329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10837607656883849406328877 4064102871331443527373329)
            ·
              refine ⟨3048077153498582645529997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4064102871331443527373329 3048077153498582645529997)
              ·
                refine ⟨1143028932561968492073749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3048077153498582645529997 1143028932561968492073749)
                ·
                  refine ⟨53579481213842273065957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1143028932561968492073749 53579481213842273065957)
                  ·
                    rfl

theorem cell23_939111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 3, 6].length) (baseStart_939111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_939111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_939111 prefixEnd_939111 := by exact prefixLift 939111
  have htrace : WordTrace (prefixWord ++ tailWord_939111) baseStart_939111 baseEnd_939111 := by
    simpa [prefixWord, tailWord_939111, baseEnd_939111] using wordTrace_append hprefix tailTrace_939111
  have hstable : (prefixWord ++ tailWord_939111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939111).length < 2 ^ (prefixWord ++ tailWord_939111).sum := by decide
  have hdescent : baseEnd_939111 < baseStart_939111 := by decide
  rcases family_descends (prefixWord ++ tailWord_939111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939125 : List Nat := [1, 3, 4, 3, 1, 1, 1, 1, 1, 4, 3]
def baseStart_939125 : Nat := 118140960795 + 939125 * 2 ^ 59
def prefixEnd_939125 : Nat := 4983230072969 + 3 ^ 40 * 939125 * 2
def baseEnd_939125 : Nat := 482222519653743402818549

theorem tailTrace_939125 : CollatzResearch.WordTrace tailWord_939125 prefixEnd_939125 482222519653743402818549 := by
  unfold tailWord_939125
  simp only [CollatzResearch.WordTrace]
  refine ⟨34252702722717989625826829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22835135148478659750551219 34252702722717989625826829)
  ·
    refine ⟨12844763521019246109685061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34252702722717989625826829 12844763521019246109685061)
    ·
      refine ⟨2408393160191108645565949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12844763521019246109685061 2408393160191108645565949)
      ·
        refine ⟨903147435071665742087231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2408393160191108645565949 903147435071665742087231)
        ·
          refine ⟨1354721152607498613130847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 903147435071665742087231 1354721152607498613130847)
          ·
            refine ⟨2032081728911247919696271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1354721152607498613130847 2032081728911247919696271)
            ·
              refine ⟨3048122593366871879544407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2032081728911247919696271 3048122593366871879544407)
              ·
                refine ⟨4572183890050307819316611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3048122593366871879544407 4572183890050307819316611)
                ·
                  refine ⟨6858275835075461728974917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4572183890050307819316611 6858275835075461728974917)
                  ·
                    refine ⟨1285926719076649074182797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6858275835075461728974917 1285926719076649074182797)
                    ·
                      refine ⟨482222519653743402818549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1285926719076649074182797 482222519653743402818549)
                      ·
                        rfl

theorem cell23_939125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_939125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_939125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_939125 prefixEnd_939125 := by exact prefixLift 939125
  have htrace : WordTrace (prefixWord ++ tailWord_939125) baseStart_939125 baseEnd_939125 := by
    simpa [prefixWord, tailWord_939125, baseEnd_939125] using wordTrace_append hprefix tailTrace_939125
  have hstable : (prefixWord ++ tailWord_939125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939125).length < 2 ^ (prefixWord ++ tailWord_939125).sum := by decide
  have hdescent : baseEnd_939125 < baseStart_939125 := by decide
  rcases family_descends (prefixWord ++ tailWord_939125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939148 : List Nat := [2, 2, 1, 2, 1, 1, 1, 6, 2, 3, 2]
def baseStart_939148 : Nat := 118140960795 + 939148 * 2 ^ 59
def prefixEnd_939148 : Nat := 4983230072969 + 3 ^ 40 * 939148 * 2
def baseEnd_939148 : Nat := 482234329708796812830943

theorem tailTrace_939148 : CollatzResearch.WordTrace tailWord_939148 prefixEnd_939148 482234329708796812830943 := by
  unfold tailWord_939148
  simp only [CollatzResearch.WordTrace]
  refine ⟨17126770800817332276957049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22835694401089776369276065 17126770800817332276957049)
  ·
    refine ⟨12845078100612999207717787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17126770800817332276957049 12845078100612999207717787)
    ·
      refine ⟨19267617150919498811576681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12845078100612999207717787 19267617150919498811576681)
      ·
        refine ⟨14450712863189624108682511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19267617150919498811576681 14450712863189624108682511)
        ·
          refine ⟨21676069294784436163023767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14450712863189624108682511 21676069294784436163023767)
          ·
            refine ⟨32514103942176654244535651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21676069294784436163023767 32514103942176654244535651)
            ·
              refine ⟨48771155913264981366803477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32514103942176654244535651 48771155913264981366803477)
              ·
                refine ⟨2286147933434296001568913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 48771155913264981366803477 2286147933434296001568913)
                ·
                  refine ⟨1714610950075722001176685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2286147933434296001568913 1714610950075722001176685)
                  ·
                    refine ⟨642979106278395750441257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1714610950075722001176685 642979106278395750441257)
                    ·
                      refine ⟨482234329708796812830943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 642979106278395750441257 482234329708796812830943)
                      ·
                        rfl

theorem cell23_939148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 6, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 6, 2, 3, 2].length) (baseStart_939148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_939148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_939148 prefixEnd_939148 := by exact prefixLift 939148
  have htrace : WordTrace (prefixWord ++ tailWord_939148) baseStart_939148 baseEnd_939148 := by
    simpa [prefixWord, tailWord_939148, baseEnd_939148] using wordTrace_append hprefix tailTrace_939148
  have hstable : (prefixWord ++ tailWord_939148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939148).length < 2 ^ (prefixWord ++ tailWord_939148).sum := by decide
  have hdescent : baseEnd_939148 < baseStart_939148 := by decide
  rcases family_descends (prefixWord ++ tailWord_939148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939155 : List Nat := [1, 1, 1, 2, 1, 2, 6, 4, 1, 1, 3]
def baseStart_939155 : Nat := 118140960795 + 939155 * 2 ^ 59
def prefixEnd_939155 : Nat := 4983230072969 + 3 ^ 40 * 939155 * 2
def baseEnd_939155 : Nat := 482237924073378285443411

theorem tailTrace_939155 : CollatzResearch.WordTrace tailWord_939155 prefixEnd_939155 482237924073378285443411 := by
  unfold tailWord_939155
  simp only [CollatzResearch.WordTrace]
  refine ⟨34253796912609304749418919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22835864608406203166279279 34253796912609304749418919)
  ·
    refine ⟨51380695368913957124128379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34253796912609304749418919 51380695368913957124128379)
    ·
      refine ⟨77071043053370935686192569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51380695368913957124128379 77071043053370935686192569)
      ·
        refine ⟨57803282290028201764644427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77071043053370935686192569 57803282290028201764644427)
        ·
          refine ⟨86704923435042302646966641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57803282290028201764644427 86704923435042302646966641)
          ·
            refine ⟨65028692576281726985224981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86704923435042302646966641 65028692576281726985224981)
            ·
              refine ⟨3048219964513205952432421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 65028692576281726985224981 3048219964513205952432421)
              ·
                refine ⟨571541243346226116081079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3048219964513205952432421 571541243346226116081079)
                ·
                  refine ⟨857311865019339174121619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 571541243346226116081079 857311865019339174121619)
                  ·
                    refine ⟨1285967797529008761182429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 857311865019339174121619 1285967797529008761182429)
                    ·
                      refine ⟨482237924073378285443411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1285967797529008761182429 482237924073378285443411)
                      ·
                        rfl

theorem cell23_939155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 4, 1, 1, 3].length) (baseStart_939155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_939155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_939155 prefixEnd_939155 := by exact prefixLift 939155
  have htrace : WordTrace (prefixWord ++ tailWord_939155) baseStart_939155 baseEnd_939155 := by
    simpa [prefixWord, tailWord_939155, baseEnd_939155] using wordTrace_append hprefix tailTrace_939155
  have hstable : (prefixWord ++ tailWord_939155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939155).length < 2 ^ (prefixWord ++ tailWord_939155).sum := by decide
  have hdescent : baseEnd_939155 < baseStart_939155 := by decide
  rcases family_descends (prefixWord ++ tailWord_939155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939175 : List Nat := [1, 1, 6, 2, 1, 2, 2, 2, 1, 5]
def baseStart_939175 : Nat := 118140960795 + 939175 * 2 ^ 59
def prefixEnd_939175 : Nat := 4983230072969 + 3 ^ 40 * 939175 * 2
def baseEnd_939175 : Nat := 160749397895489402397773

theorem tailTrace_939175 : CollatzResearch.WordTrace tailWord_939175 prefixEnd_939175 160749397895489402397773 := by
  unfold tailWord_939175
  simp only [CollatzResearch.WordTrace]
  refine ⟨34254526372536848165146979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22836350915024565443431319 34254526372536848165146979)
  ·
    refine ⟨51381789558805272247720469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34254526372536848165146979 51381789558805272247720469)
    ·
      refine ⟨2408521385568997136611897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 51381789558805272247720469 2408521385568997136611897)
      ·
        refine ⟨1806391039176747852458923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2408521385568997136611897 1806391039176747852458923)
        ·
          refine ⟨2709586558765121778688385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1806391039176747852458923 2709586558765121778688385)
          ·
            refine ⟨2032189919073841334016289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2709586558765121778688385 2032189919073841334016289)
            ·
              refine ⟨1524142439305381000512217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2032189919073841334016289 1524142439305381000512217)
              ·
                refine ⟨1143106829479035750384163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1524142439305381000512217 1143106829479035750384163)
                ·
                  refine ⟨1714660244218553625576245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1143106829479035750384163 1714660244218553625576245)
                  ·
                    refine ⟨160749397895489402397773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1714660244218553625576245 160749397895489402397773)
                    ·
                      rfl

theorem cell23_939175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 2, 2, 1, 5].length) (baseStart_939175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_939175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_939175 prefixEnd_939175 := by exact prefixLift 939175
  have htrace : WordTrace (prefixWord ++ tailWord_939175) baseStart_939175 baseEnd_939175 := by
    simpa [prefixWord, tailWord_939175, baseEnd_939175] using wordTrace_append hprefix tailTrace_939175
  have hstable : (prefixWord ++ tailWord_939175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939175).length < 2 ^ (prefixWord ++ tailWord_939175).sum := by decide
  have hdescent : baseEnd_939175 < baseStart_939175 := by decide
  rcases family_descends (prefixWord ++ tailWord_939175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939184 : List Nat := [2, 1, 1, 1, 2, 1, 2, 13]
def baseStart_939184 : Nat := 118140960795 + 939184 * 2 ^ 59
def prefixEnd_939184 : Nat := 4983230072969 + 3 ^ 40 * 939184 * 2
def baseEnd_939184 : Nat := 17861215370828098962251

theorem tailTrace_939184 : CollatzResearch.WordTrace tailWord_939184 prefixEnd_939184 17861215370828098962251 := by
  unfold tailWord_939184
  simp only [CollatzResearch.WordTrace]
  refine ⟨17127427314752121351112303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22836569753002828468149737 17127427314752121351112303)
  ·
    refine ⟨25691140972128182026668455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17127427314752121351112303 25691140972128182026668455)
    ·
      refine ⟨38536711458192273040002683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25691140972128182026668455 38536711458192273040002683)
      ·
        refine ⟨57805067187288409560004025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38536711458192273040002683 57805067187288409560004025)
        ·
          refine ⟨43353800390466307170003019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57805067187288409560004025 43353800390466307170003019)
          ·
            refine ⟨65030700585699460755004529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43353800390466307170003019 65030700585699460755004529)
            ·
              refine ⟨48773025439274595566253397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65030700585699460755004529 48773025439274595566253397)
              ·
                refine ⟨17861215370828098962251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 48773025439274595566253397 17861215370828098962251)
                ·
                  rfl

theorem cell23_939184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 13].length) (baseStart_939184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_939184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_939184 prefixEnd_939184 := by exact prefixLift 939184
  have htrace : WordTrace (prefixWord ++ tailWord_939184) baseStart_939184 baseEnd_939184 := by
    simpa [prefixWord, tailWord_939184, baseEnd_939184] using wordTrace_append hprefix tailTrace_939184
  have hstable : (prefixWord ++ tailWord_939184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939184).length < 2 ^ (prefixWord ++ tailWord_939184).sum := by decide
  have hdescent : baseEnd_939184 < baseStart_939184 := by decide
  rcases family_descends (prefixWord ++ tailWord_939184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939191 : List Nat := [1, 1, 3, 1, 4, 1, 2, 1, 3, 2, 4]
def baseStart_939191 : Nat := 118140960795 + 939191 * 2 ^ 59
def prefixEnd_939191 : Nat := 4983230072969 + 3 ^ 40 * 939191 * 2
def baseEnd_939191 : Nat := 482256409376940144593245

theorem tailTrace_939191 : CollatzResearch.WordTrace tailWord_939191 prefixEnd_939191 482256409376940144593245 := by
  unfold tailWord_939191
  simp only [CollatzResearch.WordTrace]
  refine ⟨34255109940478882897729427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22836739960319255265152951 34255109940478882897729427)
  ·
    refine ⟨51382664910718324346594141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34255109940478882897729427 51382664910718324346594141)
    ·
      refine ⟨19268499341519371629972803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51382664910718324346594141 19268499341519371629972803)
      ·
        refine ⟨28902749012279057444959205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19268499341519371629972803 28902749012279057444959205)
        ·
          refine ⟨5419265439802323270929851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28902749012279057444959205 5419265439802323270929851)
          ·
            refine ⟨8128898159703484906394777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5419265439802323270929851 8128898159703484906394777)
            ·
              refine ⟨6096673619777613679796083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8128898159703484906394777 6096673619777613679796083)
              ·
                refine ⟨9145010429666420519694125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6096673619777613679796083 9145010429666420519694125)
                ·
                  refine ⟨3429378911124907694885297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9145010429666420519694125 3429378911124907694885297)
                  ·
                    refine ⟨2572034183343680771163973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3429378911124907694885297 2572034183343680771163973)
                    ·
                      refine ⟨482256409376940144593245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2572034183343680771163973 482256409376940144593245)
                      ·
                        rfl

theorem cell23_939191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 1, 3, 2, 4].length) (baseStart_939191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_939191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_939191 prefixEnd_939191 := by exact prefixLift 939191
  have htrace : WordTrace (prefixWord ++ tailWord_939191) baseStart_939191 baseEnd_939191 := by
    simpa [prefixWord, tailWord_939191, baseEnd_939191] using wordTrace_append hprefix tailTrace_939191
  have hstable : (prefixWord ++ tailWord_939191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939191).length < 2 ^ (prefixWord ++ tailWord_939191).sum := by decide
  have hdescent : baseEnd_939191 < baseStart_939191 := by decide
  rcases family_descends (prefixWord ++ tailWord_939191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939198 : List Nat := [4, 2, 1, 1, 3, 1, 1, 3, 1, 1, 5]
def baseStart_939198 : Nat := 118140960795 + 939198 * 2 ^ 59
def prefixEnd_939198 : Nat := 4983230072969 + 3 ^ 40 * 939198 * 2
def baseEnd_939198 : Nat := 482260003741521617205713

theorem tailTrace_939198 : CollatzResearch.WordTrace tailWord_939198 prefixEnd_939198 482260003741521617205713 := by
  unfold tailWord_939198
  simp only [CollatzResearch.WordTrace]
  refine ⟨4281920656431690386654281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22836910167635682062156165 4281920656431690386654281)
  ·
    refine ⟨3211440492323767789990711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4281920656431690386654281 3211440492323767789990711)
    ·
      refine ⟨4817160738485651684986067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3211440492323767789990711 4817160738485651684986067)
      ·
        refine ⟨7225741107728477527479101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4817160738485651684986067 7225741107728477527479101)
        ·
          refine ⟨2709652915398179072804663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7225741107728477527479101 2709652915398179072804663)
          ·
            refine ⟨4064479373097268609206995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2709652915398179072804663 4064479373097268609206995)
            ·
              refine ⟨6096719059645902913810493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4064479373097268609206995 6096719059645902913810493)
              ·
                refine ⟨2286269647367213592678935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6096719059645902913810493 2286269647367213592678935)
                ·
                  refine ⟨3429404471050820389018403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2286269647367213592678935 3429404471050820389018403)
                  ·
                    refine ⟨5144106706576230583527605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3429404471050820389018403 5144106706576230583527605)
                    ·
                      refine ⟨482260003741521617205713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5144106706576230583527605 482260003741521617205713)
                      ·
                        rfl

theorem cell23_939198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 3, 1, 1, 5].length) (baseStart_939198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_939198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_939198 prefixEnd_939198 := by exact prefixLift 939198
  have htrace : WordTrace (prefixWord ++ tailWord_939198) baseStart_939198 baseEnd_939198 := by
    simpa [prefixWord, tailWord_939198, baseEnd_939198] using wordTrace_append hprefix tailTrace_939198
  have hstable : (prefixWord ++ tailWord_939198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939198).length < 2 ^ (prefixWord ++ tailWord_939198).sum := by decide
  have hdescent : baseEnd_939198 < baseStart_939198 := by decide
  rcases family_descends (prefixWord ++ tailWord_939198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939211 : List Nat := [1, 1, 1, 1, 3, 2, 2, 1, 5, 3, 3]
def baseStart_939211 : Nat := 118140960795 + 939211 * 2 ^ 59
def prefixEnd_939211 : Nat := 4983230072969 + 3 ^ 40 * 939211 * 2
def baseEnd_939211 : Nat := 482266678990030066343153

theorem tailTrace_939211 : CollatzResearch.WordTrace tailWord_939211 prefixEnd_939211 482266678990030066343153 := by
  unfold tailWord_939211
  simp only [CollatzResearch.WordTrace]
  refine ⟨34255839400406426313457487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22837226266937617542304991 34255839400406426313457487)
  ·
    refine ⟨51383759100609639470186231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34255839400406426313457487 51383759100609639470186231)
    ·
      refine ⟨77075638650914459205279347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51383759100609639470186231 77075638650914459205279347)
      ·
        refine ⟨115613457976371688807919021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77075638650914459205279347 115613457976371688807919021)
        ·
          refine ⟨43355046741139383302969633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115613457976371688807919021 43355046741139383302969633)
          ·
            refine ⟨32516285055854537477227225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43355046741139383302969633 32516285055854537477227225)
            ·
              refine ⟨24387213791890903107920419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32516285055854537477227225 24387213791890903107920419)
              ·
                refine ⟨36580820687836354661880629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24387213791890903107920419 36580820687836354661880629)
                ·
                  refine ⟨3429451939484658249551309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36580820687836354661880629 3429451939484658249551309)
                  ·
                    refine ⟨1286044477306746843581741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3429451939484658249551309 1286044477306746843581741)
                    ·
                      refine ⟨482266678990030066343153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1286044477306746843581741 482266678990030066343153)
                      ·
                        rfl

theorem cell23_939211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 5, 3, 3].length) (baseStart_939211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_939211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_939211 prefixEnd_939211 := by exact prefixLift 939211
  have htrace : WordTrace (prefixWord ++ tailWord_939211) baseStart_939211 baseEnd_939211 := by
    simpa [prefixWord, tailWord_939211, baseEnd_939211] using wordTrace_append hprefix tailTrace_939211
  have hstable : (prefixWord ++ tailWord_939211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939211).length < 2 ^ (prefixWord ++ tailWord_939211).sum := by decide
  have hdescent : baseEnd_939211 < baseStart_939211 := by decide
  rcases family_descends (prefixWord ++ tailWord_939211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939229 : List Nat := [1, 4, 3, 2, 3, 1, 1, 2, 1, 1, 4]
def baseStart_939229 : Nat := 118140960795 + 939229 * 2 ^ 59
def prefixEnd_939229 : Nat := 4983230072969 + 3 ^ 40 * 939229 * 2
def baseEnd_939229 : Nat := 482275921641810995918071

theorem tailTrace_939229 : CollatzResearch.WordTrace tailWord_939229 prefixEnd_939229 482275921641810995918071 := by
  unfold tailWord_939229
  simp only [CollatzResearch.WordTrace]
  refine ⟨34256495914341215387612741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22837663942894143591741827 34256495914341215387612741)
  ·
    refine ⟨6423092983938977885177389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34256495914341215387612741 6423092983938977885177389)
    ·
      refine ⟨2408659868977116706941521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6423092983938977885177389 2408659868977116706941521)
      ·
        refine ⟨1806494901732837530206141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2408659868977116706941521 1806494901732837530206141)
        ·
          refine ⟨677435588149814073827303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1806494901732837530206141 677435588149814073827303)
          ·
            refine ⟨1016153382224721110740955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 677435588149814073827303 1016153382224721110740955)
            ·
              refine ⟨1524230073337081666111433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1016153382224721110740955 1524230073337081666111433)
              ·
                refine ⟨1143172555002811249583575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1524230073337081666111433 1143172555002811249583575)
                ·
                  refine ⟨1714758832504216874375363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1143172555002811249583575 1714758832504216874375363)
                  ·
                    refine ⟨2572138248756325311563045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1714758832504216874375363 2572138248756325311563045)
                    ·
                      refine ⟨482275921641810995918071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2572138248756325311563045 482275921641810995918071)
                      ·
                        rfl

theorem cell23_939229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 1, 2, 1, 1, 4].length) (baseStart_939229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_939229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_939229 prefixEnd_939229 := by exact prefixLift 939229
  have htrace : WordTrace (prefixWord ++ tailWord_939229) baseStart_939229 baseEnd_939229 := by
    simpa [prefixWord, tailWord_939229, baseEnd_939229] using wordTrace_append hprefix tailTrace_939229
  have hstable : (prefixWord ++ tailWord_939229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939229).length < 2 ^ (prefixWord ++ tailWord_939229).sum := by decide
  have hdescent : baseEnd_939229 < baseStart_939229 := by decide
  rcases family_descends (prefixWord ++ tailWord_939229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939245 : List Nat := [1, 5, 1, 2, 2, 2, 1, 2, 1, 3, 3]
def baseStart_939245 : Nat := 118140960795 + 939245 * 2 ^ 59
def prefixEnd_939245 : Nat := 4983230072969 + 3 ^ 40 * 939245 * 2
def baseEnd_939245 : Nat := 482284137332282933317997

theorem tailTrace_939245 : CollatzResearch.WordTrace tailWord_939245 prefixEnd_939245 482284137332282933317997 := by
  unfold tailWord_939245
  simp only [CollatzResearch.WordTrace]
  refine ⟨34257079482283250120195189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22838052988188833413463459 34257079482283250120195189)
  ·
    refine ⟨3211601201464054698768299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34257079482283250120195189 3211601201464054698768299)
    ·
      refine ⟨4817401802196082048152449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3211601201464054698768299 4817401802196082048152449)
      ·
        refine ⟨3613051351647061536114337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4817401802196082048152449 3613051351647061536114337)
        ·
          refine ⟨2709788513735296152085753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3613051351647061536114337 2709788513735296152085753)
          ·
            refine ⟨2032341385301472114064315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2709788513735296152085753 2032341385301472114064315)
            ·
              refine ⟨3048512077952208171096473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2032341385301472114064315 3048512077952208171096473)
              ·
                refine ⟨2286384058464156128322355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3048512077952208171096473 2286384058464156128322355)
                ·
                  refine ⟨3429576087696234192483533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2286384058464156128322355 3429576087696234192483533)
                  ·
                    refine ⟨1286091032886087822181325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3429576087696234192483533 1286091032886087822181325)
                    ·
                      refine ⟨482284137332282933317997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1286091032886087822181325 482284137332282933317997)
                      ·
                        rfl

theorem cell23_939245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 2, 1, 3, 3].length) (baseStart_939245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_939245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_939245 prefixEnd_939245 := by exact prefixLift 939245
  have htrace : WordTrace (prefixWord ++ tailWord_939245) baseStart_939245 baseEnd_939245 := by
    simpa [prefixWord, tailWord_939245, baseEnd_939245] using wordTrace_append hprefix tailTrace_939245
  have hstable : (prefixWord ++ tailWord_939245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939245).length < 2 ^ (prefixWord ++ tailWord_939245).sum := by decide
  have hdescent : baseEnd_939245 < baseStart_939245 := by decide
  rcases family_descends (prefixWord ++ tailWord_939245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939252 : List Nat := [2, 6, 1, 2, 2, 10]
def baseStart_939252 : Nat := 118140960795 + 939252 * 2 ^ 59
def prefixEnd_939252 : Nat := 4983230072969 + 3 ^ 40 * 939252 * 2
def baseEnd_939252 : Nat := 1984723175707260929755

theorem tailTrace_939252 : CollatzResearch.WordTrace tailWord_939252 prefixEnd_939252 1984723175707260929755 := by
  unfold tailWord_939252
  simp only [CollatzResearch.WordTrace]
  refine ⟨17128667396628945157850005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22838223195505260210466673 17128667396628945157850005)
  ·
    refine ⟨802906284216981804274219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 17128667396628945157850005 802906284216981804274219)
    ·
      refine ⟨1204359426325472706411329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 802906284216981804274219 1204359426325472706411329)
      ·
        refine ⟨903269569744104529808497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1204359426325472706411329 903269569744104529808497)
        ·
          refine ⟨677452177308078397356373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 903269569744104529808497 677452177308078397356373)
          ·
            refine ⟨1984723175707260929755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 677452177308078397356373 1984723175707260929755)
            ·
              rfl

theorem cell23_939252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 10].length) (baseStart_939252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_939252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_939252 prefixEnd_939252 := by exact prefixLift 939252
  have htrace : WordTrace (prefixWord ++ tailWord_939252) baseStart_939252 baseEnd_939252 := by
    simpa [prefixWord, tailWord_939252, baseEnd_939252] using wordTrace_append hprefix tailTrace_939252
  have hstable : (prefixWord ++ tailWord_939252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939252).length < 2 ^ (prefixWord ++ tailWord_939252).sum := by decide
  have hdescent : baseEnd_939252 < baseStart_939252 := by decide
  rcases family_descends (prefixWord ++ tailWord_939252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939262 : List Nat := [4, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3]
def baseStart_939262 : Nat := 118140960795 + 939262 * 2 ^ 59
def prefixEnd_939262 : Nat := 4983230072969 + 3 ^ 40 * 939262 * 2
def baseEnd_939262 : Nat := 482292866503409366805419

theorem tailTrace_939262 : CollatzResearch.WordTrace tailWord_939262 prefixEnd_939262 482292866503409366805419 := by
  unfold tailWord_939262
  simp only [CollatzResearch.WordTrace]
  refine ⟨4282212440402707752945505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22838466348814441349042693 4282212440402707752945505)
  ·
    refine ⟨3211659330302030814709129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4282212440402707752945505 3211659330302030814709129)
    ·
      refine ⟨2408744497726523111031847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3211659330302030814709129 2408744497726523111031847)
      ·
        refine ⟨3613116746589784666547771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2408744497726523111031847 3613116746589784666547771)
        ·
          refine ⟨5419675119884676999821657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3613116746589784666547771 5419675119884676999821657)
          ·
            refine ⟨4064756339913507749866243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5419675119884676999821657 4064756339913507749866243)
            ·
              refine ⟨6097134509870261624799365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4064756339913507749866243 6097134509870261624799365)
              ·
                refine ⟨1143212720600674054649881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6097134509870261624799365 1143212720600674054649881)
                ·
                  refine ⟨857409540450505540987411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1143212720600674054649881 857409540450505540987411)
                  ·
                    refine ⟨1286114310675758311481117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 857409540450505540987411 1286114310675758311481117)
                    ·
                      refine ⟨482292866503409366805419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1286114310675758311481117 482292866503409366805419)
                      ·
                        rfl

theorem cell23_939262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3].length) (baseStart_939262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_939262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_939262 prefixEnd_939262 := by exact prefixLift 939262
  have htrace : WordTrace (prefixWord ++ tailWord_939262) baseStart_939262 baseEnd_939262 := by
    simpa [prefixWord, tailWord_939262, baseEnd_939262] using wordTrace_append hprefix tailTrace_939262
  have hstable : (prefixWord ++ tailWord_939262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939262).length < 2 ^ (prefixWord ++ tailWord_939262).sum := by decide
  have hdescent : baseEnd_939262 < baseStart_939262 := by decide
  rcases family_descends (prefixWord ++ tailWord_939262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939268 : List Nat := [2, 3, 2, 2, 2, 1, 1, 1, 2, 3, 4]
def baseStart_939268 : Nat := 118140960795 + 939268 * 2 ^ 59
def prefixEnd_939268 : Nat := 4983230072969 + 3 ^ 40 * 939268 * 2
def baseEnd_939268 : Nat := 482295947387336343330391

theorem tailTrace_939268 : CollatzResearch.WordTrace tailWord_939268 prefixEnd_939268 482295947387336343330391 := by
  unfold tailWord_939268
  simp only [CollatzResearch.WordTrace]
  refine ⟨17128959180599962524141229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22838612240799950032188305 17128959180599962524141229)
  ·
    refine ⟨6423359692724985946552961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17128959180599962524141229 6423359692724985946552961)
    ·
      refine ⟨4817519769543739459914721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6423359692724985946552961 4817519769543739459914721)
      ·
        refine ⟨3613139827157804594936041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4817519769543739459914721 3613139827157804594936041)
        ·
          refine ⟨2709854870368353446202031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3613139827157804594936041 2709854870368353446202031)
          ·
            refine ⟨4064782305552530169303047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2709854870368353446202031 4064782305552530169303047)
            ·
              refine ⟨6097173458328795253954571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4064782305552530169303047 6097173458328795253954571)
              ·
                refine ⟨9145760187493192880931857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6097173458328795253954571 9145760187493192880931857)
                ·
                  refine ⟨6859320140619894660698893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9145760187493192880931857 6859320140619894660698893)
                  ·
                    refine ⟨2572245052732460497762085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6859320140619894660698893 2572245052732460497762085)
                    ·
                      refine ⟨482295947387336343330391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2572245052732460497762085 482295947387336343330391)
                      ·
                        rfl

theorem cell23_939268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_939268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_939268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_939268 prefixEnd_939268 := by exact prefixLift 939268
  have htrace : WordTrace (prefixWord ++ tailWord_939268) baseStart_939268 baseEnd_939268 := by
    simpa [prefixWord, tailWord_939268, baseEnd_939268] using wordTrace_append hprefix tailTrace_939268
  have hstable : (prefixWord ++ tailWord_939268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939268).length < 2 ^ (prefixWord ++ tailWord_939268).sum := by decide
  have hdescent : baseEnd_939268 < baseStart_939268 := by decide
  rcases family_descends (prefixWord ++ tailWord_939268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939278 : List Nat := [4, 1, 1, 2, 1, 4, 1, 1, 2, 6]
def baseStart_939278 : Nat := 118140960795 + 939278 * 2 ^ 59
def prefixEnd_939278 : Nat := 4983230072969 + 3 ^ 40 * 939278 * 2
def baseEnd_939278 : Nat := 160767027397960434735115

theorem tailTrace_939278 : CollatzResearch.WordTrace tailWord_939278 prefixEnd_939278 160767027397960434735115 := by
  unfold tailWord_939278
  simp only [CollatzResearch.WordTrace]
  refine ⟨4282285386395462094518311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22838855394109131170764325 4282285386395462094518311)
  ·
    refine ⟨6423428079593193141777467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4282285386395462094518311 6423428079593193141777467)
    ·
      refine ⟨9635142119389789712666201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6423428079593193141777467 9635142119389789712666201)
      ·
        refine ⟨7226356589542342284499651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9635142119389789712666201 7226356589542342284499651)
        ·
          refine ⟨10839534884313513426749477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7226356589542342284499651 10839534884313513426749477)
          ·
            refine ⟨2032412790808783767515527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10839534884313513426749477 2032412790808783767515527)
            ·
              refine ⟨3048619186213175651273291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2032412790808783767515527 3048619186213175651273291)
              ·
                refine ⟨4572928779319763476909937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3048619186213175651273291 4572928779319763476909937)
                ·
                  refine ⟨3429696584489822607682453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4572928779319763476909937 3429696584489822607682453)
                  ·
                    refine ⟨160767027397960434735115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3429696584489822607682453 160767027397960434735115)
                    ·
                      rfl

theorem cell23_939278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 1, 2, 6].length) (baseStart_939278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_939278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_939278 prefixEnd_939278 := by exact prefixLift 939278
  have htrace : WordTrace (prefixWord ++ tailWord_939278) baseStart_939278 baseEnd_939278 := by
    simpa [prefixWord, tailWord_939278, baseEnd_939278] using wordTrace_append hprefix tailTrace_939278
  have hstable : (prefixWord ++ tailWord_939278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939278).length < 2 ^ (prefixWord ++ tailWord_939278).sum := by decide
  have hdescent : baseEnd_939278 < baseStart_939278 := by decide
  rcases family_descends (prefixWord ++ tailWord_939278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939285 : List Nat := [1, 3, 2, 1, 2, 1, 1, 2, 6, 2, 2]
def baseStart_939285 : Nat := 118140960795 + 939285 * 2 ^ 59
def prefixEnd_939285 : Nat := 4983230072969 + 3 ^ 40 * 939285 * 2
def baseEnd_939285 : Nat := 482304676558462776817813

theorem tailTrace_939285 : CollatzResearch.WordTrace tailWord_939285 prefixEnd_939285 482304676558462776817813 := by
  unfold tailWord_939285
  simp only [CollatzResearch.WordTrace]
  refine ⟨34258538402138336951651309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22839025601425557967767539 34258538402138336951651309)
  ·
    refine ⟨12846951900801876356869241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34258538402138336951651309 12846951900801876356869241)
    ·
      refine ⟨9635213925601407267651931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12846951900801876356869241 9635213925601407267651931)
      ·
        refine ⟨14452820888402110901477897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9635213925601407267651931 14452820888402110901477897)
        ·
          refine ⟨10839615666301583176108423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14452820888402110901477897 10839615666301583176108423)
          ·
            refine ⟨16259423499452374764162635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10839615666301583176108423 16259423499452374764162635)
            ·
              refine ⟨24389135249178562146243953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16259423499452374764162635 24389135249178562146243953)
              ·
                refine ⟨18291851436883921609682965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24389135249178562146243953 18291851436883921609682965)
                ·
                  refine ⟨857430536103933825453889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 18291851436883921609682965 857430536103933825453889)
                  ·
                    refine ⟨643072902077950369090417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 857430536103933825453889 643072902077950369090417)
                    ·
                      refine ⟨482304676558462776817813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 643072902077950369090417 482304676558462776817813)
                      ·
                        rfl

theorem cell23_939285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 6, 2, 2].length) (baseStart_939285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_939285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_939285 prefixEnd_939285 := by exact prefixLift 939285
  have htrace : WordTrace (prefixWord ++ tailWord_939285) baseStart_939285 baseEnd_939285 := by
    simpa [prefixWord, tailWord_939285, baseEnd_939285] using wordTrace_append hprefix tailTrace_939285
  have hstable : (prefixWord ++ tailWord_939285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939285).length < 2 ^ (prefixWord ++ tailWord_939285).sum := by decide
  have hdescent : baseEnd_939285 < baseStart_939285 := by decide
  rcases family_descends (prefixWord ++ tailWord_939285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939306 : List Nat := [3, 1, 4, 2, 1, 3, 2, 1, 1, 3, 2]
def baseStart_939306 : Nat := 118140960795 + 939306 * 2 ^ 59
def prefixEnd_939306 : Nat := 4983230072969 + 3 ^ 40 * 939306 * 2
def baseEnd_939306 : Nat := 482315459652207194655217

theorem tailTrace_939306 : CollatzResearch.WordTrace tailWord_939306 prefixEnd_939306 482315459652207194655217 := by
  unfold tailWord_939306
  simp only [CollatzResearch.WordTrace]
  refine ⟨8564826083765564384541443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22839536223374838358777181 8564826083765564384541443)
  ·
    refine ⟨12847239125648346576812165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8564826083765564384541443 12847239125648346576812165)
    ·
      refine ⟨2408857336059064983152281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12847239125648346576812165 2408857336059064983152281)
      ·
        refine ⟨1806643002044298737364211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2408857336059064983152281 1806643002044298737364211)
        ·
          refine ⟨2709964503066448106046317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1806643002044298737364211 2709964503066448106046317)
          ·
            refine ⟨1016236688649918039767369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2709964503066448106046317 1016236688649918039767369)
            ·
              refine ⟨762177516487438529825527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1016236688649918039767369 762177516487438529825527)
              ·
                refine ⟨1143266274731157794738291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 762177516487438529825527 1143266274731157794738291)
                ·
                  refine ⟨1714899412096736692107437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1143266274731157794738291 1714899412096736692107437)
                  ·
                    refine ⟨643087279536276259540289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1714899412096736692107437 643087279536276259540289)
                    ·
                      refine ⟨482315459652207194655217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 643087279536276259540289 482315459652207194655217)
                      ·
                        rfl

theorem cell23_939306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 2, 1, 1, 3, 2].length) (baseStart_939306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_939306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_939306 prefixEnd_939306 := by exact prefixLift 939306
  have htrace : WordTrace (prefixWord ++ tailWord_939306) baseStart_939306 baseEnd_939306 := by
    simpa [prefixWord, tailWord_939306, baseEnd_939306] using wordTrace_append hprefix tailTrace_939306
  have hstable : (prefixWord ++ tailWord_939306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939306).length < 2 ^ (prefixWord ++ tailWord_939306).sum := by decide
  have hdescent : baseEnd_939306 < baseStart_939306 := by decide
  rcases family_descends (prefixWord ++ tailWord_939306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939331 : List Nat := [1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 7]
def baseStart_939331 : Nat := 118140960795 + 939331 * 2 ^ 59
def prefixEnd_939331 : Nat := 4983230072969 + 3 ^ 40 * 939331 * 2
def baseEnd_939331 : Nat := 482328296668569596842601

theorem tailTrace_939331 : CollatzResearch.WordTrace tailWord_939331 prefixEnd_939331 482328296668569596842601 := by
  unfold tailWord_939331
  simp only [CollatzResearch.WordTrace]
  refine ⟨34260216159971686807825847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22840144106647791205217231 34260216159971686807825847)
  ·
    refine ⟨51390324239957530211738771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34260216159971686807825847 51390324239957530211738771)
    ·
      refine ⟨77085486359936295317608157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51390324239957530211738771 77085486359936295317608157)
      ·
        refine ⟨28907057384976110744103059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77085486359936295317608157 28907057384976110744103059)
        ·
          refine ⟨43360586077464166116154589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28907057384976110744103059 43360586077464166116154589)
          ·
            refine ⟨16260219779049062293557971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43360586077464166116154589 16260219779049062293557971)
            ·
              refine ⟨24390329668573593440336957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16260219779049062293557971 24390329668573593440336957)
              ·
                refine ⟨9146373625715097540126359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24390329668573593440336957 9146373625715097540126359)
                ·
                  refine ⟨13719560438572646310189539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9146373625715097540126359 13719560438572646310189539)
                  ·
                    refine ⟨20579340657858969465284309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13719560438572646310189539 20579340657858969465284309)
                    ·
                      refine ⟨482328296668569596842601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 20579340657858969465284309 482328296668569596842601)
                      ·
                        rfl

theorem cell23_939331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 7].length) (baseStart_939331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_939331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_939331 prefixEnd_939331 := by exact prefixLift 939331
  have htrace : WordTrace (prefixWord ++ tailWord_939331) baseStart_939331 baseEnd_939331 := by
    simpa [prefixWord, tailWord_939331, baseEnd_939331] using wordTrace_append hprefix tailTrace_939331
  have hstable : (prefixWord ++ tailWord_939331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939331).length < 2 ^ (prefixWord ++ tailWord_939331).sum := by decide
  have hdescent : baseEnd_939331 < baseStart_939331 := by decide
  rcases family_descends (prefixWord ++ tailWord_939331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939385 : List Nat := [1, 2, 1, 3, 2, 1, 5, 1, 3, 4]
def baseStart_939385 : Nat := 118140960795 + 939385 * 2 ^ 59
def prefixEnd_939385 : Nat := 4983230072969 + 3 ^ 40 * 939385 * 2
def baseEnd_939385 : Nat := 160785341541304128522451

theorem tailTrace_939385 : CollatzResearch.WordTrace tailWord_939385 prefixEnd_939385 160785341541304128522451 := by
  unfold tailWord_939385
  simp only [CollatzResearch.WordTrace]
  refine ⟨34262185701776054030291609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22841457134517369353527739 34262185701776054030291609)
  ·
    refine ⟨25696639276332040522718707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34262185701776054030291609 25696639276332040522718707)
    ·
      refine ⟨38544958914498060784078061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25696639276332040522718707 38544958914498060784078061)
      ·
        refine ⟨14454359592936772794029273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38544958914498060784078061 14454359592936772794029273)
        ·
          refine ⟨10840769694702579595521955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14454359592936772794029273 10840769694702579595521955)
          ·
            refine ⟨16261154542053869393282933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10840769694702579595521955 16261154542053869393282933)
            ·
              refine ⟨1524483238317550255620275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16261154542053869393282933 1524483238317550255620275)
              ·
                refine ⟨2286724857476325383430413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1524483238317550255620275 2286724857476325383430413)
                ·
                  refine ⟨857521821553622018786405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2286724857476325383430413 857521821553622018786405)
                  ·
                    refine ⟨160785341541304128522451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 857521821553622018786405 160785341541304128522451)
                    ·
                      rfl

theorem cell23_939385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 5, 1, 3, 4].length) (baseStart_939385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_939385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_939385 prefixEnd_939385 := by exact prefixLift 939385
  have htrace : WordTrace (prefixWord ++ tailWord_939385) baseStart_939385 baseEnd_939385 := by
    simpa [prefixWord, tailWord_939385, baseEnd_939385] using wordTrace_append hprefix tailTrace_939385
  have hstable : (prefixWord ++ tailWord_939385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939385).length < 2 ^ (prefixWord ++ tailWord_939385).sum := by decide
  have hdescent : baseEnd_939385 < baseStart_939385 := by decide
  rcases family_descends (prefixWord ++ tailWord_939385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939412 : List Nat := [2, 4, 2, 1, 2, 1, 1, 3, 2, 2, 3]
def baseStart_939412 : Nat := 118140960795 + 939412 * 2 ^ 59
def prefixEnd_939412 : Nat := 4983230072969 + 3 ^ 40 * 939412 * 2
def baseEnd_939412 : Nat := 482369888601583779929729

theorem tailTrace_939412 : CollatzResearch.WordTrace tailWord_939412 prefixEnd_939412 482369888601583779929729 := by
  unfold tailWord_939412
  simp only [CollatzResearch.WordTrace]
  refine ⟨17131585236339118820762245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22842113648452158427682993 17131585236339118820762245)
  ·
    refine ⟨3212172231813584778892921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17131585236339118820762245 3212172231813584778892921)
    ·
      refine ⟨2409129173860188584169691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3212172231813584778892921 2409129173860188584169691)
      ·
        refine ⟨3613693760790282876254537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2409129173860188584169691 3613693760790282876254537)
        ·
          refine ⟨2710270320592712157190903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3613693760790282876254537 2710270320592712157190903)
          ·
            refine ⟨4065405480889068235786355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2710270320592712157190903 4065405480889068235786355)
            ·
              refine ⟨6098108221333602353679533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4065405480889068235786355 6098108221333602353679533)
              ·
                refine ⟨2286790583000100882629825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6098108221333602353679533 2286790583000100882629825)
                ·
                  refine ⟨1715092937250075661972369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2286790583000100882629825 1715092937250075661972369)
                  ·
                    refine ⟨1286319702937556746479277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1715092937250075661972369 1286319702937556746479277)
                    ·
                      refine ⟨482369888601583779929729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1286319702937556746479277 482369888601583779929729)
                      ·
                        rfl

theorem cell23_939412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 3, 2, 2, 3].length) (baseStart_939412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_939412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_939412 prefixEnd_939412 := by exact prefixLift 939412
  have htrace : WordTrace (prefixWord ++ tailWord_939412) baseStart_939412 baseEnd_939412 := by
    simpa [prefixWord, tailWord_939412, baseEnd_939412] using wordTrace_append hprefix tailTrace_939412
  have hstable : (prefixWord ++ tailWord_939412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939412).length < 2 ^ (prefixWord ++ tailWord_939412).sum := by decide
  have hdescent : baseEnd_939412 < baseStart_939412 := by decide
  rcases family_descends (prefixWord ++ tailWord_939412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939435 : List Nat := [1, 1, 1, 1, 2, 1, 1, 2, 8, 3, 2]
def baseStart_939435 : Nat := 118140960795 + 939435 * 2 ^ 59
def prefixEnd_939435 : Nat := 4983230072969 + 3 ^ 40 * 939435 * 2
def baseEnd_939435 : Nat := 482381698656637189942123

theorem tailTrace_939435 : CollatzResearch.WordTrace tailWord_939435 prefixEnd_939435 482381698656637189942123 := by
  unfold tailWord_939435
  simp only [CollatzResearch.WordTrace]
  refine ⟨34264009351594912569611759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22842672901063275046407839 34264009351594912569611759)
  ·
    refine ⟨51396014027392368854417639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34264009351594912569611759 51396014027392368854417639)
    ·
      refine ⟨77094021041088553281626459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51396014027392368854417639 77094021041088553281626459)
      ·
        refine ⟨115641031561632829922439689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77094021041088553281626459 115641031561632829922439689)
        ·
          refine ⟨86730773671224622441829767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115641031561632829922439689 86730773671224622441829767)
          ·
            refine ⟨130096160506836933662744651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86730773671224622441829767 130096160506836933662744651)
            ·
              refine ⟨195144240760255400494116977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130096160506836933662744651 195144240760255400494116977)
              ·
                refine ⟨146358180570191550370587733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 195144240760255400494116977 146358180570191550370587733)
                ·
                  refine ⟨1715134928556932230905325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 146358180570191550370587733 1715134928556932230905325)
                  ·
                    refine ⟨643175598208849586589497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1715134928556932230905325 643175598208849586589497)
                    ·
                      refine ⟨482381698656637189942123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 643175598208849586589497 482381698656637189942123)
                      ·
                        rfl

theorem cell23_939435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 8, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 8, 3, 2].length) (baseStart_939435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_939435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_939435 prefixEnd_939435 := by exact prefixLift 939435
  have htrace : WordTrace (prefixWord ++ tailWord_939435) baseStart_939435 baseEnd_939435 := by
    simpa [prefixWord, tailWord_939435, baseEnd_939435] using wordTrace_append hprefix tailTrace_939435
  have hstable : (prefixWord ++ tailWord_939435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939435).length < 2 ^ (prefixWord ++ tailWord_939435).sum := by decide
  have hdescent : baseEnd_939435 < baseStart_939435 := by decide
  rcases family_descends (prefixWord ++ tailWord_939435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939445 : List Nat := [1, 3, 3, 2, 2, 1, 1, 2, 3, 5]
def baseStart_939445 : Nat := 118140960795 + 939445 * 2 ^ 59
def prefixEnd_939445 : Nat := 4983230072969 + 3 ^ 40 * 939445 * 2
def baseEnd_939445 : Nat := 160795611154394050272359

theorem tailTrace_939445 : CollatzResearch.WordTrace tailWord_939445 prefixEnd_939445 160795611154394050272359 := by
  unfold tailWord_939445
  simp only [CollatzResearch.WordTrace]
  refine ⟨34264374081558684277475789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22842916054372456184983859 34264374081558684277475789)
  ·
    refine ⟨12849140280584506604053421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34264374081558684277475789 12849140280584506604053421)
    ·
      refine ⟨4818427605219189976520033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12849140280584506604053421 4818427605219189976520033)
      ·
        refine ⟨3613820703914392482390025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4818427605219189976520033 3613820703914392482390025)
        ·
          refine ⟨2710365527935794361792519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3613820703914392482390025 2710365527935794361792519)
          ·
            refine ⟨4065548291903691542688779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2710365527935794361792519 4065548291903691542688779)
            ·
              refine ⟨6098322437855537314033169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4065548291903691542688779 6098322437855537314033169)
              ·
                refine ⟨4573741828391652985524877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6098322437855537314033169 4573741828391652985524877)
                ·
                  refine ⟨1715153185646869869571829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4573741828391652985524877 1715153185646869869571829)
                  ·
                    refine ⟨160795611154394050272359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1715153185646869869571829 160795611154394050272359)
                    ·
                      rfl

theorem cell23_939445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 2, 3, 5].length) (baseStart_939445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_939445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_939445 prefixEnd_939445 := by exact prefixLift 939445
  have htrace : WordTrace (prefixWord ++ tailWord_939445) baseStart_939445 baseEnd_939445 := by
    simpa [prefixWord, tailWord_939445, baseEnd_939445] using wordTrace_append hprefix tailTrace_939445
  have hstable : (prefixWord ++ tailWord_939445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939445).length < 2 ^ (prefixWord ++ tailWord_939445).sum := by decide
  have hdescent : baseEnd_939445 < baseStart_939445 := by decide
  rcases family_descends (prefixWord ++ tailWord_939445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939465 : List Nat := [1, 2, 1, 1, 2, 1, 3, 6, 1, 1, 4]
def baseStart_939465 : Nat := 118140960795 + 939465 * 2 ^ 59
def prefixEnd_939465 : Nat := 4983230072969 + 3 ^ 40 * 939465 * 2
def baseEnd_939465 : Nat := 482397103076272072566985

theorem tailTrace_939465 : CollatzResearch.WordTrace tailWord_939465 prefixEnd_939465 482397103076272072566985 := by
  unfold tailWord_939465
  simp only [CollatzResearch.WordTrace]
  refine ⟨34265103541486227693203849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22843402360990818462135899 34265103541486227693203849)
  ·
    refine ⟨25698827656114670769902887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34265103541486227693203849 25698827656114670769902887)
    ·
      refine ⟨38548241484172006154854331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25698827656114670769902887 38548241484172006154854331)
      ·
        refine ⟨57822362226258009232281497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38548241484172006154854331 57822362226258009232281497)
        ·
          refine ⟨43366771669693506924211123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57822362226258009232281497 43366771669693506924211123)
          ·
            refine ⟨65050157504540260386316685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43366771669693506924211123 65050157504540260386316685)
            ·
              refine ⟨24393809064202597644868757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65050157504540260386316685 24393809064202597644868757)
              ·
                refine ⟨1143459799884496764603223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 24393809064202597644868757 1143459799884496764603223)
                ·
                  refine ⟨1715189699826745146904835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1143459799884496764603223 1715189699826745146904835)
                  ·
                    refine ⟨2572784549740117720357253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1715189699826745146904835 2572784549740117720357253)
                    ·
                      refine ⟨482397103076272072566985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2572784549740117720357253 482397103076272072566985)
                      ·
                        rfl

theorem cell23_939465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 6, 1, 1, 4].length) (baseStart_939465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_939465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_939465 prefixEnd_939465 := by exact prefixLift 939465
  have htrace : WordTrace (prefixWord ++ tailWord_939465) baseStart_939465 baseEnd_939465 := by
    simpa [prefixWord, tailWord_939465, baseEnd_939465] using wordTrace_append hprefix tailTrace_939465
  have hstable : (prefixWord ++ tailWord_939465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939465).length < 2 ^ (prefixWord ++ tailWord_939465).sum := by decide
  have hdescent : baseEnd_939465 < baseStart_939465 := by decide
  rcases family_descends (prefixWord ++ tailWord_939465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939482 : List Nat := [3, 1, 1, 2, 3, 3, 1, 3, 1, 1, 4]
def baseStart_939482 : Nat := 118140960795 + 939482 * 2 ^ 59
def prefixEnd_939482 : Nat := 4983230072969 + 3 ^ 40 * 939482 * 2
def baseEnd_939482 : Nat := 482405832247398506054407

theorem tailTrace_939482 : CollatzResearch.WordTrace tailWord_939482 prefixEnd_939482 482405832247398506054407 := by
  unfold tailWord_939482
  simp only [CollatzResearch.WordTrace]
  refine ⟨8566430895606159899143175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22843815721616426397715133 8566430895606159899143175)
  ·
    refine ⟨12849646343409239848714763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8566430895606159899143175 12849646343409239848714763)
    ·
      refine ⟨19274469515113859773072145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12849646343409239848714763 19274469515113859773072145)
      ·
        refine ⟨14455852136335394829804109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19274469515113859773072145 14455852136335394829804109)
        ·
          refine ⟨5420944551125773061176541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14455852136335394829804109 5420944551125773061176541)
          ·
            refine ⟨2032854206672164897941203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5420944551125773061176541 2032854206672164897941203)
            ·
              refine ⟨3049281310008247346911805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2032854206672164897941203 3049281310008247346911805)
              ·
                refine ⟨1143480491253092755091927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3049281310008247346911805 1143480491253092755091927)
                ·
                  refine ⟨1715220736879639132637891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1143480491253092755091927 1715220736879639132637891)
                  ·
                    refine ⟨2572831105319458698956837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1715220736879639132637891 2572831105319458698956837)
                    ·
                      refine ⟨482405832247398506054407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2572831105319458698956837 482405832247398506054407)
                      ·
                        rfl

theorem cell23_939482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 3, 1, 1, 4].length) (baseStart_939482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_939482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_939482 prefixEnd_939482 := by exact prefixLift 939482
  have htrace : WordTrace (prefixWord ++ tailWord_939482) baseStart_939482 baseEnd_939482 := by
    simpa [prefixWord, tailWord_939482, baseEnd_939482] using wordTrace_append hprefix tailTrace_939482
  have hstable : (prefixWord ++ tailWord_939482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939482).length < 2 ^ (prefixWord ++ tailWord_939482).sum := by decide
  have hdescent : baseEnd_939482 < baseStart_939482 := by decide
  rcases family_descends (prefixWord ++ tailWord_939482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939509 : List Nat := [1, 3, 5, 1, 1, 3, 1, 1, 1, 6]
def baseStart_939509 : Nat := 118140960795 + 939509 * 2 ^ 59
def prefixEnd_939509 : Nat := 4983230072969 + 3 ^ 40 * 939509 * 2
def baseEnd_939509 : Nat := 160806565408356633472261

theorem tailTrace_939509 : CollatzResearch.WordTrace tailWord_939509 prefixEnd_939509 160806565408356633472261 := by
  unfold tailWord_939509
  simp only [CollatzResearch.WordTrace]
  refine ⟨34266708353326823207805581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22844472235551215471870387 34266708353326823207805581)
  ·
    refine ⟨12850015632497558702927093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34266708353326823207805581 12850015632497558702927093)
    ·
      refine ⟨1204688965546646128399415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12850015632497558702927093 1204688965546646128399415)
      ·
        refine ⟨1807033448319969192599123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1204688965546646128399415 1807033448319969192599123)
        ·
          refine ⟨2710550172479953788898685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1807033448319969192599123 2710550172479953788898685)
          ·
            refine ⟨1016456314679982670837007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2710550172479953788898685 1016456314679982670837007)
            ·
              refine ⟨1524684472019974006255511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1016456314679982670837007 1524684472019974006255511)
              ·
                refine ⟨2287026708029961009383267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1524684472019974006255511 2287026708029961009383267)
                ·
                  refine ⟨3430540062044941514074901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2287026708029961009383267 3430540062044941514074901)
                  ·
                    refine ⟨160806565408356633472261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3430540062044941514074901 160806565408356633472261)
                    ·
                      rfl

theorem cell23_939509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_939509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_939509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_939509 prefixEnd_939509 := by exact prefixLift 939509
  have htrace : WordTrace (prefixWord ++ tailWord_939509) baseStart_939509 baseEnd_939509 := by
    simpa [prefixWord, tailWord_939509, baseEnd_939509] using wordTrace_append hprefix tailTrace_939509
  have hstable : (prefixWord ++ tailWord_939509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939509).length < 2 ^ (prefixWord ++ tailWord_939509).sum := by decide
  have hdescent : baseEnd_939509 < baseStart_939509 := by decide
  rcases family_descends (prefixWord ++ tailWord_939509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939512 : List Nat := [2, 1, 2, 1, 1, 7, 1, 1, 1, 2, 4]
def baseStart_939512 : Nat := 118140960795 + 939512 * 2 ^ 59
def prefixEnd_939512 : Nat := 4983230072969 + 3 ^ 40 * 939512 * 2
def baseEnd_939512 : Nat := 482421236667033388679269

theorem tailTrace_939512 : CollatzResearch.WordTrace tailWord_939512 prefixEnd_939512 482421236667033388679269 := by
  unfold tailWord_939512
  simp only [CollatzResearch.WordTrace]
  refine ⟨17133408886157977360082395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22844545181543969813443193 17133408886157977360082395)
  ·
    refine ⟨25700113329236966040123593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17133408886157977360082395 25700113329236966040123593)
    ·
      refine ⟨19275084996927724530092695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25700113329236966040123593 19275084996927724530092695)
      ·
        refine ⟨28912627495391586795139043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19275084996927724530092695 28912627495391586795139043)
        ·
          refine ⟨43368941243087380192708565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28912627495391586795139043 43368941243087380192708565)
          ·
            refine ⟨1016459560384860473266607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 43368941243087380192708565 1016459560384860473266607)
            ·
              refine ⟨1524689340577290709899911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1016459560384860473266607 1524689340577290709899911)
              ·
                refine ⟨2287034010865936064849867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1524689340577290709899911 2287034010865936064849867)
                ·
                  refine ⟨3430551016298904097274801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2287034010865936064849867 3430551016298904097274801)
                  ·
                    refine ⟨2572913262224178072956101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3430551016298904097274801 2572913262224178072956101)
                    ·
                      refine ⟨482421236667033388679269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2572913262224178072956101 482421236667033388679269)
                      ·
                        rfl

theorem cell23_939512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 1, 1, 1, 2, 4].length) (baseStart_939512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_939512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_939512 prefixEnd_939512 := by exact prefixLift 939512
  have htrace : WordTrace (prefixWord ++ tailWord_939512) baseStart_939512 baseEnd_939512 := by
    simpa [prefixWord, tailWord_939512, baseEnd_939512] using wordTrace_append hprefix tailTrace_939512
  have hstable : (prefixWord ++ tailWord_939512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939512).length < 2 ^ (prefixWord ++ tailWord_939512).sum := by decide
  have hdescent : baseEnd_939512 < baseStart_939512 := by decide
  rcases family_descends (prefixWord ++ tailWord_939512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939522 : List Nat := [3, 4, 1, 2, 1, 2, 1, 9]
def baseStart_939522 : Nat := 118140960795 + 939522 * 2 ^ 59
def prefixEnd_939522 : Nat := 4983230072969 + 3 ^ 40 * 939522 * 2
def baseEnd_939522 : Nat := 17867643387910309242749

theorem tailTrace_939522 : CollatzResearch.WordTrace tailWord_939522 prefixEnd_939522 17867643387910309242749 := by
  unfold tailWord_939522
  simp only [CollatzResearch.WordTrace]
  refine ⟨8566795625569931607007205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22844788334853150952019213 8566795625569931607007205)
  ·
    refine ⟨1606274179794362176313851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8566795625569931607007205 1606274179794362176313851)
    ·
      refine ⟨2409411269691543264470777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1606274179794362176313851 2409411269691543264470777)
      ·
        refine ⟨1807058452268657448353083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2409411269691543264470777 1807058452268657448353083)
        ·
          refine ⟨2710587678402986172529625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1807058452268657448353083 2710587678402986172529625)
          ·
            refine ⟨2032940758802239629397219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2710587678402986172529625 2032940758802239629397219)
            ·
              refine ⟨3049411138203359444095829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2032940758802239629397219 3049411138203359444095829)
              ·
                refine ⟨17867643387910309242749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3049411138203359444095829 17867643387910309242749)
                ·
                  rfl

theorem cell23_939522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 9].length) (baseStart_939522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_939522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_939522 prefixEnd_939522 := by exact prefixLift 939522
  have htrace : WordTrace (prefixWord ++ tailWord_939522) baseStart_939522 baseEnd_939522 := by
    simpa [prefixWord, tailWord_939522, baseEnd_939522] using wordTrace_append hprefix tailTrace_939522
  have hstable : (prefixWord ++ tailWord_939522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939522).length < 2 ^ (prefixWord ++ tailWord_939522).sum := by decide
  have hdescent : baseEnd_939522 < baseStart_939522 := by decide
  rcases family_descends (prefixWord ++ tailWord_939522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939549 : List Nat := [1, 4, 2, 2, 1, 1, 2, 4, 2, 1, 3]
def baseStart_939549 : Nat := 118140960795 + 939549 * 2 ^ 59
def prefixEnd_939549 : Nat := 4983230072969 + 3 ^ 40 * 939549 * 2
def baseEnd_939549 : Nat := 482440235451249743916599

theorem tailTrace_939549 : CollatzResearch.WordTrace tailWord_939549 prefixEnd_939549 482440235451249743916599 := by
  unfold tailWord_939549
  simp only [CollatzResearch.WordTrace]
  refine ⟨34268167273181910039261701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22845444848787940026174467 34268167273181910039261701)
  ·
    refine ⟨6425281363721608132361569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34268167273181910039261701 6425281363721608132361569)
    ·
      refine ⟨4818961022791206099271177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6425281363721608132361569 4818961022791206099271177)
      ·
        refine ⟨3614220767093404574453383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4818961022791206099271177 3614220767093404574453383)
        ·
          refine ⟨5421331150640106861680075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3614220767093404574453383 5421331150640106861680075)
          ·
            refine ⟨8131996725960160292520113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5421331150640106861680075 8131996725960160292520113)
            ·
              refine ⟨6098997544470120219390085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8131996725960160292520113 6098997544470120219390085)
              ·
                refine ⟨1143562039588147541135641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6098997544470120219390085 1143562039588147541135641)
                ·
                  refine ⟨857671529691110655851731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1143562039588147541135641 857671529691110655851731)
                  ·
                    refine ⟨1286507294536665983777597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 857671529691110655851731 1286507294536665983777597)
                    ·
                      refine ⟨482440235451249743916599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1286507294536665983777597 482440235451249743916599)
                      ·
                        rfl

theorem cell23_939549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 4, 2, 1, 3].length) (baseStart_939549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_939549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_939549 prefixEnd_939549 := by exact prefixLift 939549
  have htrace : WordTrace (prefixWord ++ tailWord_939549) baseStart_939549 baseEnd_939549 := by
    simpa [prefixWord, tailWord_939549, baseEnd_939549] using wordTrace_append hprefix tailTrace_939549
  have hstable : (prefixWord ++ tailWord_939549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939549).length < 2 ^ (prefixWord ++ tailWord_939549).sum := by decide
  have hdescent : baseEnd_939549 < baseStart_939549 := by decide
  rcases family_descends (prefixWord ++ tailWord_939549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939566 : List Nat := [4, 1, 3, 1, 2, 2, 1, 3, 2, 1, 3]
def baseStart_939566 : Nat := 118140960795 + 939566 * 2 ^ 59
def prefixEnd_939566 : Nat := 4983230072969 + 3 ^ 40 * 939566 * 2
def baseEnd_939566 : Nat := 482448964622376177404021

theorem tailTrace_939566 : CollatzResearch.WordTrace tailWord_939566 prefixEnd_939566 482448964622376177404021 := by
  unfold tailWord_939566
  simp only [CollatzResearch.WordTrace]
  refine ⟨4283598414265040242828819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22845858209413547961753701 4283598414265040242828819)
  ·
    refine ⟨6425397621397560364243229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4283598414265040242828819 6425397621397560364243229)
    ·
      refine ⟨2409524108024085136591211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6425397621397560364243229 2409524108024085136591211)
      ·
        refine ⟨3614286162036127704886817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2409524108024085136591211 3614286162036127704886817)
        ·
          refine ⟨2710714621527095778665113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3614286162036127704886817 2710714621527095778665113)
          ·
            refine ⟨2033035966145321833998835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2710714621527095778665113 2033035966145321833998835)
            ·
              refine ⟨3049553949217982750998253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2033035966145321833998835 3049553949217982750998253)
              ·
                refine ⟨1143582730956743531624345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3049553949217982750998253 1143582730956743531624345)
                ·
                  refine ⟨857687048217557648718259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1143582730956743531624345 857687048217557648718259)
                  ·
                    refine ⟨1286530572326336473077389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 857687048217557648718259 1286530572326336473077389)
                    ·
                      refine ⟨482448964622376177404021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1286530572326336473077389 482448964622376177404021)
                      ·
                        rfl

theorem cell23_939566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 3, 2, 1, 3].length) (baseStart_939566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_939566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_939566 prefixEnd_939566 := by exact prefixLift 939566
  have htrace : WordTrace (prefixWord ++ tailWord_939566) baseStart_939566 baseEnd_939566 := by
    simpa [prefixWord, tailWord_939566, baseEnd_939566] using wordTrace_append hprefix tailTrace_939566
  have hstable : (prefixWord ++ tailWord_939566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939566).length < 2 ^ (prefixWord ++ tailWord_939566).sum := by decide
  have hdescent : baseEnd_939566 < baseStart_939566 := by decide
  rcases family_descends (prefixWord ++ tailWord_939566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939575 : List Nat := [1, 1, 3, 1, 2, 4, 1, 2, 2, 1, 5]
def baseStart_939575 : Nat := 118140960795 + 939575 * 2 ^ 59
def prefixEnd_939575 : Nat := 4983230072969 + 3 ^ 40 * 939575 * 2
def baseEnd_939575 : Nat := 482453585948266642191479

theorem tailTrace_939575 : CollatzResearch.WordTrace tailWord_939575 prefixEnd_939575 482453585948266642191479 := by
  unfold tailWord_939575
  simp only [CollatzResearch.WordTrace]
  refine ⟨34269115571087716479708179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22846077047391810986472119 34269115571087716479708179)
  ·
    refine ⟨51403673356631574719562269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34269115571087716479708179 51403673356631574719562269)
    ·
      refine ⟨19276377508736840519835851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51403673356631574719562269 19276377508736840519835851)
      ·
        refine ⟨28914566263105260779753777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19276377508736840519835851 28914566263105260779753777)
        ·
          refine ⟨21685924697328945584815333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28914566263105260779753777 21685924697328945584815333)
          ·
            refine ⟨4066110880749177297152875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21685924697328945584815333 4066110880749177297152875)
            ·
              refine ⟨6099166321123765945729313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4066110880749177297152875 6099166321123765945729313)
              ·
                refine ⟨4574374740842824459296985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6099166321123765945729313 4574374740842824459296985)
                ·
                  refine ⟨3430781055632118344472739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4574374740842824459296985 3430781055632118344472739)
                  ·
                    refine ⟨5146171583448177516709109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3430781055632118344472739 5146171583448177516709109)
                    ·
                      refine ⟨482453585948266642191479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5146171583448177516709109 482453585948266642191479)
                      ·
                        rfl

theorem cell23_939575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 2, 2, 1, 5].length) (baseStart_939575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_939575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_939575 prefixEnd_939575 := by exact prefixLift 939575
  have htrace : WordTrace (prefixWord ++ tailWord_939575) baseStart_939575 baseEnd_939575 := by
    simpa [prefixWord, tailWord_939575, baseEnd_939575] using wordTrace_append hprefix tailTrace_939575
  have hstable : (prefixWord ++ tailWord_939575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939575).length < 2 ^ (prefixWord ++ tailWord_939575).sum := by decide
  have hdescent : baseEnd_939575 < baseStart_939575 := by decide
  rcases family_descends (prefixWord ++ tailWord_939575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939576 : List Nat := [2, 1, 2, 1, 4, 4, 1, 2, 1, 3, 2]
def baseStart_939576 : Nat := 118140960795 + 939576 * 2 ^ 59
def prefixEnd_939576 : Nat := 4983230072969 + 3 ^ 40 * 939576 * 2
def baseEnd_939576 : Nat := 482454099428921138278975

theorem tailTrace_939576 : CollatzResearch.WordTrace tailWord_939576 prefixEnd_939576 482454099428921138278975 := by
  unfold tailWord_939576
  simp only [CollatzResearch.WordTrace]
  refine ⟨17134576022042046825247291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22846101362722729100329721 17134576022042046825247291)
  ·
    refine ⟨25701864033063070237870937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17134576022042046825247291 25701864033063070237870937)
    ·
      refine ⟨19276398024797302678403203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25701864033063070237870937 19276398024797302678403203)
      ·
        refine ⟨28914597037195954017604805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19276398024797302678403203 28914597037195954017604805)
        ·
          refine ⟨5421486944474241378300901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28914597037195954017604805 5421486944474241378300901)
          ·
            refine ⟨1016528802088920258431419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5421486944474241378300901 1016528802088920258431419)
            ·
              refine ⟨1524793203133380387647129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1016528802088920258431419 1524793203133380387647129)
              ·
                refine ⟨1143594902350035290735347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1524793203133380387647129 1143594902350035290735347)
                ·
                  refine ⟨1715392353525052936103021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1143594902350035290735347 1715392353525052936103021)
                  ·
                    refine ⟨643272132571894851038633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1715392353525052936103021 643272132571894851038633)
                    ·
                      refine ⟨482454099428921138278975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 643272132571894851038633 482454099428921138278975)
                      ·
                        rfl

theorem cell23_939576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 1, 2, 1, 3, 2].length) (baseStart_939576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_939576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_939576 prefixEnd_939576 := by exact prefixLift 939576
  have htrace : WordTrace (prefixWord ++ tailWord_939576) baseStart_939576 baseEnd_939576 := by
    simpa [prefixWord, tailWord_939576, baseEnd_939576] using wordTrace_append hprefix tailTrace_939576
  have hstable : (prefixWord ++ tailWord_939576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939576).length < 2 ^ (prefixWord ++ tailWord_939576).sum := by decide
  have hdescent : baseEnd_939576 < baseStart_939576 := by decide
  rcases family_descends (prefixWord ++ tailWord_939576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939625 : List Nat := [1, 2, 1, 1, 1, 4, 2, 2, 4, 5]
def baseStart_939625 : Nat := 118140960795 + 939625 * 2 ^ 59
def prefixEnd_939625 : Nat := 4983230072969 + 3 ^ 40 * 939625 * 2
def baseEnd_939625 : Nat := 160826419993663815522083

theorem tailTrace_939625 : CollatzResearch.WordTrace tailWord_939625 prefixEnd_939625 160826419993663815522083 := by
  unfold tailWord_939625
  simp only [CollatzResearch.WordTrace]
  refine ⟨34270939220906575019028329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22847292813937716679352219 34270939220906575019028329)
  ·
    refine ⟨25703204415679931264271247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34270939220906575019028329 25703204415679931264271247)
    ·
      refine ⟨38554806623519896896406871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25703204415679931264271247 38554806623519896896406871)
      ·
        refine ⟨57832209935279845344610307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38554806623519896896406871 57832209935279845344610307)
        ·
          refine ⟨86748314902919768016915461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57832209935279845344610307 86748314902919768016915461)
          ·
            refine ⟨16265309044297456503171649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86748314902919768016915461 16265309044297456503171649)
            ·
              refine ⟨12198981783223092377378737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16265309044297456503171649 12198981783223092377378737)
              ·
                refine ⟨9149236337417319283034053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12198981783223092377378737 9149236337417319283034053)
                ·
                  refine ⟨1715481813265747365568885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9149236337417319283034053 1715481813265747365568885)
                  ·
                    refine ⟨160826419993663815522083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1715481813265747365568885 160826419993663815522083)
                    ·
                      rfl

theorem cell23_939625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 2, 4, 5].length) (baseStart_939625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_939625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_939625 prefixEnd_939625 := by exact prefixLift 939625
  have htrace : WordTrace (prefixWord ++ tailWord_939625) baseStart_939625 baseEnd_939625 := by
    simpa [prefixWord, tailWord_939625, baseEnd_939625] using wordTrace_append hprefix tailTrace_939625
  have hstable : (prefixWord ++ tailWord_939625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939625).length < 2 ^ (prefixWord ++ tailWord_939625).sum := by decide
  have hdescent : baseEnd_939625 < baseStart_939625 := by decide
  rcases family_descends (prefixWord ++ tailWord_939625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939706 : List Nat := [3, 1, 1, 1, 2, 4, 3, 3, 1, 4]
def baseStart_939706 : Nat := 118140960795 + 939706 * 2 ^ 59
def prefixEnd_939706 : Nat := 4983230072969 + 3 ^ 40 * 939706 * 2
def baseEnd_939706 : Nat := 160840283971335209884459

theorem tailTrace_939706 : CollatzResearch.WordTrace tailWord_939706 prefixEnd_939706 160840283971335209884459 := by
  unfold tailWord_939706
  simp only [CollatzResearch.WordTrace]
  refine ⟨8568473383403281463181743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22849262355742083901817981 8568473383403281463181743)
  ·
    refine ⟨12852710075104922194772615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8568473383403281463181743 12852710075104922194772615)
    ·
      refine ⟨19279065112657383292158923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12852710075104922194772615 19279065112657383292158923)
      ·
        refine ⟨28918597668986074938238385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19279065112657383292158923 28918597668986074938238385)
        ·
          refine ⟨21688948251739556203678789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28918597668986074938238385 21688948251739556203678789)
          ·
            refine ⟨4066677797201166788189773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21688948251739556203678789 4066677797201166788189773)
            ·
              refine ⟨1525004173950437545571165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4066677797201166788189773 1525004173950437545571165)
              ·
                refine ⟨571876565231414079589187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1525004173950437545571165 571876565231414079589187)
                ·
                  refine ⟨857814847847121119383781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 571876565231414079589187 857814847847121119383781)
                  ·
                    refine ⟨160840283971335209884459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 857814847847121119383781 160840283971335209884459)
                    ·
                      rfl

theorem cell23_939706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 3, 3, 1, 4].length) (baseStart_939706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_939706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_939706 prefixEnd_939706 := by exact prefixLift 939706
  have htrace : WordTrace (prefixWord ++ tailWord_939706) baseStart_939706 baseEnd_939706 := by
    simpa [prefixWord, tailWord_939706, baseEnd_939706] using wordTrace_append hprefix tailTrace_939706
  have hstable : (prefixWord ++ tailWord_939706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939706).length < 2 ^ (prefixWord ++ tailWord_939706).sum := by decide
  have hdescent : baseEnd_939706 < baseStart_939706 := by decide
  rcases family_descends (prefixWord ++ tailWord_939706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939779 : List Nat := [1, 1, 1, 3, 2, 2, 3, 4, 2, 4]
def baseStart_939779 : Nat := 118140960795 + 939779 * 2 ^ 59
def prefixEnd_939779 : Nat := 4983230072969 + 3 ^ 40 * 939779 * 2
def baseEnd_939779 : Nat := 160852778667261281346847

theorem tailTrace_939779 : CollatzResearch.WordTrace tailWord_939779 prefixEnd_939779 160852778667261281346847 := by
  unfold tailWord_939779
  simp only [CollatzResearch.WordTrace]
  refine ⟨34276556062348659320134391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22851037374899106213422927 34276556062348659320134391)
  ·
    refine ⟨51414834093522988980201587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34276556062348659320134391 51414834093522988980201587)
    ·
      refine ⟨77122251140284483470302381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51414834093522988980201587 77122251140284483470302381)
      ·
        refine ⟨28920844177606681301363393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77122251140284483470302381 28920844177606681301363393)
        ·
          refine ⟨21690633133205010976022545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28920844177606681301363393 21690633133205010976022545)
          ·
            refine ⟨16267974849903758232016909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21690633133205010976022545 16267974849903758232016909)
            ·
              refine ⟨6100490568713909337006341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16267974849903758232016909 6100490568713909337006341)
              ·
                refine ⟨1143841981633858000688689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6100490568713909337006341 1143841981633858000688689)
                ·
                  refine ⟨857881486225393500516517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1143841981633858000688689 857881486225393500516517)
                  ·
                    refine ⟨160852778667261281346847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 857881486225393500516517 160852778667261281346847)
                    ·
                      rfl

theorem cell23_939779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 4, 2, 4].length) (baseStart_939779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_939779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_939779 prefixEnd_939779 := by exact prefixLift 939779
  have htrace : WordTrace (prefixWord ++ tailWord_939779) baseStart_939779 baseEnd_939779 := by
    simpa [prefixWord, tailWord_939779, baseEnd_939779] using wordTrace_append hprefix tailTrace_939779
  have hstable : (prefixWord ++ tailWord_939779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939779).length < 2 ^ (prefixWord ++ tailWord_939779).sum := by decide
  have hdescent : baseEnd_939779 < baseStart_939779 := by decide
  rcases family_descends (prefixWord ++ tailWord_939779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939780 : List Nat := [2, 3, 2, 2, 1, 2, 4, 2, 1, 1, 3]
def baseStart_939780 : Nat := 118140960795 + 939780 * 2 ^ 59
def prefixEnd_939780 : Nat := 4983230072969 + 3 ^ 40 * 939780 * 2
def baseEnd_939780 : Nat := 482558849482438340128037

theorem tailTrace_939780 : CollatzResearch.WordTrace tailWord_939780 prefixEnd_939780 482558849482438340128037 := by
  unfold tailWord_939780
  simp only [CollatzResearch.WordTrace]
  refine ⟨17138296267672518245460397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22851061690230024327280529 17138296267672518245460397)
  ·
    refine ⟨6426861100377194342047649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17138296267672518245460397 6426861100377194342047649)
    ·
      refine ⟨4820145825282895756535737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6426861100377194342047649 4820145825282895756535737)
      ·
        refine ⟨3615109368962171817401803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4820145825282895756535737 3615109368962171817401803)
        ·
          refine ⟨5422664053443257726102705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3615109368962171817401803 5422664053443257726102705)
          ·
            refine ⟨4066998040082443294577029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5422664053443257726102705 4066998040082443294577029)
            ·
              refine ⟨762562132515458117733193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4066998040082443294577029 762562132515458117733193)
              ·
                refine ⟨571921599386593588299895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 762562132515458117733193 571921599386593588299895)
                ·
                  refine ⟨857882399079890382449843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 571921599386593588299895 857882399079890382449843)
                  ·
                    refine ⟨1286823598619835573674765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 857882399079890382449843 1286823598619835573674765)
                    ·
                      refine ⟨482558849482438340128037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1286823598619835573674765 482558849482438340128037)
                      ·
                        rfl

theorem cell23_939780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 4, 2, 1, 1, 3].length) (baseStart_939780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_939780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_939780 prefixEnd_939780 := by exact prefixLift 939780
  have htrace : WordTrace (prefixWord ++ tailWord_939780) baseStart_939780 baseEnd_939780 := by
    simpa [prefixWord, tailWord_939780, baseEnd_939780] using wordTrace_append hprefix tailTrace_939780
  have hstable : (prefixWord ++ tailWord_939780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939780).length < 2 ^ (prefixWord ++ tailWord_939780).sum := by decide
  have hdescent : baseEnd_939780 < baseStart_939780 := by decide
  rcases family_descends (prefixWord ++ tailWord_939780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939799 : List Nat := [1, 1, 3, 4, 2, 1, 1, 3, 1, 2, 4]
def baseStart_939799 : Nat := 118140960795 + 939799 * 2 ^ 59
def prefixEnd_939799 : Nat := 4983230072969 + 3 ^ 40 * 939799 * 2
def baseEnd_939799 : Nat := 482568605614873765790449

theorem tailTrace_939799 : CollatzResearch.WordTrace tailWord_939799 prefixEnd_939799 482568605614873765790449 := by
  unfold tailWord_939799
  simp only [CollatzResearch.WordTrace]
  refine ⟨34277285522276202735862451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22851523681517468490574967 34277285522276202735862451)
  ·
    refine ⟨51415928283414304103793677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34277285522276202735862451 51415928283414304103793677)
    ·
      refine ⟨19280973106280364038922629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51415928283414304103793677 19280973106280364038922629)
      ·
        refine ⟨3615182457427568257297993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19280973106280364038922629 3615182457427568257297993)
        ·
          refine ⟨2711386843070676192973495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3615182457427568257297993 2711386843070676192973495)
          ·
            refine ⟨4067080264606014289460243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2711386843070676192973495 4067080264606014289460243)
            ·
              refine ⟨6100620396909021434190365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4067080264606014289460243 6100620396909021434190365)
              ·
                refine ⟨2287732648840883037821387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6100620396909021434190365 2287732648840883037821387)
                ·
                  refine ⟨3431598973261324556732081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2287732648840883037821387 3431598973261324556732081)
                  ·
                    refine ⟨2573699229945993417549061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3431598973261324556732081 2573699229945993417549061)
                    ·
                      refine ⟨482568605614873765790449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2573699229945993417549061 482568605614873765790449)
                      ·
                        rfl

theorem cell23_939799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_939799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_939799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_939799 prefixEnd_939799 := by exact prefixLift 939799
  have htrace : WordTrace (prefixWord ++ tailWord_939799) baseStart_939799 baseEnd_939799 := by
    simpa [prefixWord, tailWord_939799, baseEnd_939799] using wordTrace_append hprefix tailTrace_939799
  have hstable : (prefixWord ++ tailWord_939799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939799).length < 2 ^ (prefixWord ++ tailWord_939799).sum := by decide
  have hdescent : baseEnd_939799 < baseStart_939799 := by decide
  rcases family_descends (prefixWord ++ tailWord_939799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939809 : List Nat := [1, 2, 3, 2, 1, 4, 3, 7]
def baseStart_939809 : Nat := 118140960795 + 939809 * 2 ^ 59
def prefixEnd_939809 : Nat := 4983230072969 + 3 ^ 40 * 939809 * 2
def baseEnd_939809 : Nat := 17873101497089582469089

theorem tailTrace_939809 : CollatzResearch.WordTrace tailWord_939809 prefixEnd_939809 17873101497089582469089 := by
  unfold tailWord_939809
  simp only [CollatzResearch.WordTrace]
  refine ⟨34277650252239974443726481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22851766834826649629150987 34277650252239974443726481)
  ·
    refine ⟨25708237689179980832794861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34277650252239974443726481 25708237689179980832794861)
    ·
      refine ⟨9640589133442492812298073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25708237689179980832794861 9640589133442492812298073)
      ·
        refine ⟨7230441850081869609223555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9640589133442492812298073 7230441850081869609223555)
        ·
          refine ⟨10845662775122804413835333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7230441850081869609223555 10845662775122804413835333)
          ·
            refine ⟨2033561770335525827594125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10845662775122804413835333 2033561770335525827594125)
            ·
              refine ⟨762585663875822185347797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2033561770335525827594125 762585663875822185347797)
              ·
                refine ⟨17873101497089582469089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 762585663875822185347797 17873101497089582469089)
                ·
                  rfl

theorem cell23_939809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 3, 7].length) (baseStart_939809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_939809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_939809 prefixEnd_939809 := by exact prefixLift 939809
  have htrace : WordTrace (prefixWord ++ tailWord_939809) baseStart_939809 baseEnd_939809 := by
    simpa [prefixWord, tailWord_939809, baseEnd_939809] using wordTrace_append hprefix tailTrace_939809
  have hstable : (prefixWord ++ tailWord_939809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939809).length < 2 ^ (prefixWord ++ tailWord_939809).sum := by decide
  have hdescent : baseEnd_939809 < baseStart_939809 := by decide
  rcases family_descends (prefixWord ++ tailWord_939809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939820 : List Nat := [2, 2, 1, 1, 1, 6, 2, 3, 1, 2, 2]
def baseStart_939820 : Nat := 118140960795 + 939820 * 2 ^ 59
def prefixEnd_939820 : Nat := 4983230072969 + 3 ^ 40 * 939820 * 2
def baseEnd_939820 : Nat := 482579388708618183627853

theorem tailTrace_939820 : CollatzResearch.WordTrace tailWord_939820 prefixEnd_939820 482579388708618183627853 := by
  unfold tailWord_939820
  simp only [CollatzResearch.WordTrace]
  refine ⟨17139025727600061661188457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22852034303466748881584609 17139025727600061661188457)
  ·
    refine ⟨12854269295700046245891343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17139025727600061661188457 12854269295700046245891343)
    ·
      refine ⟨19281403943550069368837015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12854269295700046245891343 19281403943550069368837015)
      ·
        refine ⟨28922105915325104053255523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19281403943550069368837015 28922105915325104053255523)
        ·
          refine ⟨43383158872987656079883285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28922105915325104053255523 43383158872987656079883285)
          ·
            refine ⟨2033585572171296378744529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 43383158872987656079883285 2033585572171296378744529)
            ·
              refine ⟨1525189179128472284058397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2033585572171296378744529 1525189179128472284058397)
              ·
                refine ⟨571945942173177106521899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1525189179128472284058397 571945942173177106521899)
                ·
                  refine ⟨857918913259765659782849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 571945942173177106521899 857918913259765659782849)
                  ·
                    refine ⟨643439184944824244837137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 857918913259765659782849 643439184944824244837137)
                    ·
                      refine ⟨482579388708618183627853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 643439184944824244837137 482579388708618183627853)
                      ·
                        rfl

theorem cell23_939820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 2, 3, 1, 2, 2].length) (baseStart_939820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_939820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_939820 prefixEnd_939820 := by exact prefixLift 939820
  have htrace : WordTrace (prefixWord ++ tailWord_939820) baseStart_939820 baseEnd_939820 := by
    simpa [prefixWord, tailWord_939820, baseEnd_939820] using wordTrace_append hprefix tailTrace_939820
  have hstable : (prefixWord ++ tailWord_939820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939820).length < 2 ^ (prefixWord ++ tailWord_939820).sum := by decide
  have hdescent : baseEnd_939820 < baseStart_939820 := by decide
  rcases family_descends (prefixWord ++ tailWord_939820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939830 : List Nat := [5, 1, 2, 2, 1, 3, 1, 2, 2, 4]
def baseStart_939830 : Nat := 118140960795 + 939830 * 2 ^ 59
def prefixEnd_939830 : Nat := 4983230072969 + 3 ^ 40 * 939830 * 2
def baseEnd_939830 : Nat := 160861507838387714834269

theorem tailTrace_939830 : CollatzResearch.WordTrace tailWord_939830 prefixEnd_939830 160861507838387714834269 := by
  unfold tailWord_939830
  simp only [CollatzResearch.WordTrace]
  refine ⟨2142401011572743439390059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22852277456775930020160629 2142401011572743439390059)
  ·
    refine ⟨3213601517359115159085089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2142401011572743439390059 3213601517359115159085089)
    ·
      refine ⟨2410201138019336369313817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3213601517359115159085089 2410201138019336369313817)
      ·
        refine ⟨1807650853514502276985363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2410201138019336369313817 1807650853514502276985363)
        ·
          refine ⟨2711476280271753415478045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1807650853514502276985363 2711476280271753415478045)
          ·
            refine ⟨1016803605101907530804267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2711476280271753415478045 1016803605101907530804267)
            ·
              refine ⟨1525205407652861296206401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1016803605101907530804267 1525205407652861296206401)
              ·
                refine ⟨1143904055739645972154801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1525205407652861296206401 1143904055739645972154801)
                ·
                  refine ⟨857928041804734479116101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1143904055739645972154801 857928041804734479116101)
                  ·
                    refine ⟨160861507838387714834269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 857928041804734479116101 160861507838387714834269)
                    ·
                      rfl

theorem cell23_939830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 1, 2, 2, 4].length) (baseStart_939830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_939830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_939830 prefixEnd_939830 := by exact prefixLift 939830
  have htrace : WordTrace (prefixWord ++ tailWord_939830) baseStart_939830 baseEnd_939830 := by
    simpa [prefixWord, tailWord_939830, baseEnd_939830] using wordTrace_append hprefix tailTrace_939830
  have hstable : (prefixWord ++ tailWord_939830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939830).length < 2 ^ (prefixWord ++ tailWord_939830).sum := by decide
  have hdescent : baseEnd_939830 < baseStart_939830 := by decide
  rcases family_descends (prefixWord ++ tailWord_939830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939853 : List Nat := [1, 6, 1, 2, 1, 1, 3, 1, 1, 3, 3]
def baseStart_939853 : Nat := 118140960795 + 939853 * 2 ^ 59
def prefixEnd_939853 : Nat := 4983230072969 + 3 ^ 40 * 939853 * 2
def baseEnd_939853 : Nat := 482596333570216554515201

theorem tailTrace_939853 : CollatzResearch.WordTrace tailWord_939853 prefixEnd_939853 482596333570216554515201 := by
  unfold tailWord_939853
  simp only [CollatzResearch.WordTrace]
  refine ⟨34279255064080569958328213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22852836709387046638885475 34279255064080569958328213)
  ·
    refine ⟨1606840081128776716796635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 34279255064080569958328213 1606840081128776716796635)
    ·
      refine ⟨2410260121693165075194953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1606840081128776716796635 2410260121693165075194953)
      ·
        refine ⟨1807695091269873806396215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2410260121693165075194953 1807695091269873806396215)
        ·
          refine ⟨2711542636904810709594323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1807695091269873806396215 2711542636904810709594323)
          ·
            refine ⟨4067313955357216064391485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2711542636904810709594323 4067313955357216064391485)
            ·
              refine ⟨1525242733258956024146807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4067313955357216064391485 1525242733258956024146807)
              ·
                refine ⟨2287864099888434036220211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1525242733258956024146807 2287864099888434036220211)
                ·
                  refine ⟨3431796149832651054330317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2287864099888434036220211 3431796149832651054330317)
                  ·
                    refine ⟨1286923556187244145373869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3431796149832651054330317 1286923556187244145373869)
                    ·
                      refine ⟨482596333570216554515201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1286923556187244145373869 482596333570216554515201)
                      ·
                        rfl

theorem cell23_939853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_939853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_939853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_939853 prefixEnd_939853 := by exact prefixLift 939853
  have htrace : WordTrace (prefixWord ++ tailWord_939853) baseStart_939853 baseEnd_939853 := by
    simpa [prefixWord, tailWord_939853, baseEnd_939853] using wordTrace_append hprefix tailTrace_939853
  have hstable : (prefixWord ++ tailWord_939853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939853).length < 2 ^ (prefixWord ++ tailWord_939853).sum := by decide
  have hdescent : baseEnd_939853 < baseStart_939853 := by decide
  rcases family_descends (prefixWord ++ tailWord_939853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939879 : List Nat := [1, 1, 5, 1, 2, 1, 3, 1, 2, 1, 5]
def baseStart_939879 : Nat := 118140960795 + 939879 * 2 ^ 59
def prefixEnd_939879 : Nat := 4983230072969 + 3 ^ 40 * 939879 * 2
def baseEnd_939879 : Nat := 482609684067233452790081

theorem tailTrace_939879 : CollatzResearch.WordTrace tailWord_939879 prefixEnd_939879 482609684067233452790081 := by
  unfold tailWord_939879
  simp only [CollatzResearch.WordTrace]
  refine ⟨34280203361986376398774691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22853468907990917599183127 34280203361986376398774691)
  ·
    refine ⟨51420305042979564598162037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34280203361986376398774691 51420305042979564598162037)
    ·
      refine ⟨4820653597779334181077691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51420305042979564598162037 4820653597779334181077691)
      ·
        refine ⟨7230980396669001271616537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4820653597779334181077691 7230980396669001271616537)
        ·
          refine ⟨5423235297501750953712403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7230980396669001271616537 5423235297501750953712403)
          ·
            refine ⟨8134852946252626430568605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5423235297501750953712403 8134852946252626430568605)
            ·
              refine ⟨3050569854844734911463227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8134852946252626430568605 3050569854844734911463227)
              ·
                refine ⟨4575854782267102367194841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3050569854844734911463227 4575854782267102367194841)
                ·
                  refine ⟨3431891086700326775396131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4575854782267102367194841 3431891086700326775396131)
                  ·
                    refine ⟨5147836630050490163094197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3431891086700326775396131 5147836630050490163094197)
                    ·
                      refine ⟨482609684067233452790081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5147836630050490163094197 482609684067233452790081)
                      ·
                        rfl

theorem cell23_939879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 1, 2, 1, 5].length) (baseStart_939879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_939879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_939879 prefixEnd_939879 := by exact prefixLift 939879
  have htrace : WordTrace (prefixWord ++ tailWord_939879) baseStart_939879 baseEnd_939879 := by
    simpa [prefixWord, tailWord_939879, baseEnd_939879] using wordTrace_append hprefix tailTrace_939879
  have hstable : (prefixWord ++ tailWord_939879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939879).length < 2 ^ (prefixWord ++ tailWord_939879).sum := by decide
  have hdescent : baseEnd_939879 < baseStart_939879 := by decide
  rcases family_descends (prefixWord ++ tailWord_939879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939893 : List Nat := [1, 3, 4, 1, 1, 1, 1, 3, 4, 2, 2]
def baseStart_939893 : Nat := 118140960795 + 939893 * 2 ^ 59
def prefixEnd_939893 : Nat := 4983230072969 + 3 ^ 40 * 939893 * 2
def baseEnd_939893 : Nat := 482616872796396398015017

theorem tailTrace_939893 : CollatzResearch.WordTrace tailWord_939893 prefixEnd_939893 482616872796396398015017 := by
  unfold tailWord_939893
  simp only [CollatzResearch.WordTrace]
  refine ⟨34280713983935656789784333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22853809322623771193189555 34280713983935656789784333)
  ·
    refine ⟨12855267743975871296169125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34280713983935656789784333 12855267743975871296169125)
    ·
      refine ⟨2410362701995475868031711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12855267743975871296169125 2410362701995475868031711)
      ·
        refine ⟨3615544052993213802047567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2410362701995475868031711 3615544052993213802047567)
        ·
          refine ⟨5423316079489820703071351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3615544052993213802047567 5423316079489820703071351)
          ·
            refine ⟨8134974119234731054607027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5423316079489820703071351 8134974119234731054607027)
            ·
              refine ⟨12202461178852096581910541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8134974119234731054607027 12202461178852096581910541)
              ·
                refine ⟨4575922942069536218216453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12202461178852096581910541 4575922942069536218216453)
                ·
                  refine ⟨857985551638038040915585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4575922942069536218216453 857985551638038040915585)
                  ·
                    refine ⟨643489163728528530686689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 857985551638038040915585 643489163728528530686689)
                    ·
                      refine ⟨482616872796396398015017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 643489163728528530686689 482616872796396398015017)
                      ·
                        rfl

theorem cell23_939893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 3, 4, 2, 2].length) (baseStart_939893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_939893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_939893 prefixEnd_939893 := by exact prefixLift 939893
  have htrace : WordTrace (prefixWord ++ tailWord_939893) baseStart_939893 baseEnd_939893 := by
    simpa [prefixWord, tailWord_939893, baseEnd_939893] using wordTrace_append hprefix tailTrace_939893
  have hstable : (prefixWord ++ tailWord_939893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939893).length < 2 ^ (prefixWord ++ tailWord_939893).sum := by decide
  have hdescent : baseEnd_939893 < baseStart_939893 := by decide
  rcases family_descends (prefixWord ++ tailWord_939893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939909 : List Nat := [1, 3, 1, 1, 3, 2, 2, 1, 1, 5, 3]
def baseStart_939909 : Nat := 118140960795 + 939909 * 2 ^ 59
def prefixEnd_939909 : Nat := 4983230072969 + 3 ^ 40 * 939909 * 2
def baseEnd_939909 : Nat := 482625088486868335414943

theorem tailTrace_939909 : CollatzResearch.WordTrace tailWord_939909 prefixEnd_939909 482625088486868335414943 := by
  unfold tailWord_939909
  simp only [CollatzResearch.WordTrace]
  refine ⟨34281297551877691522366781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22854198367918461014911187 34281297551877691522366781)
  ·
    refine ⟨12855486581954134320887543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34281297551877691522366781 12855486581954134320887543)
    ·
      refine ⟨19283229872931201481331315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12855486581954134320887543 19283229872931201481331315)
      ·
        refine ⟨28924844809396802221996973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19283229872931201481331315 28924844809396802221996973)
        ·
          refine ⟨10846816803523800833248865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28924844809396802221996973 10846816803523800833248865)
          ·
            refine ⟨8135112602642850624936649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10846816803523800833248865 8135112602642850624936649)
            ·
              refine ⟨6101334451982137968702487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8135112602642850624936649 6101334451982137968702487)
              ·
                refine ⟨9152001677973206953053731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6101334451982137968702487 9152001677973206953053731)
                ·
                  refine ⟨13728002516959810429580597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9152001677973206953053731 13728002516959810429580597)
                  ·
                    refine ⟨1287000235964982227773181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13728002516959810429580597 1287000235964982227773181)
                    ·
                      refine ⟨482625088486868335414943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1287000235964982227773181 482625088486868335414943)
                      ·
                        rfl

theorem cell23_939909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 1, 1, 5, 3].length) (baseStart_939909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_939909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_939909 prefixEnd_939909 := by exact prefixLift 939909
  have htrace : WordTrace (prefixWord ++ tailWord_939909) baseStart_939909 baseEnd_939909 := by
    simpa [prefixWord, tailWord_939909, baseEnd_939909] using wordTrace_append hprefix tailTrace_939909
  have hstable : (prefixWord ++ tailWord_939909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939909).length < 2 ^ (prefixWord ++ tailWord_939909).sum := by decide
  have hdescent : baseEnd_939909 < baseStart_939909 := by decide
  rcases family_descends (prefixWord ++ tailWord_939909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939929 : List Nat := [1, 2, 1, 2, 1, 3, 3, 3, 2, 5]
def baseStart_939929 : Nat := 118140960795 + 939929 * 2 ^ 59
def prefixEnd_939929 : Nat := 4983230072969 + 3 ^ 40 * 939929 * 2
def baseEnd_939929 : Nat := 160878452699986085721617

theorem tailTrace_939929 : CollatzResearch.WordTrace tailWord_939929 prefixEnd_939929 160878452699986085721617 := by
  unfold tailWord_939929
  simp only [CollatzResearch.WordTrace]
  refine ⟨34282027011805234938094841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22854684674536823292063227 34282027011805234938094841)
  ·
    refine ⟨25711520258853926203571131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34282027011805234938094841 25711520258853926203571131)
    ·
      refine ⟨38567280388280889305356697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25711520258853926203571131 38567280388280889305356697)
      ·
        refine ⟨28925460291210666979017523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38567280388280889305356697 28925460291210666979017523)
        ·
          refine ⟨43388190436816000468526285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28925460291210666979017523 43388190436816000468526285)
          ·
            refine ⟨16270571413806000175697357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43388190436816000468526285 16270571413806000175697357)
            ·
              refine ⟨6101464280177250065886509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16270571413806000175697357 6101464280177250065886509)
              ·
                refine ⟨2288049105066468774707441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6101464280177250065886509 2288049105066468774707441)
                ·
                  refine ⟨1716036828799851581030581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2288049105066468774707441 1716036828799851581030581)
                  ·
                    refine ⟨160878452699986085721617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1716036828799851581030581 160878452699986085721617)
                    ·
                      rfl

theorem cell23_939929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 3, 2, 5].length) (baseStart_939929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_939929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_939929 prefixEnd_939929 := by exact prefixLift 939929
  have htrace : WordTrace (prefixWord ++ tailWord_939929) baseStart_939929 baseEnd_939929 := by
    simpa [prefixWord, tailWord_939929, baseEnd_939929] using wordTrace_append hprefix tailTrace_939929
  have hstable : (prefixWord ++ tailWord_939929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939929).length < 2 ^ (prefixWord ++ tailWord_939929).sum := by decide
  have hdescent : baseEnd_939929 < baseStart_939929 := by decide
  rcases family_descends (prefixWord ++ tailWord_939929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939944 : List Nat := [2, 1, 6, 2, 1, 1, 2, 2, 2, 2, 2]
def baseStart_939944 : Nat := 118140960795 + 939944 * 2 ^ 59
def prefixEnd_939944 : Nat := 4983230072969 + 3 ^ 40 * 939944 * 2
def baseEnd_939944 : Nat := 482643060309775698477283

theorem tailTrace_939944 : CollatzResearch.WordTrace tailWord_939944 prefixEnd_939944 482643060309775698477283 := by
  unfold tailWord_939944
  simp only [CollatzResearch.WordTrace]
  refine ⟨17141287053375446249945443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22855049404500594999927257 17141287053375446249945443)
  ·
    refine ⟨25711930580063169374918165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17141287053375446249945443 25711930580063169374918165)
    ·
      refine ⟨1205246745940461064449289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 25711930580063169374918165 1205246745940461064449289)
      ·
        refine ⟨903935059455345798336967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1205246745940461064449289 903935059455345798336967)
        ·
          refine ⟨1355902589183018697505451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 903935059455345798336967 1355902589183018697505451)
          ·
            refine ⟨2033853883774528046258177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1355902589183018697505451 2033853883774528046258177)
            ·
              refine ⟨1525390412830896034693633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2033853883774528046258177 1525390412830896034693633)
              ·
                refine ⟨1144042809623172026020225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1525390412830896034693633 1144042809623172026020225)
                ·
                  refine ⟨858032107217379019515169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1144042809623172026020225 858032107217379019515169)
                  ·
                    refine ⟨643524080413034264636377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 858032107217379019515169 643524080413034264636377)
                    ·
                      refine ⟨482643060309775698477283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 643524080413034264636377 482643060309775698477283)
                      ·
                        rfl

theorem cell23_939944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_939944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_939944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_939944 prefixEnd_939944 := by exact prefixLift 939944
  have htrace : WordTrace (prefixWord ++ tailWord_939944) baseStart_939944 baseEnd_939944 := by
    simpa [prefixWord, tailWord_939944, baseEnd_939944] using wordTrace_append hprefix tailTrace_939944
  have hstable : (prefixWord ++ tailWord_939944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939944).length < 2 ^ (prefixWord ++ tailWord_939944).sum := by decide
  have hdescent : baseEnd_939944 < baseStart_939944 := by decide
  rcases family_descends (prefixWord ++ tailWord_939944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939976 : List Nat := [2, 1, 3, 1, 4, 1, 1, 1, 5, 4]
def baseStart_939976 : Nat := 118140960795 + 939976 * 2 ^ 59
def prefixEnd_939976 : Nat := 4983230072969 + 3 ^ 40 * 939976 * 2
def baseEnd_939976 : Nat := 160886497230239857759045

theorem tailTrace_939976 : CollatzResearch.WordTrace tailWord_939976 prefixEnd_939976 160886497230239857759045 := by
  unfold tailWord_939976
  simp only [CollatzResearch.WordTrace]
  refine ⟨17141870621317480982527891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22855827495089974643370521 17141870621317480982527891)
  ·
    refine ⟨25712805931976221473791837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17141870621317480982527891 25712805931976221473791837)
    ·
      refine ⟨9642302224491083052671939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25712805931976221473791837 9642302224491083052671939)
      ·
        refine ⟨14463453336736624579007909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9642302224491083052671939 14463453336736624579007909)
        ·
          refine ⟨2711897500638117108563983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14463453336736624579007909 2711897500638117108563983)
          ·
            refine ⟨4067846250957175662845975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2711897500638117108563983 4067846250957175662845975)
            ·
              refine ⟨6101769376435763494268963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4067846250957175662845975 6101769376435763494268963)
              ·
                refine ⟨9152654064653645241403445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6101769376435763494268963 9152654064653645241403445)
                ·
                  refine ⟨858061318561279241381573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9152654064653645241403445 858061318561279241381573)
                  ·
                    refine ⟨160886497230239857759045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 858061318561279241381573 160886497230239857759045)
                    ·
                      rfl

theorem cell23_939976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 1, 5, 4].length) (baseStart_939976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_939976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_939976 prefixEnd_939976 := by exact prefixLift 939976
  have htrace : WordTrace (prefixWord ++ tailWord_939976) baseStart_939976 baseEnd_939976 := by
    simpa [prefixWord, tailWord_939976, baseEnd_939976] using wordTrace_append hprefix tailTrace_939976
  have hstable : (prefixWord ++ tailWord_939976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939976).length < 2 ^ (prefixWord ++ tailWord_939976).sum := by decide
  have hdescent : baseEnd_939976 < baseStart_939976 := by decide
  rcases family_descends (prefixWord ++ tailWord_939976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940019 : List Nat := [1, 1, 1, 2, 2, 2, 1, 3, 5, 5]
def baseStart_940019 : Nat := 118140960795 + 940019 * 2 ^ 59
def prefixEnd_940019 : Nat := 4983230072969 + 3 ^ 40 * 940019 * 2
def baseEnd_940019 : Nat := 160893857119620968346479

theorem tailTrace_940019 : CollatzResearch.WordTrace tailWord_940019 prefixEnd_940019 160893857119620968346479 := by
  unfold tailWord_940019
  simp only [CollatzResearch.WordTrace]
  refine ⟨34285309581479180308871111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22856873054319453539247407 34285309581479180308871111)
  ·
    refine ⟨51427964372218770463306667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34285309581479180308871111 51427964372218770463306667)
    ·
      refine ⟨77141946558328155694960001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51427964372218770463306667 77141946558328155694960001)
      ·
        refine ⟨57856459918746116771220001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77141946558328155694960001 57856459918746116771220001)
        ·
          refine ⟨43392344939059587578415001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57856459918746116771220001 43392344939059587578415001)
          ·
            refine ⟨32544258704294690683811251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43392344939059587578415001 32544258704294690683811251)
            ·
              refine ⟨48816388056442036025716877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32544258704294690683811251 48816388056442036025716877)
              ·
                refine ⟨18306145521165763509643829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48816388056442036025716877 18306145521165763509643829)
                ·
                  refine ⟨1716201142609290329029109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18306145521165763509643829 1716201142609290329029109)
                  ·
                    refine ⟨160893857119620968346479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1716201142609290329029109 160893857119620968346479)
                    ·
                      rfl

theorem cell23_940019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 5, 5].length) (baseStart_940019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_940019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_940019 prefixEnd_940019 := by exact prefixLift 940019
  have htrace : WordTrace (prefixWord ++ tailWord_940019) baseStart_940019 baseEnd_940019 := by
    simpa [prefixWord, tailWord_940019, baseEnd_940019] using wordTrace_append hprefix tailTrace_940019
  have hstable : (prefixWord ++ tailWord_940019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940019).length < 2 ^ (prefixWord ++ tailWord_940019).sum := by decide
  have hdescent : baseEnd_940019 < baseStart_940019 := by decide
  rcases family_descends (prefixWord ++ tailWord_940019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940029 : List Nat := [1, 4, 1, 1, 1, 2, 2, 1, 2, 1, 7]
def baseStart_940029 : Nat := 118140960795 + 940029 * 2 ^ 59
def prefixEnd_940029 : Nat := 4983230072969 + 3 ^ 40 * 940029 * 2
def baseEnd_940029 : Nat := 482686706165407865914391

theorem tailTrace_940029 : CollatzResearch.WordTrace tailWord_940029 prefixEnd_940029 482686706165407865914391 := by
  unfold tailWord_940029
  simp only [CollatzResearch.WordTrace]
  refine ⟨34285674311442952016735141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22857116207628634677823427 34285674311442952016735141)
  ·
    refine ⟨6428563933395553503137839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34285674311442952016735141 6428563933395553503137839)
    ·
      refine ⟨9642845900093330254706759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6428563933395553503137839 9642845900093330254706759)
      ·
        refine ⟨14464268850139995382060139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9642845900093330254706759 14464268850139995382060139)
        ·
          refine ⟨21696403275209993073090209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14464268850139995382060139 21696403275209993073090209)
          ·
            refine ⟨16272302456407494804817657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21696403275209993073090209 16272302456407494804817657)
            ·
              refine ⟨12204226842305621103613243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16272302456407494804817657 12204226842305621103613243)
              ·
                refine ⟨18306340263458431655419865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12204226842305621103613243 18306340263458431655419865)
                ·
                  refine ⟨13729755197593823741564899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18306340263458431655419865 13729755197593823741564899)
                  ·
                    refine ⟨20594632796390735612347349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13729755197593823741564899 20594632796390735612347349)
                    ·
                      refine ⟨482686706165407865914391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 20594632796390735612347349 482686706165407865914391)
                      ·
                        rfl

theorem cell23_940029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 2, 1, 7].length) (baseStart_940029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_940029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_940029 prefixEnd_940029 := by exact prefixLift 940029
  have htrace : WordTrace (prefixWord ++ tailWord_940029) baseStart_940029 baseEnd_940029 := by
    simpa [prefixWord, tailWord_940029, baseEnd_940029] using wordTrace_append hprefix tailTrace_940029
  have hstable : (prefixWord ++ tailWord_940029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940029).length < 2 ^ (prefixWord ++ tailWord_940029).sum := by decide
  have hdescent : baseEnd_940029 < baseStart_940029 := by decide
  rcases family_descends (prefixWord ++ tailWord_940029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940033 : List Nat := [1, 2, 4, 1, 2, 1, 1, 4, 3, 1, 3]
def baseStart_940033 : Nat := 118140960795 + 940033 * 2 ^ 59
def prefixEnd_940033 : Nat := 4983230072969 + 3 ^ 40 * 940033 * 2
def baseEnd_940033 : Nat := 482688760088025850264373

theorem tailTrace_940033 : CollatzResearch.WordTrace tailWord_940033 prefixEnd_940033 482688760088025850264373 := by
  unfold tailWord_940033
  simp only [CollatzResearch.WordTrace]
  refine ⟨34285820203428460699880753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22857213468952307133253835 34285820203428460699880753)
  ·
    refine ⟨25714365152571345524910565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34285820203428460699880753 25714365152571345524910565)
    ·
      refine ⟨4821443466107127285920731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25714365152571345524910565 4821443466107127285920731)
      ·
        refine ⟨7232165199160690928881097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4821443466107127285920731 7232165199160690928881097)
        ·
          refine ⟨5424123899370518196660823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7232165199160690928881097 5424123899370518196660823)
          ·
            refine ⟨8136185849055777294991235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5424123899370518196660823 8136185849055777294991235)
            ·
              refine ⟨12204278773583665942486853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8136185849055777294991235 12204278773583665942486853)
              ·
                refine ⟨2288302270046937364216285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12204278773583665942486853 2288302270046937364216285)
                ·
                  refine ⟨858113351267601511581107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2288302270046937364216285 858113351267601511581107)
                  ·
                    refine ⟨1287170026901402267371661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 858113351267601511581107 1287170026901402267371661)
                    ·
                      refine ⟨482688760088025850264373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1287170026901402267371661 482688760088025850264373)
                      ·
                        rfl

theorem cell23_940033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 4, 3, 1, 3].length) (baseStart_940033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_940033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_940033 prefixEnd_940033 := by exact prefixLift 940033
  have htrace : WordTrace (prefixWord ++ tailWord_940033) baseStart_940033 baseEnd_940033 := by
    simpa [prefixWord, tailWord_940033, baseEnd_940033] using wordTrace_append hprefix tailTrace_940033
  have hstable : (prefixWord ++ tailWord_940033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940033).length < 2 ^ (prefixWord ++ tailWord_940033).sum := by decide
  have hdescent : baseEnd_940033 < baseStart_940033 := by decide
  rcases family_descends (prefixWord ++ tailWord_940033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940043 : List Nat := [1, 1, 1, 1, 6, 1, 2, 3, 2, 3, 2]
def baseStart_940043 : Nat := 118140960795 + 940043 * 2 ^ 59
def prefixEnd_940043 : Nat := 4983230072969 + 3 ^ 40 * 940043 * 2
def baseEnd_940043 : Nat := 482693894894570811139327

theorem tailTrace_940043 : CollatzResearch.WordTrace tailWord_940043 prefixEnd_940043 482693894894570811139327 := by
  unfold tailWord_940043
  simp only [CollatzResearch.WordTrace]
  refine ⟨34286184933392232407744783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22857456622261488271829855 34286184933392232407744783)
  ·
    refine ⟨51429277400088348611617175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34286184933392232407744783 51429277400088348611617175)
    ·
      refine ⟨77143916100132522917425763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51429277400088348611617175 77143916100132522917425763)
      ·
        refine ⟨115715874150198784376138645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77143916100132522917425763 115715874150198784376138645)
        ·
          refine ⟨5424181600790568017631499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 115715874150198784376138645 5424181600790568017631499)
          ·
            refine ⟨8136272401185852026447249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5424181600790568017631499 8136272401185852026447249)
            ·
              refine ⟨6102204300889389019835437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8136272401185852026447249 6102204300889389019835437)
              ·
                refine ⟨2288326612833520882438289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6102204300889389019835437 2288326612833520882438289)
                ·
                  refine ⟨1716244959625140661828717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2288326612833520882438289 1716244959625140661828717)
                  ·
                    refine ⟨643591859859427748185769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1716244959625140661828717 643591859859427748185769)
                    ·
                      refine ⟨482693894894570811139327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 643591859859427748185769 482693894894570811139327)
                      ·
                        rfl

theorem cell23_940043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 3, 2, 3, 2].length) (baseStart_940043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_940043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_940043 prefixEnd_940043 := by exact prefixLift 940043
  have htrace : WordTrace (prefixWord ++ tailWord_940043) baseStart_940043 baseEnd_940043 := by
    simpa [prefixWord, tailWord_940043, baseEnd_940043] using wordTrace_append hprefix tailTrace_940043
  have hstable : (prefixWord ++ tailWord_940043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940043).length < 2 ^ (prefixWord ++ tailWord_940043).sum := by decide
  have hdescent : baseEnd_940043 < baseStart_940043 := by decide
  rcases family_descends (prefixWord ++ tailWord_940043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940060 : List Nat := [2, 2, 3, 1, 3, 2, 1, 2, 2, 3, 2]
def baseStart_940060 : Nat := 118140960795 + 940060 * 2 ^ 59
def prefixEnd_940060 : Nat := 4983230072969 + 3 ^ 40 * 940060 * 2
def baseEnd_940060 : Nat := 482702624065697244626749

theorem tailTrace_940060 : CollatzResearch.WordTrace tailWord_940060 prefixEnd_940060 482702624065697244626749 := by
  unfold tailWord_940060
  simp only [CollatzResearch.WordTrace]
  refine ⟨17143402487165322155556817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22857869982887096207409089 17143402487165322155556817)
  ·
    refine ⟨12857551865373991616667613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17143402487165322155556817 12857551865373991616667613)
    ·
      refine ⟨4821581949515246856250355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12857551865373991616667613 4821581949515246856250355)
      ·
        refine ⟨7232372924272870284375533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4821581949515246856250355 7232372924272870284375533)
        ·
          refine ⟨2712139846602326356640825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7232372924272870284375533 2712139846602326356640825)
          ·
            refine ⟨2034104884951744767480619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2712139846602326356640825 2034104884951744767480619)
            ·
              refine ⟨3051157327427617151220929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2034104884951744767480619 3051157327427617151220929)
              ·
                refine ⟨2288367995570712863415697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3051157327427617151220929 2288367995570712863415697)
                ·
                  refine ⟨1716275996678034647561773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2288367995570712863415697 1716275996678034647561773)
                  ·
                    refine ⟨643603498754262992835665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1716275996678034647561773 643603498754262992835665)
                    ·
                      refine ⟨482702624065697244626749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 643603498754262992835665 482702624065697244626749)
                      ·
                        rfl

theorem cell23_940060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 2, 2, 3, 2].length) (baseStart_940060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_940060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_940060 prefixEnd_940060 := by exact prefixLift 940060
  have htrace : WordTrace (prefixWord ++ tailWord_940060) baseStart_940060 baseEnd_940060 := by
    simpa [prefixWord, tailWord_940060, baseEnd_940060] using wordTrace_append hprefix tailTrace_940060
  have hstable : (prefixWord ++ tailWord_940060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940060).length < 2 ^ (prefixWord ++ tailWord_940060).sum := by decide
  have hdescent : baseEnd_940060 < baseStart_940060 := by decide
  rcases family_descends (prefixWord ++ tailWord_940060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940067 : List Nat := [1, 1, 1, 4, 3, 1, 5, 2, 1, 1, 3]
def baseStart_940067 : Nat := 118140960795 + 940067 * 2 ^ 59
def prefixEnd_940067 : Nat := 4983230072969 + 3 ^ 40 * 940067 * 2
def baseEnd_940067 : Nat := 482706218430278717239217

theorem tailTrace_940067 : CollatzResearch.WordTrace tailWord_940067 prefixEnd_940067 482706218430278717239217 := by
  unfold tailWord_940067
  simp only [CollatzResearch.WordTrace]
  refine ⟨34287060285305284506618455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22858040190203523004412303 34287060285305284506618455)
  ·
    refine ⟨51430590427957926759927683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34287060285305284506618455 51430590427957926759927683)
    ·
      refine ⟨77145885641936890139891525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51430590427957926759927683 77145885641936890139891525)
      ·
        refine ⟨14464853557863166901229661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77145885641936890139891525 14464853557863166901229661)
        ·
          refine ⟨5424320084198687587961123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14464853557863166901229661 5424320084198687587961123)
          ·
            refine ⟨8136480126298031381941685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5424320084198687587961123 8136480126298031381941685)
            ·
              refine ⟨762795011840440442057033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8136480126298031381941685 762795011840440442057033)
              ·
                refine ⟨572096258880330331542775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 762795011840440442057033 572096258880330331542775)
                ·
                  refine ⟨858144388320495497314163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 572096258880330331542775 858144388320495497314163)
                  ·
                    refine ⟨1287216582480743245971245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 858144388320495497314163 1287216582480743245971245)
                    ·
                      refine ⟨482706218430278717239217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1287216582480743245971245 482706218430278717239217)
                      ·
                        rfl

theorem cell23_940067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 5, 2, 1, 1, 3].length) (baseStart_940067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_940067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_940067 prefixEnd_940067 := by exact prefixLift 940067
  have htrace : WordTrace (prefixWord ++ tailWord_940067) baseStart_940067 baseEnd_940067 := by
    simpa [prefixWord, tailWord_940067, baseEnd_940067] using wordTrace_append hprefix tailTrace_940067
  have hstable : (prefixWord ++ tailWord_940067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940067).length < 2 ^ (prefixWord ++ tailWord_940067).sum := by decide
  have hdescent : baseEnd_940067 < baseStart_940067 := by decide
  rcases family_descends (prefixWord ++ tailWord_940067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940093 : List Nat := [1, 4, 1, 3, 1, 1, 3, 1, 3, 2, 3]
def baseStart_940093 : Nat := 118140960795 + 940093 * 2 ^ 59
def prefixEnd_940093 : Nat := 4983230072969 + 3 ^ 40 * 940093 * 2
def baseEnd_940093 : Nat := 482719568927295615514097

theorem tailTrace_940093 : CollatzResearch.WordTrace tailWord_940093 prefixEnd_940093 482719568927295615514097 := by
  unfold tailWord_940093
  simp only [CollatzResearch.WordTrace]
  refine ⟨34288008583211090947064933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22858672388807393964709955 34288008583211090947064933)
  ·
    refine ⟨6429001609352079552574675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34288008583211090947064933 6429001609352079552574675)
    ·
      refine ⟨9643502414028119328862013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6429001609352079552574675 9643502414028119328862013)
      ·
        refine ⟨3616313405260544748323255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9643502414028119328862013 3616313405260544748323255)
        ·
          refine ⟨5424470107890817122484883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3616313405260544748323255 5424470107890817122484883)
          ·
            refine ⟨8136705161836225683727325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5424470107890817122484883 8136705161836225683727325)
            ·
              refine ⟨3051264435688584631397747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8136705161836225683727325 3051264435688584631397747)
              ·
                refine ⟨4576896653532876947096621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3051264435688584631397747 4576896653532876947096621)
                ·
                  refine ⟨1716336245074828855161233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4576896653532876947096621 1716336245074828855161233)
                  ·
                    refine ⟨1287252183806121641370925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1716336245074828855161233 1287252183806121641370925)
                    ·
                      refine ⟨482719568927295615514097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1287252183806121641370925 482719568927295615514097)
                      ·
                        rfl

theorem cell23_940093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 1, 3, 2, 3].length) (baseStart_940093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_940093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_940093 prefixEnd_940093 := by exact prefixLift 940093
  have htrace : WordTrace (prefixWord ++ tailWord_940093) baseStart_940093 baseEnd_940093 := by
    simpa [prefixWord, tailWord_940093, baseEnd_940093] using wordTrace_append hprefix tailTrace_940093
  have hstable : (prefixWord ++ tailWord_940093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940093).length < 2 ^ (prefixWord ++ tailWord_940093).sum := by decide
  have hdescent : baseEnd_940093 < baseStart_940093 := by decide
  rcases family_descends (prefixWord ++ tailWord_940093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940118 : List Nat := [5, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3]
def baseStart_940118 : Nat := 118140960795 + 940118 * 2 ^ 59
def prefixEnd_940118 : Nat := 4983230072969 + 3 ^ 40 * 940118 * 2
def baseEnd_940118 : Nat := 482732405943658017701483

theorem tailTrace_940118 : CollatzResearch.WordTrace tailWord_940118 prefixEnd_940118 482732405943658017701483 := by
  unfold tailWord_940118
  simp only [CollatzResearch.WordTrace]
  refine ⟨2143057525507532513545313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22859280272080346811150005 2143057525507532513545313)
  ·
    refine ⟨1607293144130649385158985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2143057525507532513545313 1607293144130649385158985)
    ·
      refine ⟨1205469858097987038869239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1607293144130649385158985 1205469858097987038869239)
      ·
        refine ⟨1808204787146980558303859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1205469858097987038869239 1808204787146980558303859)
        ·
          refine ⟨2712307180720470837455789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1808204787146980558303859 2712307180720470837455789)
          ·
            refine ⟨1017115192770176564045921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2712307180720470837455789 1017115192770176564045921)
            ·
              refine ⟨762836394577632423034441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1017115192770176564045921 762836394577632423034441)
              ·
                refine ⟨572127295933224317275831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 762836394577632423034441 572127295933224317275831)
                ·
                  refine ⟨858190943899836475913747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 572127295933224317275831 858190943899836475913747)
                  ·
                    refine ⟨1287286415849754713870621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 858190943899836475913747 1287286415849754713870621)
                    ·
                      refine ⟨482732405943658017701483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1287286415849754713870621 482732405943658017701483)
                      ·
                        rfl

theorem cell23_940118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3].length) (baseStart_940118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_940118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_940118 prefixEnd_940118 := by exact prefixLift 940118
  have htrace : WordTrace (prefixWord ++ tailWord_940118) baseStart_940118 baseEnd_940118 := by
    simpa [prefixWord, tailWord_940118, baseEnd_940118] using wordTrace_append hprefix tailTrace_940118
  have hstable : (prefixWord ++ tailWord_940118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940118).length < 2 ^ (prefixWord ++ tailWord_940118).sum := by decide
  have hdescent : baseEnd_940118 < baseStart_940118 := by decide
  rcases family_descends (prefixWord ++ tailWord_940118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940124 : List Nat := [2, 2, 4, 1, 1, 3, 1, 4, 1, 2, 2]
def baseStart_940124 : Nat := 118140960795 + 940124 * 2 ^ 59
def prefixEnd_940124 : Nat := 4983230072969 + 3 ^ 40 * 940124 * 2
def baseEnd_940124 : Nat := 482735486827584994226455

theorem tailTrace_940124 : CollatzResearch.WordTrace tailWord_940124 prefixEnd_940124 482735486827584994226455 := by
  unfold tailWord_940124
  simp only [CollatzResearch.WordTrace]
  refine ⟨17144569623049391620721713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22859426164065855494295617 17144569623049391620721713)
  ·
    refine ⟨12858427217287043715541285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17144569623049391620721713 12858427217287043715541285)
    ·
      refine ⟨2410955103241320696663991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12858427217287043715541285 2410955103241320696663991)
      ·
        refine ⟨3616432654861981044995987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2410955103241320696663991 3616432654861981044995987)
        ·
          refine ⟨5424648982292971567493981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3616432654861981044995987 5424648982292971567493981)
          ·
            refine ⟨2034243368359864337810243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5424648982292971567493981 2034243368359864337810243)
            ·
              refine ⟨3051365052539796506715365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2034243368359864337810243 3051365052539796506715365)
              ·
                refine ⟨572130947351211845009131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3051365052539796506715365 572130947351211845009131)
                ·
                  refine ⟨858196421026817767513697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 572130947351211845009131 858196421026817767513697)
                  ·
                    refine ⟨643647315770113325635273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 858196421026817767513697 643647315770113325635273)
                    ·
                      refine ⟨482735486827584994226455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 643647315770113325635273 482735486827584994226455)
                      ·
                        rfl

theorem cell23_940124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 4, 1, 2, 2].length) (baseStart_940124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_940124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_940124 prefixEnd_940124 := by exact prefixLift 940124
  have htrace : WordTrace (prefixWord ++ tailWord_940124) baseStart_940124 baseEnd_940124 := by
    simpa [prefixWord, tailWord_940124, baseEnd_940124] using wordTrace_append hprefix tailTrace_940124
  have hstable : (prefixWord ++ tailWord_940124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940124).length < 2 ^ (prefixWord ++ tailWord_940124).sum := by decide
  have hdescent : baseEnd_940124 < baseStart_940124 := by decide
  rcases family_descends (prefixWord ++ tailWord_940124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940130 : List Nat := [3, 3, 2, 2, 2, 2, 1, 8]
def baseStart_940130 : Nat := 118140960795 + 940130 * 2 ^ 59
def prefixEnd_940130 : Nat := 4983230072969 + 3 ^ 40 * 940130 * 2
def baseEnd_940130 : Nat := 17879206211537480398201

theorem tailTrace_940130 : CollatzResearch.WordTrace tailWord_940130 prefixEnd_940130 17879206211537480398201 := by
  unfold tailWord_940130
  simp only [CollatzResearch.WordTrace]
  refine ⟨8572339521019261566540461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22859572056051364177441229 8572339521019261566540461)
  ·
    refine ⟨3214627320382223087452673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8572339521019261566540461 3214627320382223087452673)
    ·
      refine ⟨2410970490286667315589505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3214627320382223087452673 2410970490286667315589505)
      ·
        refine ⟨1808227867715000486692129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2410970490286667315589505 1808227867715000486692129)
        ·
          refine ⟨1356170900786250365019097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1808227867715000486692129 1356170900786250365019097)
          ·
            refine ⟨1017128175589687773764323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1356170900786250365019097 1017128175589687773764323)
            ·
              refine ⟨1525692263384531660646485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1017128175589687773764323 1525692263384531660646485)
              ·
                refine ⟨17879206211537480398201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1525692263384531660646485 17879206211537480398201)
                ·
                  rfl

theorem cell23_940130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 1, 8].length) (baseStart_940130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_940130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_940130 prefixEnd_940130 := by exact prefixLift 940130
  have htrace : WordTrace (prefixWord ++ tailWord_940130) baseStart_940130 baseEnd_940130 := by
    simpa [prefixWord, tailWord_940130, baseEnd_940130] using wordTrace_append hprefix tailTrace_940130
  have hstable : (prefixWord ++ tailWord_940130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940130).length < 2 ^ (prefixWord ++ tailWord_940130).sum := by decide
  have hdescent : baseEnd_940130 < baseStart_940130 := by decide
  rcases family_descends (prefixWord ++ tailWord_940130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
