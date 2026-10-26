import V185TrunkScan23Chunk0784

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4642836 : List Nat := [2, 4, 3, 2, 2, 1, 2, 1, 2, 2, 2]
def baseStart_4642836 : Nat := 118140960795 + 4642836 * 2 ^ 59
def prefixEnd_4642836 : Nat := 4983230072969 + 3 ^ 40 * 4642836 * 2
def baseEnd_4642836 : Nat := 2384006467998102116497993

theorem tailTrace_4642836 : CollatzResearch.WordTrace tailWord_4642836 prefixEnd_4642836 2384006467998102116497993 := by
  unfold tailWord_4642836
  simp only [CollatzResearch.WordTrace]
  refine ⟨84669070303902790052634181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112892093738537053403512241 84669070303902790052634181)
  ·
    refine ⟨15875450681981773134868909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84669070303902790052634181 15875450681981773134868909)
    ·
      refine ⟨5953294005743164925575841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15875450681981773134868909 5953294005743164925575841)
      ·
        refine ⟨4464970504307373694181881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5953294005743164925575841 4464970504307373694181881)
        ·
          refine ⟨3348727878230530270636411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4464970504307373694181881 3348727878230530270636411)
          ·
            refine ⟨5023091817345795405954617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3348727878230530270636411 5023091817345795405954617)
            ·
              refine ⟨3767318863009346554465963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5023091817345795405954617 3767318863009346554465963)
              ·
                refine ⟨5650978294514019831698945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3767318863009346554465963 5650978294514019831698945)
                ·
                  refine ⟨4238233720885514873774209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5650978294514019831698945 4238233720885514873774209)
                  ·
                    refine ⟨3178675290664136155330657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4238233720885514873774209 3178675290664136155330657)
                    ·
                      refine ⟨2384006467998102116497993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3178675290664136155330657 2384006467998102116497993)
                      ·
                        rfl

theorem cell23_4642836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_4642836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4642836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4642836 prefixEnd_4642836 := by exact prefixLift 4642836
  have htrace : WordTrace (prefixWord ++ tailWord_4642836) baseStart_4642836 baseEnd_4642836 := by
    simpa [prefixWord, tailWord_4642836, baseEnd_4642836] using wordTrace_append hprefix tailTrace_4642836
  have hstable : (prefixWord ++ tailWord_4642836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4642836).length < 2 ^ (prefixWord ++ tailWord_4642836).sum := by decide
  have hdescent : baseEnd_4642836 < baseStart_4642836 := by decide
  rcases family_descends (prefixWord ++ tailWord_4642836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4642881 : List Nat := [1, 2, 5, 1, 2, 2, 2, 2, 6]
def baseStart_4642881 : Nat := 118140960795 + 4642881 * 2 ^ 59
def prefixEnd_4642881 : Nat := 4983230072969 + 3 ^ 40 * 4642881 * 2
def baseEnd_4642881 : Nat := 264892174958617160048365

theorem tailTrace_4642881 : CollatzResearch.WordTrace tailWord_4642881 prefixEnd_4642881 264892174958617160048365 := by
  unfold tailWord_4642881
  simp only [CollatzResearch.WordTrace]
  refine ⟨169339781892642552790656497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112893187928428368527104331 169339781892642552790656497)
  ·
    refine ⟨127004836419481914592992373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169339781892642552790656497 127004836419481914592992373)
    ·
      refine ⟨11906703414326429493093035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 127004836419481914592992373 11906703414326429493093035)
      ·
        refine ⟨17860055121489644239639553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11906703414326429493093035 17860055121489644239639553)
        ·
          refine ⟨13395041341117233179729665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17860055121489644239639553 13395041341117233179729665)
          ·
            refine ⟨10046281005837924884797249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13395041341117233179729665 10046281005837924884797249)
            ·
              refine ⟨7534710754378443663597937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10046281005837924884797249 7534710754378443663597937)
              ·
                refine ⟨5651033065783832747698453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7534710754378443663597937 5651033065783832747698453)
                ·
                  refine ⟨264892174958617160048365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5651033065783832747698453 264892174958617160048365)
                  ·
                    rfl

theorem cell23_4642881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 2, 2, 6].length) (baseStart_4642881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4642881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4642881 prefixEnd_4642881 := by exact prefixLift 4642881
  have htrace : WordTrace (prefixWord ++ tailWord_4642881) baseStart_4642881 baseEnd_4642881 := by
    simpa [prefixWord, tailWord_4642881, baseEnd_4642881] using wordTrace_append hprefix tailTrace_4642881
  have hstable : (prefixWord ++ tailWord_4642881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4642881).length < 2 ^ (prefixWord ++ tailWord_4642881).sum := by decide
  have hdescent : baseEnd_4642881 < baseStart_4642881 := by decide
  rcases family_descends (prefixWord ++ tailWord_4642881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4642894 : List Nat := [4, 1, 1, 1, 1, 4, 1, 2, 3, 5]
def baseStart_4642894 : Nat := 118140960795 + 4642894 * 2 ^ 59
def prefixEnd_4642894 : Nat := 4983230072969 + 3 ^ 40 * 4642894 * 2
def baseEnd_4642894 : Nat := 794678749958687629857575

theorem tailTrace_4642894 : CollatzResearch.WordTrace tailWord_4642894 prefixEnd_4642894 794678749958687629857575 := by
  unfold tailWord_4642894
  simp only [CollatzResearch.WordTrace]
  refine ⟨21167532005199432001359967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112893504027730304007253157 21167532005199432001359967)
  ·
    refine ⟨31751298007799148002039951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21167532005199432001359967 31751298007799148002039951)
    ·
      refine ⟨47626947011698722003059927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31751298007799148002039951 47626947011698722003059927)
      ·
        refine ⟨71440420517548083004589891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47626947011698722003059927 71440420517548083004589891)
        ·
          refine ⟨107160630776322124506884837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71440420517548083004589891 107160630776322124506884837)
          ·
            refine ⟨20092618270560398345040907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 107160630776322124506884837 20092618270560398345040907)
            ·
              refine ⟨30138927405840597517561361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20092618270560398345040907 30138927405840597517561361)
              ·
                refine ⟨22604195554380448138171021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30138927405840597517561361 22604195554380448138171021)
                ·
                  refine ⟨8476573332892668051814133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22604195554380448138171021 8476573332892668051814133)
                  ·
                    refine ⟨794678749958687629857575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8476573332892668051814133 794678749958687629857575)
                    ·
                      rfl

theorem cell23_4642894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 2, 3, 5].length) (baseStart_4642894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4642894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4642894 prefixEnd_4642894 := by exact prefixLift 4642894
  have htrace : WordTrace (prefixWord ++ tailWord_4642894) baseStart_4642894 baseEnd_4642894 := by
    simpa [prefixWord, tailWord_4642894, baseEnd_4642894] using wordTrace_append hprefix tailTrace_4642894
  have hstable : (prefixWord ++ tailWord_4642894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4642894).length < 2 ^ (prefixWord ++ tailWord_4642894).sum := by decide
  have hdescent : baseEnd_4642894 < baseStart_4642894 := by decide
  rcases family_descends (prefixWord ++ tailWord_4642894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4642908 : List Nat := [2, 2, 4, 1, 1, 3, 1, 2, 3, 1, 3]
def baseStart_4642908 : Nat := 118140960795 + 4642908 * 2 ^ 59
def prefixEnd_4642908 : Nat := 4983230072969 + 3 ^ 40 * 4642908 * 2
def baseEnd_4642908 : Nat := 2384043438605225834797661

theorem tailTrace_4642908 : CollatzResearch.WordTrace tailWord_4642908 prefixEnd_4642908 2384043438605225834797661 := by
  unfold tailWord_4642908
  simp only [CollatzResearch.WordTrace]
  refine ⟨84670383331772368200944689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112893844442363157601259585 84670383331772368200944689)
  ·
    refine ⟨63502787498829276150708517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84670383331772368200944689 63502787498829276150708517)
    ·
      refine ⟨11906772656030489278257847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63502787498829276150708517 11906772656030489278257847)
      ·
        refine ⟨17860158984045733917386771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11906772656030489278257847 17860158984045733917386771)
        ·
          refine ⟨26790238476068600876080157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17860158984045733917386771 26790238476068600876080157)
          ·
            refine ⟨10046339428525725328530059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26790238476068600876080157 10046339428525725328530059)
            ·
              refine ⟨15069509142788587992795089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10046339428525725328530059 15069509142788587992795089)
              ·
                refine ⟨11302131857091440994596317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15069509142788587992795089 11302131857091440994596317)
                ·
                  refine ⟨4238299446409290372973619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11302131857091440994596317 4238299446409290372973619)
                  ·
                    refine ⟨6357449169613935559460429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4238299446409290372973619 6357449169613935559460429)
                    ·
                      refine ⟨2384043438605225834797661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6357449169613935559460429 2384043438605225834797661)
                      ·
                        rfl

theorem cell23_4642908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 2, 3, 1, 3].length) (baseStart_4642908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4642908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4642908 prefixEnd_4642908 := by exact prefixLift 4642908
  have htrace : WordTrace (prefixWord ++ tailWord_4642908) baseStart_4642908 baseEnd_4642908 := by
    simpa [prefixWord, tailWord_4642908, baseEnd_4642908] using wordTrace_append hprefix tailTrace_4642908
  have hstable : (prefixWord ++ tailWord_4642908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4642908).length < 2 ^ (prefixWord ++ tailWord_4642908).sum := by decide
  have hdescent : baseEnd_4642908 < baseStart_4642908 := by decide
  rcases family_descends (prefixWord ++ tailWord_4642908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4642924 : List Nat := [2, 2, 1, 1, 3, 3, 2, 2, 1, 6]
def baseStart_4642924 : Nat := 118140960795 + 4642924 * 2 ^ 59
def prefixEnd_4642924 : Nat := 4983230072969 + 3 ^ 40 * 4642924 * 2
def baseEnd_4642924 : Nat := 794683884765232590732529

theorem tailTrace_4642924 : CollatzResearch.WordTrace tailWord_4642924 prefixEnd_4642924 794683884765232590732529 := by
  unfold tailWord_4642924
  simp only [CollatzResearch.WordTrace]
  refine ⟨84670675115743385567235913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112894233487657847422981217 84670675115743385567235913)
  ·
    refine ⟨63503006336807539175426935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84670675115743385567235913 63503006336807539175426935)
    ·
      refine ⟨95254509505211308763140403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63503006336807539175426935 95254509505211308763140403)
      ·
        refine ⟨142881764257816963144710605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95254509505211308763140403 142881764257816963144710605)
        ·
          refine ⟨53580661596681361179266477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 142881764257816963144710605 53580661596681361179266477)
          ·
            refine ⟨20092748098755510442224929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53580661596681361179266477 20092748098755510442224929)
            ·
              refine ⟨15069561074066632831668697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20092748098755510442224929 15069561074066632831668697)
              ·
                refine ⟨11302170805549974623751523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15069561074066632831668697 11302170805549974623751523)
                ·
                  refine ⟨16953256208324961935627285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11302170805549974623751523 16953256208324961935627285)
                  ·
                    refine ⟨794683884765232590732529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16953256208324961935627285 794683884765232590732529)
                    ·
                      rfl

theorem cell23_4642924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 6].length) (baseStart_4642924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4642924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4642924 prefixEnd_4642924 := by exact prefixLift 4642924
  have htrace : WordTrace (prefixWord ++ tailWord_4642924) baseStart_4642924 baseEnd_4642924 := by
    simpa [prefixWord, tailWord_4642924, baseEnd_4642924] using wordTrace_append hprefix tailTrace_4642924
  have hstable : (prefixWord ++ tailWord_4642924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4642924).length < 2 ^ (prefixWord ++ tailWord_4642924).sum := by decide
  have hdescent : baseEnd_4642924 < baseStart_4642924 := by decide
  rcases family_descends (prefixWord ++ tailWord_4642924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4642925 : List Nat := [1, 5, 1, 1, 2, 1, 4, 3, 1, 1, 3]
def baseStart_4642925 : Nat := 118140960795 + 4642925 * 2 ^ 59
def prefixEnd_4642925 : Nat := 4983230072969 + 3 ^ 40 * 4642925 * 2
def baseEnd_4642925 : Nat := 2384052167776352268285083

theorem tailTrace_4642925 : CollatzResearch.WordTrace tailWord_4642925 prefixEnd_4642925 2384052167776352268285083 := by
  unfold tailWord_4642925
  simp only [CollatzResearch.WordTrace]
  refine ⟨169341386704483148305258229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112894257802988765536838819 169341386704483148305258229)
  ·
    refine ⟨15875755003545295153617959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 169341386704483148305258229 15875755003545295153617959)
    ·
      refine ⟨23813632505317942730426939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15875755003545295153617959 23813632505317942730426939)
      ·
        refine ⟨35720448757976914095640409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23813632505317942730426939 35720448757976914095640409)
        ·
          refine ⟨26790336568482685571730307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35720448757976914095640409 26790336568482685571730307)
          ·
            refine ⟨40185504852724028357595461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26790336568482685571730307 40185504852724028357595461)
            ·
              refine ⟨7534782159885755317049149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40185504852724028357595461 7534782159885755317049149)
              ·
                refine ⟨2825543309957158243893431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7534782159885755317049149 2825543309957158243893431)
                ·
                  refine ⟨4238314964935737365840147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2825543309957158243893431 4238314964935737365840147)
                  ·
                    refine ⟨6357472447403606048760221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4238314964935737365840147 6357472447403606048760221)
                    ·
                      refine ⟨2384052167776352268285083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6357472447403606048760221 2384052167776352268285083)
                      ·
                        rfl

theorem cell23_4642925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 4, 3, 1, 1, 3].length) (baseStart_4642925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4642925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4642925 prefixEnd_4642925 := by exact prefixLift 4642925
  have htrace : WordTrace (prefixWord ++ tailWord_4642925) baseStart_4642925 baseEnd_4642925 := by
    simpa [prefixWord, tailWord_4642925, baseEnd_4642925] using wordTrace_append hprefix tailTrace_4642925
  have hstable : (prefixWord ++ tailWord_4642925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4642925).length < 2 ^ (prefixWord ++ tailWord_4642925).sum := by decide
  have hdescent : baseEnd_4642925 < baseStart_4642925 := by decide
  rcases family_descends (prefixWord ++ tailWord_4642925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4642928 : List Nat := [2, 1, 1, 1, 5, 4, 2, 1, 1, 5]
def baseStart_4642928 : Nat := 118140960795 + 4642928 * 2 ^ 59
def prefixEnd_4642928 : Nat := 4983230072969 + 3 ^ 40 * 4642928 * 2
def baseEnd_4642928 : Nat := 794684569406105252182523

theorem tailTrace_4642928 : CollatzResearch.WordTrace tailWord_4642928 prefixEnd_4642928 794684569406105252182523 := by
  unfold tailWord_4642928
  simp only [CollatzResearch.WordTrace]
  refine ⟨84670748061736139908808719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112894330748981519878411625 84670748061736139908808719)
  ·
    refine ⟨127006122092604209863213079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84670748061736139908808719 127006122092604209863213079)
    ·
      refine ⟨190509183138906314794819619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127006122092604209863213079 190509183138906314794819619)
      ·
        refine ⟨285763774708359472192229429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190509183138906314794819619 285763774708359472192229429)
        ·
          refine ⟨26790353878908700518021509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 285763774708359472192229429 26790353878908700518021509)
          ·
            refine ⟨5023191352295381347129033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26790353878908700518021509 5023191352295381347129033)
            ·
              refine ⟨3767393514221536010346775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5023191352295381347129033 3767393514221536010346775)
              ·
                refine ⟨5651090271332304015520163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3767393514221536010346775 5651090271332304015520163)
                ·
                  refine ⟨8476635406998456023280245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5651090271332304015520163 8476635406998456023280245)
                  ·
                    refine ⟨794684569406105252182523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8476635406998456023280245 794684569406105252182523)
                    ·
                      rfl

theorem cell23_4642928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 2, 1, 1, 5].length) (baseStart_4642928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4642928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4642928 prefixEnd_4642928 := by exact prefixLift 4642928
  have htrace : WordTrace (prefixWord ++ tailWord_4642928) baseStart_4642928 baseEnd_4642928 := by
    simpa [prefixWord, tailWord_4642928, baseEnd_4642928] using wordTrace_append hprefix tailTrace_4642928
  have hstable : (prefixWord ++ tailWord_4642928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4642928).length < 2 ^ (prefixWord ++ tailWord_4642928).sum := by decide
  have hdescent : baseEnd_4642928 < baseStart_4642928 := by decide
  rcases family_descends (prefixWord ++ tailWord_4642928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4642941 : List Nat := [1, 4, 1, 1, 3, 3, 1, 1, 4, 4]
def baseStart_4642941 : Nat := 118140960795 + 4642941 * 2 ^ 59
def prefixEnd_4642941 : Nat := 4983230072969 + 3 ^ 40 * 4642941 * 2
def baseEnd_4642941 : Nat := 794686794488941401895003

theorem tailTrace_4642941 : CollatzResearch.WordTrace tailWord_4642941 prefixEnd_4642941 794686794488941401895003 := by
  unfold tailWord_4642941
  simp only [CollatzResearch.WordTrace]
  refine ⟨169341970272425183037840677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112894646848283455358560451 169341970272425183037840677)
  ·
    refine ⟨31751619426079721819595127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 169341970272425183037840677 31751619426079721819595127)
    ·
      refine ⟨47627429139119582729392691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31751619426079721819595127 47627429139119582729392691)
      ·
        refine ⟨71441143708679374094089037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47627429139119582729392691 71441143708679374094089037)
        ·
          refine ⟨26790428890754765285283389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71441143708679374094089037 26790428890754765285283389)
          ·
            refine ⟨10046410834033036981981271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26790428890754765285283389 10046410834033036981981271)
            ·
              refine ⟨15069616251049555472971907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10046410834033036981981271 15069616251049555472971907)
              ·
                refine ⟨22604424376574333209457861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15069616251049555472971907 22604424376574333209457861)
                ·
                  refine ⟨4238329570607687476773349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22604424376574333209457861 4238329570607687476773349)
                  ·
                    refine ⟨794686794488941401895003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4238329570607687476773349 794686794488941401895003)
                    ·
                      rfl

theorem cell23_4642941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 1, 4, 4].length) (baseStart_4642941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4642941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4642941 prefixEnd_4642941 := by exact prefixLift 4642941
  have htrace : WordTrace (prefixWord ++ tailWord_4642941) baseStart_4642941 baseEnd_4642941 := by
    simpa [prefixWord, tailWord_4642941, baseEnd_4642941] using wordTrace_append hprefix tailTrace_4642941
  have hstable : (prefixWord ++ tailWord_4642941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4642941).length < 2 ^ (prefixWord ++ tailWord_4642941).sum := by decide
  have hdescent : baseEnd_4642941 < baseStart_4642941 := by decide
  rcases family_descends (prefixWord ++ tailWord_4642941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4642958 : List Nat := [4, 1, 1, 3, 3, 2, 1, 1, 1, 6]
def baseStart_4642958 : Nat := 118140960795 + 4642958 * 2 ^ 59
def prefixEnd_4642958 : Nat := 4983230072969 + 3 ^ 40 * 4642958 * 2
def baseEnd_4642958 : Nat := 794689704212650213057477

theorem tailTrace_4642958 : CollatzResearch.WordTrace tailWord_4642958 prefixEnd_4642958 794689704212650213057477 := by
  unfold tailWord_4642958
  simp only [CollatzResearch.WordTrace]
  refine ⟨21167823789170449367651191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112895060208909063294139685 21167823789170449367651191)
  ·
    refine ⟨31751735683755674051476787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21167823789170449367651191 31751735683755674051476787)
    ·
      refine ⟨47627603525633511077215181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31751735683755674051476787 47627603525633511077215181)
      ·
        refine ⟨17860351322112566653955693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47627603525633511077215181 17860351322112566653955693)
        ·
          refine ⟨6697631745792212495233385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17860351322112566653955693 6697631745792212495233385)
          ·
            refine ⟨5023223809344159371425039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6697631745792212495233385 5023223809344159371425039)
            ·
              refine ⟨7534835714016239057137559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5023223809344159371425039 7534835714016239057137559)
              ·
                refine ⟨11302253571024358585706339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7534835714016239057137559 11302253571024358585706339)
                ·
                  refine ⟨16953380356536537878559509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11302253571024358585706339 16953380356536537878559509)
                  ·
                    refine ⟨794689704212650213057477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16953380356536537878559509 794689704212650213057477)
                    ·
                      rfl

theorem cell23_4642958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 1, 1, 1, 6].length) (baseStart_4642958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4642958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4642958 prefixEnd_4642958 := by exact prefixLift 4642958
  have htrace : WordTrace (prefixWord ++ tailWord_4642958) baseStart_4642958 baseEnd_4642958 := by
    simpa [prefixWord, tailWord_4642958, baseEnd_4642958] using wordTrace_append hprefix tailTrace_4642958
  have hstable : (prefixWord ++ tailWord_4642958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4642958).length < 2 ^ (prefixWord ++ tailWord_4642958).sum := by decide
  have hdescent : baseEnd_4642958 < baseStart_4642958 := by decide
  rcases family_descends (prefixWord ++ tailWord_4642958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4642981 : List Nat := [1, 3, 1, 2, 1, 3, 1, 1, 6, 1, 3]
def baseStart_4642981 : Nat := 118140960795 + 4642981 * 2 ^ 59
def prefixEnd_4642981 : Nat := 4983230072969 + 3 ^ 40 * 4642981 * 2
def baseEnd_4642981 : Nat := 2384080922693004049184825

theorem tailTrace_4642981 : CollatzResearch.WordTrace tailWord_4642981 prefixEnd_4642981 2384080922693004049184825 := by
  unfold tailWord_4642981
  simp only [CollatzResearch.WordTrace]
  refine ⟨169343429192280269869296797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112895619461520179912864531 169343429192280269869296797)
  ·
    refine ⟨63503785947105101200986299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 169343429192280269869296797 63503785947105101200986299)
    ·
      refine ⟨95255678920657651801479449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63503785947105101200986299 95255678920657651801479449)
      ·
        refine ⟨71441759190493238851109587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95255678920657651801479449 71441759190493238851109587)
        ·
          refine ⟨107162638785739858276664381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71441759190493238851109587 107162638785739858276664381)
          ·
            refine ⟨40185989544652446853749143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 107162638785739858276664381 40185989544652446853749143)
            ·
              refine ⟨60278984316978670280623715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40185989544652446853749143 60278984316978670280623715)
              ·
                refine ⟨90418476475468005420935573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60278984316978670280623715 90418476475468005420935573)
                ·
                  refine ⟨4238366084787562754106355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 90418476475468005420935573 4238366084787562754106355)
                  ·
                    refine ⟨6357549127181344131159533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4238366084787562754106355 6357549127181344131159533)
                    ·
                      refine ⟨2384080922693004049184825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6357549127181344131159533 2384080922693004049184825)
                      ·
                        rfl

theorem cell23_4642981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 6, 1, 3].length) (baseStart_4642981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4642981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4642981 prefixEnd_4642981 := by exact prefixLift 4642981
  have htrace : WordTrace (prefixWord ++ tailWord_4642981) baseStart_4642981 baseEnd_4642981 := by
    simpa [prefixWord, tailWord_4642981, baseEnd_4642981] using wordTrace_append hprefix tailTrace_4642981
  have hstable : (prefixWord ++ tailWord_4642981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4642981).length < 2 ^ (prefixWord ++ tailWord_4642981).sum := by decide
  have hdescent : baseEnd_4642981 < baseStart_4642981 := by decide
  rcases family_descends (prefixWord ++ tailWord_4642981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4642991 : List Nat := [1, 1, 2, 1, 2, 3, 1, 2, 5, 3, 2]
def baseStart_4642991 : Nat := 118140960795 + 4642991 * 2 ^ 59
def prefixEnd_4642991 : Nat := 4983230072969 + 3 ^ 40 * 4642991 * 2
def baseEnd_4642991 : Nat := 2384086057499549010059779

theorem tailTrace_4642991 : CollatzResearch.WordTrace tailWord_4642991 prefixEnd_4642991 2384086057499549010059779 := by
  unfold tailWord_4642991
  simp only [CollatzResearch.WordTrace]
  refine ⟨169343793922244041577160827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112895862614829361051440551 169343793922244041577160827)
  ·
    refine ⟨254015690883366062365741241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169343793922244041577160827 254015690883366062365741241)
    ·
      refine ⟨190511768162524546774305931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 254015690883366062365741241 190511768162524546774305931)
      ·
        refine ⟨285767652243786820161458897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190511768162524546774305931 285767652243786820161458897)
        ·
          refine ⟨214325739182840115121094173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 285767652243786820161458897 214325739182840115121094173)
          ·
            refine ⟨80372152193565043170410315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 214325739182840115121094173 80372152193565043170410315)
            ·
              refine ⟨120558228290347564755615473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80372152193565043170410315 120558228290347564755615473)
              ·
                refine ⟨90418671217760673566711605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 120558228290347564755615473 90418671217760673566711605)
                ·
                  refine ⟨8476750426665063146879213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 90418671217760673566711605 8476750426665063146879213)
                  ·
                    refine ⟨3178781409999398680079705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8476750426665063146879213 3178781409999398680079705)
                    ·
                      refine ⟨2384086057499549010059779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3178781409999398680079705 2384086057499549010059779)
                      ·
                        rfl

theorem cell23_4642991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 5, 3, 2].length) (baseStart_4642991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4642991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4642991 prefixEnd_4642991 := by exact prefixLift 4642991
  have htrace : WordTrace (prefixWord ++ tailWord_4642991) baseStart_4642991 baseEnd_4642991 := by
    simpa [prefixWord, tailWord_4642991, baseEnd_4642991] using wordTrace_append hprefix tailTrace_4642991
  have hstable : (prefixWord ++ tailWord_4642991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4642991).length < 2 ^ (prefixWord ++ tailWord_4642991).sum := by decide
  have hdescent : baseEnd_4642991 < baseStart_4642991 := by decide
  rcases family_descends (prefixWord ++ tailWord_4642991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4642994 : List Nat := [3, 2, 1, 1, 1, 3, 1, 2, 2, 2, 5]
def baseStart_4642994 : Nat := 118140960795 + 4642994 * 2 ^ 59
def prefixEnd_4642994 : Nat := 4983230072969 + 3 ^ 40 * 4642994 * 2
def baseEnd_4642994 : Nat := 2384087597941512498322265

theorem tailTrace_4642994 : CollatzResearch.WordTrace tailWord_4642994 prefixEnd_4642994 2384087597941512498322265 := by
  unfold tailWord_4642994
  simp only [CollatzResearch.WordTrace]
  refine ⟨42335975835308293272380009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112895935560822115393013357 42335975835308293272380009)
  ·
    refine ⟨31751981876481219954285007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42335975835308293272380009 31751981876481219954285007)
    ·
      refine ⟨47627972814721829931427511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31751981876481219954285007 47627972814721829931427511)
      ·
        refine ⟨71441959222082744897141267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47627972814721829931427511 71441959222082744897141267)
        ·
          refine ⟨107162938833124117345711901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71441959222082744897141267 107162938833124117345711901)
          ·
            refine ⟨40186102062421544004641963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 107162938833124117345711901 40186102062421544004641963)
            ·
              refine ⟨60279153093632316006962945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40186102062421544004641963 60279153093632316006962945)
              ·
                refine ⟨45209364820224237005222209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60279153093632316006962945 45209364820224237005222209)
                ·
                  refine ⟨33907023615168177753916657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45209364820224237005222209 33907023615168177753916657)
                  ·
                    refine ⟨25430267711376133315437493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33907023615168177753916657 25430267711376133315437493)
                    ·
                      refine ⟨2384087597941512498322265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25430267711376133315437493 2384087597941512498322265)
                      ·
                        rfl

theorem cell23_4642994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 2, 2, 2, 5].length) (baseStart_4642994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4642994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4642994 prefixEnd_4642994 := by exact prefixLift 4642994
  have htrace : WordTrace (prefixWord ++ tailWord_4642994) baseStart_4642994 baseEnd_4642994 := by
    simpa [prefixWord, tailWord_4642994, baseEnd_4642994] using wordTrace_append hprefix tailTrace_4642994
  have hstable : (prefixWord ++ tailWord_4642994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4642994).length < 2 ^ (prefixWord ++ tailWord_4642994).sum := by decide
  have hdescent : baseEnd_4642994 < baseStart_4642994 := by decide
  rcases family_descends (prefixWord ++ tailWord_4642994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4643009 : List Nat := [1, 2, 6, 1, 3, 1, 2, 1, 2, 4]
def baseStart_4643009 : Nat := 118140960795 + 4643009 * 2 ^ 59
def prefixEnd_4643009 : Nat := 4983230072969 + 3 ^ 40 * 4643009 * 2
def baseEnd_4643009 : Nat := 794698433383776646544899

theorem tailTrace_4643009 : CollatzResearch.WordTrace tailWord_4643009 prefixEnd_4643009 794698433383776646544899 := by
  unfold tailWord_4643009
  simp only [CollatzResearch.WordTrace]
  refine ⟨169344450436178830651316081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112896300290785887100877387 169344450436178830651316081)
  ·
    refine ⟨127008337827134122988487061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169344450436178830651316081 127008337827134122988487061)
    ·
      refine ⟨5953515835646912015085331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 127008337827134122988487061 5953515835646912015085331)
      ·
        refine ⟨8930273753470368022627997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5953515835646912015085331 8930273753470368022627997)
        ·
          refine ⟨3348852657551388008485499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8930273753470368022627997 3348852657551388008485499)
          ·
            refine ⟨5023278986327082012728249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3348852657551388008485499 5023278986327082012728249)
            ·
              refine ⟨3767459239745311509546187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5023278986327082012728249 3767459239745311509546187)
              ·
                refine ⟨5651188859617967264319281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3767459239745311509546187 5651188859617967264319281)
                ·
                  refine ⟨4238391644713475448239461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5651188859617967264319281 4238391644713475448239461)
                  ·
                    refine ⟨794698433383776646544899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4238391644713475448239461 794698433383776646544899)
                    ·
                      rfl

theorem cell23_4643009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_4643009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4643009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4643009 prefixEnd_4643009 := by exact prefixLift 4643009
  have htrace : WordTrace (prefixWord ++ tailWord_4643009) baseStart_4643009 baseEnd_4643009 := by
    simpa [prefixWord, tailWord_4643009, baseEnd_4643009] using wordTrace_append hprefix tailTrace_4643009
  have hstable : (prefixWord ++ tailWord_4643009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4643009).length < 2 ^ (prefixWord ++ tailWord_4643009).sum := by decide
  have hdescent : baseEnd_4643009 < baseStart_4643009 := by decide
  rcases family_descends (prefixWord ++ tailWord_4643009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4643055 : List Nat := [1, 1, 2, 1, 6, 1, 1, 4, 2, 2, 2]
def baseStart_4643055 : Nat := 118140960795 + 4643055 * 2 ^ 59
def prefixEnd_4643055 : Nat := 4983230072969 + 3 ^ 40 * 4643055 * 2
def baseEnd_4643055 : Nat := 2384118920261436759659485

theorem tailTrace_4643055 : CollatzResearch.WordTrace tailWord_4643055 prefixEnd_4643055 2384118920261436759659485 := by
  unfold tailWord_4643055
  simp only [CollatzResearch.WordTrace]
  refine ⟨169346128194012180507490619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112897418796008120338327079 169346128194012180507490619)
  ·
    refine ⟨254019192291018270761235929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169346128194012180507490619 254019192291018270761235929)
    ·
      refine ⟨190514394218263703070926947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 254019192291018270761235929 190514394218263703070926947)
      ·
        refine ⟨285771591327395554606390421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190514394218263703070926947 285771591327395554606390421)
        ·
          refine ⟨13395543343471666622174551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 285771591327395554606390421 13395543343471666622174551)
          ·
            refine ⟨20093315015207499933261827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13395543343471666622174551 20093315015207499933261827)
            ·
              refine ⟨30139972522811249899892741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20093315015207499933261827 30139972522811249899892741)
              ·
                refine ⟨5651244848027109356229889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30139972522811249899892741 5651244848027109356229889)
                ·
                  refine ⟨4238433636020332017172417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5651244848027109356229889 4238433636020332017172417)
                  ·
                    refine ⟨3178825227015249012879313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4238433636020332017172417 3178825227015249012879313)
                    ·
                      refine ⟨2384118920261436759659485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3178825227015249012879313 2384118920261436759659485)
                      ·
                        rfl

theorem cell23_4643055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 4, 2, 2, 2].length) (baseStart_4643055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4643055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4643055 prefixEnd_4643055 := by exact prefixLift 4643055
  have htrace : WordTrace (prefixWord ++ tailWord_4643055) baseStart_4643055 baseEnd_4643055 := by
    simpa [prefixWord, tailWord_4643055, baseEnd_4643055] using wordTrace_append hprefix tailTrace_4643055
  have hstable : (prefixWord ++ tailWord_4643055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4643055).length < 2 ^ (prefixWord ++ tailWord_4643055).sum := by decide
  have hdescent : baseEnd_4643055 < baseStart_4643055 := by decide
  rcases family_descends (prefixWord ++ tailWord_4643055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4643071 : List Nat := [1, 1, 2, 2, 1, 4, 3, 1, 2, 3, 3]
def baseStart_4643071 : Nat := 118140960795 + 4643071 * 2 ^ 59
def prefixEnd_4643071 : Nat := 4983230072969 + 3 ^ 40 * 4643071 * 2
def baseEnd_4643071 : Nat := 2384127135951908697059411

theorem tailTrace_4643071 : CollatzResearch.WordTrace tailWord_4643071 prefixEnd_4643071 2384127135951908697059411 := by
  unfold tailWord_4643071
  simp only [CollatzResearch.WordTrace]
  refine ⟨169346711761954215240073067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112897807841302810160048711 169346711761954215240073067)
  ·
    refine ⟨254020067642931322860109601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169346711761954215240073067 254020067642931322860109601)
    ·
      refine ⟨190515050732198492145082201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 254020067642931322860109601 190515050732198492145082201)
      ·
        refine ⟨142886288049148869108811651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 190515050732198492145082201 142886288049148869108811651)
        ·
          refine ⟨214329432073723303663217477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142886288049148869108811651 214329432073723303663217477)
          ·
            refine ⟨40186768513823119436853277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 214329432073723303663217477 40186768513823119436853277)
            ·
              refine ⟨15070038192683669788819979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40186768513823119436853277 15070038192683669788819979)
              ·
                refine ⟨22605057289025504683229969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15070038192683669788819979 22605057289025504683229969)
                ·
                  refine ⟨16953792966769128512422477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22605057289025504683229969 16953792966769128512422477)
                  ·
                    refine ⟨6357672362538423192158429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16953792966769128512422477 6357672362538423192158429)
                    ·
                      refine ⟨2384127135951908697059411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6357672362538423192158429 2384127135951908697059411)
                      ·
                        rfl

theorem cell23_4643071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 1, 2, 3, 3].length) (baseStart_4643071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4643071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4643071 prefixEnd_4643071 := by exact prefixLift 4643071
  have htrace : WordTrace (prefixWord ++ tailWord_4643071) baseStart_4643071 baseEnd_4643071 := by
    simpa [prefixWord, tailWord_4643071, baseEnd_4643071] using wordTrace_append hprefix tailTrace_4643071
  have hstable : (prefixWord ++ tailWord_4643071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4643071).length < 2 ^ (prefixWord ++ tailWord_4643071).sum := by decide
  have hdescent : baseEnd_4643071 < baseStart_4643071 := by decide
  rcases family_descends (prefixWord ++ tailWord_4643071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4643128 : List Nat := [2, 1, 2, 1, 3, 1, 4, 1, 2, 4, 2]
def baseStart_4643128 : Nat := 118140960795 + 4643128 * 2 ^ 59
def prefixEnd_4643128 : Nat := 4983230072969 + 3 ^ 40 * 4643128 * 2
def baseEnd_4643128 : Nat := 2384156404349214974046649

theorem tailTrace_4643128 : CollatzResearch.WordTrace tailWord_4643128 prefixEnd_4643128 2384156404349214974046649 := by
  unfold tailWord_4643128
  simp only [CollatzResearch.WordTrace]
  refine ⟨84674395361373856987449019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112899193815165142649932025 84674395361373856987449019)
  ·
    refine ⟨127011593042060785481173529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84674395361373856987449019 127011593042060785481173529)
    ·
      refine ⟨95258694781545589110880147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127011593042060785481173529 95258694781545589110880147)
      ·
        refine ⟨142888042172318383666320221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95258694781545589110880147 142888042172318383666320221)
        ·
          refine ⟨53583015814619393874870083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 142888042172318383666320221 53583015814619393874870083)
          ·
            refine ⟨80374523721929090812305125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53583015814619393874870083 80374523721929090812305125)
            ·
              refine ⟨15070223197861704527307211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 80374523721929090812305125 15070223197861704527307211)
              ·
                refine ⟨22605334796792556790960817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15070223197861704527307211 22605334796792556790960817)
                ·
                  refine ⟨16954001097594417593220613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22605334796792556790960817 16954001097594417593220613)
                  ·
                    refine ⟨3178875205798953298728865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16954001097594417593220613 3178875205798953298728865)
                    ·
                      refine ⟨2384156404349214974046649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3178875205798953298728865 2384156404349214974046649)
                      ·
                        rfl

theorem cell23_4643128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 1, 2, 4, 2].length) (baseStart_4643128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4643128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4643128 prefixEnd_4643128 := by exact prefixLift 4643128
  have htrace : WordTrace (prefixWord ++ tailWord_4643128) baseStart_4643128 baseEnd_4643128 := by
    simpa [prefixWord, tailWord_4643128, baseEnd_4643128] using wordTrace_append hprefix tailTrace_4643128
  have hstable : (prefixWord ++ tailWord_4643128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4643128).length < 2 ^ (prefixWord ++ tailWord_4643128).sum := by decide
  have hdescent : baseEnd_4643128 < baseStart_4643128 := by decide
  rcases family_descends (prefixWord ++ tailWord_4643128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4643148 : List Nat := [2, 2, 1, 3, 2, 1, 2, 3, 2, 2, 3]
def baseStart_4643148 : Nat := 118140960795 + 4643148 * 2 ^ 59
def prefixEnd_4643148 : Nat := 4983230072969 + 3 ^ 40 * 4643148 * 2
def baseEnd_4643148 : Nat := 2384166673962304895796557

theorem tailTrace_4643148 : CollatzResearch.WordTrace tailWord_4643148 prefixEnd_4643148 2384166673962304895796557 := by
  unfold tailWord_4643148
  simp only [CollatzResearch.WordTrace]
  refine ⟨84674760091337628695313049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112899680121783504927084065 84674760091337628695313049)
  ·
    refine ⟨63506070068503221521484787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84674760091337628695313049 63506070068503221521484787)
    ·
      refine ⟨95259105102754832282227181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63506070068503221521484787 95259105102754832282227181)
      ·
        refine ⟨35722164413533062105835193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95259105102754832282227181 35722164413533062105835193)
        ·
          refine ⟨26791623310149796579376395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35722164413533062105835193 26791623310149796579376395)
          ·
            refine ⟨40187434965224694869064593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26791623310149796579376395 40187434965224694869064593)
            ·
              refine ⟨30140576223918521151798445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40187434965224694869064593 30140576223918521151798445)
              ·
                refine ⟨11302716083969445431924417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30140576223918521151798445 11302716083969445431924417)
                ·
                  refine ⟨8477037062977084073943313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11302716083969445431924417 8477037062977084073943313)
                  ·
                    refine ⟨6357777797232813055457485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8477037062977084073943313 6357777797232813055457485)
                    ·
                      refine ⟨2384166673962304895796557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6357777797232813055457485 2384166673962304895796557)
                      ·
                        rfl

theorem cell23_4643148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 3, 2, 2, 3].length) (baseStart_4643148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4643148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4643148 prefixEnd_4643148 := by exact prefixLift 4643148
  have htrace : WordTrace (prefixWord ++ tailWord_4643148) baseStart_4643148 baseEnd_4643148 := by
    simpa [prefixWord, tailWord_4643148, baseEnd_4643148] using wordTrace_append hprefix tailTrace_4643148
  have hstable : (prefixWord ++ tailWord_4643148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4643148).length < 2 ^ (prefixWord ++ tailWord_4643148).sum := by decide
  have hdescent : baseEnd_4643148 < baseStart_4643148 := by decide
  rcases family_descends (prefixWord ++ tailWord_4643148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4643172 : List Nat := [2, 3, 1, 1, 3, 1, 5, 2, 1, 4]
def baseStart_4643172 : Nat := 118140960795 + 4643172 * 2 ^ 59
def prefixEnd_4643172 : Nat := 4983230072969 + 3 ^ 40 * 4643172 * 2
def baseEnd_4643172 : Nat := 794726332499337600632149

theorem tailTrace_4643172 : CollatzResearch.WordTrace tailWord_4643172 prefixEnd_4643172 794726332499337600632149 := by
  unfold tailWord_4643172
  simp only [CollatzResearch.WordTrace]
  refine ⟨84675197767294154744749885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112900263689725539659666513 84675197767294154744749885)
  ·
    refine ⟨31753199162735308029281207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84675197767294154744749885 31753199162735308029281207)
    ·
      refine ⟨47629798744102962043921811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31753199162735308029281207 47629798744102962043921811)
      ·
        refine ⟨71444698116154443065882717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47629798744102962043921811 71444698116154443065882717)
        ·
          refine ⟨26791761793557916149706019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71444698116154443065882717 26791761793557916149706019)
          ·
            refine ⟨40187642690336874224559029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26791761793557916149706019 40187642690336874224559029)
            ·
              refine ⟨3767591502219081958552409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40187642690336874224559029 3767591502219081958552409)
              ·
                refine ⟨2825693626664311468914307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3767591502219081958552409 2825693626664311468914307)
                ·
                  refine ⟨4238540439996467203371461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2825693626664311468914307 4238540439996467203371461)
                  ·
                    refine ⟨794726332499337600632149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4238540439996467203371461 794726332499337600632149)
                    ·
                      rfl

theorem cell23_4643172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 5, 2, 1, 4].length) (baseStart_4643172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4643172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4643172 prefixEnd_4643172 := by exact prefixLift 4643172
  have htrace : WordTrace (prefixWord ++ tailWord_4643172) baseStart_4643172 baseEnd_4643172 := by
    simpa [prefixWord, tailWord_4643172, baseEnd_4643172] using wordTrace_append hprefix tailTrace_4643172
  have hstable : (prefixWord ++ tailWord_4643172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4643172).length < 2 ^ (prefixWord ++ tailWord_4643172).sum := by decide
  have hdescent : baseEnd_4643172 < baseStart_4643172 := by decide
  rcases family_descends (prefixWord ++ tailWord_4643172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4643211 : List Nat := [1, 1, 1, 1, 4, 4, 1, 1, 3, 6]
def baseStart_4643211 : Nat := 118140960795 + 4643211 * 2 ^ 59
def prefixEnd_4643211 : Nat := 4983230072969 + 3 ^ 40 * 4643211 * 2
def baseEnd_4643211 : Nat := 794733007747846049769589

theorem tailTrace_4643211 : CollatzResearch.WordTrace tailWord_4643211 prefixEnd_4643211 794733007747846049769589 := by
  unfold tailWord_4643211
  simp only [CollatzResearch.WordTrace]
  refine ⟨169351817981447019150169487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112901211987631346100112991 169351817981447019150169487)
  ·
    refine ⟨254027726972170528725254231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169351817981447019150169487 254027726972170528725254231)
    ·
      refine ⟨381041590458255793087881347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 254027726972170528725254231 381041590458255793087881347)
      ·
        refine ⟨571562385687383689631822021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 381041590458255793087881347 571562385687383689631822021)
        ·
          refine ⟨107167947316384441805966629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 571562385687383689631822021 107167947316384441805966629)
          ·
            refine ⟨20093990121822082838618743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 107167947316384441805966629 20093990121822082838618743)
            ·
              refine ⟨30140985182733124257928115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20093990121822082838618743 30140985182733124257928115)
              ·
                refine ⟨45211477774099686386892173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30140985182733124257928115 45211477774099686386892173)
                ·
                  refine ⟨16954304165287382395084565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45211477774099686386892173 16954304165287382395084565)
                  ·
                    refine ⟨794733007747846049769589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16954304165287382395084565 794733007747846049769589)
                    ·
                      rfl

theorem cell23_4643211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 1, 3, 6].length) (baseStart_4643211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4643211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4643211 prefixEnd_4643211 := by exact prefixLift 4643211
  have htrace : WordTrace (prefixWord ++ tailWord_4643211) baseStart_4643211 baseEnd_4643211 := by
    simpa [prefixWord, tailWord_4643211, baseEnd_4643211] using wordTrace_append hprefix tailTrace_4643211
  have hstable : (prefixWord ++ tailWord_4643211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4643211).length < 2 ^ (prefixWord ++ tailWord_4643211).sum := by decide
  have hdescent : baseEnd_4643211 < baseStart_4643211 := by decide
  rcases family_descends (prefixWord ++ tailWord_4643211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4643229 : List Nat := [1, 4, 2, 1, 4, 1, 1, 4, 1, 1, 3]
def baseStart_4643229 : Nat := 118140960795 + 4643229 * 2 ^ 59
def prefixEnd_4643229 : Nat := 4983230072969 + 3 ^ 40 * 4643229 * 2
def baseEnd_4643229 : Nat := 2384208265895319078883685

theorem tailTrace_4643229 : CollatzResearch.WordTrace tailWord_4643229 prefixEnd_4643229 2384208265895319078883685 := by
  unfold tailWord_4643229
  simp only [CollatzResearch.WordTrace]
  refine ⟨169352474495381808224324741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112901649663587872149549827 169352474495381808224324741)
  ·
    refine ⟨31753588967884089042060889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 169352474495381808224324741 31753588967884089042060889)
    ·
      refine ⟨23815191725913066781545667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31753588967884089042060889 23815191725913066781545667)
      ·
        refine ⟨35722787588869600172318501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23815191725913066781545667 35722787588869600172318501)
        ·
          refine ⟨6698022672913050032309719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35722787588869600172318501 6698022672913050032309719)
          ·
            refine ⟨10047034009369575048464579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6698022672913050032309719 10047034009369575048464579)
            ·
              refine ⟨15070551014054362572696869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10047034009369575048464579 15070551014054362572696869)
              ·
                refine ⟨2825728315135192982380663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15070551014054362572696869 2825728315135192982380663)
                ·
                  refine ⟨4238592472702789473570995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2825728315135192982380663 4238592472702789473570995)
                  ·
                    refine ⟨6357888709054184210356493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4238592472702789473570995 6357888709054184210356493)
                    ·
                      refine ⟨2384208265895319078883685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6357888709054184210356493 2384208265895319078883685)
                      ·
                        rfl

theorem cell23_4643229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 4, 1, 1, 3].length) (baseStart_4643229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4643229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4643229 prefixEnd_4643229 := by exact prefixLift 4643229
  have htrace : WordTrace (prefixWord ++ tailWord_4643229) baseStart_4643229 baseEnd_4643229 := by
    simpa [prefixWord, tailWord_4643229, baseEnd_4643229] using wordTrace_append hprefix tailTrace_4643229
  have hstable : (prefixWord ++ tailWord_4643229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4643229).length < 2 ^ (prefixWord ++ tailWord_4643229).sum := by decide
  have hdescent : baseEnd_4643229 < baseStart_4643229 := by decide
  rcases family_descends (prefixWord ++ tailWord_4643229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4643272 : List Nat := [2, 1, 3, 1, 3, 2, 4, 1, 1, 2, 3]
def baseStart_4643272 : Nat := 118140960795 + 4643272 * 2 ^ 59
def prefixEnd_4643272 : Nat := 4983230072969 + 3 ^ 40 * 4643272 * 2
def baseEnd_4643272 : Nat := 2384230345563462410645987

theorem tailTrace_4643272 : CollatzResearch.WordTrace tailWord_4643272 prefixEnd_4643272 2384230345563462410645987 := by
  unfold tailWord_4643272
  simp only [CollatzResearch.WordTrace]
  refine ⟨84677021417113013284070035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112902695222817351045426713 84677021417113013284070035)
  ·
    refine ⟨127015532125669519926105053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84677021417113013284070035 127015532125669519926105053)
    ·
      refine ⟨47630824547126069972289395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 127015532125669519926105053 47630824547126069972289395)
      ·
        refine ⟨71446236820689104958434093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47630824547126069972289395 71446236820689104958434093)
        ·
          refine ⟨26792338807758414359412785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71446236820689104958434093 26792338807758414359412785)
          ·
            refine ⟨20094254105818810769559589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26792338807758414359412785 20094254105818810769559589)
            ·
              refine ⟨3767672644841027019292423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20094254105818810769559589 3767672644841027019292423)
              ·
                refine ⟨5651508967261540528938635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3767672644841027019292423 5651508967261540528938635)
                ·
                  refine ⟨8477263450892310793407953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5651508967261540528938635 8477263450892310793407953)
                  ·
                    refine ⟨6357947588169233095055965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8477263450892310793407953 6357947588169233095055965)
                    ·
                      refine ⟨2384230345563462410645987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6357947588169233095055965 2384230345563462410645987)
                      ·
                        rfl

theorem cell23_4643272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 4, 1, 1, 2, 3].length) (baseStart_4643272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4643272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4643272 prefixEnd_4643272 := by exact prefixLift 4643272
  have htrace : WordTrace (prefixWord ++ tailWord_4643272) baseStart_4643272 baseEnd_4643272 := by
    simpa [prefixWord, tailWord_4643272, baseEnd_4643272] using wordTrace_append hprefix tailTrace_4643272
  have hstable : (prefixWord ++ tailWord_4643272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4643272).length < 2 ^ (prefixWord ++ tailWord_4643272).sum := by decide
  have hdescent : baseEnd_4643272 < baseStart_4643272 := by decide
  rcases family_descends (prefixWord ++ tailWord_4643272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4643286 : List Nat := [5, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2]
def baseStart_4643286 : Nat := 118140960795 + 4643286 * 2 ^ 59
def prefixEnd_4643286 : Nat := 4983230072969 + 3 ^ 40 * 4643286 * 2
def baseEnd_4643286 : Nat := 2384237534292625355870923

theorem tailTrace_4643286 : CollatzResearch.WordTrace tailWord_4643286 prefixEnd_4643286 2384237534292625355870923 := by
  unfold tailWord_4643286
  simp only [CollatzResearch.WordTrace]
  refine ⟨10584659591010956684946857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 112903035637450204639433141 10584659591010956684946857)
  ·
    refine ⟨7938494693258217513710143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10584659591010956684946857 7938494693258217513710143)
    ·
      refine ⟨11907742039887326270565215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7938494693258217513710143 11907742039887326270565215)
      ·
        refine ⟨17861613059830989405847823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11907742039887326270565215 17861613059830989405847823)
        ·
          refine ⟨26792419589746484108771735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17861613059830989405847823 26792419589746484108771735)
          ·
            refine ⟨40188629384619726163157603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26792419589746484108771735 40188629384619726163157603)
            ·
              refine ⟨60282944076929589244736405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40188629384619726163157603 60282944076929589244736405)
              ·
                refine ⟨2825763003606074495847019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 60282944076929589244736405 2825763003606074495847019)
                ·
                  refine ⟨4238644505409111743770529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2825763003606074495847019 4238644505409111743770529)
                  ·
                    refine ⟨3178983379056833807827897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4238644505409111743770529 3178983379056833807827897)
                    ·
                      refine ⟨2384237534292625355870923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3178983379056833807827897 2384237534292625355870923)
                      ·
                        rfl

theorem cell23_4643286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2].length) (baseStart_4643286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4643286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4643286 prefixEnd_4643286 := by exact prefixLift 4643286
  have htrace : WordTrace (prefixWord ++ tailWord_4643286) baseStart_4643286 baseEnd_4643286 := by
    simpa [prefixWord, tailWord_4643286, baseEnd_4643286] using wordTrace_append hprefix tailTrace_4643286
  have hstable : (prefixWord ++ tailWord_4643286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4643286).length < 2 ^ (prefixWord ++ tailWord_4643286).sum := by decide
  have hdescent : baseEnd_4643286 < baseStart_4643286 := by decide
  rcases family_descends (prefixWord ++ tailWord_4643286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4643312 : List Nat := [2, 1, 1, 1, 3, 3, 4, 2, 1, 3, 2]
def baseStart_4643312 : Nat := 118140960795 + 4643312 * 2 ^ 59
def prefixEnd_4643312 : Nat := 4983230072969 + 3 ^ 40 * 4643312 * 2
def baseEnd_4643312 : Nat := 2384250884789642254145803

theorem tailTrace_4643312 : CollatzResearch.WordTrace tailWord_4643312 prefixEnd_4643312 2384250884789642254145803 := by
  unfold tailWord_4643312
  simp only [CollatzResearch.WordTrace]
  refine ⟨84677750877040556699798095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112903667836054075599730793 84677750877040556699798095)
  ·
    refine ⟨127016626315560835049697143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84677750877040556699798095 127016626315560835049697143)
    ·
      refine ⟨190524939473341252574545715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127016626315560835049697143 190524939473341252574545715)
      ·
        refine ⟨285787409210011878861818573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190524939473341252574545715 285787409210011878861818573)
        ·
          refine ⟨107170278453754454573181965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 285787409210011878861818573 107170278453754454573181965)
          ·
            refine ⟨40188854420157920464943237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 107170278453754454573181965 40188854420157920464943237)
            ·
              refine ⟨7535410203779610087176857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40188854420157920464943237 7535410203779610087176857)
              ·
                refine ⟨5651557652834707565382643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7535410203779610087176857 5651557652834707565382643)
                ·
                  refine ⟨8477336479252061348073965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5651557652834707565382643 8477336479252061348073965)
                  ·
                    refine ⟨3179001179719523005527737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8477336479252061348073965 3179001179719523005527737)
                    ·
                      refine ⟨2384250884789642254145803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3179001179719523005527737 2384250884789642254145803)
                      ·
                        rfl

theorem cell23_4643312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 4, 2, 1, 3, 2].length) (baseStart_4643312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4643312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4643312 prefixEnd_4643312 := by exact prefixLift 4643312
  have htrace : WordTrace (prefixWord ++ tailWord_4643312) baseStart_4643312 baseEnd_4643312 := by
    simpa [prefixWord, tailWord_4643312, baseEnd_4643312] using wordTrace_append hprefix tailTrace_4643312
  have hstable : (prefixWord ++ tailWord_4643312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4643312).length < 2 ^ (prefixWord ++ tailWord_4643312).sum := by decide
  have hdescent : baseEnd_4643312 < baseStart_4643312 := by decide
  rcases family_descends (prefixWord ++ tailWord_4643312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4643325 : List Nat := [1, 4, 1, 1, 1, 3, 2, 1, 3, 4, 2]
def baseStart_4643325 : Nat := 118140960795 + 4643325 * 2 ^ 59
def prefixEnd_4643325 : Nat := 4983230072969 + 3 ^ 40 * 4643325 * 2
def baseEnd_4643325 : Nat := 2384257560038150703283243

theorem tailTrace_4643325 : CollatzResearch.WordTrace tailWord_4643325 prefixEnd_4643325 2384257560038150703283243 := by
  unfold tailWord_4643325
  simp only [CollatzResearch.WordTrace]
  refine ⟨169355975903034016619819429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112903983935356011079879619 169355975903034016619819429)
  ·
    refine ⟨31754245481818878116216143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 169355975903034016619819429 31754245481818878116216143)
    ·
      refine ⟨47631368222728317174324215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31754245481818878116216143 47631368222728317174324215)
      ·
        refine ⟨71447052334092475761486323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47631368222728317174324215 71447052334092475761486323)
        ·
          refine ⟨107170578501138713642229485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71447052334092475761486323 107170578501138713642229485)
          ·
            refine ⟨40188966937927017615836057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 107170578501138713642229485 40188966937927017615836057)
            ·
              refine ⟨30141725203445263211877043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40188966937927017615836057 30141725203445263211877043)
              ·
                refine ⟨45212587805167894817815565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30141725203445263211877043 45212587805167894817815565)
                ·
                  refine ⟨16954720426937960556680837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45212587805167894817815565 16954720426937960556680837)
                  ·
                    refine ⟨3179010080050867604377657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16954720426937960556680837 3179010080050867604377657)
                    ·
                      refine ⟨2384257560038150703283243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3179010080050867604377657 2384257560038150703283243)
                      ·
                        rfl

theorem cell23_4643325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 1, 3, 4, 2].length) (baseStart_4643325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4643325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4643325 prefixEnd_4643325 := by exact prefixLift 4643325
  have htrace : WordTrace (prefixWord ++ tailWord_4643325) baseStart_4643325 baseEnd_4643325 := by
    simpa [prefixWord, tailWord_4643325, baseEnd_4643325] using wordTrace_append hprefix tailTrace_4643325
  have hstable : (prefixWord ++ tailWord_4643325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4643325).length < 2 ^ (prefixWord ++ tailWord_4643325).sum := by decide
  have hdescent : baseEnd_4643325 < baseStart_4643325 := by decide
  rcases family_descends (prefixWord ++ tailWord_4643325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4643378 : List Nat := [3, 2, 1, 1, 2, 1, 2, 3, 1, 7]
def baseStart_4643378 : Nat := 118140960795 + 4643378 * 2 ^ 59
def prefixEnd_4643378 : Nat := 4983230072969 + 3 ^ 40 * 4643378 * 2
def baseEnd_4643378 : Nat := 794761591504279665306833

theorem tailTrace_4643378 : CollatzResearch.WordTrace tailWord_4643378 prefixEnd_4643378 794761591504279665306833 := by
  unfold tailWord_4643378
  simp only [CollatzResearch.WordTrace]
  refine ⟨42339477242960501667874697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112905272647894671114332525 42339477242960501667874697)
  ·
    refine ⟨31754607932220376250906023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42339477242960501667874697 31754607932220376250906023)
    ·
      refine ⟨47631911898330564376359035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31754607932220376250906023 47631911898330564376359035)
      ·
        refine ⟨71447867847495846564538553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47631911898330564376359035 71447867847495846564538553)
        ·
          refine ⟨53585900885621884923403915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71447867847495846564538553 53585900885621884923403915)
          ·
            refine ⟨80378851328432827385105873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53585900885621884923403915 80378851328432827385105873)
            ·
              refine ⟨60284138496324620538829405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80378851328432827385105873 60284138496324620538829405)
              ·
                refine ⟨22606551936121732702061027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60284138496324620538829405 22606551936121732702061027)
                ·
                  refine ⟨33909827904182599053091541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22606551936121732702061027 33909827904182599053091541)
                  ·
                    refine ⟨794761591504279665306833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33909827904182599053091541 794761591504279665306833)
                    ·
                      rfl

theorem cell23_4643378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 3, 1, 7].length) (baseStart_4643378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4643378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4643378 prefixEnd_4643378 := by exact prefixLift 4643378
  have htrace : WordTrace (prefixWord ++ tailWord_4643378) baseStart_4643378 baseEnd_4643378 := by
    simpa [prefixWord, tailWord_4643378, baseEnd_4643378] using wordTrace_append hprefix tailTrace_4643378
  have hstable : (prefixWord ++ tailWord_4643378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4643378).length < 2 ^ (prefixWord ++ tailWord_4643378).sum := by decide
  have hdescent : baseEnd_4643378 < baseStart_4643378 := by decide
  rcases family_descends (prefixWord ++ tailWord_4643378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4643399 : List Nat := [1, 1, 4, 1, 4, 3, 2, 2, 5]
def baseStart_4643399 : Nat := 118140960795 + 4643399 * 2 ^ 59
def prefixEnd_4643399 : Nat := 4983230072969 + 3 ^ 40 * 4643399 * 2
def baseEnd_4643399 : Nat := 264921728622953712639767

theorem tailTrace_4643399 : CollatzResearch.WordTrace tailWord_4643399 prefixEnd_4643399 264921728622953712639767 := by
  unfold tailWord_4643399
  simp only [CollatzResearch.WordTrace]
  refine ⟨169358674904765927258013251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112905783269843951505342167 169358674904765927258013251)
  ·
    refine ⟨254038012357148890887019877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169358674904765927258013251 254038012357148890887019877)
    ·
      refine ⟨47632127316965417041316227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 254038012357148890887019877 47632127316965417041316227)
      ·
        refine ⟨71448190975448125561974341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47632127316965417041316227 71448190975448125561974341)
        ·
          refine ⟨13396535807896523542870189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71448190975448125561974341 13396535807896523542870189)
          ·
            refine ⟨5023700927961196328576321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13396535807896523542870189 5023700927961196328576321)
            ·
              refine ⟨3767775695970897246432241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5023700927961196328576321 3767775695970897246432241)
              ·
                refine ⟨2825831771978172934824181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3767775695970897246432241 2825831771978172934824181)
                ·
                  refine ⟨264921728622953712639767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2825831771978172934824181 264921728622953712639767)
                  ·
                    rfl

theorem cell23_4643399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 2, 2, 5].length) (baseStart_4643399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4643399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4643399 prefixEnd_4643399 := by exact prefixLift 4643399
  have htrace : WordTrace (prefixWord ++ tailWord_4643399) baseStart_4643399 baseEnd_4643399 := by
    simpa [prefixWord, tailWord_4643399, baseEnd_4643399] using wordTrace_append hprefix tailTrace_4643399
  have hstable : (prefixWord ++ tailWord_4643399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4643399).length < 2 ^ (prefixWord ++ tailWord_4643399).sum := by decide
  have hdescent : baseEnd_4643399 < baseStart_4643399 := by decide
  rcases family_descends (prefixWord ++ tailWord_4643399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4643425 : List Nat := [1, 2, 3, 1, 1, 4, 1, 1, 5, 4]
def baseStart_4643425 : Nat := 118140960795 + 4643425 * 2 ^ 59
def prefixEnd_4643425 : Nat := 4983230072969 + 3 ^ 40 * 4643425 * 2
def baseEnd_4643425 : Nat := 794769636034533437344261

theorem tailTrace_4643425 : CollatzResearch.WordTrace tailWord_4643425 prefixEnd_4643425 794769636034533437344261 := by
  unfold tailWord_4643425
  simp only [CollatzResearch.WordTrace]
  refine ⟨169359623202671733698459729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112906415468447822465639819 169359623202671733698459729)
  ·
    refine ⟨127019717402003800273844797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169359623202671733698459729 127019717402003800273844797)
    ·
      refine ⟨47632394025751425102691799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 127019717402003800273844797 47632394025751425102691799)
      ·
        refine ⟨71448591038627137654037699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47632394025751425102691799 71448591038627137654037699)
        ·
          refine ⟨107172886557940706481056549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71448591038627137654037699 107172886557940706481056549)
          ·
            refine ⟨20094916229613882465198103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 107172886557940706481056549 20094916229613882465198103)
            ·
              refine ⟨30142374344420823697797155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20094916229613882465198103 30142374344420823697797155)
              ·
                refine ⟨45213561516631235546695733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30142374344420823697797155 45213561516631235546695733)
                ·
                  refine ⟨4238771392184178332502725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45213561516631235546695733 4238771392184178332502725)
                  ·
                    refine ⟨794769636034533437344261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4238771392184178332502725 794769636034533437344261)
                    ·
                      rfl

theorem cell23_4643425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 1, 5, 4].length) (baseStart_4643425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4643425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4643425 prefixEnd_4643425 := by exact prefixLift 4643425
  have htrace : WordTrace (prefixWord ++ tailWord_4643425) baseStart_4643425 baseEnd_4643425 := by
    simpa [prefixWord, tailWord_4643425, baseEnd_4643425] using wordTrace_append hprefix tailTrace_4643425
  have hstable : (prefixWord ++ tailWord_4643425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4643425).length < 2 ^ (prefixWord ++ tailWord_4643425).sum := by decide
  have hdescent : baseEnd_4643425 < baseStart_4643425 := by decide
  rcases family_descends (prefixWord ++ tailWord_4643425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4643429 : List Nat := [1, 3, 1, 3, 5, 1, 1, 1, 2, 5]
def baseStart_4643429 : Nat := 118140960795 + 4643429 * 2 ^ 59
def prefixEnd_4643429 : Nat := 4983230072969 + 3 ^ 40 * 4643429 * 2
def baseEnd_4643429 : Nat := 794770320675406098794255

theorem tailTrace_4643429 : CollatzResearch.WordTrace tailWord_4643429 prefixEnd_4643429 794770320675406098794255 := by
  unfold tailWord_4643429
  simp only [CollatzResearch.WordTrace]
  refine ⟨169359769094657242381605341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112906512729771494921070227 169359769094657242381605341)
  ·
    refine ⟨63509913410496465893102003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 169359769094657242381605341 63509913410496465893102003)
    ·
      refine ⟨95264870115744698839653005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63509913410496465893102003 95264870115744698839653005)
      ·
        refine ⟨35724326293404262064869877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95264870115744698839653005 35724326293404262064869877)
        ·
          refine ⟨3349155590006649568581551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 35724326293404262064869877 3349155590006649568581551)
          ·
            refine ⟨5023733385009974352872327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3349155590006649568581551 5023733385009974352872327)
            ·
              refine ⟨7535600077514961529308491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5023733385009974352872327 7535600077514961529308491)
              ·
                refine ⟨11303400116272442293962737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7535600077514961529308491 11303400116272442293962737)
                ·
                  refine ⟨8477550087204331720472053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11303400116272442293962737 8477550087204331720472053)
                  ·
                    refine ⟨794770320675406098794255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8477550087204331720472053 794770320675406098794255)
                    ·
                      rfl

theorem cell23_4643429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 1, 1, 2, 5].length) (baseStart_4643429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4643429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4643429 prefixEnd_4643429 := by exact prefixLift 4643429
  have htrace : WordTrace (prefixWord ++ tailWord_4643429) baseStart_4643429 baseEnd_4643429 := by
    simpa [prefixWord, tailWord_4643429, baseEnd_4643429] using wordTrace_append hprefix tailTrace_4643429
  have hstable : (prefixWord ++ tailWord_4643429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4643429).length < 2 ^ (prefixWord ++ tailWord_4643429).sum := by decide
  have hdescent : baseEnd_4643429 < baseStart_4643429 := by decide
  rcases family_descends (prefixWord ++ tailWord_4643429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4643432 : List Nat := [2, 1, 4, 3, 2, 1, 1, 1, 1, 3, 4]
def baseStart_4643432 : Nat := 118140960795 + 4643432 * 2 ^ 59
def prefixEnd_4643432 : Nat := 4983230072969 + 3 ^ 40 * 4643432 * 2
def baseEnd_4643432 : Nat := 2384312502468181784645251

theorem tailTrace_4643432 : CollatzResearch.WordTrace tailWord_4643432 prefixEnd_4643432 2384312502468181784645251 := by
  unfold tailWord_4643432
  simp only [CollatzResearch.WordTrace]
  refine ⟨84679939256823186946982275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112906585675764249262643033 84679939256823186946982275)
  ·
    refine ⟨127019908885234780420473413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84679939256823186946982275 127019908885234780420473413)
    ·
      refine ⟨23816232915981521328838765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 127019908885234780420473413 23816232915981521328838765)
      ·
        refine ⟨8931087343493070498314537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23816232915981521328838765 8931087343493070498314537)
        ·
          refine ⟨6698315507619802873735903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8931087343493070498314537 6698315507619802873735903)
          ·
            refine ⟨10047473261429704310603855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6698315507619802873735903 10047473261429704310603855)
            ·
              refine ⟨15071209892144556465905783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10047473261429704310603855 15071209892144556465905783)
              ·
                refine ⟨22606814838216834698858675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15071209892144556465905783 22606814838216834698858675)
                ·
                  refine ⟨33910222257325252048288013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22606814838216834698858675 33910222257325252048288013)
                  ·
                    refine ⟨12716333346496969518108005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33910222257325252048288013 12716333346496969518108005)
                    ·
                      refine ⟨2384312502468181784645251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12716333346496969518108005 2384312502468181784645251)
                      ·
                        rfl

theorem cell23_4643432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_4643432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4643432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4643432 prefixEnd_4643432 := by exact prefixLift 4643432
  have htrace : WordTrace (prefixWord ++ tailWord_4643432) baseStart_4643432 baseEnd_4643432 := by
    simpa [prefixWord, tailWord_4643432, baseEnd_4643432] using wordTrace_append hprefix tailTrace_4643432
  have hstable : (prefixWord ++ tailWord_4643432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4643432).length < 2 ^ (prefixWord ++ tailWord_4643432).sum := by decide
  have hdescent : baseEnd_4643432 < baseStart_4643432 := by decide
  rcases family_descends (prefixWord ++ tailWord_4643432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4643435 : List Nat := [1, 1, 1, 1, 2, 2, 1, 7, 2, 2, 3]
def baseStart_4643435 : Nat := 118140960795 + 4643435 * 2 ^ 59
def prefixEnd_4643435 : Nat := 4983230072969 + 3 ^ 40 * 4643435 * 2
def baseEnd_4643435 : Nat := 2384314042910145272907737

theorem tailTrace_4643435 : CollatzResearch.WordTrace tailWord_4643435 prefixEnd_4643435 2384314042910145272907737 := by
  unfold tailWord_4643435
  simp only [CollatzResearch.WordTrace]
  refine ⟨169359987932635505406323759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112906658621757003604215839 169359987932635505406323759)
  ·
    refine ⟨254039981898953258109485639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169359987932635505406323759 254039981898953258109485639)
    ·
      refine ⟨381059972848429887164228459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 254039981898953258109485639 381059972848429887164228459)
      ·
        refine ⟨571589959272644830746342689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 381059972848429887164228459 571589959272644830746342689)
        ·
          refine ⟨428692469454483623059757017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 571589959272644830746342689 428692469454483623059757017)
          ·
            refine ⟨321519352090862717294817763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 428692469454483623059757017 321519352090862717294817763)
            ·
              refine ⟨482279028136294075942226645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 321519352090862717294817763 482279028136294075942226645)
              ·
                refine ⟨11303414721944392404895937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 482279028136294075942226645 11303414721944392404895937)
                ·
                  refine ⟨8477561041458294303671953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11303414721944392404895937 8477561041458294303671953)
                  ·
                    refine ⟨6358170781093720727753965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8477561041458294303671953 6358170781093720727753965)
                    ·
                      refine ⟨2384314042910145272907737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6358170781093720727753965 2384314042910145272907737)
                      ·
                        rfl

theorem cell23_4643435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 7, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 7, 2, 2, 3].length) (baseStart_4643435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4643435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4643435 prefixEnd_4643435 := by exact prefixLift 4643435
  have htrace : WordTrace (prefixWord ++ tailWord_4643435) baseStart_4643435 baseEnd_4643435 := by
    simpa [prefixWord, tailWord_4643435, baseEnd_4643435] using wordTrace_append hprefix tailTrace_4643435
  have hstable : (prefixWord ++ tailWord_4643435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4643435).length < 2 ^ (prefixWord ++ tailWord_4643435).sum := by decide
  have hdescent : baseEnd_4643435 < baseStart_4643435 := by decide
  rcases family_descends (prefixWord ++ tailWord_4643435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4643468 : List Nat := [2, 2, 1, 2, 1, 1, 2, 1, 2, 9]
def baseStart_4643468 : Nat := 118140960795 + 4643468 * 2 ^ 59
def prefixEnd_4643468 : Nat := 4983230072969 + 3 ^ 40 * 4643468 * 2
def baseEnd_4643468 : Nat := 794776995923914547931695

theorem tailTrace_4643468 : CollatzResearch.WordTrace tailWord_4643468 prefixEnd_4643468 794776995923914547931695 := by
  unfold tailWord_4643468
  simp only [CollatzResearch.WordTrace]
  refine ⟨84680595770757976021137529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112907461027677301361516705 84680595770757976021137529)
  ·
    refine ⟨63510446828068482015853147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84680595770757976021137529 63510446828068482015853147)
    ·
      refine ⟨95265670242102723023779721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63510446828068482015853147 95265670242102723023779721)
      ·
        refine ⟨71449252681577042267834791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95265670242102723023779721 71449252681577042267834791)
        ·
          refine ⟨107173879022365563401752187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71449252681577042267834791 107173879022365563401752187)
          ·
            refine ⟨160760818533548345102628281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107173879022365563401752187 160760818533548345102628281)
            ·
              refine ⟨120570613900161258826971211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 160760818533548345102628281 120570613900161258826971211)
              ·
                refine ⟨180855920850241888240456817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 120570613900161258826971211 180855920850241888240456817)
                ·
                  refine ⟨135641940637681416180342613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 180855920850241888240456817 135641940637681416180342613)
                  ·
                    refine ⟨794776995923914547931695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 135641940637681416180342613 794776995923914547931695)
                    ·
                      rfl

theorem cell23_4643468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 9].length) (baseStart_4643468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4643468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4643468 prefixEnd_4643468 := by exact prefixLift 4643468
  have htrace : WordTrace (prefixWord ++ tailWord_4643468) baseStart_4643468 baseEnd_4643468 := by
    simpa [prefixWord, tailWord_4643468, baseEnd_4643468] using wordTrace_append hprefix tailTrace_4643468
  have hstable : (prefixWord ++ tailWord_4643468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4643468).length < 2 ^ (prefixWord ++ tailWord_4643468).sum := by decide
  have hdescent : baseEnd_4643468 < baseStart_4643468 := by decide
  rcases family_descends (prefixWord ++ tailWord_4643468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4643485 : List Nat := [1, 4, 2, 1, 1, 1, 2, 3, 3, 5]
def baseStart_4643485 : Nat := 118140960795 + 4643485 * 2 ^ 59
def prefixEnd_4643485 : Nat := 4983230072969 + 3 ^ 40 * 4643485 * 2
def baseEnd_4643485 : Nat := 794779905647623359094169

theorem tailTrace_4643485 : CollatzResearch.WordTrace tailWord_4643485 prefixEnd_4643485 794779905647623359094169 := by
  unfold tailWord_4643485
  simp only [CollatzResearch.WordTrace]
  refine ⟨169361811582454363945643909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112907874388302909297095939 169361811582454363945643909)
  ·
    refine ⟨31755339671710193239808233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 169361811582454363945643909 31755339671710193239808233)
    ·
      refine ⟨23816504753782644929856175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31755339671710193239808233 23816504753782644929856175)
      ·
        refine ⟨35724757130673967394784263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23816504753782644929856175 35724757130673967394784263)
        ·
          refine ⟨53587135696010951092176395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35724757130673967394784263 53587135696010951092176395)
          ·
            refine ⟨80380703544016426638264593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53587135696010951092176395 80380703544016426638264593)
            ·
              refine ⟨60285527658012319978698445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80380703544016426638264593 60285527658012319978698445)
              ·
                refine ⟨22607072871754619992011917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60285527658012319978698445 22607072871754619992011917)
                ·
                  refine ⟨8477652326907982497004469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22607072871754619992011917 8477652326907982497004469)
                  ·
                    refine ⟨794779905647623359094169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8477652326907982497004469 794779905647623359094169)
                    ·
                      rfl

theorem cell23_4643485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 3, 3, 5].length) (baseStart_4643485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4643485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4643485 prefixEnd_4643485 := by exact prefixLift 4643485
  have htrace : WordTrace (prefixWord ++ tailWord_4643485) baseStart_4643485 baseEnd_4643485 := by
    simpa [prefixWord, tailWord_4643485, baseEnd_4643485] using wordTrace_append hprefix tailTrace_4643485
  have hstable : (prefixWord ++ tailWord_4643485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4643485).length < 2 ^ (prefixWord ++ tailWord_4643485).sum := by decide
  have hdescent : baseEnd_4643485 < baseStart_4643485 := by decide
  rcases family_descends (prefixWord ++ tailWord_4643485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4643492 : List Nat := [2, 3, 1, 2, 2, 1, 1, 3, 1, 5, 2]
def baseStart_4643492 : Nat := 118140960795 + 4643492 * 2 ^ 59
def prefixEnd_4643492 : Nat := 4983230072969 + 3 ^ 40 * 4643492 * 2
def baseEnd_4643492 : Nat := 2384343311307451549894975

theorem tailTrace_4643492 : CollatzResearch.WordTrace tailWord_4643492 prefixEnd_4643492 2384343311307451549894975 := by
  unfold tailWord_4643492
  simp only [CollatzResearch.WordTrace]
  refine ⟨84681033446714502070574365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112908044595619336094099153 84681033446714502070574365)
  ·
    refine ⟨31755387542517938276465387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84681033446714502070574365 31755387542517938276465387)
    ·
      refine ⟨47633081313776907414698081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31755387542517938276465387 47633081313776907414698081)
      ·
        refine ⟨35724810985332680561023561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47633081313776907414698081 35724810985332680561023561)
        ·
          refine ⟨26793608238999510420767671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35724810985332680561023561 26793608238999510420767671)
          ·
            refine ⟨40190412358499265631151507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26793608238999510420767671 40190412358499265631151507)
            ·
              refine ⟨60285618537748898446727261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40190412358499265631151507 60285618537748898446727261)
              ·
                refine ⟨22607106951655836917522723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60285618537748898446727261 22607106951655836917522723)
                ·
                  refine ⟨33910660427483755376284085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22607106951655836917522723 33910660427483755376284085)
                  ·
                    refine ⟨3179124415076602066526633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33910660427483755376284085 3179124415076602066526633)
                    ·
                      refine ⟨2384343311307451549894975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3179124415076602066526633 2384343311307451549894975)
                      ·
                        rfl

theorem cell23_4643492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 3, 1, 5, 2].length) (baseStart_4643492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4643492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4643492 prefixEnd_4643492 := by exact prefixLift 4643492
  have htrace : WordTrace (prefixWord ++ tailWord_4643492) baseStart_4643492 baseEnd_4643492 := by
    simpa [prefixWord, tailWord_4643492, baseEnd_4643492] using wordTrace_append hprefix tailTrace_4643492
  have hstable : (prefixWord ++ tailWord_4643492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4643492).length < 2 ^ (prefixWord ++ tailWord_4643492).sum := by decide
  have hdescent : baseEnd_4643492 < baseStart_4643492 := by decide
  rcases family_descends (prefixWord ++ tailWord_4643492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4643509 : List Nat := [1, 3, 3, 3, 1, 1, 1, 1, 4, 3, 2]
def baseStart_4643509 : Nat := 118140960795 + 4643509 * 2 ^ 59
def prefixEnd_4643509 : Nat := 4983230072969 + 3 ^ 40 * 4643509 * 2
def baseEnd_4643509 : Nat := 2384352040478577983382397

theorem tailTrace_4643509 : CollatzResearch.WordTrace tailWord_4643509 prefixEnd_4643509 2384352040478577983382397 := by
  unfold tailWord_4643509
  simp only [CollatzResearch.WordTrace]
  refine ⟨169362686934367416044517581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112908457956244944029678387 169362686934367416044517581)
  ·
    refine ⟨63511007600387781016694093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 169362686934367416044517581 63511007600387781016694093)
    ·
      refine ⟨23816627850145417881260285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63511007600387781016694093 23816627850145417881260285)
      ·
        refine ⟨8931235443804531705472607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23816627850145417881260285 8931235443804531705472607)
        ·
          refine ⟨13396853165706797558208911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8931235443804531705472607 13396853165706797558208911)
          ·
            refine ⟨20095279748560196337313367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13396853165706797558208911 20095279748560196337313367)
            ·
              refine ⟨30142919622840294505970051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20095279748560196337313367 30142919622840294505970051)
              ·
                refine ⟨45214379434260441758955077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30142919622840294505970051 45214379434260441758955077)
                ·
                  refine ⟨8477696143923832829804077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45214379434260441758955077 8477696143923832829804077)
                  ·
                    refine ⟨3179136053971437311176529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8477696143923832829804077 3179136053971437311176529)
                    ·
                      refine ⟨2384352040478577983382397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3179136053971437311176529 2384352040478577983382397)
                      ·
                        rfl

theorem cell23_4643509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 1, 4, 3, 2].length) (baseStart_4643509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4643509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4643509 prefixEnd_4643509 := by exact prefixLift 4643509
  have htrace : WordTrace (prefixWord ++ tailWord_4643509) baseStart_4643509 baseEnd_4643509 := by
    simpa [prefixWord, tailWord_4643509, baseEnd_4643509] using wordTrace_append hprefix tailTrace_4643509
  have hstable : (prefixWord ++ tailWord_4643509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4643509).length < 2 ^ (prefixWord ++ tailWord_4643509).sum := by decide
  have hdescent : baseEnd_4643509 < baseStart_4643509 := by decide
  rcases family_descends (prefixWord ++ tailWord_4643509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4643510 : List Nat := [5, 1, 3, 1, 2, 1, 3, 2, 1, 4]
def baseStart_4643510 : Nat := 118140960795 + 4643510 * 2 ^ 59
def prefixEnd_4643510 : Nat := 4983230072969 + 3 ^ 40 * 4643510 * 2
def baseEnd_4643510 : Nat := 794784184653077493156631

theorem tailTrace_4643510 : CollatzResearch.WordTrace tailWord_4643510 prefixEnd_4643510 794784184653077493156631 := by
  unfold tailWord_4643510
  simp only [CollatzResearch.WordTrace]
  refine ⟨10585170212960237075956499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 112908482271575862143535989 10585170212960237075956499)
  ·
    refine ⟨15877755319440355613934749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10585170212960237075956499 15877755319440355613934749)
    ·
      refine ⟨5954158244790133355225531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15877755319440355613934749 5954158244790133355225531)
      ·
        refine ⟨8931237367185200032838297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5954158244790133355225531 8931237367185200032838297)
        ·
          refine ⟨6698428025388900024628723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8931237367185200032838297 6698428025388900024628723)
          ·
            refine ⟨10047642038083350036943085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6698428025388900024628723 10047642038083350036943085)
            ·
              refine ⟨3767865764281256263853657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10047642038083350036943085 3767865764281256263853657)
              ·
                refine ⟨2825899323210942197890243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3767865764281256263853657 2825899323210942197890243)
                ·
                  refine ⟨4238848984816413296835365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2825899323210942197890243 4238848984816413296835365)
                  ·
                    refine ⟨794784184653077493156631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4238848984816413296835365 794784184653077493156631)
                    ·
                      rfl

theorem cell23_4643510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_4643510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4643510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4643510 prefixEnd_4643510 := by exact prefixLift 4643510
  have htrace : WordTrace (prefixWord ++ tailWord_4643510) baseStart_4643510 baseEnd_4643510 := by
    simpa [prefixWord, tailWord_4643510, baseEnd_4643510] using wordTrace_append hprefix tailTrace_4643510
  have hstable : (prefixWord ++ tailWord_4643510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4643510).length < 2 ^ (prefixWord ++ tailWord_4643510).sum := by decide
  have hdescent : baseEnd_4643510 < baseStart_4643510 := by decide
  rcases family_descends (prefixWord ++ tailWord_4643510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4643585 : List Nat := [1, 2, 4, 1, 1, 1, 1, 2, 1, 4, 5]
def baseStart_4643585 : Nat := 118140960795 + 4643585 * 2 ^ 59
def prefixEnd_4643585 : Nat := 4983230072969 + 3 ^ 40 * 4643585 * 2
def baseEnd_4643585 : Nat := 2384391065008319686032047

theorem tailTrace_4643585 : CollatzResearch.WordTrace tailWord_4643585 prefixEnd_4643585 2384391065008319686032047 := by
  unfold tailWord_4643585
  simp only [CollatzResearch.WordTrace]
  refine ⟨169365458882092081024284209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112910305921394720682856139 169365458882092081024284209)
  ·
    refine ⟨127024094161569060768213157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169365458882092081024284209 127024094161569060768213157)
    ·
      refine ⟨23817017655294198894039967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 127024094161569060768213157 23817017655294198894039967)
      ·
        refine ⟨35725526482941298341059951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23817017655294198894039967 35725526482941298341059951)
        ·
          refine ⟨53588289724411947511589927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35725526482941298341059951 53588289724411947511589927)
          ·
            refine ⟨80382434586617921267384891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53588289724411947511589927 80382434586617921267384891)
            ·
              refine ⟨120573651879926881901077337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80382434586617921267384891 120573651879926881901077337)
              ·
                refine ⟨90430238909945161425808003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 120573651879926881901077337 90430238909945161425808003)
                ·
                  refine ⟨135645358364917742138712005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 90430238909945161425808003 135645358364917742138712005)
                  ·
                    refine ⟨25433504693422076651008501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 135645358364917742138712005 25433504693422076651008501)
                    ·
                      refine ⟨2384391065008319686032047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25433504693422076651008501 2384391065008319686032047)
                      ·
                        rfl

theorem cell23_4643585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 4, 5].length) (baseStart_4643585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4643585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4643585 prefixEnd_4643585 := by exact prefixLift 4643585
  have htrace : WordTrace (prefixWord ++ tailWord_4643585) baseStart_4643585 baseEnd_4643585 := by
    simpa [prefixWord, tailWord_4643585, baseEnd_4643585] using wordTrace_append hprefix tailTrace_4643585
  have hstable : (prefixWord ++ tailWord_4643585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4643585).length < 2 ^ (prefixWord ++ tailWord_4643585).sum := by decide
  have hdescent : baseEnd_4643585 < baseStart_4643585 := by decide
  rcases family_descends (prefixWord ++ tailWord_4643585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4643595 : List Nat := [1, 1, 1, 1, 5, 1, 1, 1, 4, 3, 4]
def baseStart_4643595 : Nat := 118140960795 + 4643595 * 2 ^ 59
def prefixEnd_4643595 : Nat := 4983230072969 + 3 ^ 40 * 4643595 * 2
def baseEnd_4643595 : Nat := 2384396199814864646907001

theorem tailTrace_4643595 : CollatzResearch.WordTrace tailWord_4643595 prefixEnd_4643595 2384396199814864646907001 := by
  unfold tailWord_4643595
  simp only [CollatzResearch.WordTrace]
  refine ⟨169365823612055852732148239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112910549074703901821432159 169365823612055852732148239)
  ·
    refine ⟨254048735418083779098222359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169365823612055852732148239 254048735418083779098222359)
    ·
      refine ⟨381073103127125668647333539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 254048735418083779098222359 381073103127125668647333539)
      ·
        refine ⟨571609654690688502971000309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 381073103127125668647333539 571609654690688502971000309)
        ·
          refine ⟨53588405127252047153531279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 571609654690688502971000309 53588405127252047153531279)
          ·
            refine ⟨80382607690878070730296919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53588405127252047153531279 80382607690878070730296919)
            ·
              refine ⟨120573911536317106095445379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80382607690878070730296919 120573911536317106095445379)
              ·
                refine ⟨180860867304475659143168069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 120573911536317106095445379 180860867304475659143168069)
                ·
                  refine ⟨33911412619589186089344013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 180860867304475659143168069 33911412619589186089344013)
                  ·
                    refine ⟨12716779732345944783504005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33911412619589186089344013 12716779732345944783504005)
                    ·
                      refine ⟨2384396199814864646907001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12716779732345944783504005 2384396199814864646907001)
                      ·
                        rfl

theorem cell23_4643595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 4, 3, 4].length) (baseStart_4643595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4643595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4643595 prefixEnd_4643595 := by exact prefixLift 4643595
  have htrace : WordTrace (prefixWord ++ tailWord_4643595) baseStart_4643595 baseEnd_4643595 := by
    simpa [prefixWord, tailWord_4643595, baseEnd_4643595] using wordTrace_append hprefix tailTrace_4643595
  have hstable : (prefixWord ++ tailWord_4643595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4643595).length < 2 ^ (prefixWord ++ tailWord_4643595).sum := by decide
  have hdescent : baseEnd_4643595 < baseStart_4643595 := by decide
  rcases family_descends (prefixWord ++ tailWord_4643595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4643599 : List Nat := [1, 1, 2, 1, 1, 1, 6, 4, 1, 3, 2]
def baseStart_4643599 : Nat := 118140960795 + 4643599 * 2 ^ 59
def prefixEnd_4643599 : Nat := 4983230072969 + 3 ^ 40 * 4643599 * 2
def baseEnd_4643599 : Nat := 2384398253737482631256983

theorem tailTrace_4643599 : CollatzResearch.WordTrace tailWord_4643599 prefixEnd_4643599 2384398253737482631256983 := by
  unfold tailWord_4643599
  simp only [CollatzResearch.WordTrace]
  refine ⟨169365969504041361415293851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112910646336027574276862567 169365969504041361415293851)
  ·
    refine ⟨254048954256062042122940777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169365969504041361415293851 254048954256062042122940777)
    ·
      refine ⟨190536715692046531592205583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 254048954256062042122940777 190536715692046531592205583)
      ·
        refine ⟨285805073538069797388308375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190536715692046531592205583 285805073538069797388308375)
        ·
          refine ⟨428707610307104696082462563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 285805073538069797388308375 428707610307104696082462563)
          ·
            refine ⟨643061415460657044123693845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 428707610307104696082462563 643061415460657044123693845)
            ·
              refine ⟨30143503849718298943298149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 643061415460657044123693845 30143503849718298943298149)
              ·
                refine ⟨5651906971822181051868403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30143503849718298943298149 5651906971822181051868403)
                ·
                  refine ⟨8477860457733271577802605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5651906971822181051868403 8477860457733271577802605)
                  ·
                    refine ⟨3179197671649976841675977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8477860457733271577802605 3179197671649976841675977)
                    ·
                      refine ⟨2384398253737482631256983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3179197671649976841675977 2384398253737482631256983)
                      ·
                        rfl

theorem cell23_4643599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 4, 1, 3, 2].length) (baseStart_4643599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4643599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4643599 prefixEnd_4643599 := by exact prefixLift 4643599
  have htrace : WordTrace (prefixWord ++ tailWord_4643599) baseStart_4643599 baseEnd_4643599 := by
    simpa [prefixWord, tailWord_4643599, baseEnd_4643599] using wordTrace_append hprefix tailTrace_4643599
  have hstable : (prefixWord ++ tailWord_4643599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4643599).length < 2 ^ (prefixWord ++ tailWord_4643599).sum := by decide
  have hdescent : baseEnd_4643599 < baseStart_4643599 := by decide
  rcases family_descends (prefixWord ++ tailWord_4643599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4643605 : List Nat := [1, 3, 2, 1, 2, 2, 1, 2, 1, 8]
def baseStart_4643605 : Nat := 118140960795 + 4643605 * 2 ^ 59
def prefixEnd_4643605 : Nat := 4983230072969 + 3 ^ 40 * 4643605 * 2
def baseEnd_4643605 : Nat := 794800444873803202593985

theorem tailTrace_4643605 : CollatzResearch.WordTrace tailWord_4643605 prefixEnd_4643605 794800444873803202593985 := by
  unfold tailWord_4643605
  simp only [CollatzResearch.WordTrace]
  refine ⟨169366188342019624440012269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112910792228013082960008179 169366188342019624440012269)
  ·
    refine ⟨63512320628257359165004601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 169366188342019624440012269 63512320628257359165004601)
    ·
      refine ⟨47634240471193019373753451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63512320628257359165004601 47634240471193019373753451)
      ·
        refine ⟨71451360706789529060630177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47634240471193019373753451 71451360706789529060630177)
        ·
          refine ⟨53588520530092146795472633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71451360706789529060630177 53588520530092146795472633)
          ·
            refine ⟨40191390397569110096604475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53588520530092146795472633 40191390397569110096604475)
            ·
              refine ⟨60287085596353665144906713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40191390397569110096604475 60287085596353665144906713)
              ·
                refine ⟨45215314197265248858680035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60287085596353665144906713 45215314197265248858680035)
                ·
                  refine ⟨67822971295897873288020053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45215314197265248858680035 67822971295897873288020053)
                  ·
                    refine ⟨794800444873803202593985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 67822971295897873288020053 794800444873803202593985)
                    ·
                      rfl

theorem cell23_4643605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 2, 1, 8].length) (baseStart_4643605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4643605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4643605 prefixEnd_4643605 := by exact prefixLift 4643605
  have htrace : WordTrace (prefixWord ++ tailWord_4643605) baseStart_4643605 baseEnd_4643605 := by
    simpa [prefixWord, tailWord_4643605, baseEnd_4643605] using wordTrace_append hprefix tailTrace_4643605
  have hstable : (prefixWord ++ tailWord_4643605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4643605).length < 2 ^ (prefixWord ++ tailWord_4643605).sum := by decide
  have hdescent : baseEnd_4643605 < baseStart_4643605 := by decide
  rcases family_descends (prefixWord ++ tailWord_4643605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4643616 : List Nat := [2, 1, 1, 5, 1, 3, 1, 3, 1, 3, 2]
def baseStart_4643616 : Nat := 118140960795 + 4643616 * 2 ^ 59
def prefixEnd_4643616 : Nat := 4983230072969 + 3 ^ 40 * 4643616 * 2
def baseEnd_4643616 : Nat := 2384406982908609064744405

theorem tailTrace_4643616 : CollatzResearch.WordTrace tailWord_4643616 prefixEnd_4643616 2384406982908609064744405 := by
  unfold tailWord_4643616
  simp only [CollatzResearch.WordTrace]
  refine ⟨84683294772489886659331351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112911059696653182212441801 84683294772489886659331351)
  ·
    refine ⟨127024942158734829988997027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84683294772489886659331351 127024942158734829988997027)
    ·
      refine ⟨190537413238102244983495541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127024942158734829988997027 190537413238102244983495541)
      ·
        refine ⟨17862882491072085467202707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 190537413238102244983495541 17862882491072085467202707)
        ·
          refine ⟨26794323736608128200804061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17862882491072085467202707 26794323736608128200804061)
          ·
            refine ⟨10047871401228048075301523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26794323736608128200804061 10047871401228048075301523)
            ·
              refine ⟨15071807101842072112952285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10047871401228048075301523 15071807101842072112952285)
              ·
                refine ⟨5651927663190777042357107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15071807101842072112952285 5651927663190777042357107)
                ·
                  refine ⟨8477891494786165563535661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5651927663190777042357107 8477891494786165563535661)
                  ·
                    refine ⟨3179209310544812086325873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8477891494786165563535661 3179209310544812086325873)
                    ·
                      refine ⟨2384406982908609064744405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3179209310544812086325873 2384406982908609064744405)
                      ·
                        rfl

theorem cell23_4643616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 3, 1, 3, 2].length) (baseStart_4643616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4643616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4643616 prefixEnd_4643616 := by exact prefixLift 4643616
  have htrace : WordTrace (prefixWord ++ tailWord_4643616) baseStart_4643616 baseEnd_4643616 := by
    simpa [prefixWord, tailWord_4643616, baseEnd_4643616] using wordTrace_append hprefix tailTrace_4643616
  have hstable : (prefixWord ++ tailWord_4643616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4643616).length < 2 ^ (prefixWord ++ tailWord_4643616).sum := by decide
  have hdescent : baseEnd_4643616 < baseStart_4643616 := by decide
  rcases family_descends (prefixWord ++ tailWord_4643616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4643625 : List Nat := [1, 2, 1, 1, 1, 1, 1, 4, 3, 4, 4]
def baseStart_4643625 : Nat := 118140960795 + 4643625 * 2 ^ 59
def prefixEnd_4643625 : Nat := 4983230072969 + 3 ^ 40 * 4643625 * 2
def baseEnd_4643625 : Nat := 2384411604234499529531863

theorem tailTrace_4643625 : CollatzResearch.WordTrace tailWord_4643625 prefixEnd_4643625 2384411604234499529531863 := by
  unfold tailWord_4643625
  simp only [CollatzResearch.WordTrace]
  refine ⟨169366917801947167855740329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112911278534631445237160219 169366917801947167855740329)
  ·
    refine ⟨127025188351460375891805247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169366917801947167855740329 127025188351460375891805247)
    ·
      refine ⟨190537782527190563837707871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127025188351460375891805247 190537782527190563837707871)
      ·
        refine ⟨285806673790785845756561807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190537782527190563837707871 285806673790785845756561807)
        ·
          refine ⟨428710010686178768634842711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 285806673790785845756561807 428710010686178768634842711)
          ·
            refine ⟨643065016029268152952264067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 428710010686178768634842711 643065016029268152952264067)
            ·
              refine ⟨964597524043902229428396101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 643065016029268152952264067 964597524043902229428396101)
              ·
                refine ⟨180862035758231668017824269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 964597524043902229428396101 180862035758231668017824269)
                ·
                  refine ⟨67823263409336875506684101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 180862035758231668017824269 67823263409336875506684101)
                  ·
                    refine ⟨12716861889250664157503269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 67823263409336875506684101 12716861889250664157503269)
                    ·
                      refine ⟨2384411604234499529531863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12716861889250664157503269 2384411604234499529531863)
                      ·
                        rfl

theorem cell23_4643625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 3, 4, 4].length) (baseStart_4643625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4643625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4643625 prefixEnd_4643625 := by exact prefixLift 4643625
  have htrace : WordTrace (prefixWord ++ tailWord_4643625) baseStart_4643625 baseEnd_4643625 := by
    simpa [prefixWord, tailWord_4643625, baseEnd_4643625] using wordTrace_append hprefix tailTrace_4643625
  have hstable : (prefixWord ++ tailWord_4643625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4643625).length < 2 ^ (prefixWord ++ tailWord_4643625).sum := by decide
  have hdescent : baseEnd_4643625 < baseStart_4643625 := by decide
  rcases family_descends (prefixWord ++ tailWord_4643625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4643662 : List Nat := [4, 1, 1, 1, 1, 1, 1, 4, 1, 5, 3]
def baseStart_4643662 : Nat := 118140960795 + 4643662 * 2 ^ 59
def prefixEnd_4643662 : Nat := 4983230072969 + 3 ^ 40 * 4643662 * 2
def baseEnd_4643662 : Nat := 2384430603018715884769193

theorem tailTrace_4643662 : CollatzResearch.WordTrace tailWord_4643662 prefixEnd_4643662 2384430603018715884769193 := by
  unfold tailWord_4643662
  simp only [CollatzResearch.WordTrace]
  refine ⟨21171033412851640396854655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112912178201875415449891493 21171033412851640396854655)
  ·
    refine ⟨31756550119277460595281983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21171033412851640396854655 31756550119277460595281983)
    ·
      refine ⟨47634825178916190892922975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31756550119277460595281983 47634825178916190892922975)
      ·
        refine ⟨71452237768374286339384463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47634825178916190892922975 71452237768374286339384463)
        ·
          refine ⟨107178356652561429509076695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71452237768374286339384463 107178356652561429509076695)
          ·
            refine ⟨160767534978842144263615043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107178356652561429509076695 160767534978842144263615043)
            ·
              refine ⟨241151302468263216395422565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 160767534978842144263615043 241151302468263216395422565)
              ·
                refine ⟨45215869212799353074141731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 241151302468263216395422565 45215869212799353074141731)
                ·
                  refine ⟨67823803819199029611212597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45215869212799353074141731 67823803819199029611212597)
                  ·
                    refine ⟨6358481608049909026051181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 67823803819199029611212597 6358481608049909026051181)
                    ·
                      refine ⟨2384430603018715884769193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6358481608049909026051181 2384430603018715884769193)
                      ·
                        rfl

theorem cell23_4643662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 4, 1, 5, 3].length) (baseStart_4643662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4643662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4643662 prefixEnd_4643662 := by exact prefixLift 4643662
  have htrace : WordTrace (prefixWord ++ tailWord_4643662) baseStart_4643662 baseEnd_4643662 := by
    simpa [prefixWord, tailWord_4643662, baseEnd_4643662] using wordTrace_append hprefix tailTrace_4643662
  have hstable : (prefixWord ++ tailWord_4643662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4643662).length < 2 ^ (prefixWord ++ tailWord_4643662).sum := by decide
  have hdescent : baseEnd_4643662 < baseStart_4643662 := by decide
  rcases family_descends (prefixWord ++ tailWord_4643662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4643675 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 4, 6, 5]
def baseStart_4643675 : Nat := 118140960795 + 4643675 * 2 ^ 59
def prefixEnd_4643675 : Nat := 4983230072969 + 3 ^ 40 * 4643675 * 2
def baseEnd_4643675 : Nat := 2384437278267224333906633

theorem tailTrace_4643675 : CollatzResearch.WordTrace tailWord_4643675 prefixEnd_4643675 2384437278267224333906633 := by
  unfold tailWord_4643675
  simp only [CollatzResearch.WordTrace]
  refine ⟨169368741451766026395060479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112912494301177350930040319 169368741451766026395060479)
  ·
    refine ⟨254053112177649039592590719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169368741451766026395060479 254053112177649039592590719)
    ·
      refine ⟨381079668266473559388886079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 254053112177649039592590719 381079668266473559388886079)
      ·
        refine ⟨571619502399710339083329119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 381079668266473559388886079 571619502399710339083329119)
        ·
          refine ⟨857429253599565508624993679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 571619502399710339083329119 857429253599565508624993679)
          ·
            refine ⟨1286143880399348262937490519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 857429253599565508624993679 1286143880399348262937490519)
            ·
              refine ⟨1929215820599022394406235779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1286143880399348262937490519 1929215820599022394406235779)
              ·
                refine ⟨2893823730898533591609353669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1929215820599022394406235779 2893823730898533591609353669)
                ·
                  refine ⟨542591949543475048426753813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2893823730898533591609353669 542591949543475048426753813)
                  ·
                    refine ⟨25433997634850392895004085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 542591949543475048426753813 25433997634850392895004085)
                    ·
                      refine ⟨2384437278267224333906633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25433997634850392895004085 2384437278267224333906633)
                      ·
                        rfl

theorem cell23_4643675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 6, 5].length) (baseStart_4643675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4643675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4643675 prefixEnd_4643675 := by exact prefixLift 4643675
  have htrace : WordTrace (prefixWord ++ tailWord_4643675) baseStart_4643675 baseEnd_4643675 := by
    simpa [prefixWord, tailWord_4643675, baseEnd_4643675] using wordTrace_append hprefix tailTrace_4643675
  have hstable : (prefixWord ++ tailWord_4643675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4643675).length < 2 ^ (prefixWord ++ tailWord_4643675).sum := by decide
  have hdescent : baseEnd_4643675 < baseStart_4643675 := by decide
  rcases family_descends (prefixWord ++ tailWord_4643675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4643692 : List Nat := [2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 5]
def baseStart_4643692 : Nat := 118140960795 + 4643692 * 2 ^ 59
def prefixEnd_4643692 : Nat := 4983230072969 + 3 ^ 40 * 4643692 * 2
def baseEnd_4643692 : Nat := 2384446007438350767394055

theorem tailTrace_4643692 : CollatzResearch.WordTrace tailWord_4643692 prefixEnd_4643692 2384446007438350767394055 := by
  unfold tailWord_4643692
  simp only [CollatzResearch.WordTrace]
  refine ⟨84684680746352219149214665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112912907661802958865619553 84684680746352219149214665)
  ·
    refine ⟨63513510559764164361910999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84684680746352219149214665 63513510559764164361910999)
    ·
      refine ⟨95270265839646246542866499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63513510559764164361910999 95270265839646246542866499)
      ·
        refine ⟨142905398759469369814299749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95270265839646246542866499 142905398759469369814299749)
        ·
          refine ⟨26794762267400506840181203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 142905398759469369814299749 26794762267400506840181203)
          ·
            refine ⟨40192143401100760260271805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26794762267400506840181203 40192143401100760260271805)
            ·
              refine ⟨15072053775412785097601927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40192143401100760260271805 15072053775412785097601927)
              ·
                refine ⟨22608080663119177646402891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15072053775412785097601927 22608080663119177646402891)
                ·
                  refine ⟨33912120994678766469604337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22608080663119177646402891 33912120994678766469604337)
                  ·
                    refine ⟨25434090746009074852203253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33912120994678766469604337 25434090746009074852203253)
                    ·
                      refine ⟨2384446007438350767394055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25434090746009074852203253 2384446007438350767394055)
                      ·
                        rfl

theorem cell23_4643692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 5].length) (baseStart_4643692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4643692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4643692 prefixEnd_4643692 := by exact prefixLift 4643692
  have htrace : WordTrace (prefixWord ++ tailWord_4643692) baseStart_4643692 baseEnd_4643692 := by
    simpa [prefixWord, tailWord_4643692, baseEnd_4643692] using wordTrace_append hprefix tailTrace_4643692
  have hstable : (prefixWord ++ tailWord_4643692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4643692).length < 2 ^ (prefixWord ++ tailWord_4643692).sum := by decide
  have hdescent : baseEnd_4643692 < baseStart_4643692 := by decide
  rcases family_descends (prefixWord ++ tailWord_4643692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4643719 : List Nat := [1, 1, 4, 2, 3, 1, 1, 3, 2, 1, 4]
def baseStart_4643719 : Nat := 118140960795 + 4643719 * 2 ^ 59
def prefixEnd_4643719 : Nat := 4983230072969 + 3 ^ 40 * 4643719 * 2
def baseEnd_4643719 : Nat := 2384459871416022161756431

theorem tailTrace_4643719 : CollatzResearch.WordTrace tailWord_4643719 prefixEnd_4643719 2384459871416022161756431 := by
  unfold tailWord_4643719
  simp only [CollatzResearch.WordTrace]
  refine ⟨169370346263606621909662211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112913564175737747939774807 169370346263606621909662211)
  ·
    refine ⟨254055519395409932864493317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169370346263606621909662211 254055519395409932864493317)
    ·
      refine ⟨47635409886639362412092497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 254055519395409932864493317 47635409886639362412092497)
      ·
        refine ⟨35726557414979521809069373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47635409886639362412092497 35726557414979521809069373)
        ·
          refine ⟨13397459030617320678401015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35726557414979521809069373 13397459030617320678401015)
          ·
            refine ⟨20096188545925981017601523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13397459030617320678401015 20096188545925981017601523)
            ·
              refine ⟨30144282818888971526402285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20096188545925981017601523 30144282818888971526402285)
              ·
                refine ⟨11304106057083364322400857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30144282818888971526402285 11304106057083364322400857)
                ·
                  refine ⟨8478079542812523241800643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11304106057083364322400857 8478079542812523241800643)
                  ·
                    refine ⟨12717119314218784862700965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8478079542812523241800643 12717119314218784862700965)
                    ·
                      refine ⟨2384459871416022161756431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12717119314218784862700965 2384459871416022161756431)
                      ·
                        rfl

theorem cell23_4643719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 3, 2, 1, 4].length) (baseStart_4643719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4643719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4643719 prefixEnd_4643719 := by exact prefixLift 4643719
  have htrace : WordTrace (prefixWord ++ tailWord_4643719) baseStart_4643719 baseEnd_4643719 := by
    simpa [prefixWord, tailWord_4643719, baseEnd_4643719] using wordTrace_append hprefix tailTrace_4643719
  have hstable : (prefixWord ++ tailWord_4643719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4643719).length < 2 ^ (prefixWord ++ tailWord_4643719).sum := by decide
  have hdescent : baseEnd_4643719 < baseStart_4643719 := by decide
  rcases family_descends (prefixWord ++ tailWord_4643719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4643773 : List Nat := [1, 4, 1, 2, 4, 2, 1, 1, 2, 2, 3]
def baseStart_4643773 : Nat := 118140960795 + 4643773 * 2 ^ 59
def prefixEnd_4643773 : Nat := 4983230072969 + 3 ^ 40 * 4643773 * 2
def baseEnd_4643773 : Nat := 2384487599371364950481183

theorem tailTrace_4643773 : CollatzResearch.WordTrace tailWord_4643773 prefixEnd_4643773 2384487599371364950481183 := by
  unfold tailWord_4643773
  simp only [CollatzResearch.WordTrace]
  refine ⟨169372315805410989132127973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112914877203607326088085315 169372315805410989132127973)
  ·
    refine ⟨31757309213514560462273995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 169372315805410989132127973 31757309213514560462273995)
    ·
      refine ⟨47635963820271840693410993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31757309213514560462273995 47635963820271840693410993)
      ·
        refine ⟨35726972865203880520058245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47635963820271840693410993 35726972865203880520058245)
        ·
          refine ⟨6698807412225727597510921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35726972865203880520058245 6698807412225727597510921)
          ·
            refine ⟨5024105559169295698133191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6698807412225727597510921 5024105559169295698133191)
            ·
              refine ⟨7536158338753943547199787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5024105559169295698133191 7536158338753943547199787)
              ·
                refine ⟨11304237508130915320799681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7536158338753943547199787 11304237508130915320799681)
                ·
                  refine ⟨8478178131098186490599761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11304237508130915320799681 8478178131098186490599761)
                  ·
                    refine ⟨6358633598323639867949821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8478178131098186490599761 6358633598323639867949821)
                    ·
                      refine ⟨2384487599371364950481183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6358633598323639867949821 2384487599371364950481183)
                      ·
                        rfl

theorem cell23_4643773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 1, 1, 2, 2, 3].length) (baseStart_4643773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4643773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4643773 prefixEnd_4643773 := by exact prefixLift 4643773
  have htrace : WordTrace (prefixWord ++ tailWord_4643773) baseStart_4643773 baseEnd_4643773 := by
    simpa [prefixWord, tailWord_4643773, baseEnd_4643773] using wordTrace_append hprefix tailTrace_4643773
  have hstable : (prefixWord ++ tailWord_4643773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4643773).length < 2 ^ (prefixWord ++ tailWord_4643773).sum := by decide
  have hdescent : baseEnd_4643773 < baseStart_4643773 := by decide
  rcases family_descends (prefixWord ++ tailWord_4643773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4643779 : List Nat := [1, 1, 1, 3, 1, 1, 2, 5, 1, 5, 2]
def baseStart_4643779 : Nat := 118140960795 + 4643779 * 2 ^ 59
def prefixEnd_4643779 : Nat := 4983230072969 + 3 ^ 40 * 4643779 * 2
def baseEnd_4643779 : Nat := 2384490680255291927006155

theorem tailTrace_4643779 : CollatzResearch.WordTrace tailWord_4643779 prefixEnd_4643779 2384490680255291927006155 := by
  unfold tailWord_4643779
  simp only [CollatzResearch.WordTrace]
  refine ⟨169372534643389252156846391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112915023095592834771230927 169372534643389252156846391)
  ·
    refine ⟨254058801965083878235269587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169372534643389252156846391 254058801965083878235269587)
    ·
      refine ⟨381088202947625817352904381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 254058801965083878235269587 381088202947625817352904381)
      ·
        refine ⟨142908076105359681507339143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 381088202947625817352904381 142908076105359681507339143)
        ·
          refine ⟨214362114158039522261008715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142908076105359681507339143 214362114158039522261008715)
          ·
            refine ⟨321543171237059283391513073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 214362114158039522261008715 321543171237059283391513073)
            ·
              refine ⟨241157378427794462543634805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 321543171237059283391513073 241157378427794462543634805)
              ·
                refine ⟨22608504227605730863465763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 241157378427794462543634805 22608504227605730863465763)
                ·
                  refine ⟨33912756341408596295198645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22608504227605730863465763 33912756341408596295198645)
                  ·
                    refine ⟨3179320907007055902674873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33912756341408596295198645 3179320907007055902674873)
                    ·
                      refine ⟨2384490680255291927006155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3179320907007055902674873 2384490680255291927006155)
                      ·
                        rfl

theorem cell23_4643779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 5, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 5, 1, 5, 2].length) (baseStart_4643779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4643779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4643779 prefixEnd_4643779 := by exact prefixLift 4643779
  have htrace : WordTrace (prefixWord ++ tailWord_4643779) baseStart_4643779 baseEnd_4643779 := by
    simpa [prefixWord, tailWord_4643779, baseEnd_4643779] using wordTrace_append hprefix tailTrace_4643779
  have hstable : (prefixWord ++ tailWord_4643779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4643779).length < 2 ^ (prefixWord ++ tailWord_4643779).sum := by decide
  have hdescent : baseEnd_4643779 < baseStart_4643779 := by decide
  rcases family_descends (prefixWord ++ tailWord_4643779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4643916 : List Nat := [2, 2, 1, 3, 1, 1, 1, 1, 5, 4, 2]
def baseStart_4643916 : Nat := 118140960795 + 4643916 * 2 ^ 59
def prefixEnd_4643916 : Nat := 4983230072969 + 3 ^ 40 * 4643916 * 2
def baseEnd_4643916 : Nat := 2384561027104957890993025

theorem tailTrace_4643916 : CollatzResearch.WordTrace tailWord_4643916 prefixEnd_4643916 2384561027104957890993025 := by
  unfold tailWord_4643916
  simp only [CollatzResearch.WordTrace]
  refine ⟨84688765721946462277291801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112918354295928616369722401 84688765721946462277291801)
  ·
    refine ⟨63516574291459846707968851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84688765721946462277291801 63516574291459846707968851)
    ·
      refine ⟨95274861437189770061953277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63516574291459846707968851 95274861437189770061953277)
      ·
        refine ⟨35728073038946163773232479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95274861437189770061953277 35728073038946163773232479)
        ·
          refine ⟨53592109558419245659848719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35728073038946163773232479 53592109558419245659848719)
          ·
            refine ⟨80388164337628868489773079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53592109558419245659848719 80388164337628868489773079)
            ·
              refine ⟨120582246506443302734659619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80388164337628868489773079 120582246506443302734659619)
              ·
                refine ⟨180873369759664954101989429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 120582246506443302734659619 180873369759664954101989429)
                ·
                  refine ⟨16956878414968589447061509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 180873369759664954101989429 16956878414968589447061509)
                  ·
                    refine ⟨3179414702806610521324033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16956878414968589447061509 3179414702806610521324033)
                    ·
                      refine ⟨2384561027104957890993025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3179414702806610521324033 2384561027104957890993025)
                      ·
                        rfl

theorem cell23_4643916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 5, 4, 2].length) (baseStart_4643916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4643916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4643916 prefixEnd_4643916 := by exact prefixLift 4643916
  have htrace : WordTrace (prefixWord ++ tailWord_4643916) baseStart_4643916 baseEnd_4643916 := by
    simpa [prefixWord, tailWord_4643916, baseEnd_4643916] using wordTrace_append hprefix tailTrace_4643916
  have hstable : (prefixWord ++ tailWord_4643916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4643916).length < 2 ^ (prefixWord ++ tailWord_4643916).sum := by decide
  have hdescent : baseEnd_4643916 < baseStart_4643916 := by decide
  rcases family_descends (prefixWord ++ tailWord_4643916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4643979 : List Nat := [1, 1, 1, 1, 4, 1, 1, 5, 1, 2, 5]
def baseStart_4643979 : Nat := 118140960795 + 4643979 * 2 ^ 59
def prefixEnd_4643979 : Nat := 4983230072969 + 3 ^ 40 * 4643979 * 2
def baseEnd_4643979 : Nat := 2384593376386191144505235

theorem tailTrace_4643979 : CollatzResearch.WordTrace tailWord_4643979 prefixEnd_4643979 2384593376386191144505235 := by
  unfold tailWord_4643979
  simp only [CollatzResearch.WordTrace]
  refine ⟨169379829242664686314126991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112919886161776457542751327 169379829242664686314126991)
  ·
    refine ⟨254069743863997029471190487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169379829242664686314126991 254069743863997029471190487)
    ·
      refine ⟨381104615795995544206785731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 254069743863997029471190487 381104615795995544206785731)
      ·
        refine ⟨571656923693993316310178597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 381104615795995544206785731 571656923693993316310178597)
        ·
          refine ⟨107185673192623746808158487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 571656923693993316310178597 107185673192623746808158487)
          ·
            refine ⟨160778509788935620212237731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107185673192623746808158487 160778509788935620212237731)
            ·
              refine ⟨241167764683403430318356597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 160778509788935620212237731 241167764683403430318356597)
              ·
                refine ⟨22609477939069071592345931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 241167764683403430318356597 22609477939069071592345931)
                ·
                  refine ⟨33914216908603607388518897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22609477939069071592345931 33914216908603607388518897)
                  ·
                    refine ⟨25435662681452705541389173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33914216908603607388518897 25435662681452705541389173)
                    ·
                      refine ⟨2384593376386191144505235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25435662681452705541389173 2384593376386191144505235)
                      ·
                        rfl

theorem cell23_4643979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 5, 1, 2, 5].length) (baseStart_4643979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4643979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4643979 prefixEnd_4643979 := by exact prefixLift 4643979
  have htrace : WordTrace (prefixWord ++ tailWord_4643979) baseStart_4643979 baseEnd_4643979 := by
    simpa [prefixWord, tailWord_4643979, baseEnd_4643979] using wordTrace_append hprefix tailTrace_4643979
  have hstable : (prefixWord ++ tailWord_4643979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4643979).length < 2 ^ (prefixWord ++ tailWord_4643979).sum := by decide
  have hdescent : baseEnd_4643979 < baseStart_4643979 := by decide
  rcases family_descends (prefixWord ++ tailWord_4643979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4643986 : List Nat := [3, 2, 3, 1, 1, 2, 1, 2, 1, 7]
def baseStart_4643986 : Nat := 118140960795 + 4643986 * 2 ^ 59
def prefixEnd_4643986 : Nat := 4983230072969 + 3 ^ 40 * 4643986 * 2
def baseEnd_4643986 : Nat := 794865656916924205705901

theorem tailTrace_4643986 : CollatzResearch.WordTrace tailWord_4643986 prefixEnd_4643986 794865656916924205705901 := by
  unfold tailWord_4643986
  simp only [CollatzResearch.WordTrace]
  refine ⟨42345021138409831627407953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112920056369092884339754541 42345021138409831627407953)
  ·
    refine ⟨31758765853807373720555965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42345021138409831627407953 31758765853807373720555965)
    ·
      refine ⟨11909537195177765145208487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31758765853807373720555965 11909537195177765145208487)
      ·
        refine ⟨17864305792766647717812731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11909537195177765145208487 17864305792766647717812731)
        ·
          refine ⟨26796458689149971576719097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17864305792766647717812731 26796458689149971576719097)
          ·
            refine ⟨20097344016862478682539323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26796458689149971576719097 20097344016862478682539323)
            ·
              refine ⟨30146016025293718023808985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20097344016862478682539323 30146016025293718023808985)
              ·
                refine ⟨22609512018970288517856739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30146016025293718023808985 22609512018970288517856739)
                ·
                  refine ⟨33914268028455432776785109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22609512018970288517856739 33914268028455432776785109)
                  ·
                    refine ⟨794865656916924205705901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33914268028455432776785109 794865656916924205705901)
                    ·
                      rfl

theorem cell23_4643986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 2, 1, 7].length) (baseStart_4643986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4643986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4643986 prefixEnd_4643986 := by exact prefixLift 4643986
  have htrace : WordTrace (prefixWord ++ tailWord_4643986) baseStart_4643986 baseEnd_4643986 := by
    simpa [prefixWord, tailWord_4643986, baseEnd_4643986] using wordTrace_append hprefix tailTrace_4643986
  have hstable : (prefixWord ++ tailWord_4643986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4643986).length < 2 ^ (prefixWord ++ tailWord_4643986).sum := by decide
  have hdescent : baseEnd_4643986 < baseStart_4643986 := by decide
  rcases family_descends (prefixWord ++ tailWord_4643986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4644019 : List Nat := [1, 1, 1, 2, 3, 2, 2, 1, 1, 3, 6]
def baseStart_4644019 : Nat := 118140960795 + 4644019 * 2 ^ 59
def prefixEnd_4644019 : Nat := 4983230072969 + 3 ^ 40 * 4644019 * 2
def baseEnd_4644019 : Nat := 2384613915612370988005051

theorem tailTrace_4644019 : CollatzResearch.WordTrace tailWord_4644019 prefixEnd_4644019 2384613915612370988005051 := by
  unfold tailWord_4644019
  simp only [CollatzResearch.WordTrace]
  refine ⟨169381288162519773145583111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112920858775013182097055407 169381288162519773145583111)
  ·
    refine ⟨254071932243779659718374667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169381288162519773145583111 254071932243779659718374667)
    ·
      refine ⟨381107898365669489577562001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 254071932243779659718374667 381107898365669489577562001)
      ·
        refine ⟨285830923774252117183171501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 381107898365669489577562001 285830923774252117183171501)
        ·
          refine ⟨107186596415344543943689313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 285830923774252117183171501 107186596415344543943689313)
          ·
            refine ⟨80389947311508407957766985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107186596415344543943689313 80389947311508407957766985)
            ·
              refine ⟨60292460483631305968325239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80389947311508407957766985 60292460483631305968325239)
              ·
                refine ⟨90438690725446958952487859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60292460483631305968325239 90438690725446958952487859)
                ·
                  refine ⟨135658036088170438428731789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 90438690725446958952487859 135658036088170438428731789)
                  ·
                    refine ⟨50871763533063914410774421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 135658036088170438428731789 50871763533063914410774421)
                    ·
                      refine ⟨2384613915612370988005051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50871763533063914410774421 2384613915612370988005051)
                      ·
                        rfl

theorem cell23_4644019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 3, 6].length) (baseStart_4644019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4644019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4644019 prefixEnd_4644019 := by exact prefixLift 4644019
  have htrace : WordTrace (prefixWord ++ tailWord_4644019) baseStart_4644019 baseEnd_4644019 := by
    simpa [prefixWord, tailWord_4644019, baseEnd_4644019] using wordTrace_append hprefix tailTrace_4644019
  have hstable : (prefixWord ++ tailWord_4644019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4644019).length < 2 ^ (prefixWord ++ tailWord_4644019).sum := by decide
  have hdescent : baseEnd_4644019 < baseStart_4644019 := by decide
  rcases family_descends (prefixWord ++ tailWord_4644019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4644113 : List Nat := [1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 4]
def baseStart_4644113 : Nat := 118140960795 + 4644113 * 2 ^ 59
def prefixEnd_4644113 : Nat := 4983230072969 + 3 ^ 40 * 4644113 * 2
def baseEnd_4644113 : Nat := 2384662182793893620229619

theorem tailTrace_4644113 : CollatzResearch.WordTrace tailWord_4644113 prefixEnd_4644113 2384662182793893620229619 := by
  unfold tailWord_4644113
  simp only [CollatzResearch.WordTrace]
  refine ⟨169384716624179227199504993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112923144416119484799669995 169384716624179227199504993)
  ·
    refine ⟨127038537468134420399628745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169384716624179227199504993 127038537468134420399628745)
    ·
      refine ⟨95278903101100815299721559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127038537468134420399628745 95278903101100815299721559)
      ·
        refine ⟨142918354651651222949582339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95278903101100815299721559 142918354651651222949582339)
        ·
          refine ⟨214377531977476834424373509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142918354651651222949582339 214377531977476834424373509)
          ·
            refine ⟨40195787245776906454570033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 214377531977476834424373509 40195787245776906454570033)
            ·
              refine ⟨30146840434332679840927525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40195787245776906454570033 30146840434332679840927525)
              ·
                refine ⟨5652532581437377470173911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30146840434332679840927525 5652532581437377470173911)
                ·
                  refine ⟨8478798872156066205260867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5652532581437377470173911 8478798872156066205260867)
                  ·
                    refine ⟨12718198308234099307891301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8478798872156066205260867 12718198308234099307891301)
                    ·
                      refine ⟨2384662182793893620229619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12718198308234099307891301 2384662182793893620229619)
                      ·
                        rfl

theorem cell23_4644113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 4].length) (baseStart_4644113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4644113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4644113 prefixEnd_4644113 := by exact prefixLift 4644113
  have htrace : WordTrace (prefixWord ++ tailWord_4644113) baseStart_4644113 baseEnd_4644113 := by
    simpa [prefixWord, tailWord_4644113, baseEnd_4644113] using wordTrace_append hprefix tailTrace_4644113
  have hstable : (prefixWord ++ tailWord_4644113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4644113).length < 2 ^ (prefixWord ++ tailWord_4644113).sum := by decide
  have hdescent : baseEnd_4644113 < baseStart_4644113 := by decide
  rcases family_descends (prefixWord ++ tailWord_4644113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4644127 : List Nat := [1, 1, 2, 4, 4, 2, 2, 1, 1, 5]
def baseStart_4644127 : Nat := 118140960795 + 4644127 * 2 ^ 59
def prefixEnd_4644127 : Nat := 4983230072969 + 3 ^ 40 * 4644127 * 2
def baseEnd_4644127 : Nat := 794889790507685521818185

theorem tailTrace_4644127 : CollatzResearch.WordTrace tailWord_4644127 prefixEnd_4644127 794889790507685521818185 := by
  unfold tailWord_4644127
  simp only [CollatzResearch.WordTrace]
  refine ⟨169385227246128507590514635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112923484830752338393676423 169385227246128507590514635)
  ·
    refine ⟨254077840869192761385771953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169385227246128507590514635 254077840869192761385771953)
    ·
      refine ⟨190558380651894571039328965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 254077840869192761385771953 190558380651894571039328965)
      ·
        refine ⟨35729696372230232069874181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 190558380651894571039328965 35729696372230232069874181)
        ·
          refine ⟨6699318069793168513101409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35729696372230232069874181 6699318069793168513101409)
          ·
            refine ⟨5024488552344876384826057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6699318069793168513101409 5024488552344876384826057)
            ·
              refine ⟨3768366414258657288619543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5024488552344876384826057 3768366414258657288619543)
              ·
                refine ⟨5652549621387985932929315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3768366414258657288619543 5652549621387985932929315)
                ·
                  refine ⟨8478824432081978899393973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5652549621387985932929315 8478824432081978899393973)
                  ·
                    refine ⟨794889790507685521818185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8478824432081978899393973 794889790507685521818185)
                    ·
                      rfl

theorem cell23_4644127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 2, 1, 1, 5].length) (baseStart_4644127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4644127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4644127 prefixEnd_4644127 := by exact prefixLift 4644127
  have htrace : WordTrace (prefixWord ++ tailWord_4644127) baseStart_4644127 baseEnd_4644127 := by
    simpa [prefixWord, tailWord_4644127, baseEnd_4644127] using wordTrace_append hprefix tailTrace_4644127
  have hstable : (prefixWord ++ tailWord_4644127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4644127).length < 2 ^ (prefixWord ++ tailWord_4644127).sum := by decide
  have hdescent : baseEnd_4644127 < baseStart_4644127 := by decide
  rcases family_descends (prefixWord ++ tailWord_4644127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4644147 : List Nat := [1, 1, 1, 2, 5, 3, 2, 1, 3, 2, 2]
def baseStart_4644147 : Nat := 118140960795 + 4644147 * 2 ^ 59
def prefixEnd_4644147 : Nat := 4983230072969 + 3 ^ 40 * 4644147 * 2
def baseEnd_4644147 : Nat := 2384679641136146487204463

theorem tailTrace_4644147 : CollatzResearch.WordTrace tailWord_4644147 prefixEnd_4644147 2384679641136146487204463 := by
  unfold tailWord_4644147
  simp only [CollatzResearch.WordTrace]
  refine ⟨169385956706056051006242695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112923971137370700670828463 169385956706056051006242695)
  ·
    refine ⟨254078935059084076509364043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169385956706056051006242695 254078935059084076509364043)
    ·
      refine ⟨381118402588626114764046065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 254078935059084076509364043 381118402588626114764046065)
      ·
        refine ⟨285838801941469586073034549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 381118402588626114764046065 285838801941469586073034549)
        ·
          refine ⟨26797387682012773694346989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 285838801941469586073034549 26797387682012773694346989)
          ·
            refine ⟨10049020380754790135380121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26797387682012773694346989 10049020380754790135380121)
            ·
              refine ⟨7536765285566092601535091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10049020380754790135380121 7536765285566092601535091)
              ·
                refine ⟨11305147928349138902302637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7536765285566092601535091 11305147928349138902302637)
                ·
                  refine ⟨4239430473130927088363489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11305147928349138902302637 4239430473130927088363489)
                  ·
                    refine ⟨3179572854848195316272617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4239430473130927088363489 3179572854848195316272617)
                    ·
                      refine ⟨2384679641136146487204463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3179572854848195316272617 2384679641136146487204463)
                      ·
                        rfl

theorem cell23_4644147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 2, 1, 3, 2, 2].length) (baseStart_4644147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4644147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4644147 prefixEnd_4644147 := by exact prefixLift 4644147
  have htrace : WordTrace (prefixWord ++ tailWord_4644147) baseStart_4644147 baseEnd_4644147 := by
    simpa [prefixWord, tailWord_4644147, baseEnd_4644147] using wordTrace_append hprefix tailTrace_4644147
  have hstable : (prefixWord ++ tailWord_4644147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4644147).length < 2 ^ (prefixWord ++ tailWord_4644147).sum := by decide
  have hdescent : baseEnd_4644147 < baseStart_4644147 := by decide
  rcases family_descends (prefixWord ++ tailWord_4644147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4644157 : List Nat := [1, 4, 1, 5, 1, 2, 1, 1, 1, 6]
def baseStart_4644157 : Nat := 118140960795 + 4644157 * 2 ^ 59
def prefixEnd_4644157 : Nat := 4983230072969 + 3 ^ 40 * 4644157 * 2
def baseEnd_4644157 : Nat := 794894925314230482693139

theorem tailTrace_4644157 : CollatzResearch.WordTrace tailWord_4644157 prefixEnd_4644157 794894925314230482693139 := by
  unfold tailWord_4644157
  simp only [CollatzResearch.WordTrace]
  refine ⟨169386321436019822714106725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112924214290679881809404483 169386321436019822714106725)
  ·
    refine ⟨31759935269253716758895011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 169386321436019822714106725 31759935269253716758895011)
    ·
      refine ⟨47639902903880575138342517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31759935269253716758895011 47639902903880575138342517)
      ·
        refine ⟨4466240897238803919219611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 47639902903880575138342517 4466240897238803919219611)
        ·
          refine ⟨6699361345858205878829417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4466240897238803919219611 6699361345858205878829417)
          ·
            refine ⟨5024521009393654409122063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6699361345858205878829417 5024521009393654409122063)
            ·
              refine ⟨7536781514090481613683095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5024521009393654409122063 7536781514090481613683095)
              ·
                refine ⟨11305172271135722420524643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7536781514090481613683095 11305172271135722420524643)
                ·
                  refine ⟨16957758406703583630786965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11305172271135722420524643 16957758406703583630786965)
                  ·
                    refine ⟨794894925314230482693139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16957758406703583630786965 794894925314230482693139)
                    ·
                      rfl

theorem cell23_4644157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 1, 1, 1, 6].length) (baseStart_4644157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4644157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4644157 prefixEnd_4644157 := by exact prefixLift 4644157
  have htrace : WordTrace (prefixWord ++ tailWord_4644157) baseStart_4644157 baseEnd_4644157 := by
    simpa [prefixWord, tailWord_4644157, baseEnd_4644157] using wordTrace_append hprefix tailTrace_4644157
  have hstable : (prefixWord ++ tailWord_4644157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4644157).length < 2 ^ (prefixWord ++ tailWord_4644157).sum := by decide
  have hdescent : baseEnd_4644157 < baseStart_4644157 := by decide
  rcases family_descends (prefixWord ++ tailWord_4644157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4644164 : List Nat := [2, 3, 4, 1, 1, 1, 2, 2, 3, 2, 2]
def baseStart_4644164 : Nat := 118140960795 + 4644164 * 2 ^ 59
def prefixEnd_4644164 : Nat := 4983230072969 + 3 ^ 40 * 4644164 * 2
def baseEnd_4644164 : Nat := 2384688370307272920691885

theorem tailTrace_4644164 : CollatzResearch.WordTrace tailWord_4644164 prefixEnd_4644164 2384688370307272920691885 := by
  unfold tailWord_4644164
  simp only [CollatzResearch.WordTrace]
  refine ⟨84693288373497231454805773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112924384497996308606407697 84693288373497231454805773)
  ·
    refine ⟨31759983140061461795552165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84693288373497231454805773 31759983140061461795552165)
    ·
      refine ⟨5954996838761524086666031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31759983140061461795552165 5954996838761524086666031)
      ·
        refine ⟨8932495258142286129999047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5954996838761524086666031 8932495258142286129999047)
        ·
          refine ⟨13398742887213429194998571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8932495258142286129999047 13398742887213429194998571)
          ·
            refine ⟨20098114330820143792497857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13398742887213429194998571 20098114330820143792497857)
            ·
              refine ⟨15073585748115107844373393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20098114330820143792497857 15073585748115107844373393)
              ·
                refine ⟨11305189311086330883280045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15073585748115107844373393 11305189311086330883280045)
                ·
                  refine ⟨4239445991657374081230017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11305189311086330883280045 4239445991657374081230017)
                  ·
                    refine ⟨3179584493743030560922513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4239445991657374081230017 3179584493743030560922513)
                    ·
                      refine ⟨2384688370307272920691885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3179584493743030560922513 2384688370307272920691885)
                      ·
                        rfl

theorem cell23_4644164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 2, 3, 2, 2].length) (baseStart_4644164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4644164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4644164 prefixEnd_4644164 := by exact prefixLift 4644164
  have htrace : WordTrace (prefixWord ++ tailWord_4644164) baseStart_4644164 baseEnd_4644164 := by
    simpa [prefixWord, tailWord_4644164, baseEnd_4644164] using wordTrace_append hprefix tailTrace_4644164
  have hstable : (prefixWord ++ tailWord_4644164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4644164).length < 2 ^ (prefixWord ++ tailWord_4644164).sum := by decide
  have hdescent : baseEnd_4644164 < baseStart_4644164 := by decide
  rcases family_descends (prefixWord ++ tailWord_4644164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4644176 : List Nat := [2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 5]
def baseStart_4644176 : Nat := 118140960795 + 4644176 * 2 ^ 59
def prefixEnd_4644176 : Nat := 4983230072969 + 3 ^ 40 * 4644176 * 2
def baseEnd_4644176 : Nat := 2384694532075126873741829

theorem tailTrace_4644176 : CollatzResearch.WordTrace tailWord_4644176 prefixEnd_4644176 2384694532075126873741829 := by
  unfold tailWord_4644176
  simp only [CollatzResearch.WordTrace]
  refine ⟨84693507211475494479524191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112924676281967325972698921 84693507211475494479524191)
  ·
    refine ⟨127040260817213241719286287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84693507211475494479524191 127040260817213241719286287)
    ·
      refine ⟨190560391225819862578929431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127040260817213241719286287 190560391225819862578929431)
      ·
        refine ⟨285840586838729793868394147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190560391225819862578929431 285840586838729793868394147)
        ·
          refine ⟨428760880258094690802591221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 285840586838729793868394147 428760880258094690802591221)
          ·
            refine ⟨40196332524196377262742927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 428760880258094690802591221 40196332524196377262742927)
            ·
              refine ⟨60294498786294565894114391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40196332524196377262742927 60294498786294565894114391)
              ·
                refine ⟨90441748179441848841171587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60294498786294565894114391 90441748179441848841171587)
                ·
                  refine ⟨135662622269162773261757381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 90441748179441848841171587 135662622269162773261757381)
                  ·
                    refine ⟨25436741675468019986579509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 135662622269162773261757381 25436741675468019986579509)
                    ·
                      refine ⟨2384694532075126873741829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25436741675468019986579509 2384694532075126873741829)
                      ·
                        rfl

theorem cell23_4644176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 5].length) (baseStart_4644176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4644176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4644176 prefixEnd_4644176 := by exact prefixLift 4644176
  have htrace : WordTrace (prefixWord ++ tailWord_4644176) baseStart_4644176 baseEnd_4644176 := by
    simpa [prefixWord, tailWord_4644176, baseEnd_4644176] using wordTrace_append hprefix tailTrace_4644176
  have hstable : (prefixWord ++ tailWord_4644176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4644176).length < 2 ^ (prefixWord ++ tailWord_4644176).sum := by decide
  have hdescent : baseEnd_4644176 < baseStart_4644176 := by decide
  rcases family_descends (prefixWord ++ tailWord_4644176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4644180 : List Nat := [2, 4, 1, 1, 2, 1, 1, 1, 6, 1, 3]
def baseStart_4644180 : Nat := 118140960795 + 4644180 * 2 ^ 59
def prefixEnd_4644180 : Nat := 4983230072969 + 3 ^ 40 * 4644180 * 2
def baseEnd_4644180 : Nat := 2384696585997744858091811

theorem tailTrace_4644180 : CollatzResearch.WordTrace tailWord_4644180 prefixEnd_4644180 2384696585997744858091811 := by
  unfold tailWord_4644180
  simp only [CollatzResearch.WordTrace]
  refine ⟨84693580157468248821096997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112924773543290998428129329 84693580157468248821096997)
  ·
    refine ⟨15880046279525296653955687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84693580157468248821096997 15880046279525296653955687)
    ·
      refine ⟨23820069419287944980933531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15880046279525296653955687 23820069419287944980933531)
      ·
        refine ⟨35730104128931917471400297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23820069419287944980933531 35730104128931917471400297)
        ·
          refine ⟨26797578096698938103550223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35730104128931917471400297 26797578096698938103550223)
          ·
            refine ⟨40196367145048407155325335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26797578096698938103550223 40196367145048407155325335)
            ·
              refine ⟨60294550717572610732988003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40196367145048407155325335 60294550717572610732988003)
              ·
                refine ⟨90441826076358916099482005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60294550717572610732988003 90441826076358916099482005)
                ·
                  refine ⟨4239460597329324192163219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 90441826076358916099482005 4239460597329324192163219)
                  ·
                    refine ⟨6359190895993986288244829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4239460597329324192163219 6359190895993986288244829)
                    ·
                      refine ⟨2384696585997744858091811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6359190895993986288244829 2384696585997744858091811)
                      ·
                        rfl

theorem cell23_4644180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 6, 1, 3].length) (baseStart_4644180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4644180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4644180 prefixEnd_4644180 := by exact prefixLift 4644180
  have htrace : WordTrace (prefixWord ++ tailWord_4644180) baseStart_4644180 baseEnd_4644180 := by
    simpa [prefixWord, tailWord_4644180, baseEnd_4644180] using wordTrace_append hprefix tailTrace_4644180
  have hstable : (prefixWord ++ tailWord_4644180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4644180).length < 2 ^ (prefixWord ++ tailWord_4644180).sum := by decide
  have hdescent : baseEnd_4644180 < baseStart_4644180 := by decide
  rcases family_descends (prefixWord ++ tailWord_4644180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4644181 : List Nat := [1, 3, 2, 2, 3, 3, 1, 3, 1, 2, 2]
def baseStart_4644181 : Nat := 118140960795 + 4644181 * 2 ^ 59
def prefixEnd_4644181 : Nat := 4983230072969 + 3 ^ 40 * 4644181 * 2
def baseEnd_4644181 : Nat := 2384697099478399354179307

theorem tailTrace_4644181 : CollatzResearch.WordTrace tailWord_4644181 prefixEnd_4644181 2384697099478399354179307 := by
  unfold tailWord_4644181
  simp only [CollatzResearch.WordTrace]
  refine ⟨169387196787932874812980397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112924797858621916541986931 169387196787932874812980397)
  ·
    refine ⟨63520198795474828054867649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 169387196787932874812980397 63520198795474828054867649)
    ·
      refine ⟨47640149096606121041150737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63520198795474828054867649 47640149096606121041150737)
      ·
        refine ⟨35730111822454590780863053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47640149096606121041150737 35730111822454590780863053)
        ·
          refine ⟨13398791933420471542823645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35730111822454590780863053 13398791933420471542823645)
          ·
            refine ⟨5024546975032676828558867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13398791933420471542823645 5024546975032676828558867)
            ·
              refine ⟨7536820462549015242838301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5024546975032676828558867 7536820462549015242838301)
              ·
                refine ⟨2826307673455880716064363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7536820462549015242838301 2826307673455880716064363)
                ·
                  refine ⟨4239461510183821074096545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2826307673455880716064363 4239461510183821074096545)
                  ·
                    refine ⟨3179596132637865805572409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4239461510183821074096545 3179596132637865805572409)
                    ·
                      refine ⟨2384697099478399354179307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3179596132637865805572409 2384697099478399354179307)
                      ·
                        rfl

theorem cell23_4644181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 1, 3, 1, 2, 2].length) (baseStart_4644181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4644181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4644181 prefixEnd_4644181 := by exact prefixLift 4644181
  have htrace : WordTrace (prefixWord ++ tailWord_4644181) baseStart_4644181 baseEnd_4644181 := by
    simpa [prefixWord, tailWord_4644181, baseEnd_4644181] using wordTrace_append hprefix tailTrace_4644181
  have hstable : (prefixWord ++ tailWord_4644181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4644181).length < 2 ^ (prefixWord ++ tailWord_4644181).sum := by decide
  have hdescent : baseEnd_4644181 < baseStart_4644181 := by decide
  rcases family_descends (prefixWord ++ tailWord_4644181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4644203 : List Nat := [1, 1, 1, 1, 2, 2, 2, 1, 2, 8, 2]
def baseStart_4644203 : Nat := 118140960795 + 4644203 * 2 ^ 59
def prefixEnd_4644203 : Nat := 4983230072969 + 3 ^ 40 * 4644203 * 2
def baseEnd_4644203 : Nat := 2384708396052798268104205

theorem tailTrace_4644203 : CollatzResearch.WordTrace tailWord_4644203 prefixEnd_4644203 2384708396052798268104205 := by
  unfold tailWord_4644203
  simp only [CollatzResearch.WordTrace]
  refine ⟨169387999193853172570281263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112925332795902115046854175 169387999193853172570281263)
  ·
    refine ⟨254081998790779758855421895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169387999193853172570281263 254081998790779758855421895)
    ·
      refine ⟨381122998186169638283132843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 254081998790779758855421895 381122998186169638283132843)
      ·
        refine ⟨571684497279254457424699265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 381122998186169638283132843 571684497279254457424699265)
        ·
          refine ⟨428763372959440843068524449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 571684497279254457424699265 428763372959440843068524449)
          ·
            refine ⟨321572529719580632301393337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 428763372959440843068524449 321572529719580632301393337)
            ·
              refine ⟨241179397289685474226045003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 321572529719580632301393337 241179397289685474226045003)
              ·
                refine ⟨361769095934528211339067505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 241179397289685474226045003 361769095934528211339067505)
                ·
                  refine ⟨271326821950896158504300629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 361769095934528211339067505 271326821950896158504300629)
                  ·
                    refine ⟨3179611194737064357472273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 271326821950896158504300629 3179611194737064357472273)
                    ·
                      refine ⟨2384708396052798268104205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3179611194737064357472273 2384708396052798268104205)
                      ·
                        rfl

theorem cell23_4644203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 8, 2].length) (baseStart_4644203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4644203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4644203 prefixEnd_4644203 := by exact prefixLift 4644203
  have htrace : WordTrace (prefixWord ++ tailWord_4644203) baseStart_4644203 baseEnd_4644203 := by
    simpa [prefixWord, tailWord_4644203, baseEnd_4644203] using wordTrace_append hprefix tailTrace_4644203
  have hstable : (prefixWord ++ tailWord_4644203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4644203).length < 2 ^ (prefixWord ++ tailWord_4644203).sum := by decide
  have hdescent : baseEnd_4644203 < baseStart_4644203 := by decide
  rcases family_descends (prefixWord ++ tailWord_4644203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4644216 : List Nat := [2, 1, 2, 1, 1, 1, 1, 1, 4, 3, 6]
def baseStart_4644216 : Nat := 118140960795 + 4644216 * 2 ^ 59
def prefixEnd_4644216 : Nat := 4983230072969 + 3 ^ 40 * 4644216 * 2
def baseEnd_4644216 : Nat := 2384715071301306717241645

theorem tailTrace_4644216 : CollatzResearch.WordTrace tailWord_4644216 prefixEnd_4644216 2384715071301306717241645 := by
  unfold tailWord_4644216
  simp only [CollatzResearch.WordTrace]
  refine ⟨84694236671403037895252251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112925648895204050527003001 84694236671403037895252251)
  ·
    refine ⟨127041355007104556842878377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84694236671403037895252251 127041355007104556842878377)
    ·
      refine ⟨95281016255328417632158783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127041355007104556842878377 95281016255328417632158783)
      ·
        refine ⟨142921524382992626448238175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95281016255328417632158783 142921524382992626448238175)
        ·
          refine ⟨214382286574488939672357263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142921524382992626448238175 214382286574488939672357263)
          ·
            refine ⟨321573429861733409508535895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 214382286574488939672357263 321573429861733409508535895)
            ·
              refine ⟨482360144792600114262803843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 321573429861733409508535895 482360144792600114262803843)
              ·
                refine ⟨723540217188900171394205765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 482360144792600114262803843 723540217188900171394205765)
                ·
                  refine ⟨135663790722918782136413581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 723540217188900171394205765 135663790722918782136413581)
                  ·
                    refine ⟨50873921521094543301155093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 135663790722918782136413581 50873921521094543301155093)
                    ·
                      refine ⟨2384715071301306717241645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50873921521094543301155093 2384715071301306717241645)
                      ·
                        rfl

theorem cell23_4644216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 4, 3, 6].length) (baseStart_4644216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4644216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4644216 prefixEnd_4644216 := by exact prefixLift 4644216
  have htrace : WordTrace (prefixWord ++ tailWord_4644216) baseStart_4644216 baseEnd_4644216 := by
    simpa [prefixWord, tailWord_4644216, baseEnd_4644216] using wordTrace_append hprefix tailTrace_4644216
  have hstable : (prefixWord ++ tailWord_4644216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4644216).length < 2 ^ (prefixWord ++ tailWord_4644216).sum := by decide
  have hdescent : baseEnd_4644216 < baseStart_4644216 := by decide
  rcases family_descends (prefixWord ++ tailWord_4644216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4644220 : List Nat := [2, 2, 2, 1, 1, 1, 4, 3, 1, 4, 2]
def baseStart_4644220 : Nat := 118140960795 + 4644220 * 2 ^ 59
def prefixEnd_4644220 : Nat := 4983230072969 + 3 ^ 40 * 4644220 * 2
def baseEnd_4644220 : Nat := 2384717125223924701591627

theorem tailTrace_4644220 : CollatzResearch.WordTrace tailWord_4644220 prefixEnd_4644220 2384717125223924701591627 := by
  unfold tailWord_4644220
  simp only [CollatzResearch.WordTrace]
  refine ⟨84694309617395792236825057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112925746156527722982433409 84694309617395792236825057)
  ·
    refine ⟨63520732213046844177618793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84694309617395792236825057 63520732213046844177618793)
    ·
      refine ⟨47640549159785133133214095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63520732213046844177618793 47640549159785133133214095)
      ·
        refine ⟨71460823739677699699821143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47640549159785133133214095 71460823739677699699821143)
        ·
          refine ⟨107191235609516549549731715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71460823739677699699821143 107191235609516549549731715)
          ·
            refine ⟨160786853414274824324597573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107191235609516549549731715 160786853414274824324597573)
            ·
              refine ⟨30147535015176529560862045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 160786853414274824324597573 30147535015176529560862045)
              ·
                refine ⟨11305325630691198585323267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30147535015176529560862045 11305325630691198585323267)
                ·
                  refine ⟨16957988446036797877984901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11305325630691198585323267 16957988446036797877984901)
                  ·
                    refine ⟨3179622833631899602122169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16957988446036797877984901 3179622833631899602122169)
                    ·
                      refine ⟨2384717125223924701591627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3179622833631899602122169 2384717125223924701591627)
                      ·
                        rfl

theorem cell23_4644220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 3, 1, 4, 2].length) (baseStart_4644220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4644220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4644220 prefixEnd_4644220 := by exact prefixLift 4644220
  have htrace : WordTrace (prefixWord ++ tailWord_4644220) baseStart_4644220 baseEnd_4644220 := by
    simpa [prefixWord, tailWord_4644220, baseEnd_4644220] using wordTrace_append hprefix tailTrace_4644220
  have hstable : (prefixWord ++ tailWord_4644220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4644220).length < 2 ^ (prefixWord ++ tailWord_4644220).sum := by decide
  have hdescent : baseEnd_4644220 < baseStart_4644220 := by decide
  rcases family_descends (prefixWord ++ tailWord_4644220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4644273 : List Nat := [1, 2, 2, 4, 1, 1, 2, 2, 1, 7]
def baseStart_4644273 : Nat := 118140960795 + 4644273 * 2 ^ 59
def prefixEnd_4644273 : Nat := 4983230072969 + 3 ^ 40 * 4644273 * 2
def baseEnd_4644273 : Nat := 794914779899537664742961

theorem tailTrace_4644273 : CollatzResearch.WordTrace tailWord_4644273 prefixEnd_4644273 794914779899537664742961 := by
  unfold tailWord_4644273
  simp only [CollatzResearch.WordTrace]
  refine ⟨169390552303599574525329473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112927034869066383016886315 169390552303599574525329473)
  ·
    refine ⟨127042914227699680893997105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169390552303599574525329473 127042914227699680893997105)
    ·
      refine ⟨95282185670774760670497829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127042914227699680893997105 95282185670774760670497829)
      ·
        refine ⟨17865409813270267625718343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 95282185670774760670497829 17865409813270267625718343)
        ·
          refine ⟨26798114719905401438577515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17865409813270267625718343 26798114719905401438577515)
          ·
            refine ⟨40197172079858102157866273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26798114719905401438577515 40197172079858102157866273)
            ·
              refine ⟨30147879059893576618399705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40197172079858102157866273 30147879059893576618399705)
              ·
                refine ⟨22610909294920182463799779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30147879059893576618399705 22610909294920182463799779)
                ·
                  refine ⟨33916363942380273695699669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22610909294920182463799779 33916363942380273695699669)
                  ·
                    refine ⟨794914779899537664742961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33916363942380273695699669 794914779899537664742961)
                    ·
                      rfl

theorem cell23_4644273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 2, 1, 7].length) (baseStart_4644273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4644273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4644273 prefixEnd_4644273 := by exact prefixLift 4644273
  have htrace : WordTrace (prefixWord ++ tailWord_4644273) baseStart_4644273 baseEnd_4644273 := by
    simpa [prefixWord, tailWord_4644273, baseEnd_4644273] using wordTrace_append hprefix tailTrace_4644273
  have hstable : (prefixWord ++ tailWord_4644273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4644273).length < 2 ^ (prefixWord ++ tailWord_4644273).sum := by decide
  have hdescent : baseEnd_4644273 < baseStart_4644273 := by decide
  rcases family_descends (prefixWord ++ tailWord_4644273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4644327 : List Nat := [1, 1, 5, 2, 1, 2, 2, 1, 2, 4, 2]
def baseStart_4644327 : Nat := 118140960795 + 4644327 * 2 ^ 59
def prefixEnd_4644327 : Nat := 4983230072969 + 3 ^ 40 * 4644327 * 2
def baseEnd_4644327 : Nat := 2384772067653955782953635

theorem tailTrace_4644327 : CollatzResearch.WordTrace tailWord_4644327 prefixEnd_4644327 2384772067653955782953635 := by
  unfold tailWord_4644327
  simp only [CollatzResearch.WordTrace]
  refine ⟨169392521845403941747795235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112928347896935961165196823 169392521845403941747795235)
  ·
    refine ⟨254088782768105912621692853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169392521845403941747795235 254088782768105912621692853)
    ·
      refine ⟨23820823384509929308283705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 254088782768105912621692853 23820823384509929308283705)
      ·
        refine ⟨17865617538382446981212779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23820823384509929308283705 17865617538382446981212779)
        ·
          refine ⟨26798426307573670471819169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17865617538382446981212779 26798426307573670471819169)
          ·
            refine ⟨20098819730680252853864377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26798426307573670471819169 20098819730680252853864377)
            ·
              refine ⟨15074114798010189640398283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20098819730680252853864377 15074114798010189640398283)
              ·
                refine ⟨22611172197015284460597425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15074114798010189640398283 22611172197015284460597425)
                ·
                  refine ⟨16958379147761463345448069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22611172197015284460597425 16958379147761463345448069)
                  ·
                    refine ⟨3179696090205274377271513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16958379147761463345448069 3179696090205274377271513)
                    ·
                      refine ⟨2384772067653955782953635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3179696090205274377271513 2384772067653955782953635)
                      ·
                        rfl

theorem cell23_4644327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 1, 2, 4, 2].length) (baseStart_4644327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4644327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4644327 prefixEnd_4644327 := by exact prefixLift 4644327
  have htrace : WordTrace (prefixWord ++ tailWord_4644327) baseStart_4644327 baseEnd_4644327 := by
    simpa [prefixWord, tailWord_4644327, baseEnd_4644327] using wordTrace_append hprefix tailTrace_4644327
  have hstable : (prefixWord ++ tailWord_4644327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4644327).length < 2 ^ (prefixWord ++ tailWord_4644327).sum := by decide
  have hdescent : baseEnd_4644327 < baseStart_4644327 := by decide
  rcases family_descends (prefixWord ++ tailWord_4644327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4644380 : List Nat := [2, 2, 3, 1, 2, 1, 2, 2, 3, 5]
def baseStart_4644380 : Nat := 118140960795 + 4644380 * 2 ^ 59
def prefixEnd_4644380 : Nat := 4983230072969 + 3 ^ 40 * 4644380 * 2
def baseEnd_4644380 : Nat := 794933094042881358530297

theorem tailTrace_4644380 : CollatzResearch.WordTrace tailWord_4644380 prefixEnd_4644380 794933094042881358530297 := by
  unfold tailWord_4644380
  simp only [CollatzResearch.WordTrace]
  refine ⟨84697227457105965899737297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112929636609474621199649729 84697227457105965899737297)
  ·
    refine ⟨63522920592829474424802973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84697227457105965899737297 63522920592829474424802973)
    ·
      refine ⟨23821095222311052909301115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63522920592829474424802973 23821095222311052909301115)
      ·
        refine ⟨35731642833466579363951673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23821095222311052909301115 35731642833466579363951673)
        ·
          refine ⟨26798732125099934522963755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35731642833466579363951673 26798732125099934522963755)
          ·
            refine ⟨40198098187649901784445633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26798732125099934522963755 40198098187649901784445633)
            ·
              refine ⟨30148573640737426338334225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40198098187649901784445633 30148573640737426338334225)
              ·
                refine ⟨22611430230553069753750669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30148573640737426338334225 22611430230553069753750669)
                ·
                  refine ⟨8479286336457401157656501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22611430230553069753750669 8479286336457401157656501)
                  ·
                    refine ⟨794933094042881358530297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8479286336457401157656501 794933094042881358530297)
                    ·
                      rfl

theorem cell23_4644380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 2, 3, 5].length) (baseStart_4644380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4644380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4644380 prefixEnd_4644380 := by exact prefixLift 4644380
  have htrace : WordTrace (prefixWord ++ tailWord_4644380) baseStart_4644380 baseEnd_4644380 := by
    simpa [prefixWord, tailWord_4644380, baseEnd_4644380] using wordTrace_append hprefix tailTrace_4644380
  have hstable : (prefixWord ++ tailWord_4644380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4644380).length < 2 ^ (prefixWord ++ tailWord_4644380).sum := by decide
  have hdescent : baseEnd_4644380 < baseStart_4644380 := by decide
  rcases family_descends (prefixWord ++ tailWord_4644380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4644384 : List Nat := [2, 1, 1, 6, 1, 3, 2, 1, 6]
def baseStart_4644384 : Nat := 118140960795 + 4644384 * 2 ^ 59
def prefixEnd_4644384 : Nat := 4983230072969 + 3 ^ 40 * 4644384 * 2
def baseEnd_4644384 : Nat := 264977926227918006660097

theorem tailTrace_4644384 : CollatzResearch.WordTrace tailWord_4644384 prefixEnd_4644384 264977926227918006660097 := by
  unfold tailWord_4644384
  simp only [CollatzResearch.WordTrace]
  refine ⟨84697300403098720241310103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112929733870798293655080137 84697300403098720241310103)
  ·
    refine ⟨127045950604648080361965155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84697300403098720241310103 127045950604648080361965155)
    ·
      refine ⟨190568925906972120542947733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127045950604648080361965155 190568925906972120542947733)
      ·
        refine ⟨8932918401889318150450675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 190568925906972120542947733 8932918401889318150450675)
        ·
          refine ⟨13399377602833977225676013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8932918401889318150450675 13399377602833977225676013)
          ·
            refine ⟨5024766601062741459628505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13399377602833977225676013 5024766601062741459628505)
            ·
              refine ⟨3768574950797056094721379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5024766601062741459628505 3768574950797056094721379)
              ·
                refine ⟨5652862426195584142082069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3768574950797056094721379 5652862426195584142082069)
                ·
                  refine ⟨264977926227918006660097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5652862426195584142082069 264977926227918006660097)
                  ·
                    rfl

theorem cell23_4644384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 2, 1, 6].length) (baseStart_4644384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4644384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4644384 prefixEnd_4644384 := by exact prefixLift 4644384
  have htrace : WordTrace (prefixWord ++ tailWord_4644384) baseStart_4644384 baseEnd_4644384 := by
    simpa [prefixWord, tailWord_4644384, baseEnd_4644384] using wordTrace_append hprefix tailTrace_4644384
  have hstable : (prefixWord ++ tailWord_4644384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4644384).length < 2 ^ (prefixWord ++ tailWord_4644384).sum := by decide
  have hdescent : baseEnd_4644384 < baseStart_4644384 := by decide
  rcases family_descends (prefixWord ++ tailWord_4644384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4644410 : List Nat := [3, 1, 1, 1, 3, 2, 3, 2, 1, 6]
def baseStart_4644410 : Nat := 118140960795 + 4644410 * 2 ^ 59
def prefixEnd_4644410 : Nat := 4983230072969 + 3 ^ 40 * 4644410 * 2
def baseEnd_4644410 : Nat := 794938228849426319405251

theorem tailTrace_4644410 : CollatzResearch.WordTrace tailWord_4644410 prefixEnd_4644410 794938228849426319405251 := by
  unfold tailWord_4644410
  simp only [CollatzResearch.WordTrace]
  refine ⟨42348887276025811730766671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112930366069402164615377789 42348887276025811730766671)
  ·
    refine ⟨63523330914038717596150007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42348887276025811730766671 63523330914038717596150007)
    ·
      refine ⟨95284996371058076394225011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63523330914038717596150007 95284996371058076394225011)
      ·
        refine ⟨142927494556587114591337517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95284996371058076394225011 142927494556587114591337517)
        ·
          refine ⟨53597810458720167971751569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 142927494556587114591337517 53597810458720167971751569)
          ·
            refine ⟨40198357844040125978813677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53597810458720167971751569 40198357844040125978813677)
            ·
              refine ⟨15074384191515047242055129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40198357844040125978813677 15074384191515047242055129)
              ·
                refine ⟨11305788143636285431541347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15074384191515047242055129 11305788143636285431541347)
                ·
                  refine ⟨16958682215454428147312021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11305788143636285431541347 16958682215454428147312021)
                  ·
                    refine ⟨794938228849426319405251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16958682215454428147312021 794938228849426319405251)
                    ·
                      rfl

theorem cell23_4644410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 2, 1, 6].length) (baseStart_4644410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4644410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4644410 prefixEnd_4644410 := by exact prefixLift 4644410
  have htrace : WordTrace (prefixWord ++ tailWord_4644410) baseStart_4644410 baseEnd_4644410 := by
    simpa [prefixWord, tailWord_4644410, baseEnd_4644410] using wordTrace_append hprefix tailTrace_4644410
  have hstable : (prefixWord ++ tailWord_4644410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4644410).length < 2 ^ (prefixWord ++ tailWord_4644410).sum := by decide
  have hdescent : baseEnd_4644410 < baseStart_4644410 := by decide
  rcases family_descends (prefixWord ++ tailWord_4644410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4644422 : List Nat := [6, 1, 1, 1, 4, 1, 2, 2, 1, 4]
def baseStart_4644422 : Nat := 118140960795 + 4644422 * 2 ^ 59
def prefixEnd_4644422 : Nat := 4983230072969 + 3 ^ 40 * 4644422 * 2
def baseEnd_4644422 : Nat := 794940282772044303755233

theorem tailTrace_4644422 : CollatzResearch.WordTrace tailWord_4644422 prefixEnd_4644422 794940282772044303755233 := by
  unfold tailWord_4644422
  simp only [CollatzResearch.WordTrace]
  refine ⟨5293624586876867905390735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 112930657853373181981669013 5293624586876867905390735)
  ·
    refine ⟨7940436880315301858086103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5293624586876867905390735 7940436880315301858086103)
    ·
      refine ⟨11910655320472952787129155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7940436880315301858086103 11910655320472952787129155)
      ·
        refine ⟨17865982980709429180693733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11910655320472952787129155 17865982980709429180693733)
        ·
          refine ⟨3349871808883017971380075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17865982980709429180693733 3349871808883017971380075)
          ·
            refine ⟨5024807713324526957070113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3349871808883017971380075 5024807713324526957070113)
            ·
              refine ⟨3768605784993395217802585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5024807713324526957070113 3768605784993395217802585)
              ·
                refine ⟨2826454338745046413351939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3768605784993395217802585 2826454338745046413351939)
                ·
                  refine ⟨4239681508117569620027909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2826454338745046413351939 4239681508117569620027909)
                  ·
                    refine ⟨794940282772044303755233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4239681508117569620027909 794940282772044303755233)
                    ·
                      rfl

theorem cell23_4644422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 2, 2, 1, 4].length) (baseStart_4644422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4644422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4644422 prefixEnd_4644422 := by exact prefixLift 4644422
  have htrace : WordTrace (prefixWord ++ tailWord_4644422) baseStart_4644422 baseEnd_4644422 := by
    simpa [prefixWord, tailWord_4644422, baseEnd_4644422] using wordTrace_append hprefix tailTrace_4644422
  have hstable : (prefixWord ++ tailWord_4644422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4644422).length < 2 ^ (prefixWord ++ tailWord_4644422).sum := by decide
  have hdescent : baseEnd_4644422 < baseStart_4644422 := by decide
  rcases family_descends (prefixWord ++ tailWord_4644422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4644423 : List Nat := [1, 1, 4, 1, 16]
def baseStart_4644423 : Nat := 118140960795 + 4644423 * 2 ^ 59
def prefixEnd_4644423 : Nat := 4983230072969 + 3 ^ 40 * 4644423 * 2
def baseEnd_4644423 : Nat := 3271359892725359955217

theorem tailTrace_4644423 : CollatzResearch.WordTrace tailWord_4644423 prefixEnd_4644423 3271359892725359955217 := by
  unfold tailWord_4644423
  simp only [CollatzResearch.WordTrace]
  refine ⟨169396023253056150143289923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112930682168704100095526615 169396023253056150143289923)
  ·
    refine ⟨254094034879584225214934885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169396023253056150143289923 254094034879584225214934885)
    ·
      refine ⟨47642631539922042227800291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 254094034879584225214934885 47642631539922042227800291)
      ·
        refine ⟨71463947309883063341700437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47642631539922042227800291 71463947309883063341700437)
        ·
          refine ⟨3271359892725359955217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 16 71463947309883063341700437 3271359892725359955217)
          ·
            rfl

theorem cell23_4644423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 16].length) (baseStart_4644423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4644423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4644423 prefixEnd_4644423 := by exact prefixLift 4644423
  have htrace : WordTrace (prefixWord ++ tailWord_4644423) baseStart_4644423 baseEnd_4644423 := by
    simpa [prefixWord, tailWord_4644423, baseEnd_4644423] using wordTrace_append hprefix tailTrace_4644423
  have hstable : (prefixWord ++ tailWord_4644423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4644423).length < 2 ^ (prefixWord ++ tailWord_4644423).sum := by decide
  have hdescent : baseEnd_4644423 < baseStart_4644423 := by decide
  rcases family_descends (prefixWord ++ tailWord_4644423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4644428 : List Nat := [2, 2, 1, 3, 1, 5, 2, 2, 1, 1, 3]
def baseStart_4644428 : Nat := 118140960795 + 4644428 * 2 ^ 59
def prefixEnd_4644428 : Nat := 4983230072969 + 3 ^ 40 * 4644428 * 2
def baseEnd_4644428 : Nat := 2384823929200059887790671

theorem tailTrace_4644428 : CollatzResearch.WordTrace tailWord_4644428 prefixEnd_4644428 2384823929200059887790671 := by
  unfold tailWord_4644428
  simp only [CollatzResearch.WordTrace]
  refine ⟨84698102809019017998610969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112930803745358690664814625 84698102809019017998610969)
  ·
    refine ⟨63523577106764263498958227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84698102809019017998610969 63523577106764263498958227)
    ·
      refine ⟨95285365660146395248437341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63523577106764263498958227 95285365660146395248437341)
      ·
        refine ⟨35732012122554898218164003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95285365660146395248437341 35732012122554898218164003)
        ·
          refine ⟨53598018183832347327246005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35732012122554898218164003 53598018183832347327246005)
          ·
            refine ⟨5024814204734282561929313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 53598018183832347327246005 5024814204734282561929313)
            ·
              refine ⟨3768610653550711921446985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5024814204734282561929313 3768610653550711921446985)
              ·
                refine ⟨2826457990163033941085239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3768610653550711921446985 2826457990163033941085239)
                ·
                  refine ⟨4239686985244550911627859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2826457990163033941085239 4239686985244550911627859)
                  ·
                    refine ⟨6359530477866826367441789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4239686985244550911627859 6359530477866826367441789)
                    ·
                      refine ⟨2384823929200059887790671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6359530477866826367441789 2384823929200059887790671)
                      ·
                        rfl

theorem cell23_4644428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 2, 2, 1, 1, 3].length) (baseStart_4644428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4644428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4644428 prefixEnd_4644428 := by exact prefixLift 4644428
  have htrace : WordTrace (prefixWord ++ tailWord_4644428) baseStart_4644428 baseEnd_4644428 := by
    simpa [prefixWord, tailWord_4644428, baseEnd_4644428] using wordTrace_append hprefix tailTrace_4644428
  have hstable : (prefixWord ++ tailWord_4644428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4644428).length < 2 ^ (prefixWord ++ tailWord_4644428).sum := by decide
  have hdescent : baseEnd_4644428 < baseStart_4644428 := by decide
  rcases family_descends (prefixWord ++ tailWord_4644428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4644430 : List Nat := [4, 1, 1, 1, 1, 2, 1, 1, 5, 2, 4]
def baseStart_4644430 : Nat := 118140960795 + 4644430 * 2 ^ 59
def prefixEnd_4644430 : Nat := 4983230072969 + 3 ^ 40 * 4644430 * 2
def baseEnd_4644430 : Nat := 2384824956161368879965661

theorem tailTrace_4644430 : CollatzResearch.WordTrace tailWord_4644430 prefixEnd_4644430 2384824956161368879965661 := by
  unfold tailWord_4644430
  simp only [CollatzResearch.WordTrace]
  refine ⟨21174534820503848792349343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112930852376020526892529829 21174534820503848792349343)
  ·
    refine ⟨31761802230755773188524015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21174534820503848792349343 31761802230755773188524015)
    ·
      refine ⟨47642703346133659782786023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31761802230755773188524015 47642703346133659782786023)
      ·
        refine ⟨71464055019200489674179035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47642703346133659782786023 71464055019200489674179035)
        ·
          refine ⟨107196082528800734511268553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71464055019200489674179035 107196082528800734511268553)
          ·
            refine ⟨80397061896600550883451415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107196082528800734511268553 80397061896600550883451415)
            ·
              refine ⟨120595592844900826325177123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80397061896600550883451415 120595592844900826325177123)
              ·
                refine ⟨180893389267351239487765685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 120595592844900826325177123 180893389267351239487765685)
                ·
                  refine ⟨16958755243814178701978033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 180893389267351239487765685 16958755243814178701978033)
                  ·
                    refine ⟨12719066432860634026483525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16958755243814178701978033 12719066432860634026483525)
                    ·
                      refine ⟨2384824956161368879965661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12719066432860634026483525 2384824956161368879965661)
                      ·
                        rfl

theorem cell23_4644430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 5, 2, 4].length) (baseStart_4644430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4644430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4644430 prefixEnd_4644430 := by exact prefixLift 4644430
  have htrace : WordTrace (prefixWord ++ tailWord_4644430) baseStart_4644430 baseEnd_4644430 := by
    simpa [prefixWord, tailWord_4644430, baseEnd_4644430] using wordTrace_append hprefix tailTrace_4644430
  have hstable : (prefixWord ++ tailWord_4644430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4644430).length < 2 ^ (prefixWord ++ tailWord_4644430).sum := by decide
  have hdescent : baseEnd_4644430 < baseStart_4644430 := by decide
  rcases family_descends (prefixWord ++ tailWord_4644430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4644443 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 12]
def baseStart_4644443 : Nat := 118140960795 + 4644443 * 2 ^ 59
def prefixEnd_4644443 : Nat := 4983230072969 + 3 ^ 40 * 4644443 * 2
def baseEnd_4644443 : Nat := 2384831631409877329103101

theorem tailTrace_4644443 : CollatzResearch.WordTrace tailWord_4644443 prefixEnd_4644443 2384831631409877329103101 := by
  unfold tailWord_4644443
  simp only [CollatzResearch.WordTrace]
  refine ⟨169396752712983693559017983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112931168475322462372678655 169396752712983693559017983)
  ·
    refine ⟨254095129069475540338526975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169396752712983693559017983 254095129069475540338526975)
    ·
      refine ⟨381142693604213310507790463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 254095129069475540338526975 381142693604213310507790463)
      ·
        refine ⟨571714040406319965761685695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 381142693604213310507790463 571714040406319965761685695)
        ·
          refine ⟨857571060609479948642528543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 571714040406319965761685695 857571060609479948642528543)
          ·
            refine ⟨1286356590914219922963792815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 857571060609479948642528543 1286356590914219922963792815)
            ·
              refine ⟨1929534886371329884445689223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1286356590914219922963792815 1929534886371329884445689223)
              ·
                refine ⟨2894302329556994826668533835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1929534886371329884445689223 2894302329556994826668533835)
                ·
                  refine ⟨4341453494335492240002800753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2894302329556994826668533835 4341453494335492240002800753)
                  ·
                    refine ⟨3256090120751619180002100565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4341453494335492240002800753 3256090120751619180002100565)
                    ·
                      refine ⟨2384831631409877329103101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 12 3256090120751619180002100565 2384831631409877329103101)
                      ·
                        rfl

theorem cell23_4644443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 12].length) (baseStart_4644443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4644443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4644443 prefixEnd_4644443 := by exact prefixLift 4644443
  have htrace : WordTrace (prefixWord ++ tailWord_4644443) baseStart_4644443 baseEnd_4644443 := by
    simpa [prefixWord, tailWord_4644443, baseEnd_4644443] using wordTrace_append hprefix tailTrace_4644443
  have hstable : (prefixWord ++ tailWord_4644443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4644443).length < 2 ^ (prefixWord ++ tailWord_4644443).sum := by decide
  have hdescent : baseEnd_4644443 < baseStart_4644443 := by decide
  rcases family_descends (prefixWord ++ tailWord_4644443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4644444 : List Nat := [2, 2, 4, 1, 2, 1, 2, 3, 2, 4]
def baseStart_4644444 : Nat := 118140960795 + 4644444 * 2 ^ 59
def prefixEnd_4644444 : Nat := 4983230072969 + 3 ^ 40 * 4644444 * 2
def baseEnd_4644444 : Nat := 794944048296843941730199

theorem tailTrace_4644444 : CollatzResearch.WordTrace tailWord_4644444 prefixEnd_4644444 794944048296843941730199 := by
  unfold tailWord_4644444
  simp only [CollatzResearch.WordTrace]
  refine ⟨84698394592990035364902193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112931192790653380486536257 84698394592990035364902193)
  ·
    refine ⟨63523795944742526523676645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84698394592990035364902193 63523795944742526523676645)
    ·
      refine ⟨11910711739639223723189371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63523795944742526523676645 11910711739639223723189371)
      ·
        refine ⟨17866067609458835584784057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11910711739639223723189371 17866067609458835584784057)
        ·
          refine ⟨13399550707094126688588043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17866067609458835584784057 13399550707094126688588043)
          ·
            refine ⟨20099326060641190032882065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13399550707094126688588043 20099326060641190032882065)
            ·
              refine ⟨15074494545480892524661549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20099326060641190032882065 15074494545480892524661549)
              ·
                refine ⟨5652935454555334696748081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15074494545480892524661549 5652935454555334696748081)
                ·
                  refine ⟨4239701590916501022561061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5652935454555334696748081 4239701590916501022561061)
                  ·
                    refine ⟨794944048296843941730199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4239701590916501022561061 794944048296843941730199)
                    ·
                      rfl

theorem cell23_4644444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 3, 2, 4].length) (baseStart_4644444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4644444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4644444 prefixEnd_4644444 := by exact prefixLift 4644444
  have htrace : WordTrace (prefixWord ++ tailWord_4644444) baseStart_4644444 baseEnd_4644444 := by
    simpa [prefixWord, tailWord_4644444, baseEnd_4644444] using wordTrace_append hprefix tailTrace_4644444
  have hstable : (prefixWord ++ tailWord_4644444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4644444).length < 2 ^ (prefixWord ++ tailWord_4644444).sum := by decide
  have hdescent : baseEnd_4644444 < baseStart_4644444 := by decide
  rcases family_descends (prefixWord ++ tailWord_4644444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4644530 : List Nat := [3, 2, 1, 1, 1, 2, 2, 2, 9]
def baseStart_4644530 : Nat := 118140960795 + 4644530 * 2 ^ 59
def prefixEnd_4644530 : Nat := 4983230072969 + 3 ^ 40 * 4644530 * 2
def baseEnd_4644530 : Nat := 264986256025202054301689

theorem tailTrace_4644530 : CollatzResearch.WordTrace tailWord_4644530 prefixEnd_4644530 264986256025202054301689 := by
  unfold tailWord_4644530
  simp only [CollatzResearch.WordTrace]
  refine ⟨42349981465917126854358761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112933283909112338278290029 42349981465917126854358761)
  ·
    refine ⟨31762486099437845140769071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42349981465917126854358761 31762486099437845140769071)
    ·
      refine ⟨47643729149156767711153607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31762486099437845140769071 47643729149156767711153607)
      ·
        refine ⟨71465593723735151566730411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47643729149156767711153607 71465593723735151566730411)
        ·
          refine ⟨107198390585602727350095617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71465593723735151566730411 107198390585602727350095617)
          ·
            refine ⟨80398792939202045512571713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107198390585602727350095617 80398792939202045512571713)
            ·
              refine ⟨60299094704401534134428785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80398792939202045512571713 60299094704401534134428785)
              ·
                refine ⟨45224321028301150600821589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60299094704401534134428785 45224321028301150600821589)
                ·
                  refine ⟨264986256025202054301689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 45224321028301150600821589 264986256025202054301689)
                  ·
                    rfl

theorem cell23_4644530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 2, 9].length) (baseStart_4644530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4644530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4644530 prefixEnd_4644530 := by exact prefixLift 4644530
  have htrace : WordTrace (prefixWord ++ tailWord_4644530) baseStart_4644530 baseEnd_4644530 := by
    simpa [prefixWord, tailWord_4644530, baseEnd_4644530] using wordTrace_append hprefix tailTrace_4644530
  have hstable : (prefixWord ++ tailWord_4644530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4644530).length < 2 ^ (prefixWord ++ tailWord_4644530).sum := by decide
  have hdescent : baseEnd_4644530 < baseStart_4644530 := by decide
  rcases family_descends (prefixWord ++ tailWord_4644530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4644541 : List Nat := [1, 4, 1, 2, 1, 2, 2, 4, 2, 2, 2]
def baseStart_4644541 : Nat := 118140960795 + 4644541 * 2 ^ 59
def prefixEnd_4644541 : Nat := 4983230072969 + 3 ^ 40 * 4644541 * 2
def baseEnd_4644541 : Nat := 2384881952514017945677651

theorem tailTrace_4644541 : CollatzResearch.WordTrace tailWord_4644541 prefixEnd_4644541 2384881952514017945677651 := by
  unfold tailWord_4644541
  simp only [CollatzResearch.WordTrace]
  refine ⟨169400327066628656296085477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112933551377752437530723651 169400327066628656296085477)
  ·
    refine ⟨31762561324992873055516027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 169400327066628656296085477 31762561324992873055516027)
    ·
      refine ⟨47643841987489309583274041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31762561324992873055516027 47643841987489309583274041)
      ·
        refine ⟨35732881490616982187455531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47643841987489309583274041 35732881490616982187455531)
        ·
          refine ⟨53599322235925473281183297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35732881490616982187455531 53599322235925473281183297)
          ·
            refine ⟨40199491676944104960887473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53599322235925473281183297 40199491676944104960887473)
            ·
              refine ⟨30149618757708078720665605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40199491676944104960887473 30149618757708078720665605)
              ·
                refine ⟨5653053517070264760124801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30149618757708078720665605 5653053517070264760124801)
                ·
                  refine ⟨4239790137802698570093601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5653053517070264760124801 4239790137802698570093601)
                  ·
                    refine ⟨3179842603352023927570201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4239790137802698570093601 3179842603352023927570201)
                    ·
                      refine ⟨2384881952514017945677651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3179842603352023927570201 2384881952514017945677651)
                      ·
                        rfl

theorem cell23_4644541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 4, 2, 2, 2].length) (baseStart_4644541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4644541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4644541 prefixEnd_4644541 := by exact prefixLift 4644541
  have htrace : WordTrace (prefixWord ++ tailWord_4644541) baseStart_4644541 baseEnd_4644541 := by
    simpa [prefixWord, tailWord_4644541, baseEnd_4644541] using wordTrace_append hprefix tailTrace_4644541
  have hstable : (prefixWord ++ tailWord_4644541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4644541).length < 2 ^ (prefixWord ++ tailWord_4644541).sum := by decide
  have hdescent : baseEnd_4644541 < baseStart_4644541 := by decide
  rcases family_descends (prefixWord ++ tailWord_4644541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4644560 : List Nat := [2, 1, 1, 1, 1, 2, 1, 6, 1, 7]
def baseStart_4644560 : Nat := 118140960795 + 4644560 * 2 ^ 59
def prefixEnd_4644560 : Nat := 4983230072969 + 3 ^ 40 * 4644560 * 2
def baseEnd_4644560 : Nat := 794963902882151123780021

theorem tailTrace_4644560 : CollatzResearch.WordTrace tailWord_4644560 prefixEnd_4644560 794963902882151123780021 := by
  unfold tailWord_4644560
  simp only [CollatzResearch.WordTrace]
  refine ⟨84700510026779911270513567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112934013369039881694018089 84700510026779911270513567)
  ·
    refine ⟨127050765040169866905770351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84700510026779911270513567 127050765040169866905770351)
    ·
      refine ⟨190576147560254800358655527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127050765040169866905770351 190576147560254800358655527)
      ·
        refine ⟨285864221340382200537983291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190576147560254800358655527 285864221340382200537983291)
        ·
          refine ⟨428796332010573300806974937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 285864221340382200537983291 428796332010573300806974937)
          ·
            refine ⟨321597249007929975605231203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 428796332010573300806974937 321597249007929975605231203)
            ·
              refine ⟨482395873511894963407846805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 321597249007929975605231203 482395873511894963407846805)
              ·
                refine ⟨22612306570870076409742819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 482395873511894963407846805 22612306570870076409742819)
                ·
                  refine ⟨33918459856305114614614229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22612306570870076409742819 33918459856305114614614229)
                  ·
                    refine ⟨794963902882151123780021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33918459856305114614614229 794963902882151123780021)
                    ·
                      rfl

theorem cell23_4644560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 6, 1, 7].length) (baseStart_4644560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4644560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4644560 prefixEnd_4644560 := by exact prefixLift 4644560
  have htrace : WordTrace (prefixWord ++ tailWord_4644560) baseStart_4644560 baseEnd_4644560 := by
    simpa [prefixWord, tailWord_4644560, baseEnd_4644560] using wordTrace_append hprefix tailTrace_4644560
  have hstable : (prefixWord ++ tailWord_4644560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4644560).length < 2 ^ (prefixWord ++ tailWord_4644560).sum := by decide
  have hdescent : baseEnd_4644560 < baseStart_4644560 := by decide
  rcases family_descends (prefixWord ++ tailWord_4644560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4644598 : List Nat := [5, 1, 1, 1, 1, 5, 2, 2, 5]
def baseStart_4644598 : Nat := 118140960795 + 4644598 * 2 ^ 59
def prefixEnd_4644598 : Nat := 4983230072969 + 3 ^ 40 * 4644598 * 2
def baseEnd_4644598 : Nat := 264990135656813802518321

theorem tailTrace_4644598 : CollatzResearch.WordTrace tailWord_4644598 prefixEnd_4644598 264990135656813802518321 := by
  unfold tailWord_4644598
  simp only [CollatzResearch.WordTrace]
  refine ⟨10587650376713884689431903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 112934937351614770020606965 10587650376713884689431903)
  ·
    refine ⟨15881475565070827034147855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10587650376713884689431903 15881475565070827034147855)
    ·
      refine ⟨23822213347606240551221783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15881475565070827034147855 23822213347606240551221783)
      ·
        refine ⟨35733320021409360826832675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23822213347606240551221783 35733320021409360826832675)
        ·
          refine ⟨53599980032114041240249013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35733320021409360826832675 53599980032114041240249013)
          ·
            refine ⟨5024998128010691366273345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 53599980032114041240249013 5024998128010691366273345)
            ·
              refine ⟨3768748596008018524705009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5024998128010691366273345 3768748596008018524705009)
              ·
                refine ⟨2826561447006013893528757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3768748596008018524705009 2826561447006013893528757)
                ·
                  refine ⟨264990135656813802518321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2826561447006013893528757 264990135656813802518321)
                  ·
                    rfl

theorem cell23_4644598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 2, 2, 5].length) (baseStart_4644598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4644598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4644598 prefixEnd_4644598 := by exact prefixLift 4644598
  have htrace : WordTrace (prefixWord ++ tailWord_4644598) baseStart_4644598 baseEnd_4644598 := by
    simpa [prefixWord, tailWord_4644598, baseEnd_4644598] using wordTrace_append hprefix tailTrace_4644598
  have hstable : (prefixWord ++ tailWord_4644598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4644598).length < 2 ^ (prefixWord ++ tailWord_4644598).sum := by decide
  have hdescent : baseEnd_4644598 < baseStart_4644598 := by decide
  rcases family_descends (prefixWord ++ tailWord_4644598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4644617 : List Nat := [1, 2, 1, 1, 3, 2, 1, 4, 1, 4, 3]
def baseStart_4644617 : Nat := 118140960795 + 4644617 * 2 ^ 59
def prefixEnd_4644617 : Nat := 4983230072969 + 3 ^ 40 * 4644617 * 2
def baseEnd_4644617 : Nat := 2384920977043759648327301

theorem tailTrace_4644617 : CollatzResearch.WordTrace tailWord_4644617 prefixEnd_4644617 2384920977043759648327301 := by
  unfold tailWord_4644617
  simp only [CollatzResearch.WordTrace]
  refine ⟨169403099014353321275852105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112935399342902214183901403 169403099014353321275852105)
  ·
    refine ⟨127052324260764990956889079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169403099014353321275852105 127052324260764990956889079)
    ·
      refine ⟨190578486391147486435333619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127052324260764990956889079 190578486391147486435333619)
      ·
        refine ⟨285867729586721229653000429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190578486391147486435333619 285867729586721229653000429)
        ·
          refine ⟨107200398595020461119875161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 285867729586721229653000429 107200398595020461119875161)
          ·
            refine ⟨80400298946265345839906371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107200398595020461119875161 80400298946265345839906371)
            ·
              refine ⟨120600448419398018759859557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80400298946265345839906371 120600448419398018759859557)
              ·
                refine ⟨22612584078637128517473667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 120600448419398018759859557 22612584078637128517473667)
                ·
                  refine ⟨33918876117955692776210501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22612584078637128517473667 33918876117955692776210501)
                  ·
                    refine ⟨6359789272116692395539469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33918876117955692776210501 6359789272116692395539469)
                    ·
                      refine ⟨2384920977043759648327301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6359789272116692395539469 2384920977043759648327301)
                      ·
                        rfl

theorem cell23_4644617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 4, 1, 4, 3].length) (baseStart_4644617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4644617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4644617 prefixEnd_4644617 := by exact prefixLift 4644617
  have htrace : WordTrace (prefixWord ++ tailWord_4644617) baseStart_4644617 baseEnd_4644617 := by
    simpa [prefixWord, tailWord_4644617, baseEnd_4644617] using wordTrace_append hprefix tailTrace_4644617
  have hstable : (prefixWord ++ tailWord_4644617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4644617).length < 2 ^ (prefixWord ++ tailWord_4644617).sum := by decide
  have hdescent : baseEnd_4644617 < baseStart_4644617 := by decide
  rcases family_descends (prefixWord ++ tailWord_4644617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4644628 : List Nat := [2, 4, 4, 1, 1, 1, 1, 1, 1, 7]
def baseStart_4644628 : Nat := 118140960795 + 4644628 * 2 ^ 59
def prefixEnd_4644628 : Nat := 4983230072969 + 3 ^ 40 * 4644628 * 2
def baseEnd_4644628 : Nat := 794975541776986368429917

theorem tailTrace_4644628 : CollatzResearch.WordTrace tailWord_4644628 prefixEnd_4644628 794975541776986368429917 := by
  unfold tailWord_4644628
  simp only [CollatzResearch.WordTrace]
  refine ⟨84701750108656735077251269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112935666811542313436335025 84701750108656735077251269)
  ·
    refine ⟨15881578145373137826984613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84701750108656735077251269 15881578145373137826984613)
    ·
      refine ⟨2977795902257463342559615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15881578145373137826984613 2977795902257463342559615)
      ·
        refine ⟨4466693853386195013839423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2977795902257463342559615 4466693853386195013839423)
        ·
          refine ⟨6700040780079292520759135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4466693853386195013839423 6700040780079292520759135)
          ·
            refine ⟨10050061170118938781138703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6700040780079292520759135 10050061170118938781138703)
            ·
              refine ⟨15075091755178408171708055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10050061170118938781138703 15075091755178408171708055)
              ·
                refine ⟨22612637632767612257562083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15075091755178408171708055 22612637632767612257562083)
                ·
                  refine ⟨33918956449151418386343125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22612637632767612257562083 33918956449151418386343125)
                  ·
                    refine ⟨794975541776986368429917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33918956449151418386343125 794975541776986368429917)
                    ·
                      rfl

theorem cell23_4644628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_4644628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4644628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4644628 prefixEnd_4644628 := by exact prefixLift 4644628
  have htrace : WordTrace (prefixWord ++ tailWord_4644628) baseStart_4644628 baseEnd_4644628 := by
    simpa [prefixWord, tailWord_4644628, baseEnd_4644628] using wordTrace_append hprefix tailTrace_4644628
  have hstable : (prefixWord ++ tailWord_4644628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4644628).length < 2 ^ (prefixWord ++ tailWord_4644628).sum := by decide
  have hdescent : baseEnd_4644628 < baseStart_4644628 := by decide
  rcases family_descends (prefixWord ++ tailWord_4644628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4644631 : List Nat := [1, 1, 3, 4, 2, 3, 1, 1, 2, 1, 4]
def baseStart_4644631 : Nat := 118140960795 + 4644631 * 2 ^ 59
def prefixEnd_4644631 : Nat := 4983230072969 + 3 ^ 40 * 4644631 * 2
def baseEnd_4644631 : Nat := 2384928165772922593552237

theorem tailTrace_4644631 : CollatzResearch.WordTrace tailWord_4644631 prefixEnd_4644631 2384928165772922593552237 := by
  unfold tailWord_4644631
  simp only [CollatzResearch.WordTrace]
  refine ⟨169403609636302601666861747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112935739757535067777907831 169403609636302601666861747)
  ·
    refine ⟨254105414454453902500292621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169403609636302601666861747 254105414454453902500292621)
    ·
      refine ⟨95289530420420213437609733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 254105414454453902500292621 95289530420420213437609733)
      ·
        refine ⟨17866786953828790019551825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 95289530420420213437609733 17866786953828790019551825)
        ·
          refine ⟨13400090215371592514663869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17866786953828790019551825 13400090215371592514663869)
          ·
            refine ⟨5025033830764347192998951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13400090215371592514663869 5025033830764347192998951)
            ·
              refine ⟨7537550746146520789498427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5025033830764347192998951 7537550746146520789498427)
              ·
                refine ⟨11306326119219781184247641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7537550746146520789498427 11306326119219781184247641)
                ·
                  refine ⟨8479744589414835888185731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11306326119219781184247641 8479744589414835888185731)
                  ·
                    refine ⟨12719616884122253832278597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8479744589414835888185731 12719616884122253832278597)
                    ·
                      refine ⟨2384928165772922593552237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12719616884122253832278597 2384928165772922593552237)
                      ·
                        rfl

theorem cell23_4644631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 1, 1, 2, 1, 4].length) (baseStart_4644631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4644631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4644631 prefixEnd_4644631 := by exact prefixLift 4644631
  have htrace : WordTrace (prefixWord ++ tailWord_4644631) baseStart_4644631 baseEnd_4644631 := by
    simpa [prefixWord, tailWord_4644631, baseEnd_4644631] using wordTrace_append hprefix tailTrace_4644631
  have hstable : (prefixWord ++ tailWord_4644631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4644631).length < 2 ^ (prefixWord ++ tailWord_4644631).sum := by decide
  have hdescent : baseEnd_4644631 < baseStart_4644631 := by decide
  rcases family_descends (prefixWord ++ tailWord_4644631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4644634 : List Nat := [3, 1, 1, 3, 2, 3, 1, 1, 1, 4, 3]
def baseStart_4644634 : Nat := 118140960795 + 4644634 * 2 ^ 59
def prefixEnd_4644634 : Nat := 4983230072969 + 3 ^ 40 * 4644634 * 2
def baseEnd_4644634 : Nat := 2384929706214886081814723

theorem tailTrace_4644634 : CollatzResearch.WordTrace tailWord_4644634 prefixEnd_4644634 2384929706214886081814723 := by
  unfold tailWord_4644634
  simp only [CollatzResearch.WordTrace]
  refine ⟨42350929763822933294805239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112935812703527822119480637 42350929763822933294805239)
  ·
    refine ⟨63526394645734399942207859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42350929763822933294805239 63526394645734399942207859)
    ·
      refine ⟨95289591968601599913311789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63526394645734399942207859 95289591968601599913311789)
      ·
        refine ⟨35733596988225599967491921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95289591968601599913311789 35733596988225599967491921)
        ·
          refine ⟨26800197741169199975618941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35733596988225599967491921 26800197741169199975618941)
          ·
            refine ⟨10050074152938449990857103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26800197741169199975618941 10050074152938449990857103)
            ·
              refine ⟨15075111229407674986285655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10050074152938449990857103 15075111229407674986285655)
              ·
                refine ⟨22612666844111512479428483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15075111229407674986285655 22612666844111512479428483)
                ·
                  refine ⟨33919000266167268719142725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22612666844111512479428483 33919000266167268719142725)
                  ·
                    refine ⟨6359812549906362884839261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33919000266167268719142725 6359812549906362884839261)
                    ·
                      refine ⟨2384929706214886081814723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6359812549906362884839261 2384929706214886081814723)
                      ·
                        rfl

theorem cell23_4644634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 1, 1, 4, 3].length) (baseStart_4644634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4644634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4644634 prefixEnd_4644634 := by exact prefixLift 4644634
  have htrace : WordTrace (prefixWord ++ tailWord_4644634) baseStart_4644634 baseEnd_4644634 := by
    simpa [prefixWord, tailWord_4644634, baseEnd_4644634] using wordTrace_append hprefix tailTrace_4644634
  have hstable : (prefixWord ++ tailWord_4644634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4644634).length < 2 ^ (prefixWord ++ tailWord_4644634).sum := by decide
  have hdescent : baseEnd_4644634 < baseStart_4644634 := by decide
  rcases family_descends (prefixWord ++ tailWord_4644634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4644641 : List Nat := [1, 2, 3, 2, 1, 3, 1, 5, 1, 4]
def baseStart_4644641 : Nat := 118140960795 + 4644641 * 2 ^ 59
def prefixEnd_4644641 : Nat := 4983230072969 + 3 ^ 40 * 4644641 * 2
def baseEnd_4644641 : Nat := 794977766859822518142397

theorem tailTrace_4644641 : CollatzResearch.WordTrace tailWord_4644641 prefixEnd_4644641 794977766859822518142397 := by
  unfold tailWord_4644641
  simp only [CollatzResearch.WordTrace]
  refine ⟨169403974366266373374725777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112935982910844248916483851 169403974366266373374725777)
  ·
    refine ⟨127052980774699780031044333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169403974366266373374725777 127052980774699780031044333)
    ·
      refine ⟨47644867790512417511641625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 127052980774699780031044333 47644867790512417511641625)
      ·
        refine ⟨35733650842884313133731219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47644867790512417511641625 35733650842884313133731219)
        ·
          refine ⟨53600476264326469700596829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35733650842884313133731219 53600476264326469700596829)
          ·
            refine ⟨20100178599122426137723811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53600476264326469700596829 20100178599122426137723811)
            ·
              refine ⟨30150267898683639206585717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20100178599122426137723811 30150267898683639206585717)
              ·
                refine ⟨2826587615501591175617411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30150267898683639206585717 2826587615501591175617411)
                ·
                  refine ⟨4239881423252386763426117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2826587615501591175617411 4239881423252386763426117)
                  ·
                    refine ⟨794977766859822518142397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4239881423252386763426117 794977766859822518142397)
                    ·
                      rfl

theorem cell23_4644641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 5, 1, 4].length) (baseStart_4644641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4644641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4644641 prefixEnd_4644641 := by exact prefixLift 4644641
  have htrace : WordTrace (prefixWord ++ tailWord_4644641) baseStart_4644641 baseEnd_4644641 := by
    simpa [prefixWord, tailWord_4644641, baseEnd_4644641] using wordTrace_append hprefix tailTrace_4644641
  have hstable : (prefixWord ++ tailWord_4644641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4644641).length < 2 ^ (prefixWord ++ tailWord_4644641).sum := by decide
  have hdescent : baseEnd_4644641 < baseStart_4644641 := by decide
  rcases family_descends (prefixWord ++ tailWord_4644641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4644657 : List Nat := [1, 2, 2, 3, 2, 2, 1, 1, 1, 2, 6]
def baseStart_4644657 : Nat := 118140960795 + 4644657 * 2 ^ 59
def prefixEnd_4644657 : Nat := 4983230072969 + 3 ^ 40 * 4644657 * 2
def baseEnd_4644657 : Nat := 2384941516269939491827117

theorem tailTrace_4644657 : CollatzResearch.WordTrace tailWord_4644657 prefixEnd_4644657 2384941516269939491827117 := by
  unfold tailWord_4644657
  simp only [CollatzResearch.WordTrace]
  refine ⟨169404557934208408107308225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112936371956138938738205483 169404557934208408107308225)
  ·
    refine ⟨127053418450656306080481169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169404557934208408107308225 127053418450656306080481169)
    ·
      refine ⟨95290063837992229560360877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127053418450656306080481169 95290063837992229560360877)
      ·
        refine ⟨35733773939247086085135329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95290063837992229560360877 35733773939247086085135329)
        ·
          refine ⟨26800330454435314563851497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35733773939247086085135329 26800330454435314563851497)
          ·
            refine ⟨20100247840826485922888623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26800330454435314563851497 20100247840826485922888623)
            ·
              refine ⟨30150371761239728884332935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20100247840826485922888623 30150371761239728884332935)
              ·
                refine ⟨45225557641859593326499403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30150371761239728884332935 45225557641859593326499403)
                ·
                  refine ⟨67838336462789389989749105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45225557641859593326499403 67838336462789389989749105)
                  ·
                    refine ⟨50878752347092042492311829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 67838336462789389989749105 50878752347092042492311829)
                    ·
                      refine ⟨2384941516269939491827117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50878752347092042492311829 2384941516269939491827117)
                      ·
                        rfl

theorem cell23_4644657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 1, 1, 2, 6].length) (baseStart_4644657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4644657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4644657 prefixEnd_4644657 := by exact prefixLift 4644657
  have htrace : WordTrace (prefixWord ++ tailWord_4644657) baseStart_4644657 baseEnd_4644657 := by
    simpa [prefixWord, tailWord_4644657, baseEnd_4644657] using wordTrace_append hprefix tailTrace_4644657
  have hstable : (prefixWord ++ tailWord_4644657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4644657).length < 2 ^ (prefixWord ++ tailWord_4644657).sum := by decide
  have hdescent : baseEnd_4644657 < baseStart_4644657 := by decide
  rcases family_descends (prefixWord ++ tailWord_4644657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4644671 : List Nat := [1, 1, 2, 2, 6, 1, 3, 1, 6]
def baseStart_4644671 : Nat := 118140960795 + 4644671 * 2 ^ 59
def prefixEnd_4644671 : Nat := 4983230072969 + 3 ^ 40 * 4644671 * 2
def baseEnd_4644671 : Nat := 264994300555455826339117

theorem tailTrace_4644671 : CollatzResearch.WordTrace tailWord_4644671 prefixEnd_4644671 264994300555455826339117 := by
  unfold tailWord_4644671
  simp only [CollatzResearch.WordTrace]
  refine ⟨169405068556157688498317867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112936712370771792332211911 169405068556157688498317867)
  ·
    refine ⟨254107602834236532747476801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169405068556157688498317867 254107602834236532747476801)
    ·
      refine ⟨190580702125677399560607601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 254107602834236532747476801 190580702125677399560607601)
      ·
        refine ⟨142935526594258049670455701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 190580702125677399560607601 142935526594258049670455701)
        ·
          refine ⟨6700102809105846078302611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 142935526594258049670455701 6700102809105846078302611)
          ·
            refine ⟨10050154213658769117453917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6700102809105846078302611 10050154213658769117453917)
            ·
              refine ⟨3768807830122038419045219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10050154213658769117453917 3768807830122038419045219)
              ·
                refine ⟨5653211745183057628567829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3768807830122038419045219 5653211745183057628567829)
                ·
                  refine ⟨264994300555455826339117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5653211745183057628567829 264994300555455826339117)
                  ·
                    rfl

theorem cell23_4644671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 3, 1, 6].length) (baseStart_4644671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4644671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4644671 prefixEnd_4644671 := by exact prefixLift 4644671
  have htrace : WordTrace (prefixWord ++ tailWord_4644671) baseStart_4644671 baseEnd_4644671 := by
    simpa [prefixWord, tailWord_4644671, baseEnd_4644671] using wordTrace_append hprefix tailTrace_4644671
  have hstable : (prefixWord ++ tailWord_4644671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4644671).length < 2 ^ (prefixWord ++ tailWord_4644671).sum := by decide
  have hdescent : baseEnd_4644671 < baseStart_4644671 := by decide
  rcases family_descends (prefixWord ++ tailWord_4644671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4644697 : List Nat := [1, 2, 1, 2, 2, 3, 2, 1, 3, 6]
def baseStart_4644697 : Nat := 118140960795 + 4644697 * 2 ^ 59
def prefixEnd_4644697 : Nat := 4983230072969 + 3 ^ 40 * 4644697 * 2
def baseEnd_4644697 : Nat := 794987351832039778442311

theorem tailTrace_4644697 : CollatzResearch.WordTrace tailWord_4644697 prefixEnd_4644697 794987351832039778442311 := by
  unfold tailWord_4644697
  simp only [CollatzResearch.WordTrace]
  refine ⟨169406016854063494938764345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112937344569375663292509563 169406016854063494938764345)
  ·
    refine ⟨127054512640547621204073259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169406016854063494938764345 127054512640547621204073259)
    ·
      refine ⟨190581768960821431806109889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127054512640547621204073259 190581768960821431806109889)
      ·
        refine ⟨142936326720616073854582417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 190581768960821431806109889 142936326720616073854582417)
        ·
          refine ⟨107202245040462055390936813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142936326720616073854582417 107202245040462055390936813)
          ·
            refine ⟨40200841890173270771601305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 107202245040462055390936813 40200841890173270771601305)
            ·
              refine ⟨30150631417629953078700979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40200841890173270771601305 30150631417629953078700979)
              ·
                refine ⟨45225947126444929618051469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30150631417629953078700979 45225947126444929618051469)
                ·
                  refine ⟨16959730172416848606769301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45225947126444929618051469 16959730172416848606769301)
                  ·
                    refine ⟨794987351832039778442311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16959730172416848606769301 794987351832039778442311)
                    ·
                      rfl

theorem cell23_4644697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 1, 3, 6].length) (baseStart_4644697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4644697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4644697 prefixEnd_4644697 := by exact prefixLift 4644697
  have htrace : WordTrace (prefixWord ++ tailWord_4644697) baseStart_4644697 baseEnd_4644697 := by
    simpa [prefixWord, tailWord_4644697, baseEnd_4644697] using wordTrace_append hprefix tailTrace_4644697
  have hstable : (prefixWord ++ tailWord_4644697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4644697).length < 2 ^ (prefixWord ++ tailWord_4644697).sum := by decide
  have hdescent : baseEnd_4644697 < baseStart_4644697 := by decide
  rcases family_descends (prefixWord ++ tailWord_4644697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4644708 : List Nat := [2, 3, 1, 1, 5, 1, 1, 2, 2, 3, 2]
def baseStart_4644708 : Nat := 118140960795 + 4644708 * 2 ^ 59
def prefixEnd_4644708 : Nat := 4983230072969 + 3 ^ 40 * 4644708 * 2
def baseEnd_4644708 : Nat := 2384967703783318792289383

theorem tailTrace_4644708 : CollatzResearch.WordTrace tailWord_4644708 prefixEnd_4644708 2384967703783318792289383 := by
  unfold tailWord_4644708
  simp only [CollatzResearch.WordTrace]
  refine ⟨84703209028511821908707389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112937612038015762544943185 84703209028511821908707389)
  ·
    refine ⟨31763703385691933215765271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84703209028511821908707389 31763703385691933215765271)
    ·
      refine ⟨47645555078537899823647907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31763703385691933215765271 47645555078537899823647907)
      ·
        refine ⟨71468332617806849735471861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47645555078537899823647907 71468332617806849735471861)
        ·
          refine ⟨6700156182919392162700487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 71468332617806849735471861 6700156182919392162700487)
          ·
            refine ⟨10050234274379088244050731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6700156182919392162700487 10050234274379088244050731)
            ·
              refine ⟨15075351411568632366076097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10050234274379088244050731 15075351411568632366076097)
              ·
                refine ⟨11306513558676474274557073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15075351411568632366076097 11306513558676474274557073)
                ·
                  refine ⟨8479885169007355705917805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11306513558676474274557073 8479885169007355705917805)
                  ·
                    refine ⟨3179956938377758389719177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8479885169007355705917805 3179956938377758389719177)
                    ·
                      refine ⟨2384967703783318792289383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3179956938377758389719177 2384967703783318792289383)
                      ·
                        rfl

theorem cell23_4644708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 2, 2, 3, 2].length) (baseStart_4644708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4644708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4644708 prefixEnd_4644708 := by exact prefixLift 4644708
  have htrace : WordTrace (prefixWord ++ tailWord_4644708) baseStart_4644708 baseEnd_4644708 := by
    simpa [prefixWord, tailWord_4644708, baseEnd_4644708] using wordTrace_append hprefix tailTrace_4644708
  have hstable : (prefixWord ++ tailWord_4644708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4644708).length < 2 ^ (prefixWord ++ tailWord_4644708).sum := by decide
  have hdescent : baseEnd_4644708 < baseStart_4644708 := by decide
  rcases family_descends (prefixWord ++ tailWord_4644708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4644766 : List Nat := [4, 3, 1, 3, 1, 2, 2, 2, 1, 1, 3]
def baseStart_4644766 : Nat := 118140960795 + 4644766 * 2 ^ 59
def prefixEnd_4644766 : Nat := 4983230072969 + 3 ^ 40 * 4644766 * 2
def baseEnd_4644766 : Nat := 2384997485661279565364117

theorem tailTrace_4644766 : CollatzResearch.WordTrace tailWord_4644766 prefixEnd_4644766 2384997485661279565364117 := by
  unfold tailWord_4644766
  simp only [CollatzResearch.WordTrace]
  refine ⟨21176066686351689965378269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112939022327209013148684101 21176066686351689965378269)
  ·
    refine ⟨7941025007381883737016851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21176066686351689965378269 7941025007381883737016851)
    ·
      refine ⟨11911537511072825605525277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7941025007381883737016851 11911537511072825605525277)
      ·
        refine ⟨4466826566652309602071979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11911537511072825605525277 4466826566652309602071979)
        ·
          refine ⟨6700239849978464403107969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4466826566652309602071979 6700239849978464403107969)
          ·
            refine ⟨5025179887483848302330977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6700239849978464403107969 5025179887483848302330977)
            ·
              refine ⟨3768884915612886226748233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5025179887483848302330977 3768884915612886226748233)
              ·
                refine ⟨2826663686709664670061175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3768884915612886226748233 2826663686709664670061175)
                ·
                  refine ⟨4239995530064497005091763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2826663686709664670061175 4239995530064497005091763)
                  ·
                    refine ⟨6359993295096745507637645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4239995530064497005091763 6359993295096745507637645)
                    ·
                      refine ⟨2384997485661279565364117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6359993295096745507637645 2384997485661279565364117)
                      ·
                        rfl

theorem cell23_4644766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_4644766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4644766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4644766 prefixEnd_4644766 := by exact prefixLift 4644766
  have htrace : WordTrace (prefixWord ++ tailWord_4644766) baseStart_4644766 baseEnd_4644766 := by
    simpa [prefixWord, tailWord_4644766, baseEnd_4644766] using wordTrace_append hprefix tailTrace_4644766
  have hstable : (prefixWord ++ tailWord_4644766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4644766).length < 2 ^ (prefixWord ++ tailWord_4644766).sum := by decide
  have hdescent : baseEnd_4644766 < baseStart_4644766 := by decide
  rcases family_descends (prefixWord ++ tailWord_4644766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4644772 : List Nat := [2, 3, 1, 2, 1, 3, 4, 2, 1, 2, 2]
def baseStart_4644772 : Nat := 118140960795 + 4644772 * 2 ^ 59
def prefixEnd_4644772 : Nat := 4983230072969 + 3 ^ 40 * 4644772 * 2
def baseEnd_4644772 : Nat := 2385000566545206541889089

theorem tailTrace_4644772 : CollatzResearch.WordTrace tailWord_4644772 prefixEnd_4644772 2385000566545206541889089 := by
  unfold tailWord_4644772
  simp only [CollatzResearch.WordTrace]
  refine ⟨84704376164395891373872285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112939168219194521831829713 84704376164395891373872285)
  ·
    refine ⟨31764141061648459265202107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84704376164395891373872285 31764141061648459265202107)
    ·
      refine ⟨47646211592472688897803161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31764141061648459265202107 47646211592472688897803161)
      ·
        refine ⟨35734658694354516673352371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47646211592472688897803161 35734658694354516673352371)
        ·
          refine ⟨53601988041531775010028557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35734658694354516673352371 53601988041531775010028557)
          ·
            refine ⟨20100745515574415628760709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53601988041531775010028557 20100745515574415628760709)
            ·
              refine ⟨3768889784170202930392633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20100745515574415628760709 3768889784170202930392633)
              ·
                refine ⟨2826667338127652197794475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3768889784170202930392633 2826667338127652197794475)
                ·
                  refine ⟨4240001007191478296691713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2826667338127652197794475 4240001007191478296691713)
                  ·
                    refine ⟨3180000755393608722518785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4240001007191478296691713 3180000755393608722518785)
                    ·
                      refine ⟨2385000566545206541889089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3180000755393608722518785 2385000566545206541889089)
                      ·
                        rfl

theorem cell23_4644772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 4, 2, 1, 2, 2].length) (baseStart_4644772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4644772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4644772 prefixEnd_4644772 := by exact prefixLift 4644772
  have htrace : WordTrace (prefixWord ++ tailWord_4644772) baseStart_4644772 baseEnd_4644772 := by
    simpa [prefixWord, tailWord_4644772, baseEnd_4644772] using wordTrace_append hprefix tailTrace_4644772
  have hstable : (prefixWord ++ tailWord_4644772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4644772).length < 2 ^ (prefixWord ++ tailWord_4644772).sum := by decide
  have hdescent : baseEnd_4644772 < baseStart_4644772 := by decide
  rcases family_descends (prefixWord ++ tailWord_4644772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4644798 : List Nat := [4, 2, 1, 1, 1, 3, 2, 1, 3, 3, 2]
def baseStart_4644798 : Nat := 118140960795 + 4644798 * 2 ^ 59
def prefixEnd_4644798 : Nat := 4983230072969 + 3 ^ 40 * 4644798 * 2
def baseEnd_4644798 : Nat := 2385013917042223440163969

theorem tailTrace_4644798 : CollatzResearch.WordTrace tailWord_4644798 prefixEnd_4644798 2385013917042223440163969 := by
  unfold tailWord_4644798
  simp only [CollatzResearch.WordTrace]
  refine ⟨21176212578337198648523881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112939800417798392792127365 21176212578337198648523881)
  ·
    refine ⟨15882159433752898986392911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21176212578337198648523881 15882159433752898986392911)
    ·
      refine ⟨23823239150629348479589367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15882159433752898986392911 23823239150629348479589367)
      ·
        refine ⟨35734858725944022719384051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23823239150629348479589367 35734858725944022719384051)
        ·
          refine ⟨53602288088916034079076077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35734858725944022719384051 53602288088916034079076077)
          ·
            refine ⟨20100858033343512779653529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53602288088916034079076077 20100858033343512779653529)
            ·
              refine ⟨15075643525007634584740147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20100858033343512779653529 15075643525007634584740147)
              ·
                refine ⟨22613465287511451877110221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15075643525007634584740147 22613465287511451877110221)
                ·
                  refine ⟨8480049482816794453916333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22613465287511451877110221 8480049482816794453916333)
                  ·
                    refine ⟨3180018556056297920218625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8480049482816794453916333 3180018556056297920218625)
                    ·
                      refine ⟨2385013917042223440163969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3180018556056297920218625 2385013917042223440163969)
                      ·
                        rfl

theorem cell23_4644798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 1, 3, 3, 2].length) (baseStart_4644798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4644798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4644798 prefixEnd_4644798 := by exact prefixLift 4644798
  have htrace : WordTrace (prefixWord ++ tailWord_4644798) baseStart_4644798 baseEnd_4644798 := by
    simpa [prefixWord, tailWord_4644798, baseEnd_4644798] using wordTrace_append hprefix tailTrace_4644798
  have hstable : (prefixWord ++ tailWord_4644798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4644798).length < 2 ^ (prefixWord ++ tailWord_4644798).sum := by decide
  have hdescent : baseEnd_4644798 < baseStart_4644798 := by decide
  rcases family_descends (prefixWord ++ tailWord_4644798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4644811 : List Nat := [1, 1, 1, 1, 3, 4, 1, 4, 1, 4, 2]
def baseStart_4644811 : Nat := 118140960795 + 4644811 * 2 ^ 59
def prefixEnd_4644811 : Nat := 4983230072969 + 3 ^ 40 * 4644811 * 2
def baseEnd_4644811 : Nat := 2385020592290731889301409

theorem tailTrace_4644811 : CollatzResearch.WordTrace tailWord_4644811 prefixEnd_4644811 2385020592290731889301409 := by
  unfold tailWord_4644811
  simp only [CollatzResearch.WordTrace]
  refine ⟨169410174775650492408414287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112940116517100328272276191 169410174775650492408414287)
  ·
    refine ⟨254115262163475738612621431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169410174775650492408414287 254115262163475738612621431)
    ·
      refine ⟨381172893245213607918932147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 254115262163475738612621431 381172893245213607918932147)
      ·
        refine ⟨571759339867820411878398221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 381172893245213607918932147 571759339867820411878398221)
        ·
          refine ⟨214409752450432654454399333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 571759339867820411878398221 214409752450432654454399333)
          ·
            refine ⟨40201828584456122710199875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 214409752450432654454399333 40201828584456122710199875)
            ·
              refine ⟨60302742876684184065299813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40201828584456122710199875 60302742876684184065299813)
              ·
                refine ⟨11306764289378284512243715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60302742876684184065299813 11306764289378284512243715)
                ·
                  refine ⟨16960146434067426768365573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11306764289378284512243715 16960146434067426768365573)
                  ·
                    refine ⟨3180027456387642519068545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16960146434067426768365573 3180027456387642519068545)
                    ·
                      refine ⟨2385020592290731889301409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3180027456387642519068545 2385020592290731889301409)
                      ·
                        rfl

theorem cell23_4644811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 1, 4, 2].length) (baseStart_4644811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4644811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4644811 prefixEnd_4644811 := by exact prefixLift 4644811
  have htrace : WordTrace (prefixWord ++ tailWord_4644811) baseStart_4644811 baseEnd_4644811 := by
    simpa [prefixWord, tailWord_4644811, baseEnd_4644811] using wordTrace_append hprefix tailTrace_4644811
  have hstable : (prefixWord ++ tailWord_4644811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4644811).length < 2 ^ (prefixWord ++ tailWord_4644811).sum := by decide
  have hdescent : baseEnd_4644811 < baseStart_4644811 := by decide
  rcases family_descends (prefixWord ++ tailWord_4644811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4644814 : List Nat := [4, 1, 1, 1, 2, 2, 2, 1, 1, 3, 5]
def baseStart_4644814 : Nat := 118140960795 + 4644814 * 2 ^ 59
def prefixEnd_4644814 : Nat := 4983230072969 + 3 ^ 40 * 4644814 * 2
def baseEnd_4644814 : Nat := 2385022132732695377563895

theorem tailTrace_4644814 : CollatzResearch.WordTrace tailWord_4644814 prefixEnd_4644814 2385022132732695377563895 := by
  unfold tailWord_4644814
  simp only [CollatzResearch.WordTrace]
  refine ⟨21176285524329952990096687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112940189463093082613848997 21176285524329952990096687)
  ·
    refine ⟨31764428286494929485145031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21176285524329952990096687 31764428286494929485145031)
    ·
      refine ⟨47646642429742394227717547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31764428286494929485145031 47646642429742394227717547)
      ·
        refine ⟨71469963644613591341576321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47646642429742394227717547 71469963644613591341576321)
        ·
          refine ⟨53602472733460193506182241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71469963644613591341576321 53602472733460193506182241)
          ·
            refine ⟨40201854550095145129636681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53602472733460193506182241 40201854550095145129636681)
            ·
              refine ⟨30151390912571358847227511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40201854550095145129636681 30151390912571358847227511)
              ·
                refine ⟨45227086368857038270841267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30151390912571358847227511 45227086368857038270841267)
                ·
                  refine ⟨67840629553285557406261901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45227086368857038270841267 67840629553285557406261901)
                  ·
                    refine ⟨25440236082482084027348213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 67840629553285557406261901 25440236082482084027348213)
                    ·
                      refine ⟨2385022132732695377563895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25440236082482084027348213 2385022132732695377563895)
                      ·
                        rfl

theorem cell23_4644814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 1, 1, 3, 5].length) (baseStart_4644814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4644814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4644814 prefixEnd_4644814 := by exact prefixLift 4644814
  have htrace : WordTrace (prefixWord ++ tailWord_4644814) baseStart_4644814 baseEnd_4644814 := by
    simpa [prefixWord, tailWord_4644814, baseEnd_4644814] using wordTrace_append hprefix tailTrace_4644814
  have hstable : (prefixWord ++ tailWord_4644814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4644814).length < 2 ^ (prefixWord ++ tailWord_4644814).sum := by decide
  have hdescent : baseEnd_4644814 < baseStart_4644814 := by decide
  rcases family_descends (prefixWord ++ tailWord_4644814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4644824 : List Nat := [2, 1, 2, 2, 2, 2, 1, 1, 4, 2, 4]
def baseStart_4644824 : Nat := 118140960795 + 4644824 * 2 ^ 59
def prefixEnd_4644824 : Nat := 4983230072969 + 3 ^ 40 * 4644824 * 2
def baseEnd_4644824 : Nat := 2385027267539240338438849

theorem tailTrace_4644824 : CollatzResearch.WordTrace tailWord_4644824 prefixEnd_4644824 2385027267539240338438849 := by
  unfold tailWord_4644824
  simp only [CollatzResearch.WordTrace]
  refine ⟨84705324462301697814318763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112940432616402263752425017 84705324462301697814318763)
  ·
    refine ⟨127057986693452546721478145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84705324462301697814318763 127057986693452546721478145)
    ·
      refine ⟨95293490020089410041108609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127057986693452546721478145 95293490020089410041108609)
      ·
        refine ⟨71470117515067057530831457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95293490020089410041108609 71470117515067057530831457)
        ·
          refine ⟨53602588136300293148123593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71470117515067057530831457 53602588136300293148123593)
          ·
            refine ⟨40201941102225219861092695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53602588136300293148123593 40201941102225219861092695)
            ·
              refine ⟨60302911653337829791639043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40201941102225219861092695 60302911653337829791639043)
              ·
                refine ⟨90454367480006744687458565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60302911653337829791639043 90454367480006744687458565)
                ·
                  refine ⟨16960193902501264628898481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 90454367480006744687458565 16960193902501264628898481)
                  ·
                    refine ⟨12720145426875948471673861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16960193902501264628898481 12720145426875948471673861)
                    ·
                      refine ⟨2385027267539240338438849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12720145426875948471673861 2385027267539240338438849)
                      ·
                        rfl

theorem cell23_4644824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 4, 2, 4].length) (baseStart_4644824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4644824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4644824 prefixEnd_4644824 := by exact prefixLift 4644824
  have htrace : WordTrace (prefixWord ++ tailWord_4644824) baseStart_4644824 baseEnd_4644824 := by
    simpa [prefixWord, tailWord_4644824, baseEnd_4644824] using wordTrace_append hprefix tailTrace_4644824
  have hstable : (prefixWord ++ tailWord_4644824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4644824).length < 2 ^ (prefixWord ++ tailWord_4644824).sum := by decide
  have hdescent : baseEnd_4644824 < baseStart_4644824 := by decide
  rcases family_descends (prefixWord ++ tailWord_4644824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4644885 : List Nat := [1, 3, 2, 1, 5, 1, 3, 2, 5]
def baseStart_4644885 : Nat := 118140960795 + 4644885 * 2 ^ 59
def prefixEnd_4644885 : Nat := 4983230072969 + 3 ^ 40 * 4644885 * 2
def baseEnd_4644885 : Nat := 265006509984351622197341

theorem tailTrace_4644885 : CollatzResearch.WordTrace tailWord_4644885 prefixEnd_4644885 265006509984351622197341 := by
  unfold tailWord_4644885
  simp only [CollatzResearch.WordTrace]
  refine ⟨169412873777382403046608109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112941915851588268697738739 169412873777382403046608109)
  ·
    refine ⟨63529827666518401142478041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 169412873777382403046608109 63529827666518401142478041)
    ·
      refine ⟨47647370749888800856858531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63529827666518401142478041 47647370749888800856858531)
      ·
        refine ⟨71471056124833201285287797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47647370749888800856858531 71471056124833201285287797)
        ·
          refine ⟨6700411511703112620495731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 71471056124833201285287797 6700411511703112620495731)
          ·
            refine ⟨10050617267554668930743597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6700411511703112620495731 10050617267554668930743597)
            ·
              refine ⟨3768981475333000849028849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10050617267554668930743597 3768981475333000849028849)
              ·
                refine ⟨2826736106499750636771637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3768981475333000849028849 2826736106499750636771637)
                ·
                  refine ⟨265006509984351622197341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2826736106499750636771637 265006509984351622197341)
                  ·
                    rfl

theorem cell23_4644885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 3, 2, 5].length) (baseStart_4644885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4644885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4644885 prefixEnd_4644885 := by exact prefixLift 4644885
  have htrace : WordTrace (prefixWord ++ tailWord_4644885) baseStart_4644885 baseEnd_4644885 := by
    simpa [prefixWord, tailWord_4644885, baseEnd_4644885] using wordTrace_append hprefix tailTrace_4644885
  have hstable : (prefixWord ++ tailWord_4644885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4644885).length < 2 ^ (prefixWord ++ tailWord_4644885).sum := by decide
  have hdescent : baseEnd_4644885 < baseStart_4644885 := by decide
  rcases family_descends (prefixWord ++ tailWord_4644885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4644988 : List Nat := [2, 2, 2, 1, 1, 5, 1, 3, 1, 5]
def baseStart_4644988 : Nat := 118140960795 + 4644988 * 2 ^ 59
def prefixEnd_4644988 : Nat := 4983230072969 + 3 ^ 40 * 4644988 * 2
def baseEnd_4644988 : Nat := 795037159455525898929365

theorem tailTrace_4644988 : CollatzResearch.WordTrace tailWord_4644988 prefixEnd_4644988 795037159455525898929365 := by
  unfold tailWord_4644988
  simp only [CollatzResearch.WordTrace]
  refine ⟨84708315248004625818803809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112944420330672834425071745 84708315248004625818803809)
  ·
    refine ⟨63531236436003469364102857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84708315248004625818803809 63531236436003469364102857)
    ·
      refine ⟨47648427327002602023077143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63531236436003469364102857 47648427327002602023077143)
      ·
        refine ⟨71472640990503903034615715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47648427327002602023077143 71472640990503903034615715)
        ·
          refine ⟨107208961485755854551923573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71472640990503903034615715 107208961485755854551923573)
          ·
            refine ⟨10050840139289611364242835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 107208961485755854551923573 10050840139289611364242835)
            ·
              refine ⟨15076260208934417046364253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10050840139289611364242835 15076260208934417046364253)
              ·
                refine ⟨5653597578350406392386595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15076260208934417046364253 5653597578350406392386595)
                ·
                  refine ⟨8480396367525609588579893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5653597578350406392386595 8480396367525609588579893)
                  ·
                    refine ⟨795037159455525898929365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8480396367525609588579893 795037159455525898929365)
                    ·
                      rfl

theorem cell23_4644988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 3, 1, 5].length) (baseStart_4644988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4644988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4644988 prefixEnd_4644988 := by exact prefixLift 4644988
  have htrace : WordTrace (prefixWord ++ tailWord_4644988) baseStart_4644988 baseEnd_4644988 := by
    simpa [prefixWord, tailWord_4644988, baseEnd_4644988] using wordTrace_append hprefix tailTrace_4644988
  have hstable : (prefixWord ++ tailWord_4644988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4644988).length < 2 ^ (prefixWord ++ tailWord_4644988).sum := by decide
  have hdescent : baseEnd_4644988 < baseStart_4644988 := by decide
  rcases family_descends (prefixWord ++ tailWord_4644988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4645002 : List Nat := [3, 1, 2, 3, 1, 2, 2, 4, 1, 1, 3]
def baseStart_4645002 : Nat := 118140960795 + 4645002 * 2 ^ 59
def prefixEnd_4645002 : Nat := 4983230072969 + 3 ^ 40 * 4645002 * 2
def baseEnd_4645002 : Nat := 2385118667095740642013031

theorem tailTrace_4645002 : CollatzResearch.WordTrace tailWord_4645002 prefixEnd_4645002 2385118667095740642013031 := by
  unfold tailWord_4645002
  simp only [CollatzResearch.WordTrace]
  refine ⟨42354285279489633007154315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112944760745305688019078173 42354285279489633007154315)
  ·
    refine ⟨63531427919234449510731473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42354285279489633007154315 63531427919234449510731473)
    ·
      refine ⟨47648570939425837133048605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63531427919234449510731473 47648570939425837133048605)
      ·
        refine ⟨17868214102284688924893227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47648570939425837133048605 17868214102284688924893227)
        ·
          refine ⟨26802321153427033387339841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17868214102284688924893227 26802321153427033387339841)
          ·
            refine ⟨20101740865070275040504881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26802321153427033387339841 20101740865070275040504881)
            ·
              refine ⟨15076305648802706280378661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20101740865070275040504881 15076305648802706280378661)
              ·
                refine ⟨2826807309150507427570999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15076305648802706280378661 2826807309150507427570999)
                ·
                  refine ⟨4240210963725761141356499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2826807309150507427570999 4240210963725761141356499)
                  ·
                    refine ⟨6360316445588641712034749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4240210963725761141356499 6360316445588641712034749)
                    ·
                      refine ⟨2385118667095740642013031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6360316445588641712034749 2385118667095740642013031)
                      ·
                        rfl

theorem cell23_4645002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 4, 1, 1, 3].length) (baseStart_4645002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4645002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4645002 prefixEnd_4645002 := by exact prefixLift 4645002
  have htrace : WordTrace (prefixWord ++ tailWord_4645002) baseStart_4645002 baseEnd_4645002 := by
    simpa [prefixWord, tailWord_4645002, baseEnd_4645002] using wordTrace_append hprefix tailTrace_4645002
  have hstable : (prefixWord ++ tailWord_4645002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4645002).length < 2 ^ (prefixWord ++ tailWord_4645002).sum := by decide
  have hdescent : baseEnd_4645002 < baseStart_4645002 := by decide
  rcases family_descends (prefixWord ++ tailWord_4645002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4645022 : List Nat := [4, 3, 1, 1, 3, 1, 2, 2, 1, 5]
def baseStart_4645022 : Nat := 118140960795 + 4645022 * 2 ^ 59
def prefixEnd_4645022 : Nat := 4983230072969 + 3 ^ 40 * 4645022 * 2
def baseEnd_4645022 : Nat := 795042978902943521254313

theorem tailTrace_4645022 : CollatzResearch.WordTrace tailWord_4645022 prefixEnd_4645022 795042978902943521254313 := by
  unfold tailWord_4645022
  simp only [CollatzResearch.WordTrace]
  refine ⟨21177233822235759430543165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112945247051924050296230213 21177233822235759430543165)
  ·
    refine ⟨7941462683338409786453687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21177233822235759430543165 7941462683338409786453687)
    ·
      refine ⟨11912194025007614679680531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7941462683338409786453687 11912194025007614679680531)
      ·
        refine ⟨17868291037511422019520797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11912194025007614679680531 17868291037511422019520797)
        ·
          refine ⟨6700609139066783257320299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17868291037511422019520797 6700609139066783257320299)
          ·
            refine ⟨10050913708600174885980449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6700609139066783257320299 10050913708600174885980449)
            ·
              refine ⟨7538185281450131164485337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10050913708600174885980449 7538185281450131164485337)
              ·
                refine ⟨5653638961087598373364003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7538185281450131164485337 5653638961087598373364003)
                ·
                  refine ⟨8480458441631397560046005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5653638961087598373364003 8480458441631397560046005)
                  ·
                    refine ⟨795042978902943521254313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8480458441631397560046005 795042978902943521254313)
                    ·
                      rfl

theorem cell23_4645022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 2, 2, 1, 5].length) (baseStart_4645022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4645022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4645022 prefixEnd_4645022 := by exact prefixLift 4645022
  have htrace : WordTrace (prefixWord ++ tailWord_4645022) baseStart_4645022 baseEnd_4645022 := by
    simpa [prefixWord, tailWord_4645022, baseEnd_4645022] using wordTrace_append hprefix tailTrace_4645022
  have hstable : (prefixWord ++ tailWord_4645022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4645022).length < 2 ^ (prefixWord ++ tailWord_4645022).sum := by decide
  have hdescent : baseEnd_4645022 < baseStart_4645022 := by decide
  rcases family_descends (prefixWord ++ tailWord_4645022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4645025 : List Nat := [1, 2, 3, 3, 1, 3, 2, 2, 1, 1, 4]
def baseStart_4645025 : Nat := 118140960795 + 4645025 * 2 ^ 59
def prefixEnd_4645025 : Nat := 4983230072969 + 3 ^ 40 * 4645025 * 2
def baseEnd_4645025 : Nat := 2385130477150794052025425

theorem tailTrace_4645025 : CollatzResearch.WordTrace tailWord_4645025 prefixEnd_4645025 2385130477150794052025425 := by
  unfold tailWord_4645025
  simp only [CollatzResearch.WordTrace]
  refine ⟨169417979996875206956704529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112945319997916804637803019 169417979996875206956704529)
  ·
    refine ⟨127063484997656405217528397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169417979996875206956704529 127063484997656405217528397)
    ·
      refine ⟨47648806874121151956573149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 127063484997656405217528397 47648806874121151956573149)
      ·
        refine ⟨17868302577795431983714931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47648806874121151956573149 17868302577795431983714931)
        ·
          refine ⟨26802453866693147975572397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17868302577795431983714931 26802453866693147975572397)
          ·
            refine ⟨10050920200009930490839649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26802453866693147975572397 10050920200009930490839649)
            ·
              refine ⟨7538190150007447868129737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10050920200009930490839649 7538190150007447868129737)
              ·
                refine ⟨5653642612505585901097303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7538190150007447868129737 5653642612505585901097303)
                ·
                  refine ⟨8480463918758378851645955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5653642612505585901097303 8480463918758378851645955)
                  ·
                    refine ⟨12720695878137568277468933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8480463918758378851645955 12720695878137568277468933)
                    ·
                      refine ⟨2385130477150794052025425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12720695878137568277468933 2385130477150794052025425)
                      ·
                        rfl

theorem cell23_4645025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 2, 2, 1, 1, 4].length) (baseStart_4645025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4645025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4645025 prefixEnd_4645025 := by exact prefixLift 4645025
  have htrace : WordTrace (prefixWord ++ tailWord_4645025) baseStart_4645025 baseEnd_4645025 := by
    simpa [prefixWord, tailWord_4645025, baseEnd_4645025] using wordTrace_append hprefix tailTrace_4645025
  have hstable : (prefixWord ++ tailWord_4645025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4645025).length < 2 ^ (prefixWord ++ tailWord_4645025).sum := by decide
  have hdescent : baseEnd_4645025 < baseStart_4645025 := by decide
  rcases family_descends (prefixWord ++ tailWord_4645025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4645128 : List Nat := [2, 1, 3, 2, 3, 1, 1, 1, 1, 4, 4]
def baseStart_4645128 : Nat := 118140960795 + 4645128 * 2 ^ 59
def prefixEnd_4645128 : Nat := 4983230072969 + 3 ^ 40 * 4645128 * 2
def baseEnd_4645128 : Nat := 2385183365658207149037451

theorem tailTrace_4645128 : CollatzResearch.WordTrace tailWord_4645128 prefixEnd_4645128 2385183365658207149037451 := by
  unfold tailWord_4645128
  simp only [CollatzResearch.WordTrace]
  refine ⟨84710868357751027773852019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112947824477001370365136025 84710868357751027773852019)
  ·
    refine ⟨127066302536626541660778029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84710868357751027773852019 127066302536626541660778029)
    ·
      refine ⟨47649863451234953122791761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 127066302536626541660778029 47649863451234953122791761)
      ·
        refine ⟨35737397588426214842093821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47649863451234953122791761 35737397588426214842093821)
        ·
          refine ⟨13401524095659830565785183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35737397588426214842093821 13401524095659830565785183)
          ·
            refine ⟨20102286143489745848677775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13401524095659830565785183 20102286143489745848677775)
            ·
              refine ⟨30153429215234618773016663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20102286143489745848677775 30153429215234618773016663)
              ·
                refine ⟨45230143822851928159524995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30153429215234618773016663 45230143822851928159524995)
                ·
                  refine ⟨67845215734277892239287493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45230143822851928159524995 67845215734277892239287493)
                  ·
                    refine ⟨12720977950177104794866405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 67845215734277892239287493 12720977950177104794866405)
                    ·
                      refine ⟨2385183365658207149037451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12720977950177104794866405 2385183365658207149037451)
                      ·
                        rfl

theorem cell23_4645128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 1, 1, 4, 4].length) (baseStart_4645128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4645128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4645128 prefixEnd_4645128 := by exact prefixLift 4645128
  have htrace : WordTrace (prefixWord ++ tailWord_4645128) baseStart_4645128 baseEnd_4645128 := by
    simpa [prefixWord, tailWord_4645128, baseEnd_4645128] using wordTrace_append hprefix tailTrace_4645128
  have hstable : (prefixWord ++ tailWord_4645128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4645128).length < 2 ^ (prefixWord ++ tailWord_4645128).sum := by decide
  have hdescent : baseEnd_4645128 < baseStart_4645128 := by decide
  rcases family_descends (prefixWord ++ tailWord_4645128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4645132 : List Nat := [2, 2, 1, 2, 2, 2, 1, 5, 2, 2, 2]
def baseStart_4645132 : Nat := 118140960795 + 4645132 * 2 ^ 59
def prefixEnd_4645132 : Nat := 4983230072969 + 3 ^ 40 * 4645132 * 2
def baseEnd_4645132 : Nat := 2385185419580825133387433

theorem tailTrace_4645132 : CollatzResearch.WordTrace tailWord_4645132 prefixEnd_4645132 2385185419580825133387433 := by
  unfold tailWord_4645132
  simp only [CollatzResearch.WordTrace]
  refine ⟨84710941303743782115424825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112947921738325042820566433 84710941303743782115424825)
  ·
    refine ⟨63533205977807836586568619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84710941303743782115424825 63533205977807836586568619)
    ·
      refine ⟨95299808966711754879852929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63533205977807836586568619 95299808966711754879852929)
      ·
        refine ⟨71474856725033816159889697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95299808966711754879852929 71474856725033816159889697)
        ·
          refine ⟨53606142543775362119917273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71474856725033816159889697 53606142543775362119917273)
          ·
            refine ⟨40204606907831521589937955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53606142543775362119917273 40204606907831521589937955)
            ·
              refine ⟨60306910361747282384906933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40204606907831521589937955 60306910361747282384906933)
              ·
                refine ⟨5653772846413807723585025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 60306910361747282384906933 5653772846413807723585025)
                ·
                  refine ⟨4240329634810355792688769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5653772846413807723585025 4240329634810355792688769)
                  ·
                    refine ⟨3180247226107766844516577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4240329634810355792688769 3180247226107766844516577)
                    ·
                      refine ⟨2385185419580825133387433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3180247226107766844516577 2385185419580825133387433)
                      ·
                        rfl

theorem cell23_4645132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 5, 2, 2, 2].length) (baseStart_4645132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4645132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4645132 prefixEnd_4645132 := by exact prefixLift 4645132
  have htrace : WordTrace (prefixWord ++ tailWord_4645132) baseStart_4645132 baseEnd_4645132 := by
    simpa [prefixWord, tailWord_4645132, baseEnd_4645132] using wordTrace_append hprefix tailTrace_4645132
  have hstable : (prefixWord ++ tailWord_4645132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4645132).length < 2 ^ (prefixWord ++ tailWord_4645132).sum := by decide
  have hdescent : baseEnd_4645132 < baseStart_4645132 := by decide
  rcases family_descends (prefixWord ++ tailWord_4645132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4645148 : List Nat := [2, 2, 3, 1, 1, 1, 1, 1, 3, 5, 3]
def baseStart_4645148 : Nat := 118140960795 + 4645148 * 2 ^ 59
def prefixEnd_4645148 : Nat := 4983230072969 + 3 ^ 40 * 4645148 * 2
def baseEnd_4645148 : Nat := 2385193635271297070787359

theorem tailTrace_4645148 : CollatzResearch.WordTrace tailWord_4645148 prefixEnd_4645148 2385193635271297070787359 := by
  unfold tailWord_4645148
  simp only [CollatzResearch.WordTrace]
  refine ⟨84711233087714799481716049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112948310783619732642288065 84711233087714799481716049)
  ·
    refine ⟨63533424815786099611287037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84711233087714799481716049 63533424815786099611287037)
    ·
      refine ⟨23825034305919787354232639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63533424815786099611287037 23825034305919787354232639)
      ·
        refine ⟨35737551458879681031348959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23825034305919787354232639 35737551458879681031348959)
        ·
          refine ⟨53606327188319521547023439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35737551458879681031348959 53606327188319521547023439)
          ·
            refine ⟨80409490782479282320535159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53606327188319521547023439 80409490782479282320535159)
            ·
              refine ⟨120614236173718923480802739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80409490782479282320535159 120614236173718923480802739)
              ·
                refine ⟨180921354260578385221204109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 120614236173718923480802739 180921354260578385221204109)
                ·
                  refine ⟨67845507847716894457951541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 180921354260578385221204109 67845507847716894457951541)
                  ·
                    refine ⟨6360516360723458855432957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 67845507847716894457951541 6360516360723458855432957)
                    ·
                      refine ⟨2385193635271297070787359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6360516360723458855432957 2385193635271297070787359)
                      ·
                        rfl

theorem cell23_4645148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 3, 5, 3].length) (baseStart_4645148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4645148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4645148 prefixEnd_4645148 := by exact prefixLift 4645148
  have htrace : WordTrace (prefixWord ++ tailWord_4645148) baseStart_4645148 baseEnd_4645148 := by
    simpa [prefixWord, tailWord_4645148, baseEnd_4645148] using wordTrace_append hprefix tailTrace_4645148
  have hstable : (prefixWord ++ tailWord_4645148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4645148).length < 2 ^ (prefixWord ++ tailWord_4645148).sum := by decide
  have hdescent : baseEnd_4645148 < baseStart_4645148 := by decide
  rcases family_descends (prefixWord ++ tailWord_4645148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4645155 : List Nat := [1, 1, 1, 4, 2, 2, 4, 3, 5]
def baseStart_4645155 : Nat := 118140960795 + 4645155 * 2 ^ 59
def prefixEnd_4645155 : Nat := 4983230072969 + 3 ^ 40 * 4645155 * 2
def baseEnd_4645155 : Nat := 265021914403986504822203

theorem tailTrace_4645155 : CollatzResearch.WordTrace tailWord_4645155 prefixEnd_4645155 265021914403986504822203 := by
  unfold tailWord_4645155
  simp only [CollatzResearch.WordTrace]
  refine ⟨169422721486404239158936919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112948480990936159439291279 169422721486404239158936919)
  ·
    refine ⟨254134082229606358738405379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169422721486404239158936919 254134082229606358738405379)
    ·
      refine ⟨381201123344409538107608069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 254134082229606358738405379 381201123344409538107608069)
      ·
        refine ⟨71475210627076788395176513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 381201123344409538107608069 71475210627076788395176513)
        ·
          refine ⟨53606407970307591296382385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71475210627076788395176513 53606407970307591296382385)
          ·
            refine ⟨40204805977730693472286789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53606407970307591296382385 40204805977730693472286789)
            ·
              refine ⟨7538401120824505026053773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40204805977730693472286789 7538401120824505026053773)
              ·
                refine ⟨2826900420309189384770165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7538401120824505026053773 2826900420309189384770165)
                ·
                  refine ⟨265021914403986504822203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2826900420309189384770165 265021914403986504822203)
                  ·
                    rfl

theorem cell23_4645155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 4, 3, 5].length) (baseStart_4645155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4645155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4645155 prefixEnd_4645155 := by exact prefixLift 4645155
  have htrace : WordTrace (prefixWord ++ tailWord_4645155) baseStart_4645155 baseEnd_4645155 := by
    simpa [prefixWord, tailWord_4645155, baseEnd_4645155] using wordTrace_append hprefix tailTrace_4645155
  have hstable : (prefixWord ++ tailWord_4645155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4645155).length < 2 ^ (prefixWord ++ tailWord_4645155).sum := by decide
  have hdescent : baseEnd_4645155 < baseStart_4645155 := by decide
  rcases family_descends (prefixWord ++ tailWord_4645155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4645166 : List Nat := [4, 1, 3, 3, 1, 1, 1, 1, 4, 2, 2]
def baseStart_4645166 : Nat := 118140960795 + 4645166 * 2 ^ 59
def prefixEnd_4645166 : Nat := 4983230072969 + 3 ^ 40 * 4645166 * 2
def baseEnd_4645166 : Nat := 2385202877923078000362277

theorem tailTrace_4645166 : CollatzResearch.WordTrace tailWord_4645166 prefixEnd_4645166 2385202877923078000362277 := by
  unfold tailWord_4645166
  simp only [CollatzResearch.WordTrace]
  refine ⟨21177890336170548504698419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112948748459576258691724901 21177890336170548504698419)
  ·
    refine ⟨31766835504255822757047629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21177890336170548504698419 31766835504255822757047629)
    ·
      refine ⟨11912563314095933533892861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31766835504255822757047629 11912563314095933533892861)
      ·
        refine ⟨4467211242785975075209823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11912563314095933533892861 4467211242785975075209823)
        ·
          refine ⟨6700816864178962612814735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4467211242785975075209823 6700816864178962612814735)
          ·
            refine ⟨10051225296268443919222103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6700816864178962612814735 10051225296268443919222103)
            ·
              refine ⟨15076837944402665878833155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10051225296268443919222103 15076837944402665878833155)
              ·
                refine ⟨22615256916603998818249733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15076837944402665878833155 22615256916603998818249733)
                ·
                  refine ⟨4240360671863249778421825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22615256916603998818249733 4240360671863249778421825)
                  ·
                    refine ⟨3180270503897437333816369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4240360671863249778421825 3180270503897437333816369)
                    ·
                      refine ⟨2385202877923078000362277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3180270503897437333816369 2385202877923078000362277)
                      ·
                        rfl

theorem cell23_4645166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_4645166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4645166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4645166 prefixEnd_4645166 := by exact prefixLift 4645166
  have htrace : WordTrace (prefixWord ++ tailWord_4645166) baseStart_4645166 baseEnd_4645166 := by
    simpa [prefixWord, tailWord_4645166, baseEnd_4645166] using wordTrace_append hprefix tailTrace_4645166
  have hstable : (prefixWord ++ tailWord_4645166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4645166).length < 2 ^ (prefixWord ++ tailWord_4645166).sum := by decide
  have hdescent : baseEnd_4645166 < baseStart_4645166 := by decide
  rcases family_descends (prefixWord ++ tailWord_4645166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4645172 : List Nat := [2, 5, 1, 1, 1, 2, 2, 4, 5]
def baseStart_4645172 : Nat := 118140960795 + 4645172 * 2 ^ 59
def prefixEnd_4645172 : Nat := 4983230072969 + 3 ^ 40 * 4645172 * 2
def baseEnd_4645172 : Nat := 265022884311889441876361

theorem tailTrace_4645172 : CollatzResearch.WordTrace tailWord_4645172 prefixEnd_4645172 265022884311889441876361 := by
  unfold tailWord_4645172
  simp only [CollatzResearch.WordTrace]
  refine ⟨84711670763671325531152885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112948894351561767374870513 84711670763671325531152885)
  ·
    refine ⟨7941719134094186768545583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 84711670763671325531152885 7941719134094186768545583)
    ·
      refine ⟨11912578701141280152818375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7941719134094186768545583 11912578701141280152818375)
      ·
        refine ⟨17868868051711920229227563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11912578701141280152818375 17868868051711920229227563)
        ·
          refine ⟨26803302077567880343841345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17868868051711920229227563 26803302077567880343841345)
          ·
            refine ⟨20102476558175910257881009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26803302077567880343841345 20102476558175910257881009)
            ·
              refine ⟨15076857418631932693410757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20102476558175910257881009 15076857418631932693410757)
              ·
                refine ⟨2826910765993487380014517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15076857418631932693410757 2826910765993487380014517)
                ·
                  refine ⟨265022884311889441876361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2826910765993487380014517 265022884311889441876361)
                  ·
                    rfl

theorem cell23_4645172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 4, 5].length) (baseStart_4645172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4645172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4645172 prefixEnd_4645172 := by exact prefixLift 4645172
  have htrace : WordTrace (prefixWord ++ tailWord_4645172) baseStart_4645172 baseEnd_4645172 := by
    simpa [prefixWord, tailWord_4645172, baseEnd_4645172] using wordTrace_append hprefix tailTrace_4645172
  have hstable : (prefixWord ++ tailWord_4645172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4645172).length < 2 ^ (prefixWord ++ tailWord_4645172).sum := by decide
  have hdescent : baseEnd_4645172 < baseStart_4645172 := by decide
  rcases family_descends (prefixWord ++ tailWord_4645172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4645225 : List Nat := [1, 2, 1, 1, 1, 3, 5, 2, 2, 2, 3]
def baseStart_4645225 : Nat := 118140960795 + 4645225 * 2 ^ 59
def prefixEnd_4645225 : Nat := 4983230072969 + 3 ^ 40 * 4645225 * 2
def baseEnd_4645225 : Nat := 2385233173281693269524505

theorem tailTrace_4645225 : CollatzResearch.WordTrace tailWord_4645225 prefixEnd_4645225 2385233173281693269524505 := by
  unfold tailWord_4645225
  simp only [CollatzResearch.WordTrace]
  refine ⟨169425274596150641113985129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112950183064100427409323419 169425274596150641113985129)
  ·
    refine ⟨127068955947112980835488847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169425274596150641113985129 127068955947112980835488847)
    ·
      refine ⟨190603433920669471253233271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127068955947112980835488847 190603433920669471253233271)
      ·
        refine ⟨285905150881004206879849907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190603433920669471253233271 285905150881004206879849907)
        ·
          refine ⟨428857726321506310319774861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 285905150881004206879849907 428857726321506310319774861)
          ·
            refine ⟨160821647370564866369915573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 428857726321506310319774861 160821647370564866369915573)
            ·
              refine ⟨15077029440990456222179585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 160821647370564866369915573 15077029440990456222179585)
              ·
                refine ⟨11307772080742842166634689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15077029440990456222179585 11307772080742842166634689)
                ·
                  refine ⟨8480829060557131624976017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11307772080742842166634689 8480829060557131624976017)
                  ·
                    refine ⟨6360621795417848718732013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8480829060557131624976017 6360621795417848718732013)
                    ·
                      refine ⟨2385233173281693269524505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6360621795417848718732013 2385233173281693269524505)
                      ·
                        rfl

theorem cell23_4645225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 2, 2, 2, 3].length) (baseStart_4645225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4645225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4645225 prefixEnd_4645225 := by exact prefixLift 4645225
  have htrace : WordTrace (prefixWord ++ tailWord_4645225) baseStart_4645225 baseEnd_4645225 := by
    simpa [prefixWord, tailWord_4645225, baseEnd_4645225] using wordTrace_append hprefix tailTrace_4645225
  have hstable : (prefixWord ++ tailWord_4645225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4645225).length < 2 ^ (prefixWord ++ tailWord_4645225).sum := by decide
  have hdescent : baseEnd_4645225 < baseStart_4645225 := by decide
  rcases family_descends (prefixWord ++ tailWord_4645225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4645232 : List Nat := [2, 1, 1, 1, 4, 5, 1, 1, 3, 4]
def baseStart_4645232 : Nat := 118140960795 + 4645232 * 2 ^ 59
def prefixEnd_4645232 : Nat := 4983230072969 + 3 ^ 40 * 4645232 * 2
def baseEnd_4645232 : Nat := 795078922548758247378991

theorem tailTrace_4645232 : CollatzResearch.WordTrace tailWord_4645232 prefixEnd_4645232 795078922548758247378991 := by
  unfold tailWord_4645232
  simp only [CollatzResearch.WordTrace]
  refine ⟨84712764953562640654744975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112950353271416854206326633 84712764953562640654744975)
  ·
    refine ⟨127069147430343960982117463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84712764953562640654744975 127069147430343960982117463)
    ·
      refine ⟨190603721145515941473176195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127069147430343960982117463 190603721145515941473176195)
      ·
        refine ⟨285905581718273912209764293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190603721145515941473176195 285905581718273912209764293)
        ·
          refine ⟨53607296572176358539330805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 285905581718273912209764293 53607296572176358539330805)
          ·
            refine ⟨5025684053641533613062263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 53607296572176358539330805 5025684053641533613062263)
            ·
              refine ⟨7538526080462300419593395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5025684053641533613062263 7538526080462300419593395)
              ·
                refine ⟨11307789120693450629390093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7538526080462300419593395 11307789120693450629390093)
                ·
                  refine ⟨4240420920260043986021285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11307789120693450629390093 4240420920260043986021285)
                  ·
                    refine ⟨795078922548758247378991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4240420920260043986021285 795078922548758247378991)
                    ·
                      rfl

theorem cell23_4645232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 1, 1, 3, 4].length) (baseStart_4645232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4645232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4645232 prefixEnd_4645232 := by exact prefixLift 4645232
  have htrace : WordTrace (prefixWord ++ tailWord_4645232) baseStart_4645232 baseEnd_4645232 := by
    simpa [prefixWord, tailWord_4645232, baseEnd_4645232] using wordTrace_append hprefix tailTrace_4645232
  have hstable : (prefixWord ++ tailWord_4645232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4645232).length < 2 ^ (prefixWord ++ tailWord_4645232).sum := by decide
  have hdescent : baseEnd_4645232 < baseStart_4645232 := by decide
  rcases family_descends (prefixWord ++ tailWord_4645232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4645245 : List Nat := [1, 4, 1, 1, 2, 4, 1, 3, 6]
def baseStart_4645245 : Nat := 118140960795 + 4645245 * 2 ^ 59
def prefixEnd_4645245 : Nat := 4983230072969 + 3 ^ 40 * 4645245 * 2
def baseEnd_4645245 : Nat := 265027049210531465697157

theorem tailTrace_4645245 : CollatzResearch.WordTrace tailWord_4645245 prefixEnd_4645245 265027049210531465697157 := by
  unfold tailWord_4645245
  simp only [CollatzResearch.WordTrace]
  refine ⟨169426004056078184529713189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112950669370718789686475459 169426004056078184529713189)
  ·
    refine ⟨31767375760514659599321223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 169426004056078184529713189 31767375760514659599321223)
    ·
      refine ⟨47651063640771989398981835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31767375760514659599321223 47651063640771989398981835)
      ·
        refine ⟨71476595461157984098472753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47651063640771989398981835 71476595461157984098472753)
        ·
          refine ⟨53607446595868488073854565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71476595461157984098472753 53607446595868488073854565)
          ·
            refine ⟨10051396236725341513847731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53607446595868488073854565 10051396236725341513847731)
            ·
              refine ⟨15077094355088012270771597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10051396236725341513847731 15077094355088012270771597)
              ·
                refine ⟨5653910383158004601539349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15077094355088012270771597 5653910383158004601539349)
                ·
                  refine ⟨265027049210531465697157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5653910383158004601539349 265027049210531465697157)
                  ·
                    rfl

theorem cell23_4645245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 3, 6].length) (baseStart_4645245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4645245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4645245 prefixEnd_4645245 := by exact prefixLift 4645245
  have htrace : WordTrace (prefixWord ++ tailWord_4645245) baseStart_4645245 baseEnd_4645245 := by
    simpa [prefixWord, tailWord_4645245, baseEnd_4645245] using wordTrace_append hprefix tailTrace_4645245
  have hstable : (prefixWord ++ tailWord_4645245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4645245).length < 2 ^ (prefixWord ++ tailWord_4645245).sum := by decide
  have hdescent : baseEnd_4645245 < baseStart_4645245 := by decide
  rcases family_descends (prefixWord ++ tailWord_4645245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4645295 : List Nat := [1, 1, 2, 1, 2, 2, 1, 1, 4, 6, 2]
def baseStart_4645295 : Nat := 118140960795 + 4645295 * 2 ^ 59
def prefixEnd_4645295 : Nat := 4983230072969 + 3 ^ 40 * 4645295 * 2
def baseEnd_4645295 : Nat := 2385269116927507995649183

theorem tailTrace_4645295 : CollatzResearch.WordTrace tailWord_4645295 prefixEnd_4645295 2385269116927507995649183 := by
  unfold tailWord_4645295
  simp only [CollatzResearch.WordTrace]
  refine ⟨169427827705897043069033339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112951885137264695379355559 169427827705897043069033339)
  ·
    refine ⟨254141741558845564603550009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169427827705897043069033339 254141741558845564603550009)
    ·
      refine ⟨190606306169134173452662507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 254141741558845564603550009 190606306169134173452662507)
      ·
        refine ⟨285909459253701260178993761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190606306169134173452662507 285909459253701260178993761)
        ·
          refine ⟨214432094440275945134245321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 285909459253701260178993761 214432094440275945134245321)
          ·
            refine ⟨160824070830206958850683991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 214432094440275945134245321 160824070830206958850683991)
            ·
              refine ⟨241236106245310438276025987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 160824070830206958850683991 241236106245310438276025987)
              ·
                refine ⟨361854159367965657414038981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 241236106245310438276025987 361854159367965657414038981)
                ·
                  refine ⟨67847654881493560765132309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 361854159367965657414038981 67847654881493560765132309)
                  ·
                    refine ⟨3180358822570010660865577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 67847654881493560765132309 3180358822570010660865577)
                    ·
                      refine ⟨2385269116927507995649183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3180358822570010660865577 2385269116927507995649183)
                      ·
                        rfl

theorem cell23_4645295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 4, 6, 2].length) (baseStart_4645295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4645295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4645295 prefixEnd_4645295 := by exact prefixLift 4645295
  have htrace : WordTrace (prefixWord ++ tailWord_4645295) baseStart_4645295 baseEnd_4645295 := by
    simpa [prefixWord, tailWord_4645295, baseEnd_4645295] using wordTrace_append hprefix tailTrace_4645295
  have hstable : (prefixWord ++ tailWord_4645295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4645295).length < 2 ^ (prefixWord ++ tailWord_4645295).sum := by decide
  have hdescent : baseEnd_4645295 < baseStart_4645295 := by decide
  rcases family_descends (prefixWord ++ tailWord_4645295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4645305 : List Nat := [1, 2, 1, 4, 3, 1, 1, 3, 1, 6]
def baseStart_4645305 : Nat := 118140960795 + 4645305 * 2 ^ 59
def prefixEnd_4645305 : Nat := 4983230072969 + 3 ^ 40 * 4645305 * 2
def baseEnd_4645305 : Nat := 795091417244684318841379

theorem tailTrace_4645305 : CollatzResearch.WordTrace tailWord_4645305 prefixEnd_4645305 795091417244684318841379 := by
  unfold tailWord_4645305
  simp only [CollatzResearch.WordTrace]
  refine ⟨169428192435860814776897369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112952128290573876517931579 169428192435860814776897369)
  ·
    refine ⟨127071144326895611082673027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169428192435860814776897369 127071144326895611082673027)
    ·
      refine ⟨190606716490343416624009541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127071144326895611082673027 190606716490343416624009541)
      ·
        refine ⟨35738759341939390617001789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 190606716490343416624009541 35738759341939390617001789)
        ·
          refine ⟨13402034753227271481375671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35738759341939390617001789 13402034753227271481375671)
          ·
            refine ⟨20103052129840907222063507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13402034753227271481375671 20103052129840907222063507)
            ·
              refine ⟨30154578194761360833095261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20103052129840907222063507 30154578194761360833095261)
              ·
                refine ⟨11307966823035510312410723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30154578194761360833095261 11307966823035510312410723)
                ·
                  refine ⟨16961950234553265468616085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11307966823035510312410723 16961950234553265468616085)
                  ·
                    refine ⟨795091417244684318841379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16961950234553265468616085 795091417244684318841379)
                    ·
                      rfl

theorem cell23_4645305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 3, 1, 6].length) (baseStart_4645305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4645305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4645305 prefixEnd_4645305 := by exact prefixLift 4645305
  have htrace : WordTrace (prefixWord ++ tailWord_4645305) baseStart_4645305 baseEnd_4645305 := by
    simpa [prefixWord, tailWord_4645305, baseEnd_4645305] using wordTrace_append hprefix tailTrace_4645305
  have hstable : (prefixWord ++ tailWord_4645305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4645305).length < 2 ^ (prefixWord ++ tailWord_4645305).sum := by decide
  have hdescent : baseEnd_4645305 < baseStart_4645305 := by decide
  rcases family_descends (prefixWord ++ tailWord_4645305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4645380 : List Nat := [2, 3, 2, 3, 1, 3, 1, 3, 1, 2, 2]
def baseStart_4645380 : Nat := 118140960795 + 4645380 * 2 ^ 59
def prefixEnd_4645380 : Nat := 4983230072969 + 3 ^ 40 * 4645380 * 2
def baseEnd_4645380 : Nat := 2385312762783140163086293

theorem tailTrace_4645380 : CollatzResearch.WordTrace tailWord_4645380 prefixEnd_4645380 2385312762783140163086293 := by
  unfold tailWord_4645380
  simp only [CollatzResearch.WordTrace]
  refine ⟨84715463955294551292938797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112953951940392735057251729 84715463955294551292938797)
  ·
    refine ⟨31768298983235456734852049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84715463955294551292938797 31768298983235456734852049)
    ·
      refine ⟨23826224237426592551139037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31768298983235456734852049 23826224237426592551139037)
      ·
        refine ⟨8934834089034972206677139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23826224237426592551139037 8934834089034972206677139)
        ·
          refine ⟨13402251133552458310015709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8934834089034972206677139 13402251133552458310015709)
          ·
            refine ⟨5025844175082171866255891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13402251133552458310015709 5025844175082171866255891)
            ·
              refine ⟨7538766262623257799383837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5025844175082171866255891 7538766262623257799383837)
              ·
                refine ⟨2827037348483721674768939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7538766262623257799383837 2827037348483721674768939)
                ·
                  refine ⟨4240556022725582512153409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2827037348483721674768939 4240556022725582512153409)
                  ·
                    refine ⟨3180417017044186884115057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4240556022725582512153409 3180417017044186884115057)
                    ·
                      refine ⟨2385312762783140163086293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3180417017044186884115057 2385312762783140163086293)
                      ·
                        rfl

theorem cell23_4645380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 1, 3, 1, 2, 2].length) (baseStart_4645380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4645380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4645380 prefixEnd_4645380 := by exact prefixLift 4645380
  have htrace : WordTrace (prefixWord ++ tailWord_4645380) baseStart_4645380 baseEnd_4645380 := by
    simpa [prefixWord, tailWord_4645380, baseEnd_4645380] using wordTrace_append hprefix tailTrace_4645380
  have hstable : (prefixWord ++ tailWord_4645380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4645380).length < 2 ^ (prefixWord ++ tailWord_4645380).sum := by decide
  have hdescent : baseEnd_4645380 < baseStart_4645380 := by decide
  rcases family_descends (prefixWord ++ tailWord_4645380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4645396 : List Nat := [2, 4, 3, 1, 1, 1, 2, 1, 4, 1, 3]
def baseStart_4645396 : Nat := 118140960795 + 4645396 * 2 ^ 59
def prefixEnd_4645396 : Nat := 4983230072969 + 3 ^ 40 * 4645396 * 2
def baseEnd_4645396 : Nat := 2385320978473612100486219

theorem tailTrace_4645396 : CollatzResearch.WordTrace tailWord_4645396 prefixEnd_4645396 2385320978473612100486219 := by
  unfold tailWord_4645396
  simp only [CollatzResearch.WordTrace]
  refine ⟨84715755739265568659230021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112954340985687424878973361 84715755739265568659230021)
  ·
    refine ⟨15884204201112294123605629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84715755739265568659230021 15884204201112294123605629)
    ·
      refine ⟨5956576575417110296352111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15884204201112294123605629 5956576575417110296352111)
      ·
        refine ⟨8934864863125665444528167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5956576575417110296352111 8934864863125665444528167)
        ·
          refine ⟨13402297294688498166792251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8934864863125665444528167 13402297294688498166792251)
          ·
            refine ⟨20103445942032747250188377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13402297294688498166792251 20103445942032747250188377)
            ·
              refine ⟨15077584456524560437641283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20103445942032747250188377 15077584456524560437641283)
              ·
                refine ⟨22616376684786840656461925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15077584456524560437641283 22616376684786840656461925)
                ·
                  refine ⟨4240570628397532623086611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22616376684786840656461925 4240570628397532623086611)
                  ·
                    refine ⟨6360855942596298934629917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4240570628397532623086611 6360855942596298934629917)
                    ·
                      refine ⟨2385320978473612100486219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6360855942596298934629917 2385320978473612100486219)
                      ·
                        rfl

theorem cell23_4645396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_4645396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4645396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4645396 prefixEnd_4645396 := by exact prefixLift 4645396
  have htrace : WordTrace (prefixWord ++ tailWord_4645396) baseStart_4645396 baseEnd_4645396 := by
    simpa [prefixWord, tailWord_4645396, baseEnd_4645396] using wordTrace_append hprefix tailTrace_4645396
  have hstable : (prefixWord ++ tailWord_4645396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4645396).length < 2 ^ (prefixWord ++ tailWord_4645396).sum := by decide
  have hdescent : baseEnd_4645396 < baseStart_4645396 := by decide
  rcases family_descends (prefixWord ++ tailWord_4645396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4645425 : List Nat := [1, 2, 2, 3, 1, 1, 2, 4, 7]
def baseStart_4645425 : Nat := 118140960795 + 4645425 * 2 ^ 59
def prefixEnd_4645425 : Nat := 4983230072969 + 3 ^ 40 * 4645425 * 2
def baseEnd_4645425 : Nat := 265037318823621387447065

theorem tailTrace_4645425 : CollatzResearch.WordTrace tailWord_4645425 prefixEnd_4645425 265037318823621387447065 := by
  unfold tailWord_4645425
  simp only [CollatzResearch.WordTrace]
  refine ⟨169432569195426075271265729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112955046130284050180843819 169432569195426075271265729)
  ·
    refine ⟨127074426896569556453449297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169432569195426075271265729 127074426896569556453449297)
    ·
      refine ⟨95305820172427167340086973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127074426896569556453449297 95305820172427167340086973)
      ·
        refine ⟨35739682564660187752532615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95305820172427167340086973 35739682564660187752532615)
        ·
          refine ⟨53609523846990281628798923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35739682564660187752532615 53609523846990281628798923)
          ·
            refine ⟨80414285770485422443198385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53609523846990281628798923 80414285770485422443198385)
            ·
              refine ⟨60310714327864066832398789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80414285770485422443198385 60310714327864066832398789)
              ·
                refine ⟨11308258936474512531074773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60310714327864066832398789 11308258936474512531074773)
                ·
                  refine ⟨265037318823621387447065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11308258936474512531074773 265037318823621387447065)
                  ·
                    rfl

theorem cell23_4645425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 4, 7].length) (baseStart_4645425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4645425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4645425 prefixEnd_4645425 := by exact prefixLift 4645425
  have htrace : WordTrace (prefixWord ++ tailWord_4645425) baseStart_4645425 baseEnd_4645425 := by
    simpa [prefixWord, tailWord_4645425, baseEnd_4645425] using wordTrace_append hprefix tailTrace_4645425
  have hstable : (prefixWord ++ tailWord_4645425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4645425).length < 2 ^ (prefixWord ++ tailWord_4645425).sum := by decide
  have hdescent : baseEnd_4645425 < baseStart_4645425 := by decide
  rcases family_descends (prefixWord ++ tailWord_4645425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4645452 : List Nat := [2, 2, 1, 3, 1, 2, 2, 2, 2, 3, 3]
def baseStart_4645452 : Nat := 118140960795 + 4645452 * 2 ^ 59
def prefixEnd_4645452 : Nat := 4983230072969 + 3 ^ 40 * 4645452 * 2
def baseEnd_4645452 : Nat := 2385349733390263881385961

theorem tailTrace_4645452 : CollatzResearch.WordTrace tailWord_4645452 prefixEnd_4645452 2385349733390263881385961 := by
  unfold tailWord_4645452
  simp only [CollatzResearch.WordTrace]
  refine ⟨84716776983164129441249305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112955702644218839254999073 84716776983164129441249305)
  ·
    refine ⟨63537582737373097080936979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84716776983164129441249305 63537582737373097080936979)
    ·
      refine ⟨95306374106059645621405469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63537582737373097080936979 95306374106059645621405469)
      ·
        refine ⟨35739890289772367108027051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95306374106059645621405469 35739890289772367108027051)
        ·
          refine ⟨53609835434658550662040577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35739890289772367108027051 53609835434658550662040577)
          ·
            refine ⟨40207376575993912996530433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53609835434658550662040577 40207376575993912996530433)
            ·
              refine ⟨30155532431995434747397825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40207376575993912996530433 30155532431995434747397825)
              ·
                refine ⟨22616649323996576060548369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30155532431995434747397825 22616649323996576060548369)
                ·
                  refine ⟨16962486992997432045411277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22616649323996576060548369 16962486992997432045411277)
                  ·
                    refine ⟨6360932622374037017029229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16962486992997432045411277 6360932622374037017029229)
                    ·
                      refine ⟨2385349733390263881385961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6360932622374037017029229 2385349733390263881385961)
                      ·
                        rfl

theorem cell23_4645452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 2, 2, 3, 3].length) (baseStart_4645452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4645452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4645452 prefixEnd_4645452 := by exact prefixLift 4645452
  have htrace : WordTrace (prefixWord ++ tailWord_4645452) baseStart_4645452 baseEnd_4645452 := by
    simpa [prefixWord, tailWord_4645452, baseEnd_4645452] using wordTrace_append hprefix tailTrace_4645452
  have hstable : (prefixWord ++ tailWord_4645452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4645452).length < 2 ^ (prefixWord ++ tailWord_4645452).sum := by decide
  have hdescent : baseEnd_4645452 < baseStart_4645452 := by decide
  rcases family_descends (prefixWord ++ tailWord_4645452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4645453 : List Nat := [1, 6, 1, 1, 2, 1, 1, 4, 2, 2, 2]
def baseStart_4645453 : Nat := 118140960795 + 4645453 * 2 ^ 59
def prefixEnd_4645453 : Nat := 4983230072969 + 3 ^ 40 * 4645453 * 2
def baseEnd_4645453 : Nat := 2385350246870918377473457

theorem tailTrace_4645453 : CollatzResearch.WordTrace tailWord_4645453 prefixEnd_4645453 2385350246870918377473457 := by
  unfold tailWord_4645453
  simp only [CollatzResearch.WordTrace]
  refine ⟨169433590439324636053285013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112955726959549757368856675 169433590439324636053285013)
  ·
    refine ⟨7942199551843342314997735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 169433590439324636053285013 7942199551843342314997735)
    ·
      refine ⟨11913299327765013472496603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7942199551843342314997735 11913299327765013472496603)
      ·
        refine ⟨17869948991647520208744905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11913299327765013472496603 17869948991647520208744905)
        ·
          refine ⟨13402461743735640156558679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17869948991647520208744905 13402461743735640156558679)
          ·
            refine ⟨20103692615603460234838019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13402461743735640156558679 20103692615603460234838019)
            ·
              refine ⟨30155538923405190352257029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20103692615603460234838019 30155538923405190352257029)
              ·
                refine ⟨5654163548138473191048193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30155538923405190352257029 5654163548138473191048193)
                ·
                  refine ⟨4240622661103854893286145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5654163548138473191048193 4240622661103854893286145)
                  ·
                    refine ⟨3180466995827891169964609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4240622661103854893286145 3180466995827891169964609)
                    ·
                      refine ⟨2385350246870918377473457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3180466995827891169964609 2385350246870918377473457)
                      ·
                        rfl

theorem cell23_4645453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 4, 2, 2, 2].length) (baseStart_4645453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4645453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4645453 prefixEnd_4645453 := by exact prefixLift 4645453
  have htrace : WordTrace (prefixWord ++ tailWord_4645453) baseStart_4645453 baseEnd_4645453 := by
    simpa [prefixWord, tailWord_4645453, baseEnd_4645453] using wordTrace_append hprefix tailTrace_4645453
  have hstable : (prefixWord ++ tailWord_4645453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4645453).length < 2 ^ (prefixWord ++ tailWord_4645453).sum := by decide
  have hdescent : baseEnd_4645453 < baseStart_4645453 := by decide
  rcases family_descends (prefixWord ++ tailWord_4645453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4645509 : List Nat := [1, 3, 1, 1, 4, 2, 1, 2, 2, 4, 2]
def baseStart_4645509 : Nat := 118140960795 + 4645509 * 2 ^ 59
def prefixEnd_4645509 : Nat := 4983230072969 + 3 ^ 40 * 4645509 * 2
def baseEnd_4645509 : Nat := 2385379001787570158373199

theorem tailTrace_4645509 : CollatzResearch.WordTrace tailWord_4645509 prefixEnd_4645509 2385379001787570158373199 := by
  unfold tailWord_4645509
  simp only [CollatzResearch.WordTrace]
  refine ⟨169435632927121757617323581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112957088618081171744882387 169435632927121757617323581)
  ·
    refine ⟨63538362347670659106496343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 169435632927121757617323581 63538362347670659106496343)
    ·
      refine ⟨95307543521505988659744515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63538362347670659106496343 95307543521505988659744515)
      ·
        refine ⟨142961315282258982989616773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95307543521505988659744515 142961315282258982989616773)
        ·
          refine ⟨26805246615423559310553145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 142961315282258982989616773 26805246615423559310553145)
          ·
            refine ⟨20103934961567669482914859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26805246615423559310553145 20103934961567669482914859)
            ·
              refine ⟨30155902442351504224372289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20103934961567669482914859 30155902442351504224372289)
              ·
                refine ⟨22616926831763628168279217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30155902442351504224372289 22616926831763628168279217)
                ·
                  refine ⟨16962695123822721126209413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22616926831763628168279217 16962695123822721126209413)
                  ·
                    refine ⟨3180505335716760211164265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16962695123822721126209413 3180505335716760211164265)
                    ·
                      refine ⟨2385379001787570158373199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3180505335716760211164265 2385379001787570158373199)
                      ·
                        rfl

theorem cell23_4645509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 2, 2, 4, 2].length) (baseStart_4645509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4645509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4645509 prefixEnd_4645509 := by exact prefixLift 4645509
  have htrace : WordTrace (prefixWord ++ tailWord_4645509) baseStart_4645509 baseEnd_4645509 := by
    simpa [prefixWord, tailWord_4645509, baseEnd_4645509] using wordTrace_append hprefix tailTrace_4645509
  have hstable : (prefixWord ++ tailWord_4645509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4645509).length < 2 ^ (prefixWord ++ tailWord_4645509).sum := by decide
  have hdescent : baseEnd_4645509 < baseStart_4645509 := by decide
  rcases family_descends (prefixWord ++ tailWord_4645509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4645576 : List Nat := [2, 1, 3, 1, 2, 3, 3, 1, 3, 1, 3]
def baseStart_4645576 : Nat := 118140960795 + 4645576 * 2 ^ 59
def prefixEnd_4645576 : Nat := 4983230072969 + 3 ^ 40 * 4645576 * 2
def baseEnd_4645576 : Nat := 2385413404991421396235391

theorem tailTrace_4645576 : CollatzResearch.WordTrace tailWord_4645576 prefixEnd_4645576 2385413404991421396235391 := by
  unfold tailWord_4645576
  simp only [CollatzResearch.WordTrace]
  refine ⟨84719038308939514030006291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112958717745252685373341721 84719038308939514030006291)
  ·
    refine ⟨127078557463409271045009437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84719038308939514030006291 127078557463409271045009437)
    ·
      refine ⟨47654459048778476641878539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 127078557463409271045009437 47654459048778476641878539)
      ·
        refine ⟨71481688573167714962817809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47654459048778476641878539 71481688573167714962817809)
        ·
          refine ⟨53611266429875786222113357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71481688573167714962817809 53611266429875786222113357)
          ·
            refine ⟨20104224911203419833292509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53611266429875786222113357 20104224911203419833292509)
            ·
              refine ⟨7539084341701282437484691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20104224911203419833292509 7539084341701282437484691)
              ·
                refine ⟨11308626512551923656227037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7539084341701282437484691 11308626512551923656227037)
                ·
                  refine ⟨4240734942206971371085139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11308626512551923656227037 4240734942206971371085139)
                  ·
                    refine ⟨6361102413310457056627709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4240734942206971371085139 6361102413310457056627709)
                    ·
                      refine ⟨2385413404991421396235391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6361102413310457056627709 2385413404991421396235391)
                      ·
                        rfl

theorem cell23_4645576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 3, 1, 3, 1, 3].length) (baseStart_4645576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4645576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4645576 prefixEnd_4645576 := by exact prefixLift 4645576
  have htrace : WordTrace (prefixWord ++ tailWord_4645576) baseStart_4645576 baseEnd_4645576 := by
    simpa [prefixWord, tailWord_4645576, baseEnd_4645576] using wordTrace_append hprefix tailTrace_4645576
  have hstable : (prefixWord ++ tailWord_4645576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4645576).length < 2 ^ (prefixWord ++ tailWord_4645576).sum := by decide
  have hdescent : baseEnd_4645576 < baseStart_4645576 := by decide
  rcases family_descends (prefixWord ++ tailWord_4645576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4645596 : List Nat := [2, 2, 5, 1, 1, 2, 1, 1, 3, 5]
def baseStart_4645596 : Nat := 118140960795 + 4645596 * 2 ^ 59
def prefixEnd_4645596 : Nat := 4983230072969 + 3 ^ 40 * 4645596 * 2
def baseEnd_4645596 : Nat := 795141224868170439328433

theorem tailTrace_4645596 : CollatzResearch.WordTrace tailWord_4645596 prefixEnd_4645596 795141224868170439328433 := by
  unfold tailWord_4645596
  simp only [CollatzResearch.WordTrace]
  refine ⟨84719403038903285737870321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112959204051871047650493761 84719403038903285737870321)
  ·
    refine ⟨63539552279177464303402741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84719403038903285737870321 63539552279177464303402741)
    ·
      refine ⟨5956833026172887278444007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 63539552279177464303402741 5956833026172887278444007)
      ·
        refine ⟨8935249539259330917666011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5956833026172887278444007 8935249539259330917666011)
        ·
          refine ⟨13402874308888996376499017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8935249539259330917666011 13402874308888996376499017)
          ·
            refine ⟨10052155731666747282374263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13402874308888996376499017 10052155731666747282374263)
            ·
              refine ⟨15078233597500120923561395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10052155731666747282374263 15078233597500120923561395)
              ·
                refine ⟨22617350396250181385342093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15078233597500120923561395 22617350396250181385342093)
                ·
                  refine ⟨8481506398593818019503285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22617350396250181385342093 8481506398593818019503285)
                  ·
                    refine ⟨795141224868170439328433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8481506398593818019503285 795141224868170439328433)
                    ·
                      rfl

theorem cell23_4645596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_4645596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4645596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4645596 prefixEnd_4645596 := by exact prefixLift 4645596
  have htrace : WordTrace (prefixWord ++ tailWord_4645596) baseStart_4645596 baseEnd_4645596 := by
    simpa [prefixWord, tailWord_4645596, baseEnd_4645596] using wordTrace_append hprefix tailTrace_4645596
  have hstable : (prefixWord ++ tailWord_4645596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4645596).length < 2 ^ (prefixWord ++ tailWord_4645596).sum := by decide
  have hdescent : baseEnd_4645596 < baseStart_4645596 := by decide
  rcases family_descends (prefixWord ++ tailWord_4645596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4645599 : List Nat := [1, 1, 2, 3, 2, 4, 1, 1, 3, 1, 4]
def baseStart_4645599 : Nat := 118140960795 + 4645599 * 2 ^ 59
def prefixEnd_4645599 : Nat := 4983230072969 + 3 ^ 40 * 4645599 * 2
def baseEnd_4645599 : Nat := 2385425215046474806247785

theorem tailTrace_4645599 : CollatzResearch.WordTrace tailWord_4645599 prefixEnd_4645599 2385425215046474806247785 := by
  unfold tailWord_4645599
  simp only [CollatzResearch.WordTrace]
  refine ⟨169438915496795702988099851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112959276997863801992066567 169438915496795702988099851)
  ·
    refine ⟨254158373245193554482149777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169438915496795702988099851 254158373245193554482149777)
    ·
      refine ⟨190618779933895165861612333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 254158373245193554482149777 190618779933895165861612333)
      ·
        refine ⟨71482042475210687198104625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 190618779933895165861612333 71482042475210687198104625)
        ·
          refine ⟨53611531856408015398578469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71482042475210687198104625 53611531856408015398578469)
          ·
            refine ⟨10052162223076502887233463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53611531856408015398578469 10052162223076502887233463)
            ·
              refine ⟨15078243334614754330850195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10052162223076502887233463 15078243334614754330850195)
              ·
                refine ⟨22617365001922131496275293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15078243334614754330850195 22617365001922131496275293)
                ·
                  refine ⟨8481511875720799311103235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22617365001922131496275293 8481511875720799311103235)
                  ·
                    refine ⟨12722267813581198966654853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8481511875720799311103235 12722267813581198966654853)
                    ·
                      refine ⟨2385425215046474806247785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12722267813581198966654853 2385425215046474806247785)
                      ·
                        rfl

theorem cell23_4645599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 1, 3, 1, 4].length) (baseStart_4645599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4645599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4645599 prefixEnd_4645599 := by exact prefixLift 4645599
  have htrace : WordTrace (prefixWord ++ tailWord_4645599) baseStart_4645599 baseEnd_4645599 := by
    simpa [prefixWord, tailWord_4645599, baseEnd_4645599] using wordTrace_append hprefix tailTrace_4645599
  have hstable : (prefixWord ++ tailWord_4645599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4645599).length < 2 ^ (prefixWord ++ tailWord_4645599).sum := by decide
  have hdescent : baseEnd_4645599 < baseStart_4645599 := by decide
  rcases family_descends (prefixWord ++ tailWord_4645599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4645603 : List Nat := [1, 1, 1, 7, 1, 2, 2, 1, 2, 3, 2]
def baseStart_4645603 : Nat := 118140960795 + 4645603 * 2 ^ 59
def prefixEnd_4645603 : Nat := 4983230072969 + 3 ^ 40 * 4645603 * 2
def baseEnd_4645603 : Nat := 2385427268969092790597767

theorem tailTrace_4645603 : CollatzResearch.WordTrace tailWord_4645603 prefixEnd_4645603 2385427268969092790597767 := by
  unfold tailWord_4645603
  simp only [CollatzResearch.WordTrace]
  refine ⟨169439061388781211671245463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112959374259187474447496975 169439061388781211671245463)
  ·
    refine ⟨254158592083171817506868195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169439061388781211671245463 254158592083171817506868195)
    ·
      refine ⟨381237888124757726260302293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 254158592083171817506868195 381237888124757726260302293)
      ·
        refine ⟨8935263002924009209225835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 381237888124757726260302293 8935263002924009209225835)
        ·
          refine ⟨13402894504386013813838753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8935263002924009209225835 13402894504386013813838753)
          ·
            refine ⟨10052170878289510360379065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13402894504386013813838753 10052170878289510360379065)
            ·
              refine ⟨7539128158717132770284299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10052170878289510360379065 7539128158717132770284299)
              ·
                refine ⟨11308692238075699155426449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7539128158717132770284299 11308692238075699155426449)
                ·
                  refine ⟨8481519178556774366569837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11308692238075699155426449 8481519178556774366569837)
                  ·
                    refine ⟨3180569691958790387463689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8481519178556774366569837 3180569691958790387463689)
                    ·
                      refine ⟨2385427268969092790597767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3180569691958790387463689 2385427268969092790597767)
                      ·
                        rfl

theorem cell23_4645603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 2, 1, 2, 3, 2].length) (baseStart_4645603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4645603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4645603 prefixEnd_4645603 := by exact prefixLift 4645603
  have htrace : WordTrace (prefixWord ++ tailWord_4645603) baseStart_4645603 baseEnd_4645603 := by
    simpa [prefixWord, tailWord_4645603, baseEnd_4645603] using wordTrace_append hprefix tailTrace_4645603
  have hstable : (prefixWord ++ tailWord_4645603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4645603).length < 2 ^ (prefixWord ++ tailWord_4645603).sum := by decide
  have hdescent : baseEnd_4645603 < baseStart_4645603 := by decide
  rcases family_descends (prefixWord ++ tailWord_4645603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4645616 : List Nat := [2, 1, 1, 1, 3, 1, 7, 1, 1, 1, 4]
def baseStart_4645616 : Nat := 118140960795 + 4645616 * 2 ^ 59
def prefixEnd_4645616 : Nat := 4983230072969 + 3 ^ 40 * 4645616 * 2
def baseEnd_4645616 : Nat := 2385433944217601239735207

theorem tailTrace_4645616 : CollatzResearch.WordTrace tailWord_4645616 prefixEnd_4645616 2385433944217601239735207 := by
  unfold tailWord_4645616
  simp only [CollatzResearch.WordTrace]
  refine ⟨84719767768867057445734351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112959690358489409927645801 84719767768867057445734351)
  ·
    refine ⟨127079651653300586168601527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84719767768867057445734351 127079651653300586168601527)
    ·
      refine ⟨190619477479950879252902291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127079651653300586168601527 190619477479950879252902291)
      ·
        refine ⟨285929216219926318879353437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190619477479950879252902291 285929216219926318879353437)
        ·
          refine ⟨107223456082472369579757539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 285929216219926318879353437 107223456082472369579757539)
          ·
            refine ⟨160835184123708554369636309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107223456082472369579757539 160835184123708554369636309)
            ·
              refine ⟨3769574627899419243038351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 160835184123708554369636309 3769574627899419243038351)
              ·
                refine ⟨5654361941849128864557527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3769574627899419243038351 5654361941849128864557527)
                ·
                  refine ⟨8481542912773693296836291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5654361941849128864557527 8481542912773693296836291)
                  ·
                    refine ⟨12722314369160539945254437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8481542912773693296836291 12722314369160539945254437)
                    ·
                      refine ⟨2385433944217601239735207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12722314369160539945254437 2385433944217601239735207)
                      ·
                        rfl

theorem cell23_4645616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 7, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 7, 1, 1, 1, 4].length) (baseStart_4645616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4645616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4645616 prefixEnd_4645616 := by exact prefixLift 4645616
  have htrace : WordTrace (prefixWord ++ tailWord_4645616) baseStart_4645616 baseEnd_4645616 := by
    simpa [prefixWord, tailWord_4645616, baseEnd_4645616] using wordTrace_append hprefix tailTrace_4645616
  have hstable : (prefixWord ++ tailWord_4645616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4645616).length < 2 ^ (prefixWord ++ tailWord_4645616).sum := by decide
  have hdescent : baseEnd_4645616 < baseStart_4645616 := by decide
  rcases family_descends (prefixWord ++ tailWord_4645616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4645621 : List Nat := [1, 3, 6, 1, 2, 1, 2, 2, 1, 4]
def baseStart_4645621 : Nat := 118140960795 + 4645621 * 2 ^ 59
def prefixEnd_4645621 : Nat := 4983230072969 + 3 ^ 40 * 4645621 * 2
def baseEnd_4645621 : Nat := 795145503873624573390895

theorem tailTrace_4645621 : CollatzResearch.WordTrace tailWord_4645621 prefixEnd_4645621 795145503873624573390895 := by
  unfold tailWord_4645621
  simp only [CollatzResearch.WordTrace]
  refine ⟨169439717902716000745400717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112959811935144000496933811 169439717902716000745400717)
  ·
    refine ⟨63539894213518500279525269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 169439717902716000745400717 63539894213518500279525269)
    ·
      refine ⟨2978432541258679700602747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 63539894213518500279525269 2978432541258679700602747)
      ·
        refine ⟨4467648811888019550904121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2978432541258679700602747 4467648811888019550904121)
        ·
          refine ⟨3350736608916014663178091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4467648811888019550904121 3350736608916014663178091)
          ·
            refine ⟨5026104913374021994767137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3350736608916014663178091 5026104913374021994767137)
            ·
              refine ⟨3769578685030516496075353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5026104913374021994767137 3769578685030516496075353)
              ·
                refine ⟨2827184013772887372056515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3769578685030516496075353 2827184013772887372056515)
                ·
                  refine ⟨4240776020659331058084773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2827184013772887372056515 4240776020659331058084773)
                  ·
                    refine ⟨795145503873624573390895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4240776020659331058084773 795145503873624573390895)
                    ·
                      rfl

theorem cell23_4645621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_4645621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4645621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4645621 prefixEnd_4645621 := by exact prefixLift 4645621
  have htrace : WordTrace (prefixWord ++ tailWord_4645621) baseStart_4645621 baseEnd_4645621 := by
    simpa [prefixWord, tailWord_4645621, baseEnd_4645621] using wordTrace_append hprefix tailTrace_4645621
  have hstable : (prefixWord ++ tailWord_4645621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4645621).length < 2 ^ (prefixWord ++ tailWord_4645621).sum := by decide
  have hdescent : baseEnd_4645621 < baseStart_4645621 := by decide
  rcases family_descends (prefixWord ++ tailWord_4645621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4645639 : List Nat := [1, 1, 4, 4, 1, 1, 3, 8]
def baseStart_4645639 : Nat := 118140960795 + 4645639 * 2 ^ 59
def prefixEnd_4645639 : Nat := 4983230072969 + 3 ^ 40 * 4645639 * 2
def baseEnd_4645639 : Nat := 88349842750839061101763

theorem tailTrace_4645639 : CollatzResearch.WordTrace tailWord_4645639 prefixEnd_4645639 88349842750839061101763 := by
  unfold tailWord_4645639
  simp only [CollatzResearch.WordTrace]
  refine ⟨169440374416650789819555971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112960249611100526546370647 169440374416650789819555971)
  ·
    refine ⟨254160561624976184729333957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169440374416650789819555971 254160561624976184729333957)
    ·
      refine ⟨47655105304683034636750117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 254160561624976184729333957 47655105304683034636750117)
      ·
        refine ⟨8935332244628068994390647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47655105304683034636750117 8935332244628068994390647)
        ·
          refine ⟨13402998366942103491585971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8935332244628068994390647 13402998366942103491585971)
          ·
            refine ⟨20104497550413155237378957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13402998366942103491585971 20104497550413155237378957)
            ·
              refine ⟨7539186581404933214017109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20104497550413155237378957 7539186581404933214017109)
              ·
                refine ⟨88349842750839061101763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7539186581404933214017109 88349842750839061101763)
                ·
                  rfl

theorem cell23_4645639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 3, 8].length) (baseStart_4645639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4645639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4645639 prefixEnd_4645639 := by exact prefixLift 4645639
  have htrace : WordTrace (prefixWord ++ tailWord_4645639) baseStart_4645639 baseEnd_4645639 := by
    simpa [prefixWord, tailWord_4645639, baseEnd_4645639] using wordTrace_append hprefix tailTrace_4645639
  have hstable : (prefixWord ++ tailWord_4645639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4645639).length < 2 ^ (prefixWord ++ tailWord_4645639).sum := by decide
  have hdescent : baseEnd_4645639 < baseStart_4645639 := by decide
  rcases family_descends (prefixWord ++ tailWord_4645639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4645649 : List Nat := [1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 3]
def baseStart_4645649 : Nat := 118140960795 + 4645649 * 2 ^ 59
def prefixEnd_4645649 : Nat := 4983230072969 + 3 ^ 40 * 4645649 * 2
def baseEnd_4645649 : Nat := 2385450889079199610622555

theorem tailTrace_4645649 : CollatzResearch.WordTrace tailWord_4645649 prefixEnd_4645649 2385450889079199610622555 := by
  unfold tailWord_4645649
  simp only [CollatzResearch.WordTrace]
  refine ⟨169440739146614561527420001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112960492764409707684946667 169440739146614561527420001)
  ·
    refine ⟨127080554359960921145565001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169440739146614561527420001 127080554359960921145565001)
    ·
      refine ⟨95310415769970690859173751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127080554359960921145565001 95310415769970690859173751)
      ·
        refine ⟨142965623654956036288760627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95310415769970690859173751 142965623654956036288760627)
        ·
          refine ⟨214448435482434054433140941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142965623654956036288760627 214448435482434054433140941)
          ·
            refine ⟨80418163305912770412427853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 214448435482434054433140941 80418163305912770412427853)
            ·
              refine ⟨30156811239717288904660445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80418163305912770412427853 30156811239717288904660445)
              ·
                refine ⟨11308804214893983339247667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30156811239717288904660445 11308804214893983339247667)
                ·
                  refine ⟨16963206322340975008871501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11308804214893983339247667 16963206322340975008871501)
                  ·
                    refine ⟨6361202370877865628326813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16963206322340975008871501 6361202370877865628326813)
                    ·
                      refine ⟨2385450889079199610622555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6361202370877865628326813 2385450889079199610622555)
                      ·
                        rfl

theorem cell23_4645649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 3].length) (baseStart_4645649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4645649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4645649 prefixEnd_4645649 := by exact prefixLift 4645649
  have htrace : WordTrace (prefixWord ++ tailWord_4645649) baseStart_4645649 baseEnd_4645649 := by
    simpa [prefixWord, tailWord_4645649, baseEnd_4645649] using wordTrace_append hprefix tailTrace_4645649
  have hstable : (prefixWord ++ tailWord_4645649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4645649).length < 2 ^ (prefixWord ++ tailWord_4645649).sum := by decide
  have hdescent : baseEnd_4645649 < baseStart_4645649 := by decide
  rcases family_descends (prefixWord ++ tailWord_4645649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4645666 : List Nat := [3, 3, 1, 1, 2, 2, 2, 2, 1, 3, 3]
def baseStart_4645666 : Nat := 118140960795 + 4645666 * 2 ^ 59
def prefixEnd_4645666 : Nat := 4983230072969 + 3 ^ 40 * 4645666 * 2
def baseEnd_4645666 : Nat := 2385459618250326044109977

theorem tailTrace_4645666 : CollatzResearch.WordTrace tailWord_4645666 prefixEnd_4645666 2385459618250326044109977 := by
  unfold tailWord_4645666
  simp only [CollatzResearch.WordTrace]
  refine ⟨42360339796888243357697213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112960906125035315620525901 42360339796888243357697213)
  ·
    refine ⟨15885127423833091259136455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42360339796888243357697213 15885127423833091259136455)
    ·
      refine ⟨23827691135749636888704683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15885127423833091259136455 23827691135749636888704683)
      ·
        refine ⟨35741536703624455333057025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23827691135749636888704683 35741536703624455333057025)
        ·
          refine ⟨26806152527718341499792769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35741536703624455333057025 26806152527718341499792769)
          ·
            refine ⟨20104614395788756124844577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26806152527718341499792769 20104614395788756124844577)
            ·
              refine ⟨15078460796841567093633433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20104614395788756124844577 15078460796841567093633433)
              ·
                refine ⟨11308845597631175320225075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15078460796841567093633433 11308845597631175320225075)
                ·
                  refine ⟨16963268396446762980337613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11308845597631175320225075 16963268396446762980337613)
                  ·
                    refine ⟨6361225648667536117626605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16963268396446762980337613 6361225648667536117626605)
                    ·
                      refine ⟨2385459618250326044109977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6361225648667536117626605 2385459618250326044109977)
                      ·
                        rfl

theorem cell23_4645666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 2, 1, 3, 3].length) (baseStart_4645666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4645666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4645666 prefixEnd_4645666 := by exact prefixLift 4645666
  have htrace : WordTrace (prefixWord ++ tailWord_4645666) baseStart_4645666 baseEnd_4645666 := by
    simpa [prefixWord, tailWord_4645666, baseEnd_4645666] using wordTrace_append hprefix tailTrace_4645666
  have hstable : (prefixWord ++ tailWord_4645666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4645666).length < 2 ^ (prefixWord ++ tailWord_4645666).sum := by decide
  have hdescent : baseEnd_4645666 < baseStart_4645666 := by decide
  rcases family_descends (prefixWord ++ tailWord_4645666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4645677 : List Nat := [1, 5, 3, 2, 1, 2, 1, 2, 2, 4]
def baseStart_4645677 : Nat := 118140960795 + 4645677 * 2 ^ 59
def prefixEnd_4645677 : Nat := 4983230072969 + 3 ^ 40 * 4645677 * 2
def baseEnd_4645677 : Nat := 795155088845841833690809

theorem tailTrace_4645677 : CollatzResearch.WordTrace tailWord_4645677 prefixEnd_4645677 795155088845841833690809 := by
  unfold tailWord_4645677
  simp only [CollatzResearch.WordTrace]
  refine ⟨169441760390513122309439285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112961173593675414872959523 169441760390513122309439285)
  ·
    refine ⟨15885165036610605216509933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 169441760390513122309439285 15885165036610605216509933)
    ·
      refine ⟨5956936888728976956191225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15885165036610605216509933 5956936888728976956191225)
      ·
        refine ⟨4467702666546732717143419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5956936888728976956191225 4467702666546732717143419)
        ·
          refine ⟨6701553999820099075715129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4467702666546732717143419 6701553999820099075715129)
          ·
            refine ⟨5026165499865074306786347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6701553999820099075715129 5026165499865074306786347)
            ·
              refine ⟨7539248249797611460179521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5026165499865074306786347 7539248249797611460179521)
              ·
                refine ⟨5654436187348208595134641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7539248249797611460179521 5654436187348208595134641)
                ·
                  refine ⟨4240827140511156446350981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5654436187348208595134641 4240827140511156446350981)
                  ·
                    refine ⟨795155088845841833690809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4240827140511156446350981 795155088845841833690809)
                    ·
                      rfl

theorem cell23_4645677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_4645677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4645677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4645677 prefixEnd_4645677 := by exact prefixLift 4645677
  have htrace : WordTrace (prefixWord ++ tailWord_4645677) baseStart_4645677 baseEnd_4645677 := by
    simpa [prefixWord, tailWord_4645677, baseEnd_4645677] using wordTrace_append hprefix tailTrace_4645677
  have hstable : (prefixWord ++ tailWord_4645677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4645677).length < 2 ^ (prefixWord ++ tailWord_4645677).sum := by decide
  have hdescent : baseEnd_4645677 < baseStart_4645677 := by decide
  rcases family_descends (prefixWord ++ tailWord_4645677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4645683 : List Nat := [1, 1, 1, 2, 6, 1, 3, 2, 2, 1, 3]
def baseStart_4645683 : Nat := 118140960795 + 4645683 * 2 ^ 59
def prefixEnd_4645683 : Nat := 4983230072969 + 3 ^ 40 * 4645683 * 2
def baseEnd_4645683 : Nat := 2385468347421452477597399

theorem tailTrace_4645683 : CollatzResearch.WordTrace tailWord_4645683 prefixEnd_4645683 2385468347421452477597399 := by
  unfold tailWord_4645683
  simp only [CollatzResearch.WordTrace]
  refine ⟨169441979228491385334157703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112961319485660923556105135 169441979228491385334157703)
  ·
    refine ⟨254162968842737078001236555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169441979228491385334157703 254162968842737078001236555)
    ·
      refine ⟨381244453264105617001854833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 254162968842737078001236555 381244453264105617001854833)
      ·
        refine ⟨285933339948079212751391125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 381244453264105617001854833 285933339948079212751391125)
        ·
          refine ⟨13403125310066213097721459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 285933339948079212751391125 13403125310066213097721459)
          ·
            refine ⟨20104687965099319646582189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13403125310066213097721459 20104687965099319646582189)
            ·
              refine ⟨7539257986912244867468321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20104687965099319646582189 7539257986912244867468321)
              ·
                refine ⟨5654443490184183650601241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7539257986912244867468321 5654443490184183650601241)
                ·
                  refine ⟨4240832617638137737950931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5654443490184183650601241 4240832617638137737950931)
                  ·
                    refine ⟨6361248926457206606926397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4240832617638137737950931 6361248926457206606926397)
                    ·
                      refine ⟨2385468347421452477597399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6361248926457206606926397 2385468347421452477597399)
                      ·
                        rfl

theorem cell23_4645683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 3, 2, 2, 1, 3].length) (baseStart_4645683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4645683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4645683 prefixEnd_4645683 := by exact prefixLift 4645683
  have htrace : WordTrace (prefixWord ++ tailWord_4645683) baseStart_4645683 baseEnd_4645683 := by
    simpa [prefixWord, tailWord_4645683, baseEnd_4645683] using wordTrace_append hprefix tailTrace_4645683
  have hstable : (prefixWord ++ tailWord_4645683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4645683).length < 2 ^ (prefixWord ++ tailWord_4645683).sum := by decide
  have hdescent : baseEnd_4645683 < baseStart_4645683 := by decide
  rcases family_descends (prefixWord ++ tailWord_4645683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4645706 : List Nat := [3, 1, 2, 1, 1, 1, 2, 5, 1, 4, 2]
def baseStart_4645706 : Nat := 118140960795 + 4645706 * 2 ^ 59
def prefixEnd_4645706 : Nat := 4983230072969 + 3 ^ 40 * 4645706 * 2
def baseEnd_4645706 : Nat := 2385480157476505887609793

theorem tailTrace_4645706 : CollatzResearch.WordTrace tailWord_4645706 prefixEnd_4645706 2385480157476505887609793 := by
  unfold tailWord_4645706
  simp only [CollatzResearch.WordTrace]
  refine ⟨42360704526852015065561243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112961878738272040174829981 42360704526852015065561243)
  ·
    refine ⟨63541056790278022598341865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42360704526852015065561243 63541056790278022598341865)
    ·
      refine ⟨47655792592708516948756399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63541056790278022598341865 47655792592708516948756399)
      ·
        refine ⟨71483688889062775423134599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47655792592708516948756399 71483688889062775423134599)
        ·
          refine ⟨107225533333594163134701899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71483688889062775423134599 107225533333594163134701899)
          ·
            refine ⟨160838300000391244702052849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107225533333594163134701899 160838300000391244702052849)
            ·
              refine ⟨120628725000293433526539637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 160838300000391244702052849 120628725000293433526539637)
              ·
                refine ⟨11308942968777509393113091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 120628725000293433526539637 11308942968777509393113091)
                ·
                  refine ⟨16963414453166264089669637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11308942968777509393113091 16963414453166264089669637)
                  ·
                    refine ⟨3180640209968674516813057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16963414453166264089669637 3180640209968674516813057)
                    ·
                      refine ⟨2385480157476505887609793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3180640209968674516813057 2385480157476505887609793)
                      ·
                        rfl

theorem cell23_4645706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 5, 1, 4, 2].length) (baseStart_4645706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4645706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4645706 prefixEnd_4645706 := by exact prefixLift 4645706
  have htrace : WordTrace (prefixWord ++ tailWord_4645706) baseStart_4645706 baseEnd_4645706 := by
    simpa [prefixWord, tailWord_4645706, baseEnd_4645706] using wordTrace_append hprefix tailTrace_4645706
  have hstable : (prefixWord ++ tailWord_4645706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4645706).length < 2 ^ (prefixWord ++ tailWord_4645706).sum := by decide
  have hdescent : baseEnd_4645706 < baseStart_4645706 := by decide
  rcases family_descends (prefixWord ++ tailWord_4645706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4645739 : List Nat := [1, 1, 1, 1, 2, 2, 4, 1, 4, 3, 3]
def baseStart_4645739 : Nat := 118140960795 + 4645739 * 2 ^ 59
def prefixEnd_4645739 : Nat := 4983230072969 + 3 ^ 40 * 4645739 * 2
def baseEnd_4645739 : Nat := 2385497102338104258497141

theorem tailTrace_4645739 : CollatzResearch.WordTrace tailWord_4645739 prefixEnd_4645739 2385497102338104258497141 := by
  unfold tailWord_4645739
  simp only [CollatzResearch.WordTrace]
  refine ⟨169444021716288506898196271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112962681144192337932130847 169444021716288506898196271)
  ·
    refine ⟨254166032574432760347294407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169444021716288506898196271 254166032574432760347294407)
    ·
      refine ⟨381249048861649140520941611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 254166032574432760347294407 381249048861649140520941611)
      ·
        refine ⟨571873573292473710781412417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 381249048861649140520941611 571873573292473710781412417)
        ·
          refine ⟨428905179969355283086059313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 571873573292473710781412417 428905179969355283086059313)
          ·
            refine ⟨321678884977016462314544485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 428905179969355283086059313 321678884977016462314544485)
            ·
              refine ⟨60314790933190586683977091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 321678884977016462314544485 60314790933190586683977091)
              ·
                refine ⟨90472186399785880025965637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60314790933190586683977091 90472186399785880025965637)
                ·
                  refine ⟨16963534949959852504868557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 90472186399785880025965637 16963534949959852504868557)
                  ·
                    refine ⟨6361325606234944689325709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16963534949959852504868557 6361325606234944689325709)
                    ·
                      refine ⟨2385497102338104258497141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6361325606234944689325709 2385497102338104258497141)
                      ·
                        rfl

theorem cell23_4645739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 4, 3, 3].length) (baseStart_4645739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4645739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4645739 prefixEnd_4645739 := by exact prefixLift 4645739
  have htrace : WordTrace (prefixWord ++ tailWord_4645739) baseStart_4645739 baseEnd_4645739 := by
    simpa [prefixWord, tailWord_4645739, baseEnd_4645739] using wordTrace_append hprefix tailTrace_4645739
  have hstable : (prefixWord ++ tailWord_4645739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4645739).length < 2 ^ (prefixWord ++ tailWord_4645739).sum := by decide
  have hdescent : baseEnd_4645739 < baseStart_4645739 := by decide
  rcases family_descends (prefixWord ++ tailWord_4645739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4645746 : List Nat := [3, 2, 1, 2, 1, 1, 2, 6, 5]
def baseStart_4645746 : Nat := 118140960795 + 4645746 * 2 ^ 59
def prefixEnd_4645746 : Nat := 4983230072969 + 3 ^ 40 * 4645746 * 2
def baseEnd_4645746 : Nat := 265055632966965081234401

theorem tailTrace_4645746 : CollatzResearch.WordTrace tailWord_4645746 prefixEnd_4645746 265055632966965081234401 := by
  unfold tailWord_4645746
  simp only [CollatzResearch.WordTrace]
  refine ⟨42361069256815786773425273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112962851351508764729134061 42361069256815786773425273)
  ·
    refine ⟨31770801942611840080068955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42361069256815786773425273 31770801942611840080068955)
    ·
      refine ⟨47656202913917760120103433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31770801942611840080068955 47656202913917760120103433)
      ·
        refine ⟨35742152185438320090077575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47656202913917760120103433 35742152185438320090077575)
        ·
          refine ⟨53613228278157480135116363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35742152185438320090077575 53613228278157480135116363)
          ·
            refine ⟨80419842417236220202674545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53613228278157480135116363 80419842417236220202674545)
            ·
              refine ⟨60314881812927165152005909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80419842417236220202674545 60314881812927165152005909)
              ·
                refine ⟨2827260084980960866500277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 60314881812927165152005909 2827260084980960866500277)
                ·
                  refine ⟨265055632966965081234401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2827260084980960866500277 265055632966965081234401)
                  ·
                    rfl

theorem cell23_4645746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 6, 5].length) (baseStart_4645746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4645746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4645746 prefixEnd_4645746 := by exact prefixLift 4645746
  have htrace : WordTrace (prefixWord ++ tailWord_4645746) baseStart_4645746 baseEnd_4645746 := by
    simpa [prefixWord, tailWord_4645746, baseEnd_4645746] using wordTrace_append hprefix tailTrace_4645746
  have hstable : (prefixWord ++ tailWord_4645746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4645746).length < 2 ^ (prefixWord ++ tailWord_4645746).sum := by decide
  have hdescent : baseEnd_4645746 < baseStart_4645746 := by decide
  rcases family_descends (prefixWord ++ tailWord_4645746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4645796 : List Nat := [2, 3, 1, 2, 1, 2, 1, 4, 2, 1, 4]
def baseStart_4645796 : Nat := 118140960795 + 4645796 * 2 ^ 59
def prefixEnd_4645796 : Nat := 4983230072969 + 3 ^ 40 * 4645796 * 2
def baseEnd_4645796 : Nat := 2385526370735410535484379

theorem tailTrace_4645796 : CollatzResearch.WordTrace tailWord_4645796 prefixEnd_4645796 2385526370735410535484379 := by
  unfold tailWord_4645796
  simp only [CollatzResearch.WordTrace]
  refine ⟨84723050338541002816510621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112964067118054670422014161 84723050338541002816510621)
  ·
    refine ⟨31771143876952876056191483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84723050338541002816510621 31771143876952876056191483)
    ·
      refine ⟨47656715815429314084287225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31771143876952876056191483 47656715815429314084287225)
      ·
        refine ⟨35742536861571985563215419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47656715815429314084287225 35742536861571985563215419)
        ·
          refine ⟨53613805292357978344823129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35742536861571985563215419 53613805292357978344823129)
          ·
            refine ⟨40210353969268483758617347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53613805292357978344823129 40210353969268483758617347)
            ·
              refine ⟨60315530953902725637926021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40210353969268483758617347 60315530953902725637926021)
              ·
                refine ⟨11309162053856761057111129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60315530953902725637926021 11309162053856761057111129)
                ·
                  refine ⟨8481871540392570792833347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11309162053856761057111129 8481871540392570792833347)
                  ·
                    refine ⟨12722807310588856189250021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8481871540392570792833347 12722807310588856189250021)
                    ·
                      refine ⟨2385526370735410535484379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12722807310588856189250021 2385526370735410535484379)
                      ·
                        rfl

theorem cell23_4645796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 4, 2, 1, 4].length) (baseStart_4645796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4645796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4645796 prefixEnd_4645796 := by exact prefixLift 4645796
  have htrace : WordTrace (prefixWord ++ tailWord_4645796) baseStart_4645796 baseEnd_4645796 := by
    simpa [prefixWord, tailWord_4645796, baseEnd_4645796] using wordTrace_append hprefix tailTrace_4645796
  have hstable : (prefixWord ++ tailWord_4645796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4645796).length < 2 ^ (prefixWord ++ tailWord_4645796).sum := by decide
  have hdescent : baseEnd_4645796 < baseStart_4645796 := by decide
  rcases family_descends (prefixWord ++ tailWord_4645796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4645813 : List Nat := [1, 3, 3, 2, 1, 1, 3, 1, 2, 4, 2]
def baseStart_4645813 : Nat := 118140960795 + 4645813 * 2 ^ 59
def prefixEnd_4645813 : Nat := 4983230072969 + 3 ^ 40 * 4645813 * 2
def baseEnd_4645813 : Nat := 2385535099906536968971801

theorem tailTrace_4645813 : CollatzResearch.WordTrace tailWord_4645813 prefixEnd_4645813 2385535099906536968971801 := by
  unfold tailWord_4645813
  simp only [CollatzResearch.WordTrace]
  refine ⟨169446720718020417536390093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112964480478680278357593395 169446720718020417536390093)
  ·
    refine ⟨63542520269257656576146285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 169446720718020417536390093 63542520269257656576146285)
    ·
      refine ⟨23828445100971621216054857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63542520269257656576146285 23828445100971621216054857)
      ·
        refine ⟨17871333825728715912041143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23828445100971621216054857 17871333825728715912041143)
        ·
          refine ⟨26807000738593073868061715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17871333825728715912041143 26807000738593073868061715)
          ·
            refine ⟨40210501107889610802092573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26807000738593073868061715 40210501107889610802092573)
            ·
              refine ⟨15078937915458604050784715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40210501107889610802092573 15078937915458604050784715)
              ·
                refine ⟨22618406873187906076177073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15078937915458604050784715 22618406873187906076177073)
                ·
                  refine ⟨16963805154890929557132805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22618406873187906076177073 16963805154890929557132805)
                  ·
                    refine ⟨3180713466542049291962401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16963805154890929557132805 3180713466542049291962401)
                    ·
                      refine ⟨2385535099906536968971801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3180713466542049291962401 2385535099906536968971801)
                      ·
                        rfl

theorem cell23_4645813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 1, 2, 4, 2].length) (baseStart_4645813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4645813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4645813 prefixEnd_4645813 := by exact prefixLift 4645813
  have htrace : WordTrace (prefixWord ++ tailWord_4645813) baseStart_4645813 baseEnd_4645813 := by
    simpa [prefixWord, tailWord_4645813, baseEnd_4645813] using wordTrace_append hprefix tailTrace_4645813
  have hstable : (prefixWord ++ tailWord_4645813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4645813).length < 2 ^ (prefixWord ++ tailWord_4645813).sum := by decide
  have hdescent : baseEnd_4645813 < baseStart_4645813 := by decide
  rcases family_descends (prefixWord ++ tailWord_4645813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4645853 : List Nat := [1, 4, 3, 1, 2, 1, 3, 2, 6]
def baseStart_4645853 : Nat := 118140960795 + 4645853 * 2 ^ 59
def prefixEnd_4645853 : Nat := 4983230072969 + 3 ^ 40 * 4645853 * 2
def baseEnd_4645853 : Nat := 265061737681412979163513

theorem tailTrace_4645853 : CollatzResearch.WordTrace tailWord_4645853 prefixEnd_4645853 265061737681412979163513 := by
  unfold tailWord_4645853
  simp only [CollatzResearch.WordTrace]
  refine ⟨169448179637875504367846213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112965453091917002911897475 169448179637875504367846213)
  ·
    refine ⟨31771533682101657068971165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 169448179637875504367846213 31771533682101657068971165)
    ·
      refine ⟨11914325130788121400864187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31771533682101657068971165 11914325130788121400864187)
      ·
        refine ⟨17871487696182182101296281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11914325130788121400864187 17871487696182182101296281)
        ·
          refine ⟨13403615772136636575972211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17871487696182182101296281 13403615772136636575972211)
          ·
            refine ⟨20105423658204954863958317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13403615772136636575972211 20105423658204954863958317)
            ·
              refine ⟨7539533871826858073984369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20105423658204954863958317 7539533871826858073984369)
              ·
                refine ⟨5654650403870143555488277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7539533871826858073984369 5654650403870143555488277)
                ·
                  refine ⟨265061737681412979163513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5654650403870143555488277 265061737681412979163513)
                  ·
                    rfl

theorem cell23_4645853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 3, 2, 6].length) (baseStart_4645853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4645853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4645853 prefixEnd_4645853 := by exact prefixLift 4645853
  have htrace : WordTrace (prefixWord ++ tailWord_4645853) baseStart_4645853 baseEnd_4645853 := by
    simpa [prefixWord, tailWord_4645853, baseEnd_4645853] using wordTrace_append hprefix tailTrace_4645853
  have hstable : (prefixWord ++ tailWord_4645853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4645853).length < 2 ^ (prefixWord ++ tailWord_4645853).sum := by decide
  have hdescent : baseEnd_4645853 < baseStart_4645853 := by decide
  rcases family_descends (prefixWord ++ tailWord_4645853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4645870 : List Nat := [4, 1, 2, 1, 4, 1, 3, 1, 6]
def baseStart_4645870 : Nat := 118140960795 + 4645870 * 2 ^ 59
def prefixEnd_4645870 : Nat := 4983230072969 + 3 ^ 40 * 4645870 * 2
def baseEnd_4645870 : Nat := 265062707589315916217671

theorem tailTrace_4645870 : CollatzResearch.WordTrace tailWord_4645870 prefixEnd_4645870 265062707589315916217671 := by
  unfold tailWord_4645870
  simp only [CollatzResearch.WordTrace]
  refine ⟨21181099959851739533901883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112965866452542610847476709 21181099959851739533901883)
  ·
    refine ⟨31771649939777609300852825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21181099959851739533901883 31771649939777609300852825)
    ·
      refine ⟨23828737454833206975639619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31771649939777609300852825 23828737454833206975639619)
      ·
        refine ⟨35743106182249810463459429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23828737454833206975639619 35743106182249810463459429)
        ·
          refine ⟨6701832409171839461898643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35743106182249810463459429 6701832409171839461898643)
          ·
            refine ⟨10052748613757759192847965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6701832409171839461898643 10052748613757759192847965)
            ·
              refine ⟨3769780730159159697317987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10052748613757759192847965 3769780730159159697317987)
              ·
                refine ⟨5654671095238739545976981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3769780730159159697317987 5654671095238739545976981)
                ·
                  refine ⟨265062707589315916217671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5654671095238739545976981 265062707589315916217671)
                  ·
                    rfl

theorem cell23_4645870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 3, 1, 6].length) (baseStart_4645870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4645870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4645870 prefixEnd_4645870 := by exact prefixLift 4645870
  have htrace : WordTrace (prefixWord ++ tailWord_4645870) baseStart_4645870 baseEnd_4645870 := by
    simpa [prefixWord, tailWord_4645870, baseEnd_4645870] using wordTrace_append hprefix tailTrace_4645870
  have hstable : (prefixWord ++ tailWord_4645870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4645870).length < 2 ^ (prefixWord ++ tailWord_4645870).sum := by decide
  have hdescent : baseEnd_4645870 < baseStart_4645870 := by decide
  rcases family_descends (prefixWord ++ tailWord_4645870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4645873 : List Nat := [1, 2, 2, 2, 4, 1, 1, 2, 1, 5, 2]
def baseStart_4645873 : Nat := 118140960795 + 4645873 * 2 ^ 59
def prefixEnd_4645873 : Nat := 4983230072969 + 3 ^ 40 * 4645873 * 2
def baseEnd_4645873 : Nat := 2385565908745806734221525

theorem tailTrace_4645873 : CollatzResearch.WordTrace tailWord_4645873 prefixEnd_4645873 2385565908745806734221525 := by
  unfold tailWord_4645873
  simp only [CollatzResearch.WordTrace]
  refine ⟨169448909097803047783574273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112965939398535365189049515 169448909097803047783574273)
  ·
    refine ⟨127086681823352285837680705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169448909097803047783574273 127086681823352285837680705)
    ·
      refine ⟨95315011367514214378260529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127086681823352285837680705 95315011367514214378260529)
      ·
        refine ⟨71486258525635660783695397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95315011367514214378260529 71486258525635660783695397)
        ·
          refine ⟨13403673473556686396942887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71486258525635660783695397 13403673473556686396942887)
          ·
            refine ⟨20105510210335029595414331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13403673473556686396942887 20105510210335029595414331)
            ·
              refine ⟨30158265315502544393121497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20105510210335029595414331 30158265315502544393121497)
              ·
                refine ⟨22618698986626908294841123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30158265315502544393121497 22618698986626908294841123)
                ·
                  refine ⟨33928048479940362442261685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22618698986626908294841123 33928048479940362442261685)
                  ·
                    refine ⟨3180754544994408978962033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33928048479940362442261685 3180754544994408978962033)
                    ·
                      refine ⟨2385565908745806734221525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3180754544994408978962033 2385565908745806734221525)
                      ·
                        rfl

theorem cell23_4645873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 2, 1, 5, 2].length) (baseStart_4645873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4645873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4645873 prefixEnd_4645873 := by exact prefixLift 4645873
  have htrace : WordTrace (prefixWord ++ tailWord_4645873) baseStart_4645873 baseEnd_4645873 := by
    simpa [prefixWord, tailWord_4645873, baseEnd_4645873] using wordTrace_append hprefix tailTrace_4645873
  have hstable : (prefixWord ++ tailWord_4645873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4645873).length < 2 ^ (prefixWord ++ tailWord_4645873).sum := by decide
  have hdescent : baseEnd_4645873 < baseStart_4645873 := by decide
  rcases family_descends (prefixWord ++ tailWord_4645873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4645950 : List Nat := [4, 2, 1, 3, 1, 2, 1, 2, 1, 2, 4]
def baseStart_4645950 : Nat := 118140960795 + 4645950 * 2 ^ 59
def prefixEnd_4645950 : Nat := 4983230072969 + 3 ^ 40 * 4645950 * 2
def baseEnd_4645950 : Nat := 2385605446756202932958671

theorem tailTrace_4645950 : CollatzResearch.WordTrace tailWord_4645950 prefixEnd_4645950 2385605446756202932958671 := by
  unfold tailWord_4645950
  simp only [CollatzResearch.WordTrace]
  refine ⟨21181464689815511241765913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112967811679016059956084869 21181464689815511241765913)
  ·
    refine ⟨15886098517361633431324435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21181464689815511241765913 15886098517361633431324435)
    ·
      refine ⟨23829147776042450146986653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15886098517361633431324435 23829147776042450146986653)
      ·
        refine ⟨8935930416015918805119995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23829147776042450146986653 8935930416015918805119995)
        ·
          refine ⟨13403895624023878207679993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8935930416015918805119995 13403895624023878207679993)
          ·
            refine ⟨10052921718017908655759995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13403895624023878207679993 10052921718017908655759995)
            ·
              refine ⟨15079382577026862983639993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10052921718017908655759995 15079382577026862983639993)
              ·
                refine ⟨11309536932770147237729995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15079382577026862983639993 11309536932770147237729995)
                ·
                  refine ⟨16964305399155220856594993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11309536932770147237729995 16964305399155220856594993)
                  ·
                    refine ⟨12723229049366415642446245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16964305399155220856594993 12723229049366415642446245)
                    ·
                      refine ⟨2385605446756202932958671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12723229049366415642446245 2385605446756202932958671)
                      ·
                        rfl

theorem cell23_4645950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_4645950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4645950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4645950 prefixEnd_4645950 := by exact prefixLift 4645950
  have htrace : WordTrace (prefixWord ++ tailWord_4645950) baseStart_4645950 baseEnd_4645950 := by
    simpa [prefixWord, tailWord_4645950, baseEnd_4645950] using wordTrace_append hprefix tailTrace_4645950
  have hstable : (prefixWord ++ tailWord_4645950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4645950).length < 2 ^ (prefixWord ++ tailWord_4645950).sum := by decide
  have hdescent : baseEnd_4645950 < baseStart_4645950 := by decide
  rcases family_descends (prefixWord ++ tailWord_4645950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4645963 : List Nat := [1, 1, 1, 1, 3, 1, 2, 1, 7, 3, 2]
def baseStart_4645963 : Nat := 118140960795 + 4645963 * 2 ^ 59
def prefixEnd_4645963 : Nat := 4983230072969 + 3 ^ 40 * 4645963 * 2
def baseEnd_4645963 : Nat := 2385612122004711382096111

theorem tailTrace_4645963 : CollatzResearch.WordTrace tailWord_4645963 prefixEnd_4645963 2385612122004711382096111 := by
  unfold tailWord_4645963
  simp only [CollatzResearch.WordTrace]
  refine ⟨169452191667476993154350543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112968127778317995436233695 169452191667476993154350543)
  ·
    refine ⟨254178287501215489731525815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169452191667476993154350543 254178287501215489731525815)
    ·
      refine ⟨381267431251823234597288723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 254178287501215489731525815 381267431251823234597288723)
      ·
        refine ⟨571901146877734851895933085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 381267431251823234597288723 571901146877734851895933085)
        ·
          refine ⟨214462930079150569460974907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 571901146877734851895933085 214462930079150569460974907)
          ·
            refine ⟨321694395118725854191462361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 214462930079150569460974907 321694395118725854191462361)
            ·
              refine ⟨241270796339044390643596771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 321694395118725854191462361 241270796339044390643596771)
              ·
                refine ⟨361906194508566585965395157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 241270796339044390643596771 361906194508566585965395157)
                ·
                  refine ⟨8482176433794529358563949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 361906194508566585965395157 8482176433794529358563949)
                  ·
                    refine ⟨3180816162672948509461481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8482176433794529358563949 3180816162672948509461481)
                    ·
                      refine ⟨2385612122004711382096111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3180816162672948509461481 2385612122004711382096111)
                      ·
                        rfl

theorem cell23_4645963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 7, 3, 2].length) (baseStart_4645963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4645963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4645963 prefixEnd_4645963 := by exact prefixLift 4645963
  have htrace : WordTrace (prefixWord ++ tailWord_4645963) baseStart_4645963 baseEnd_4645963 := by
    simpa [prefixWord, tailWord_4645963, baseEnd_4645963] using wordTrace_append hprefix tailTrace_4645963
  have hstable : (prefixWord ++ tailWord_4645963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4645963).length < 2 ^ (prefixWord ++ tailWord_4645963).sum := by decide
  have hdescent : baseEnd_4645963 < baseStart_4645963 := by decide
  rcases family_descends (prefixWord ++ tailWord_4645963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4645976 : List Nat := [2, 1, 2, 2, 1, 3, 1, 1, 1, 5, 4]
def baseStart_4645976 : Nat := 118140960795 + 4645976 * 2 ^ 59
def prefixEnd_4645976 : Nat := 4983230072969 + 3 ^ 40 * 4645976 * 2
def baseEnd_4645976 : Nat := 2385618797253219831233551

theorem tailTrace_4645976 : CollatzResearch.WordTrace tailWord_4645976 prefixEnd_4645976 2385618797253219831233551 := by
  unfold tailWord_4645976
  simp only [CollatzResearch.WordTrace]
  refine ⟨84726332908214948187286891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112968443877619930916382521 84726332908214948187286891)
  ·
    refine ⟨127089499362322422280930337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84726332908214948187286891 127089499362322422280930337)
    ·
      refine ⟨95317124521741816710697753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127089499362322422280930337 95317124521741816710697753)
      ·
        refine ⟨71487843391306362533023315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95317124521741816710697753 71487843391306362533023315)
        ·
          refine ⟨107231765086959543799534973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71487843391306362533023315 107231765086959543799534973)
          ·
            refine ⟨40211911907609828924825615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 107231765086959543799534973 40211911907609828924825615)
            ·
              refine ⟨60317867861414743387238423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40211911907609828924825615 60317867861414743387238423)
              ·
                refine ⟨90476801792122115080857635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60317867861414743387238423 90476801792122115080857635)
                ·
                  refine ⟨135715202688183172621286453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 90476801792122115080857635 135715202688183172621286453)
                  ·
                    refine ⟨12723300252017172433245605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 135715202688183172621286453 12723300252017172433245605)
                    ·
                      refine ⟨2385618797253219831233551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12723300252017172433245605 2385618797253219831233551)
                      ·
                        rfl

theorem cell23_4645976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 1, 5, 4].length) (baseStart_4645976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4645976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4645976 prefixEnd_4645976 := by exact prefixLift 4645976
  have htrace : WordTrace (prefixWord ++ tailWord_4645976) baseStart_4645976 baseEnd_4645976 := by
    simpa [prefixWord, tailWord_4645976, baseEnd_4645976] using wordTrace_append hprefix tailTrace_4645976
  have hstable : (prefixWord ++ tailWord_4645976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4645976).length < 2 ^ (prefixWord ++ tailWord_4645976).sum := by decide
  have hdescent : baseEnd_4645976 < baseStart_4645976 := by decide
  rcases family_descends (prefixWord ++ tailWord_4645976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4645980 : List Nat := [2, 2, 4, 1, 1, 1, 1, 1, 5, 3, 2]
def baseStart_4645980 : Nat := 118140960795 + 4645980 * 2 ^ 59
def prefixEnd_4645980 : Nat := 4983230072969 + 3 ^ 40 * 4645980 * 2
def baseEnd_4645980 : Nat := 2385620851175837815583533

theorem tailTrace_4645980 : CollatzResearch.WordTrace tailWord_4645980 prefixEnd_4645980 2385620851175837815583533 := by
  unfold tailWord_4645980
  simp only [CollatzResearch.WordTrace]
  refine ⟨84726405854207702528859697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112968541138943603371812929 84726405854207702528859697)
  ·
    refine ⟨63544804390655776896644773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84726405854207702528859697 63544804390655776896644773)
    ·
      refine ⟨11914650823247958168120895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63544804390655776896644773 11914650823247958168120895)
      ·
        refine ⟨17871976234871937252181343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11914650823247958168120895 17871976234871937252181343)
        ·
          refine ⟨26807964352307905878272015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17871976234871937252181343 26807964352307905878272015)
          ·
            refine ⟨40211946528461858817408023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26807964352307905878272015 40211946528461858817408023)
            ·
              refine ⟨60317919792692788226112035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40211946528461858817408023 60317919792692788226112035)
              ·
                refine ⟨90476879689039182339168053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60317919792692788226112035 90476879689039182339168053)
                ·
                  refine ⟨8482207470847423344297005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 90476879689039182339168053 8482207470847423344297005)
                  ·
                    refine ⟨3180827801567783754111377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8482207470847423344297005 3180827801567783754111377)
                    ·
                      refine ⟨2385620851175837815583533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3180827801567783754111377 2385620851175837815583533)
                      ·
                        rfl

theorem cell23_4645980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 5, 3, 2].length) (baseStart_4645980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4645980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4645980 prefixEnd_4645980 := by exact prefixLift 4645980
  have htrace : WordTrace (prefixWord ++ tailWord_4645980) baseStart_4645980 baseEnd_4645980 := by
    simpa [prefixWord, tailWord_4645980, baseEnd_4645980] using wordTrace_append hprefix tailTrace_4645980
  have hstable : (prefixWord ++ tailWord_4645980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4645980).length < 2 ^ (prefixWord ++ tailWord_4645980).sum := by decide
  have hdescent : baseEnd_4645980 < baseStart_4645980 := by decide
  rcases family_descends (prefixWord ++ tailWord_4645980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4646080 : List Nat := [2, 1, 1, 2, 6, 1, 1, 2, 2, 5]
def baseStart_4646080 : Nat := 118140960795 + 4646080 * 2 ^ 59
def prefixEnd_4646080 : Nat := 4983230072969 + 3 ^ 40 * 4646080 * 2
def baseEnd_4646080 : Nat := 795224066413762474777691

theorem tailTrace_4646080 : CollatzResearch.WordTrace tailWord_4646080 prefixEnd_4646080 795224066413762474777691 := by
  unfold tailWord_4646080
  simp only [CollatzResearch.WordTrace]
  refine ⟨84728229504026561068179847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112970972672035414757573129 84728229504026561068179847)
  ·
    refine ⟨127092344256039841602269771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84728229504026561068179847 127092344256039841602269771)
    ·
      refine ⟨190638516384059762403404657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127092344256039841602269771 190638516384059762403404657)
      ·
        refine ⟨142978887288044821802553493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 190638516384059762403404657 142978887288044821802553493)
        ·
          refine ⟨6702135341627101021994695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 142978887288044821802553493 6702135341627101021994695)
          ·
            refine ⟨10053203012440651532992043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6702135341627101021994695 10053203012440651532992043)
            ·
              refine ⟨15079804518660977299488065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10053203012440651532992043 15079804518660977299488065)
              ·
                refine ⟨11309853388995732974616049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15079804518660977299488065 11309853388995732974616049)
                ·
                  refine ⟨8482390041746799730962037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11309853388995732974616049 8482390041746799730962037)
                  ·
                    refine ⟨795224066413762474777691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8482390041746799730962037 795224066413762474777691)
                    ·
                      rfl

theorem cell23_4646080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 2, 2, 5].length) (baseStart_4646080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4646080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4646080 prefixEnd_4646080 := by exact prefixLift 4646080
  have htrace : WordTrace (prefixWord ++ tailWord_4646080) baseStart_4646080 baseEnd_4646080 := by
    simpa [prefixWord, tailWord_4646080, baseEnd_4646080] using wordTrace_append hprefix tailTrace_4646080
  have hstable : (prefixWord ++ tailWord_4646080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4646080).length < 2 ^ (prefixWord ++ tailWord_4646080).sum := by decide
  have hdescent : baseEnd_4646080 < baseStart_4646080 := by decide
  rcases family_descends (prefixWord ++ tailWord_4646080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4646084 : List Nat := [2, 3, 3, 1, 3, 1, 3, 2, 5]
def baseStart_4646084 : Nat := 118140960795 + 4646084 * 2 ^ 59
def prefixEnd_4646084 : Nat := 4983230072969 + 3 ^ 40 * 4646084 * 2
def baseEnd_4646084 : Nat := 265074917018211712075895

theorem tailTrace_4646084 : CollatzResearch.WordTrace tailWord_4646084 prefixEnd_4646084 265074917018211712075895 := by
  unfold tailWord_4646084
  simp only [CollatzResearch.WordTrace]
  refine ⟨84728302450019315409752653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112971069933359087213003537 84728302450019315409752653)
  ·
    refine ⟨31773113418757243278657245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84728302450019315409752653 31773113418757243278657245)
    ·
      refine ⟨11914917532033966229496467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31773113418757243278657245 11914917532033966229496467)
      ·
        refine ⟨17872376298050949344244701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11914917532033966229496467 17872376298050949344244701)
        ·
          refine ⟨6702141111769106004091763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17872376298050949344244701 6702141111769106004091763)
          ·
            refine ⟨10053211667653659006137645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6702141111769106004091763 10053211667653659006137645)
            ·
              refine ⟨3769954375370122127301617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10053211667653659006137645 3769954375370122127301617)
              ·
                refine ⟨2827465781527591595476213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3769954375370122127301617 2827465781527591595476213)
                ·
                  refine ⟨265074917018211712075895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2827465781527591595476213 265074917018211712075895)
                  ·
                    rfl

theorem cell23_4646084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 3, 2, 5].length) (baseStart_4646084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4646084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4646084 prefixEnd_4646084 := by exact prefixLift 4646084
  have htrace : WordTrace (prefixWord ++ tailWord_4646084) baseStart_4646084 baseEnd_4646084 := by
    simpa [prefixWord, tailWord_4646084, baseEnd_4646084] using wordTrace_append hprefix tailTrace_4646084
  have hstable : (prefixWord ++ tailWord_4646084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4646084).length < 2 ^ (prefixWord ++ tailWord_4646084).sum := by decide
  have hdescent : baseEnd_4646084 < baseStart_4646084 := by decide
  rcases family_descends (prefixWord ++ tailWord_4646084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4646103 : List Nat := [1, 1, 3, 2, 1, 2, 2, 1, 3, 4, 3]
def baseStart_4646103 : Nat := 118140960795 + 4646103 * 2 ^ 59
def prefixEnd_4646103 : Nat := 4983230072969 + 3 ^ 40 * 4646103 * 2
def baseEnd_4646103 : Nat := 2385684009296340834345467

theorem tailTrace_4646103 : CollatzResearch.WordTrace tailWord_4646103 prefixEnd_4646103 2385684009296340834345467 := by
  unfold tailWord_4646103
  simp only [CollatzResearch.WordTrace]
  refine ⟨169457297886969797064446963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112971531924646531376297975 169457297886969797064446963)
  ·
    refine ⟨254185946830454695596670445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169457297886969797064446963 254185946830454695596670445)
    ·
      refine ⟨95319730061420510848751417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 254185946830454695596670445 95319730061420510848751417)
      ·
        refine ⟨71489797546065383136563563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95319730061420510848751417 71489797546065383136563563)
        ·
          refine ⟨107234696319098074704845345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71489797546065383136563563 107234696319098074704845345)
          ·
            refine ⟨80426022239323556028634009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107234696319098074704845345 80426022239323556028634009)
            ·
              refine ⟨60319516679492667021475507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80426022239323556028634009 60319516679492667021475507)
              ·
                refine ⟨90479275019239000532213261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60319516679492667021475507 90479275019239000532213261)
                ·
                  refine ⟨33929728132214625199579973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 90479275019239000532213261 33929728132214625199579973)
                  ·
                    refine ⟨6361824024790242224921245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33929728132214625199579973 6361824024790242224921245)
                    ·
                      refine ⟨2385684009296340834345467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6361824024790242224921245 2385684009296340834345467)
                      ·
                        rfl

theorem cell23_4646103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 3, 4, 3].length) (baseStart_4646103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4646103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4646103 prefixEnd_4646103 := by exact prefixLift 4646103
  have htrace : WordTrace (prefixWord ++ tailWord_4646103) baseStart_4646103 baseEnd_4646103 := by
    simpa [prefixWord, tailWord_4646103, baseEnd_4646103] using wordTrace_append hprefix tailTrace_4646103
  have hstable : (prefixWord ++ tailWord_4646103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4646103).length < 2 ^ (prefixWord ++ tailWord_4646103).sum := by decide
  have hdescent : baseEnd_4646103 < baseStart_4646103 := by decide
  rcases family_descends (prefixWord ++ tailWord_4646103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4646117 : List Nat := [1, 3, 1, 4, 3, 1, 2, 1, 2, 1, 4]
def baseStart_4646117 : Nat := 118140960795 + 4646117 * 2 ^ 59
def prefixEnd_4646117 : Nat := 4983230072969 + 3 ^ 40 * 4646117 * 2
def baseEnd_4646117 : Nat := 2385691198025503779570403

theorem tailTrace_4646117 : CollatzResearch.WordTrace tailWord_4646117 prefixEnd_4646117 2385691198025503779570403 := by
  unfold tailWord_4646117
  simp only [CollatzResearch.WordTrace]
  refine ⟨169457808508919077455456605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112971872339279384970304403 169457808508919077455456605)
  ·
    refine ⟨63546678190844654045796227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 169457808508919077455456605 63546678190844654045796227)
    ·
      refine ⟨95320017286266981068694341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63546678190844654045796227 95320017286266981068694341)
      ·
        refine ⟨17872503241175058950380189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 95320017286266981068694341 17872503241175058950380189)
        ·
          refine ⟨6702188715440647106392571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17872503241175058950380189 6702188715440647106392571)
          ·
            refine ⟨10053283073160970659588857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6702188715440647106392571 10053283073160970659588857)
            ·
              refine ⟨7539962304870727994691643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10053283073160970659588857 7539962304870727994691643)
              ·
                refine ⟨11309943457306091992037465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7539962304870727994691643 11309943457306091992037465)
                ·
                  refine ⟨8482457592979568994028099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11309943457306091992037465 8482457592979568994028099)
                  ·
                    refine ⟨12723686389469353491042149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8482457592979568994028099 12723686389469353491042149)
                    ·
                      refine ⟨2385691198025503779570403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12723686389469353491042149 2385691198025503779570403)
                      ·
                        rfl

theorem cell23_4646117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 2, 1, 2, 1, 4].length) (baseStart_4646117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4646117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4646117 prefixEnd_4646117 := by exact prefixLift 4646117
  have htrace : WordTrace (prefixWord ++ tailWord_4646117) baseStart_4646117 baseEnd_4646117 := by
    simpa [prefixWord, tailWord_4646117, baseEnd_4646117] using wordTrace_append hprefix tailTrace_4646117
  have hstable : (prefixWord ++ tailWord_4646117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4646117).length < 2 ^ (prefixWord ++ tailWord_4646117).sum := by decide
  have hdescent : baseEnd_4646117 < baseStart_4646117 := by decide
  rcases family_descends (prefixWord ++ tailWord_4646117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4646153 : List Nat := [1, 2, 1, 1, 3, 3, 1, 1, 5, 5]
def baseStart_4646153 : Nat := 118140960795 + 4646153 * 2 ^ 59
def prefixEnd_4646153 : Nat := 4983230072969 + 3 ^ 40 * 4646153 * 2
def baseEnd_4646153 : Nat := 795236561109688546240079

theorem tailTrace_4646153 : CollatzResearch.WordTrace tailWord_4646153 prefixEnd_4646153 795236561109688546240079 := by
  unfold tailWord_4646153
  simp only [CollatzResearch.WordTrace]
  refine ⟨169459121536788655603767113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112972747691192437069178075 169459121536788655603767113)
  ·
    refine ⟨127094341152591491702825335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169459121536788655603767113 127094341152591491702825335)
    ·
      refine ⟨190641511728887237554238003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127094341152591491702825335 190641511728887237554238003)
      ·
        refine ⟨285962267593330856331357005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190641511728887237554238003 285962267593330856331357005)
        ·
          refine ⟨107235850347499071124258877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 285962267593330856331357005 107235850347499071124258877)
          ·
            refine ⟨40213443880312151671597079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 107235850347499071124258877 40213443880312151671597079)
            ·
              refine ⟨60320165820468227507395619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40213443880312151671597079 60320165820468227507395619)
              ·
                refine ⟨90480248730702341261093429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60320165820468227507395619 90480248730702341261093429)
                ·
                  refine ⟨8482523318503344493227509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 90480248730702341261093429 8482523318503344493227509)
                  ·
                    refine ⟨795236561109688546240079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8482523318503344493227509 795236561109688546240079)
                    ·
                      rfl

theorem cell23_4646153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 5, 5].length) (baseStart_4646153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4646153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4646153 prefixEnd_4646153 := by exact prefixLift 4646153
  have htrace : WordTrace (prefixWord ++ tailWord_4646153) baseStart_4646153 baseEnd_4646153 := by
    simpa [prefixWord, tailWord_4646153, baseEnd_4646153] using wordTrace_append hprefix tailTrace_4646153
  have hstable : (prefixWord ++ tailWord_4646153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4646153).length < 2 ^ (prefixWord ++ tailWord_4646153).sum := by decide
  have hdescent : baseEnd_4646153 < baseStart_4646153 := by decide
  rcases family_descends (prefixWord ++ tailWord_4646153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4646167 : List Nat := [1, 1, 3, 4, 1, 1, 3, 2, 3, 1, 3]
def baseStart_4646167 : Nat := 118140960795 + 4646167 * 2 ^ 59
def prefixEnd_4646167 : Nat := 4983230072969 + 3 ^ 40 * 4646167 * 2
def baseEnd_4646167 : Nat := 2385716872058228583945173

theorem tailTrace_4646167 : CollatzResearch.WordTrace tailWord_4646167 prefixEnd_4646167 2385716872058228583945173 := by
  unfold tailWord_4646167
  simp only [CollatzResearch.WordTrace]
  refine ⟨169459632158737935994776755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112973088105825290663184503 169459632158737935994776755)
  ·
    refine ⟨254189448238106903992165133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169459632158737935994776755 254189448238106903992165133)
    ·
      refine ⟨95321043089290088997061925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 254189448238106903992165133 95321043089290088997061925)
      ·
        refine ⟨17872695579241891686949111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 95321043089290088997061925 17872695579241891686949111)
        ·
          refine ⟨26809043368862837530423667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17872695579241891686949111 26809043368862837530423667)
          ·
            refine ⟨40213565053294256295635501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26809043368862837530423667 40213565053294256295635501)
            ·
              refine ⟨15080086894985346110863313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40213565053294256295635501 15080086894985346110863313)
              ·
                refine ⟨11310065171239009583147485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15080086894985346110863313 11310065171239009583147485)
                ·
                  refine ⟨4241274439214628593680307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11310065171239009583147485 4241274439214628593680307)
                  ·
                    refine ⟨6361911658821942890520461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4241274439214628593680307 6361911658821942890520461)
                    ·
                      refine ⟨2385716872058228583945173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6361911658821942890520461 2385716872058228583945173)
                      ·
                        rfl

theorem cell23_4646167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 2, 3, 1, 3].length) (baseStart_4646167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4646167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4646167 prefixEnd_4646167 := by exact prefixLift 4646167
  have htrace : WordTrace (prefixWord ++ tailWord_4646167) baseStart_4646167 baseEnd_4646167 := by
    simpa [prefixWord, tailWord_4646167, baseEnd_4646167] using wordTrace_append hprefix tailTrace_4646167
  have hstable : (prefixWord ++ tailWord_4646167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4646167).length < 2 ^ (prefixWord ++ tailWord_4646167).sum := by decide
  have hdescent : baseEnd_4646167 < baseStart_4646167 := by decide
  rcases family_descends (prefixWord ++ tailWord_4646167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4646170 : List Nat := [3, 1, 1, 3, 3, 1, 2, 1, 3, 5]
def baseStart_4646170 : Nat := 118140960795 + 4646170 * 2 ^ 59
def prefixEnd_4646170 : Nat := 4983230072969 + 3 ^ 40 * 4646170 * 2
def baseEnd_4646170 : Nat := 795239470833397357402553

theorem tailTrace_4646170 : CollatzResearch.WordTrace tailWord_4646170 prefixEnd_4646170 795239470833397357402553 := by
  unfold tailWord_4646170
  simp only [CollatzResearch.WordTrace]
  refine ⟨42364935394431766876783991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112973161051818045004757309 42364935394431766876783991)
  ·
    refine ⟨63547403091647650315175987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42364935394431766876783991 63547403091647650315175987)
    ·
      refine ⟨95321104637471475472763981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63547403091647650315175987 95321104637471475472763981)
      ·
        refine ⟨35745414239051803302286493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95321104637471475472763981 35745414239051803302286493)
        ·
          refine ⟨13404530339644426238357435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35745414239051803302286493 13404530339644426238357435)
          ·
            refine ⟨20106795509466639357536153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13404530339644426238357435 20106795509466639357536153)
            ·
              refine ⟨15080096632099979518152115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20106795509466639357536153 15080096632099979518152115)
              ·
                refine ⟨22620144948149969277228173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15080096632099979518152115 22620144948149969277228173)
                ·
                  refine ⟨8482554355556238478960565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22620144948149969277228173 8482554355556238478960565)
                  ·
                    refine ⟨795239470833397357402553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8482554355556238478960565 795239470833397357402553)
                    ·
                      rfl

theorem cell23_4646170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 1, 3, 5].length) (baseStart_4646170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4646170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4646170 prefixEnd_4646170 := by exact prefixLift 4646170
  have htrace : WordTrace (prefixWord ++ tailWord_4646170) baseStart_4646170 baseEnd_4646170 := by
    simpa [prefixWord, tailWord_4646170, baseEnd_4646170] using wordTrace_append hprefix tailTrace_4646170
  have hstable : (prefixWord ++ tailWord_4646170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4646170).length < 2 ^ (prefixWord ++ tailWord_4646170).sum := by decide
  have hdescent : baseEnd_4646170 < baseStart_4646170 := by decide
  rcases family_descends (prefixWord ++ tailWord_4646170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4646220 : List Nat := [2, 2, 1, 3, 2, 3, 1, 1, 1, 1, 6]
def baseStart_4646220 : Nat := 118140960795 + 4646220 * 2 ^ 59
def prefixEnd_4646220 : Nat := 4983230072969 + 3 ^ 40 * 4646220 * 2
def baseEnd_4646220 : Nat := 2385744086532916876582429

theorem tailTrace_4646220 : CollatzResearch.WordTrace tailWord_4646220 prefixEnd_4646220 2385744086532916876582429 := by
  unfold tailWord_4646220
  simp only [CollatzResearch.WordTrace]
  refine ⟨84730782613772963023228057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112974376818363950697637409 84730782613772963023228057)
  ·
    refine ⟨63548086960329722267421043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84730782613772963023228057 63548086960329722267421043)
    ·
      refine ⟨95322130440494583401131565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63548086960329722267421043 95322130440494583401131565)
      ·
        refine ⟨35745798915185468775424337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95322130440494583401131565 35745798915185468775424337)
        ·
          refine ⟨26809349186389101581568253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35745798915185468775424337 26809349186389101581568253)
          ·
            refine ⟨10053505944895913093088095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26809349186389101581568253 10053505944895913093088095)
            ·
              refine ⟨15080258917343869639632143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10053505944895913093088095 15080258917343869639632143)
              ·
                refine ⟨22620388376015804459448215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15080258917343869639632143 22620388376015804459448215)
                ·
                  refine ⟨33930582564023706689172323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22620388376015804459448215 33930582564023706689172323)
                  ·
                    refine ⟨50895873846035560033758485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33930582564023706689172323 50895873846035560033758485)
                    ·
                      refine ⟨2385744086532916876582429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50895873846035560033758485 2385744086532916876582429)
                      ·
                        rfl

theorem cell23_4646220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 1, 1, 1, 6].length) (baseStart_4646220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4646220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4646220 prefixEnd_4646220 := by exact prefixLift 4646220
  have htrace : WordTrace (prefixWord ++ tailWord_4646220) baseStart_4646220 baseEnd_4646220 := by
    simpa [prefixWord, tailWord_4646220, baseEnd_4646220] using wordTrace_append hprefix tailTrace_4646220
  have hstable : (prefixWord ++ tailWord_4646220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4646220).length < 2 ^ (prefixWord ++ tailWord_4646220).sum := by decide
  have hdescent : baseEnd_4646220 < baseStart_4646220 := by decide
  rcases family_descends (prefixWord ++ tailWord_4646220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4646221 : List Nat := [1, 6, 1, 3, 1, 1, 2, 2, 1, 5]
def baseStart_4646221 : Nat := 118140960795 + 4646221 * 2 ^ 59
def prefixEnd_4646221 : Nat := 4983230072969 + 3 ^ 40 * 4646221 * 2
def baseEnd_4646221 : Nat := 795248200004523790889975

theorem tailTrace_4646221 : CollatzResearch.WordTrace tailWord_4646221 prefixEnd_4646221 795248200004523790889975 := by
  unfold tailWord_4646221
  simp only [CollatzResearch.WordTrace]
  refine ⟨169461601700542303217242517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112974401133694868811495011 169461601700542303217242517)
  ·
    refine ⟨7943512579712920463308243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 169461601700542303217242517 7943512579712920463308243)
    ·
      refine ⟨11915268869569380694962365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7943512579712920463308243 11915268869569380694962365)
      ·
        refine ⟨4468225826088517760610887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11915268869569380694962365 4468225826088517760610887)
        ·
          refine ⟨6702338739132776640916331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4468225826088517760610887 6702338739132776640916331)
          ·
            refine ⟨10053508108699164961374497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6702338739132776640916331 10053508108699164961374497)
            ·
              refine ⟨7540131081524373721030873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10053508108699164961374497 7540131081524373721030873)
              ·
                refine ⟨5655098311143280290773155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7540131081524373721030873 5655098311143280290773155)
                ·
                  refine ⟨8482647466714920436159733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5655098311143280290773155 8482647466714920436159733)
                  ·
                    refine ⟨795248200004523790889975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8482647466714920436159733 795248200004523790889975)
                    ·
                      rfl

theorem cell23_4646221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 2, 2, 1, 5].length) (baseStart_4646221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4646221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4646221 prefixEnd_4646221 := by exact prefixLift 4646221
  have htrace : WordTrace (prefixWord ++ tailWord_4646221) baseStart_4646221 baseEnd_4646221 := by
    simpa [prefixWord, tailWord_4646221, baseEnd_4646221] using wordTrace_append hprefix tailTrace_4646221
  have hstable : (prefixWord ++ tailWord_4646221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4646221).length < 2 ^ (prefixWord ++ tailWord_4646221).sum := by decide
  have hdescent : baseEnd_4646221 < baseStart_4646221 := by decide
  rcases family_descends (prefixWord ++ tailWord_4646221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4646227 : List Nat := [1, 1, 1, 2, 1, 1, 8, 2, 1, 2, 3]
def baseStart_4646227 : Nat := 118140960795 + 4646227 * 2 ^ 59
def prefixEnd_4646227 : Nat := 4983230072969 + 3 ^ 40 * 4646227 * 2
def baseEnd_4646227 : Nat := 2385747680897498349194897

theorem tailTrace_4646227 : CollatzResearch.WordTrace tailWord_4646227 prefixEnd_4646227 2385747680897498349194897 := by
  unfold tailWord_4646227
  simp only [CollatzResearch.WordTrace]
  refine ⟨169461820538520566241960935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112974547025680377494640623 169461820538520566241960935)
  ·
    refine ⟨254192730807780849362941403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169461820538520566241960935 254192730807780849362941403)
    ·
      refine ⟨381289096211671274044412105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 254192730807780849362941403 381289096211671274044412105)
      ·
        refine ⟨285966822158753455533309079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 381289096211671274044412105 285966822158753455533309079)
        ·
          refine ⟨428950233238130183299963619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 285966822158753455533309079 428950233238130183299963619)
          ·
            refine ⟨643425349857195274949945429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 428950233238130183299963619 643425349857195274949945429)
            ·
              refine ⟨7540140818639007128319673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 643425349857195274949945429 7540140818639007128319673)
              ·
                refine ⟨5655105613979255346239755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7540140818639007128319673 5655105613979255346239755)
                ·
                  refine ⟨8482658420968883019359633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5655105613979255346239755 8482658420968883019359633)
                  ·
                    refine ⟨6361993815726662264519725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8482658420968883019359633 6361993815726662264519725)
                    ·
                      refine ⟨2385747680897498349194897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6361993815726662264519725 2385747680897498349194897)
                      ·
                        rfl

theorem cell23_4646227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 8, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 8, 2, 1, 2, 3].length) (baseStart_4646227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4646227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4646227 prefixEnd_4646227 := by exact prefixLift 4646227
  have htrace : WordTrace (prefixWord ++ tailWord_4646227) baseStart_4646227 baseEnd_4646227 := by
    simpa [prefixWord, tailWord_4646227, baseEnd_4646227] using wordTrace_append hprefix tailTrace_4646227
  have hstable : (prefixWord ++ tailWord_4646227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4646227).length < 2 ^ (prefixWord ++ tailWord_4646227).sum := by decide
  have hdescent : baseEnd_4646227 < baseStart_4646227 := by decide
  rcases family_descends (prefixWord ++ tailWord_4646227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4646247 : List Nat := [1, 1, 5, 1, 5, 1, 9]
def baseStart_4646247 : Nat := 118140960795 + 4646247 * 2 ^ 59
def prefixEnd_4646247 : Nat := 4983230072969 + 3 ^ 40 * 4646247 * 2
def baseEnd_4646247 : Nat := 29453801858155410752405

theorem tailTrace_4646247 : CollatzResearch.WordTrace tailWord_4646247 prefixEnd_4646247 29453801858155410752405 := by
  unfold tailWord_4646247
  simp only [CollatzResearch.WordTrace]
  refine ⟨169462549998448109657688995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112975033332298739771792663 169462549998448109657688995)
  ·
    refine ⟨254193824997672164486533493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169462549998448109657688995 254193824997672164486533493)
    ·
      refine ⟨23830671093531765420612515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 254193824997672164486533493 23830671093531765420612515)
      ·
        refine ⟨35746006640297648130918773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23830671093531765420612515 35746006640297648130918773)
        ·
          refine ⟨3351188122527904512273635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 35746006640297648130918773 3351188122527904512273635)
          ·
            refine ⟨5026782183791856768410453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3351188122527904512273635 5026782183791856768410453)
            ·
              refine ⟨29453801858155410752405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5026782183791856768410453 29453801858155410752405)
              ·
                rfl

theorem cell23_4646247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 9].length) (baseStart_4646247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4646247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4646247 prefixEnd_4646247 := by exact prefixLift 4646247
  have htrace : WordTrace (prefixWord ++ tailWord_4646247) baseStart_4646247 baseEnd_4646247 := by
    simpa [prefixWord, tailWord_4646247, baseEnd_4646247] using wordTrace_append hprefix tailTrace_4646247
  have hstable : (prefixWord ++ tailWord_4646247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4646247).length < 2 ^ (prefixWord ++ tailWord_4646247).sum := by decide
  have hdescent : baseEnd_4646247 < baseStart_4646247 := by decide
  rcases family_descends (prefixWord ++ tailWord_4646247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4646257 : List Nat := [1, 2, 2, 2, 1, 2, 4, 1, 4, 1, 3]
def baseStart_4646257 : Nat := 118140960795 + 4646257 * 2 ^ 59
def prefixEnd_4646257 : Nat := 4983230072969 + 3 ^ 40 * 4646257 * 2
def baseEnd_4646257 : Nat := 2385763085317133231819759

theorem tailTrace_4646257 : CollatzResearch.WordTrace tailWord_4646257 prefixEnd_4646257 2385763085317133231819759 := by
  unfold tailWord_4646257
  simp only [CollatzResearch.WordTrace]
  refine ⟨169462914728411881365553025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112975276485607920910368683 169462914728411881365553025)
  ·
    refine ⟨127097186046308911024164769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169462914728411881365553025 127097186046308911024164769)
    ·
      refine ⟨95322889534731683268123577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127097186046308911024164769 95322889534731683268123577)
      ·
        refine ⟨71492167151048762451092683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95322889534731683268123577 71492167151048762451092683)
        ·
          refine ⟨107238250726573143676639025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71492167151048762451092683 107238250726573143676639025)
          ·
            refine ⟨80428688044929857757479269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107238250726573143676639025 80428688044929857757479269)
            ·
              refine ⟨15080379008424348329527363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 80428688044929857757479269 15080379008424348329527363)
              ·
                refine ⟨22620568512636522494291045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15080379008424348329527363 22620568512636522494291045)
                ·
                  refine ⟨4241356596119347967679571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22620568512636522494291045 4241356596119347967679571)
                  ·
                    refine ⟨6362034894179021951519357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4241356596119347967679571 6362034894179021951519357)
                    ·
                      refine ⟨2385763085317133231819759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6362034894179021951519357 2385763085317133231819759)
                      ·
                        rfl

theorem cell23_4646257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 1, 4, 1, 3].length) (baseStart_4646257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4646257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4646257 prefixEnd_4646257 := by exact prefixLift 4646257
  have htrace : WordTrace (prefixWord ++ tailWord_4646257) baseStart_4646257 baseEnd_4646257 := by
    simpa [prefixWord, tailWord_4646257, baseEnd_4646257] using wordTrace_append hprefix tailTrace_4646257
  have hstable : (prefixWord ++ tailWord_4646257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4646257).length < 2 ^ (prefixWord ++ tailWord_4646257).sum := by decide
  have hdescent : baseEnd_4646257 < baseStart_4646257 := by decide
  rcases family_descends (prefixWord ++ tailWord_4646257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4646258 : List Nat := [3, 2, 1, 2, 1, 2, 5, 2, 1, 2, 2]
def baseStart_4646258 : Nat := 118140960795 + 4646258 * 2 ^ 59
def prefixEnd_4646258 : Nat := 4983230072969 + 3 ^ 40 * 4646258 * 2
def baseEnd_4646258 : Nat := 2385763598797787727907255

theorem tailTrace_4646258 : CollatzResearch.WordTrace tailWord_4646258 prefixEnd_4646258 2385763598797787727907255 := by
  unfold tailWord_4646258
  simp only [CollatzResearch.WordTrace]
  refine ⟨42365737800352064634084857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112975300800938839024226285 42365737800352064634084857)
  ·
    refine ⟨31774303350264048475563643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42365737800352064634084857 31774303350264048475563643)
    ·
      refine ⟨47661455025396072713345465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31774303350264048475563643 47661455025396072713345465)
      ·
        refine ⟨35746091269047054535009099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47661455025396072713345465 35746091269047054535009099)
        ·
          refine ⟨53619136903570581802513649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35746091269047054535009099 53619136903570581802513649)
          ·
            refine ⟨40214352677677936351885237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53619136903570581802513649 40214352677677936351885237)
            ·
              refine ⟨3770095563532306532989241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40214352677677936351885237 3770095563532306532989241)
              ·
                refine ⟨2827571672649229899741931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3770095563532306532989241 2827571672649229899741931)
                ·
                  refine ⟨4241357508973844849612897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2827571672649229899741931 4241357508973844849612897)
                  ·
                    refine ⟨3181018131730383637209673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4241357508973844849612897 3181018131730383637209673)
                    ·
                      refine ⟨2385763598797787727907255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3181018131730383637209673 2385763598797787727907255)
                      ·
                        rfl

theorem cell23_4646258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 5, 2, 1, 2, 2].length) (baseStart_4646258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4646258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4646258 prefixEnd_4646258 := by exact prefixLift 4646258
  have htrace : WordTrace (prefixWord ++ tailWord_4646258) baseStart_4646258 baseEnd_4646258 := by
    simpa [prefixWord, tailWord_4646258, baseEnd_4646258] using wordTrace_append hprefix tailTrace_4646258
  have hstable : (prefixWord ++ tailWord_4646258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4646258).length < 2 ^ (prefixWord ++ tailWord_4646258).sum := by decide
  have hdescent : baseEnd_4646258 < baseStart_4646258 := by decide
  rcases family_descends (prefixWord ++ tailWord_4646258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4646267 : List Nat := [1, 1, 1, 1, 1, 6, 2, 2, 3, 3, 2]
def baseStart_4646267 : Nat := 118140960795 + 4646267 * 2 ^ 59
def prefixEnd_4646267 : Nat := 4983230072969 + 3 ^ 40 * 4646267 * 2
def baseEnd_4646267 : Nat := 2385768220123678192694713

theorem tailTrace_4646267 : CollatzResearch.WordTrace tailWord_4646267 prefixEnd_4646267 2385768220123678192694713 := by
  unfold tailWord_4646267
  simp only [CollatzResearch.WordTrace]
  refine ⟨169463279458375653073417055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112975519638917102048944703 169463279458375653073417055)
  ·
    refine ⟨254194919187563479610125583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169463279458375653073417055 254194919187563479610125583)
    ·
      refine ⟨381292378781345219415188375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 254194919187563479610125583 381292378781345219415188375)
      ·
        refine ⟨571938568172017829122782563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 381292378781345219415188375 571938568172017829122782563)
        ·
          refine ⟨857907852258026743684173845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 571938568172017829122782563 857907852258026743684173845)
          ·
            refine ⟨40214430574595003610195649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 857907852258026743684173845 40214430574595003610195649)
            ·
              refine ⟨30160822930946252707646737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40214430574595003610195649 30160822930946252707646737)
              ·
                refine ⟨22620617198209689530735053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30160822930946252707646737 22620617198209689530735053)
                ·
                  refine ⟨8482731449328633574025645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22620617198209689530735053 8482731449328633574025645)
                  ·
                    refine ⟨3181024293498237590259617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8482731449328633574025645 3181024293498237590259617)
                    ·
                      refine ⟨2385768220123678192694713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3181024293498237590259617 2385768220123678192694713)
                      ·
                        rfl

theorem cell23_4646267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 2, 3, 3, 2].length) (baseStart_4646267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4646267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4646267 prefixEnd_4646267 := by exact prefixLift 4646267
  have htrace : WordTrace (prefixWord ++ tailWord_4646267) baseStart_4646267 baseEnd_4646267 := by
    simpa [prefixWord, tailWord_4646267, baseEnd_4646267] using wordTrace_append hprefix tailTrace_4646267
  have hstable : (prefixWord ++ tailWord_4646267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4646267).length < 2 ^ (prefixWord ++ tailWord_4646267).sum := by decide
  have hdescent : baseEnd_4646267 < baseStart_4646267 := by decide
  rcases family_descends (prefixWord ++ tailWord_4646267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4646297 : List Nat := [1, 2, 1, 2, 1, 5, 1, 1, 3, 4, 2]
def baseStart_4646297 : Nat := 118140960795 + 4646297 * 2 ^ 59
def prefixEnd_4646297 : Nat := 4983230072969 + 3 ^ 40 * 4646297 * 2
def baseEnd_4646297 : Nat := 2385783624543313075319575

theorem tailTrace_4646297 : CollatzResearch.WordTrace tailWord_4646297 prefixEnd_4646297 2385783624543313075319575 := by
  unfold tailWord_4646297
  simp only [CollatzResearch.WordTrace]
  refine ⟨169464373648266968197009145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112976249098844645464672763 169464373648266968197009145)
  ·
    refine ⟨127098280236200226147756859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169464373648266968197009145 127098280236200226147756859)
    ·
      refine ⟨190647420354300339221635289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127098280236200226147756859 190647420354300339221635289)
      ·
        refine ⟨142985565265725254416226467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 190647420354300339221635289 142985565265725254416226467)
        ·
          refine ⟨214478347898587881624339701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142985565265725254416226467 214478347898587881624339701)
          ·
            refine ⟨20107345115492613902281847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 214478347898587881624339701 20107345115492613902281847)
            ·
              refine ⟨30161017673238920853422771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20107345115492613902281847 30161017673238920853422771)
              ·
                refine ⟨45241526509858381280134157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30161017673238920853422771 45241526509858381280134157)
                ·
                  refine ⟨16965572441196892980050309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45241526509858381280134157 16965572441196892980050309)
                  ·
                    refine ⟨3181044832724417433759433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16965572441196892980050309 3181044832724417433759433)
                    ·
                      refine ⟨2385783624543313075319575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3181044832724417433759433 2385783624543313075319575)
                      ·
                        rfl

theorem cell23_4646297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 1, 3, 4, 2].length) (baseStart_4646297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4646297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4646297 prefixEnd_4646297 := by exact prefixLift 4646297
  have htrace : WordTrace (prefixWord ++ tailWord_4646297) baseStart_4646297 baseEnd_4646297 := by
    simpa [prefixWord, tailWord_4646297, baseEnd_4646297] using wordTrace_append hprefix tailTrace_4646297
  have hstable : (prefixWord ++ tailWord_4646297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4646297).length < 2 ^ (prefixWord ++ tailWord_4646297).sum := by decide
  have hdescent : baseEnd_4646297 < baseStart_4646297 := by decide
  rcases family_descends (prefixWord ++ tailWord_4646297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4646360 : List Nat := [2, 1, 2, 2, 2, 1, 2, 1, 3, 2, 5]
def baseStart_4646360 : Nat := 118140960795 + 4646360 * 2 ^ 59
def prefixEnd_4646360 : Nat := 4983230072969 + 3 ^ 40 * 4646360 * 2
def baseEnd_4646360 : Nat := 2385815973824546328831785

theorem tailTrace_4646360 : CollatzResearch.WordTrace tailWord_4646360 prefixEnd_4646360 2385815973824546328831785 := by
  unfold tailWord_4646360
  simp only [CollatzResearch.WordTrace]
  refine ⟨84733335723519364978276267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112977780964692486637701689 84733335723519364978276267)
  ·
    refine ⟨127100003585279047467414401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84733335723519364978276267 127100003585279047467414401)
    ·
      refine ⟨95325002688959285600560801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127100003585279047467414401 95325002688959285600560801)
      ·
        refine ⟨71493752016719464200420601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95325002688959285600560801 71493752016719464200420601)
        ·
          refine ⟨53620314012539598150315451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71493752016719464200420601 53620314012539598150315451)
          ·
            refine ⟨80430471018809397225473177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53620314012539598150315451 80430471018809397225473177)
            ·
              refine ⟨60322853264107047919104883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80430471018809397225473177 60322853264107047919104883)
              ·
                refine ⟨90484279896160571878657325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60322853264107047919104883 90484279896160571878657325)
                ·
                  refine ⟨33931604961060214454496497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 90484279896160571878657325 33931604961060214454496497)
                  ·
                    refine ⟨25448703720795160840872373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33931604961060214454496497 25448703720795160840872373)
                    ·
                      refine ⟨2385815973824546328831785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25448703720795160840872373 2385815973824546328831785)
                      ·
                        rfl

theorem cell23_4646360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 3, 2, 5].length) (baseStart_4646360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4646360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4646360 prefixEnd_4646360 := by exact prefixLift 4646360
  have htrace : WordTrace (prefixWord ++ tailWord_4646360) baseStart_4646360 baseEnd_4646360 := by
    simpa [prefixWord, tailWord_4646360, baseEnd_4646360] using wordTrace_append hprefix tailTrace_4646360
  have hstable : (prefixWord ++ tailWord_4646360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4646360).length < 2 ^ (prefixWord ++ tailWord_4646360).sum := by decide
  have hdescent : baseEnd_4646360 < baseStart_4646360 := by decide
  rcases family_descends (prefixWord ++ tailWord_4646360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4646387 : List Nat := [1, 1, 1, 2, 2, 2, 2, 3, 1, 6, 2]
def baseStart_4646387 : Nat := 118140960795 + 4646387 * 2 ^ 59
def prefixEnd_4646387 : Nat := 4983230072969 + 3 ^ 40 * 4646387 * 2
def baseEnd_4646387 : Nat := 2385829837802217723194161

theorem tailTrace_4646387 : CollatzResearch.WordTrace tailWord_4646387 prefixEnd_4646387 2385829837802217723194161 := by
  unfold tailWord_4646387
  simp only [CollatzResearch.WordTrace]
  refine ⟨169467656217940913567785415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112978437478627275711856943 169467656217940913567785415)
  ·
    refine ⟨254201484326911370351678123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169467656217940913567785415 254201484326911370351678123)
    ·
      refine ⟨381302226490367055527517185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 254201484326911370351678123 381302226490367055527517185)
      ·
        refine ⟨285976669867775291645637889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 381302226490367055527517185 285976669867775291645637889)
        ·
          refine ⟨214482502400831468734228417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 285976669867775291645637889 214482502400831468734228417)
          ·
            refine ⟨160861876800623601550671313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 214482502400831468734228417 160861876800623601550671313)
            ·
              refine ⟨120646407600467701163003485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 160861876800623601550671313 120646407600467701163003485)
              ·
                refine ⟨45242402850175387936126307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 120646407600467701163003485 45242402850175387936126307)
                ·
                  refine ⟨67863604275263081904189461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45242402850175387936126307 67863604275263081904189461)
                  ·
                    refine ⟨3181106450402956964258881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 67863604275263081904189461 3181106450402956964258881)
                    ·
                      refine ⟨2385829837802217723194161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3181106450402956964258881 2385829837802217723194161)
                      ·
                        rfl

theorem cell23_4646387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 1, 6, 2].length) (baseStart_4646387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4646387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4646387 prefixEnd_4646387 := by exact prefixLift 4646387
  have htrace : WordTrace (prefixWord ++ tailWord_4646387) baseStart_4646387 baseEnd_4646387 := by
    simpa [prefixWord, tailWord_4646387, baseEnd_4646387] using wordTrace_append hprefix tailTrace_4646387
  have hstable : (prefixWord ++ tailWord_4646387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4646387).length < 2 ^ (prefixWord ++ tailWord_4646387).sum := by decide
  have hdescent : baseEnd_4646387 < baseStart_4646387 := by decide
  rcases family_descends (prefixWord ++ tailWord_4646387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4646497 : List Nat := [1, 2, 3, 1, 1, 3, 2, 1, 3, 1, 5]
def baseStart_4646497 : Nat := 118140960795 + 4646497 * 2 ^ 59
def prefixEnd_4646497 : Nat := 4983230072969 + 3 ^ 40 * 4646497 * 2
def baseEnd_4646497 : Nat := 2385886320674212292818655

theorem tailTrace_4646497 : CollatzResearch.WordTrace tailWord_4646497 prefixEnd_4646497 2385886320674212292818655 := by
  unfold tailWord_4646497
  simp only [CollatzResearch.WordTrace]
  refine ⟨169471668247542402354289745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112981112165028268236193163 169471668247542402354289745)
  ·
    refine ⟨127103751185656801765717309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169471668247542402354289745 127103751185656801765717309)
    ·
      refine ⟨47663906694621300662143991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 127103751185656801765717309 47663906694621300662143991)
      ·
        refine ⟨71495860041931950993215987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47663906694621300662143991 71495860041931950993215987)
        ·
          refine ⟨107243790062897926489823981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71495860041931950993215987 107243790062897926489823981)
          ·
            refine ⟨40216421273586722433683993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 107243790062897926489823981 40216421273586722433683993)
            ·
              refine ⟨30162315955190041825262995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40216421273586722433683993 30162315955190041825262995)
              ·
                refine ⟨45243473932785062737894493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30162315955190041825262995 45243473932785062737894493)
                ·
                  refine ⟨16966302724794398526710435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45243473932785062737894493 16966302724794398526710435)
                  ·
                    refine ⟨25449454087191597790065653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16966302724794398526710435 25449454087191597790065653)
                    ·
                      refine ⟨2385886320674212292818655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25449454087191597790065653 2385886320674212292818655)
                      ·
                        rfl

theorem cell23_4646497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 1, 3, 1, 5].length) (baseStart_4646497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4646497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4646497 prefixEnd_4646497 := by exact prefixLift 4646497
  have htrace : WordTrace (prefixWord ++ tailWord_4646497) baseStart_4646497 baseEnd_4646497 := by
    simpa [prefixWord, tailWord_4646497, baseEnd_4646497] using wordTrace_append hprefix tailTrace_4646497
  have hstable : (prefixWord ++ tailWord_4646497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4646497).length < 2 ^ (prefixWord ++ tailWord_4646497).sum := by decide
  have hdescent : baseEnd_4646497 < baseStart_4646497 := by decide
  rcases family_descends (prefixWord ++ tailWord_4646497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4646504 : List Nat := [2, 1, 4, 3, 1, 1, 1, 3, 1, 6]
def baseStart_4646504 : Nat := 118140960795 + 4646504 * 2 ^ 59
def prefixEnd_4646504 : Nat := 4983230072969 + 3 ^ 40 * 4646504 * 2
def baseEnd_4646504 : Nat := 795296638346264588477041

theorem tailTrace_4646504 : CollatzResearch.WordTrace tailWord_4646504 prefixEnd_4646504 795296638346264588477041 := by
  unfold tailWord_4646504
  simp only [CollatzResearch.WordTrace]
  refine ⟨84735961779258521274897283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112981282372344695033196377 84735961779258521274897283)
  ·
    refine ⟨127103942668887781912345925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84735961779258521274897283 127103942668887781912345925)
    ·
      refine ⟨23831989250416459108564861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 127103942668887781912345925 23831989250416459108564861)
      ·
        refine ⟨8936995968906172165711823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23831989250416459108564861 8936995968906172165711823)
        ·
          refine ⟨13405493953359258248567735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8936995968906172165711823 13405493953359258248567735)
          ·
            refine ⟨20108240930038887372851603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13405493953359258248567735 20108240930038887372851603)
            ·
              refine ⟨30162361395058331059277405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20108240930038887372851603 30162361395058331059277405)
              ·
                refine ⟨11310885523146874147229027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30162361395058331059277405 11310885523146874147229027)
                ·
                  refine ⟨16966328284720311220843541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11310885523146874147229027 16966328284720311220843541)
                  ·
                    refine ⟨795296638346264588477041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16966328284720311220843541 795296638346264588477041)
                    ·
                      rfl

theorem cell23_4646504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 3, 1, 6].length) (baseStart_4646504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4646504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4646504 prefixEnd_4646504 := by exact prefixLift 4646504
  have htrace : WordTrace (prefixWord ++ tailWord_4646504) baseStart_4646504 baseEnd_4646504 := by
    simpa [prefixWord, tailWord_4646504, baseEnd_4646504] using wordTrace_append hprefix tailTrace_4646504
  have hstable : (prefixWord ++ tailWord_4646504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4646504).length < 2 ^ (prefixWord ++ tailWord_4646504).sum := by decide
  have hdescent : baseEnd_4646504 < baseStart_4646504 := by decide
  rcases family_descends (prefixWord ++ tailWord_4646504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4646527 : List Nat := [1, 1, 2, 2, 1, 1, 1, 2, 2, 7, 3]
def baseStart_4646527 : Nat := 118140960795 + 4646527 * 2 ^ 59
def prefixEnd_4646527 : Nat := 4983230072969 + 3 ^ 40 * 4646527 * 2
def baseEnd_4646527 : Nat := 2385901725093847175443517

theorem tailTrace_4646527 : CollatzResearch.WordTrace tailWord_4646527 prefixEnd_4646527 2385901725093847175443517 := by
  unfold tailWord_4646527
  simp only [CollatzResearch.WordTrace]
  refine ⟨169472762437433717477881835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112981841624955811651921223 169472762437433717477881835)
  ·
    refine ⟨254209143656150576216822753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169472762437433717477881835 254209143656150576216822753)
    ·
      refine ⟨190656857742112932162617065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 254209143656150576216822753 190656857742112932162617065)
      ·
        refine ⟨142992643306584699121962799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 190656857742112932162617065 142992643306584699121962799)
        ·
          refine ⟨214488964959877048682944199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142992643306584699121962799 214488964959877048682944199)
          ·
            refine ⟨321733447439815573024416299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 214488964959877048682944199 321733447439815573024416299)
            ·
              refine ⟨482600171159723359536624449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 321733447439815573024416299 482600171159723359536624449)
              ·
                refine ⟨361950128369792519652468337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 482600171159723359536624449 361950128369792519652468337)
                ·
                  refine ⟨271462596277344389739351253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 361950128369792519652468337 271462596277344389739351253)
                  ·
                    refine ⟨6362404600250259134516045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 271462596277344389739351253 6362404600250259134516045)
                    ·
                      refine ⟨2385901725093847175443517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6362404600250259134516045 2385901725093847175443517)
                      ·
                        rfl

theorem cell23_4646527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 7, 3].length) (baseStart_4646527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4646527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4646527 prefixEnd_4646527 := by exact prefixLift 4646527
  have htrace : WordTrace (prefixWord ++ tailWord_4646527) baseStart_4646527 baseEnd_4646527 := by
    simpa [prefixWord, tailWord_4646527, baseEnd_4646527] using wordTrace_append hprefix tailTrace_4646527
  have hstable : (prefixWord ++ tailWord_4646527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4646527).length < 2 ^ (prefixWord ++ tailWord_4646527).sum := by decide
  have hdescent : baseEnd_4646527 < baseStart_4646527 := by decide
  rcases family_descends (prefixWord ++ tailWord_4646527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4646538 : List Nat := [3, 1, 2, 3, 2, 3, 1, 2, 2, 4]
def baseStart_4646538 : Nat := 118140960795 + 4646538 * 2 ^ 59
def prefixEnd_4646538 : Nat := 4983230072969 + 3 ^ 40 * 4646538 * 2
def baseEnd_4646538 : Nat := 795302457793682210801989

theorem tailTrace_4646538 : CollatzResearch.WordTrace tailWord_4646538 prefixEnd_4646538 795302457793682210801989 := by
  unfold tailWord_4646538
  simp only [CollatzResearch.WordTrace]
  refine ⟨42368290910098466589133067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112982109093595910904354845 42368290910098466589133067)
  ·
    refine ⟨63552436365147699883699601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42368290910098466589133067 63552436365147699883699601)
    ·
      refine ⟨47664327273860774912774701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63552436365147699883699601 47664327273860774912774701)
      ·
        refine ⟨17874122727697790592290513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47664327273860774912774701 17874122727697790592290513)
        ·
          refine ⟨13405592045773342944217885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17874122727697790592290513 13405592045773342944217885)
          ·
            refine ⟨5027097017165003604081707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13405592045773342944217885 5027097017165003604081707)
            ·
              refine ⟨7540645525747505406122561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5027097017165003604081707 7540645525747505406122561)
              ·
                refine ⟨5655484144310629054591921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7540645525747505406122561 5655484144310629054591921)
                ·
                  refine ⟨4241613108232971790943941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5655484144310629054591921 4241613108232971790943941)
                  ·
                    refine ⟨795302457793682210801989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4241613108232971790943941 795302457793682210801989)
                    ·
                      rfl

theorem cell23_4646538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 1, 2, 2, 4].length) (baseStart_4646538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4646538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4646538 prefixEnd_4646538 := by exact prefixLift 4646538
  have htrace : WordTrace (prefixWord ++ tailWord_4646538) baseStart_4646538 baseEnd_4646538 := by
    simpa [prefixWord, tailWord_4646538, baseEnd_4646538] using wordTrace_append hprefix tailTrace_4646538
  have hstable : (prefixWord ++ tailWord_4646538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4646538).length < 2 ^ (prefixWord ++ tailWord_4646538).sum := by decide
  have hdescent : baseEnd_4646538 < baseStart_4646538 := by decide
  rcases family_descends (prefixWord ++ tailWord_4646538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4646558 : List Nat := [4, 3, 1, 1, 1, 4, 1, 1, 1, 2, 4]
def baseStart_4646558 : Nat := 118140960795 + 4646558 * 2 ^ 59
def prefixEnd_4646558 : Nat := 4983230072969 + 3 ^ 40 * 4646558 * 2
def baseEnd_4646558 : Nat := 2385917642994136554155875

theorem tailTrace_4646558 : CollatzResearch.WordTrace tailWord_4646558 prefixEnd_4646558 2385917642994136554155875 := by
  unfold tailWord_4646558
  simp only [CollatzResearch.WordTrace]
  refine ⟨21184236637540176221532541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112982595400214273181506885 21184236637540176221532541)
  ·
    refine ⟨7944088739077566083074703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21184236637540176221532541 7944088739077566083074703)
    ·
      refine ⟨11916133108616349124612055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7944088739077566083074703 11916133108616349124612055)
      ·
        refine ⟨17874199662924523686918083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11916133108616349124612055 17874199662924523686918083)
        ·
          refine ⟨26811299494386785530377125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17874199662924523686918083 26811299494386785530377125)
          ·
            refine ⟨5027118655197522286945711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26811299494386785530377125 5027118655197522286945711)
            ·
              refine ⟨7540677982796283430418567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5027118655197522286945711 7540677982796283430418567)
              ·
                refine ⟨11311016974194425145627851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7540677982796283430418567 11311016974194425145627851)
                ·
                  refine ⟨16966525461291637718441777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11311016974194425145627851 16966525461291637718441777)
                  ·
                    refine ⟨12724894095968728288831333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16966525461291637718441777 12724894095968728288831333)
                    ·
                      refine ⟨2385917642994136554155875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12724894095968728288831333 2385917642994136554155875)
                      ·
                        rfl

theorem cell23_4646558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 1, 1, 1, 2, 4].length) (baseStart_4646558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4646558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4646558 prefixEnd_4646558 := by exact prefixLift 4646558
  have htrace : WordTrace (prefixWord ++ tailWord_4646558) baseStart_4646558 baseEnd_4646558 := by
    simpa [prefixWord, tailWord_4646558, baseEnd_4646558] using wordTrace_append hprefix tailTrace_4646558
  have hstable : (prefixWord ++ tailWord_4646558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4646558).length < 2 ^ (prefixWord ++ tailWord_4646558).sum := by decide
  have hdescent : baseEnd_4646558 < baseStart_4646558 := by decide
  rcases family_descends (prefixWord ++ tailWord_4646558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4646561 : List Nat := [1, 2, 3, 3, 2, 1, 3, 1, 1, 3, 3]
def baseStart_4646561 : Nat := 118140960795 + 4646561 * 2 ^ 59
def prefixEnd_4646561 : Nat := 4983230072969 + 3 ^ 40 * 4646561 * 2
def baseEnd_4646561 : Nat := 2385919183436100042418361

theorem tailTrace_4646561 : CollatzResearch.WordTrace tailWord_4646561 prefixEnd_4646561 2385919183436100042418361 := by
  unfold tailWord_4646561
  simp only [CollatzResearch.WordTrace]
  refine ⟨169474002519310541284619537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112982668346207027523079691 169474002519310541284619537)
  ·
    refine ⟨127105501889482905963464653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169474002519310541284619537 127105501889482905963464653)
    ·
      refine ⟨47664563208556089736299245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 127105501889482905963464653 47664563208556089736299245)
      ·
        refine ⟨17874211203208533651112217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47664563208556089736299245 17874211203208533651112217)
        ·
          refine ⟨13405658402406400238334163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17874211203208533651112217 13405658402406400238334163)
          ·
            refine ⟨20108487603609600357501245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13405658402406400238334163 20108487603609600357501245)
            ·
              refine ⟨7540682851353600134062967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20108487603609600357501245 7540682851353600134062967)
              ·
                refine ⟨11311024277030400201094451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7540682851353600134062967 11311024277030400201094451)
                ·
                  refine ⟨16966536415545600301641677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11311024277030400201094451 16966536415545600301641677)
                  ·
                    refine ⟨6362451155829600113115629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16966536415545600301641677 6362451155829600113115629)
                    ·
                      refine ⟨2385919183436100042418361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6362451155829600113115629 2385919183436100042418361)
                      ·
                        rfl

theorem cell23_4646561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 3, 1, 1, 3, 3].length) (baseStart_4646561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4646561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4646561 prefixEnd_4646561 := by exact prefixLift 4646561
  have htrace : WordTrace (prefixWord ++ tailWord_4646561) baseStart_4646561 baseEnd_4646561 := by
    simpa [prefixWord, tailWord_4646561, baseEnd_4646561] using wordTrace_append hprefix tailTrace_4646561
  have hstable : (prefixWord ++ tailWord_4646561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4646561).length < 2 ^ (prefixWord ++ tailWord_4646561).sum := by decide
  have hdescent : baseEnd_4646561 < baseStart_4646561 := by decide
  rcases family_descends (prefixWord ++ tailWord_4646561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4646568 : List Nat := [2, 1, 7, 1, 1, 1, 1, 9]
def baseStart_4646568 : Nat := 118140960795 + 4646568 * 2 ^ 59
def prefixEnd_4646568 : Nat := 4983230072969 + 3 ^ 40 * 4646568 * 2
def baseEnd_4646568 : Nat := 88367510288914130186327

theorem tailTrace_4646568 : CollatzResearch.WordTrace tailWord_4646568 prefixEnd_4646568 88367510288914130186327 := by
  unfold tailWord_4646568
  simp only [CollatzResearch.WordTrace]
  refine ⟨84737128915142590740062179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112982838553523454320082905 84737128915142590740062179)
  ·
    refine ⟨127105693372713886110093269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84737128915142590740062179 127105693372713886110093269)
    ·
      refine ⟨2979039688422981705705311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 127105693372713886110093269 2979039688422981705705311)
      ·
        refine ⟨4468559532634472558557967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2979039688422981705705311 4468559532634472558557967)
        ·
          refine ⟨6702839298951708837836951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4468559532634472558557967 6702839298951708837836951)
          ·
            refine ⟨10054258948427563256755427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6702839298951708837836951 10054258948427563256755427)
            ·
              refine ⟨15081388422641344885133141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10054258948427563256755427 15081388422641344885133141)
              ·
                refine ⟨88367510288914130186327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15081388422641344885133141 88367510288914130186327)
                ·
                  rfl

theorem cell23_4646568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 9].length) (baseStart_4646568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4646568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4646568 prefixEnd_4646568 := by exact prefixLift 4646568
  have htrace : WordTrace (prefixWord ++ tailWord_4646568) baseStart_4646568 baseEnd_4646568 := by
    simpa [prefixWord, tailWord_4646568, baseEnd_4646568] using wordTrace_append hprefix tailTrace_4646568
  have hstable : (prefixWord ++ tailWord_4646568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4646568).length < 2 ^ (prefixWord ++ tailWord_4646568).sum := by decide
  have hdescent : baseEnd_4646568 < baseStart_4646568 := by decide
  rcases family_descends (prefixWord ++ tailWord_4646568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4646588 : List Nat := [2, 2, 2, 3, 1, 2, 2, 3, 1, 3, 2]
def baseStart_4646588 : Nat := 118140960795 + 4646588 * 2 ^ 59
def prefixEnd_4646588 : Nat := 4983230072969 + 3 ^ 40 * 4646588 * 2
def baseEnd_4646588 : Nat := 2385933047413771436780737

theorem tailTrace_4646588 : CollatzResearch.WordTrace tailWord_4646588 prefixEnd_4646588 2385933047413771436780737 := by
  unfold tailWord_4646588
  simp only [CollatzResearch.WordTrace]
  refine ⟨84737493645106362447926209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112983324860141816597234945 84737493645106362447926209)
  ·
    refine ⟨63553120233829771835944657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84737493645106362447926209 63553120233829771835944657)
    ·
      refine ⟨47664840175372328876958493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63553120233829771835944657 47664840175372328876958493)
      ·
        refine ⟨17874315065764623328859435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47664840175372328876958493 17874315065764623328859435)
        ·
          refine ⟨26811472598646934993289153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17874315065764623328859435 26811472598646934993289153)
          ·
            refine ⟨20108604448985201244966865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26811472598646934993289153 20108604448985201244966865)
            ·
              refine ⟨15081453336738900933725149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20108604448985201244966865 15081453336738900933725149)
              ·
                refine ⟨5655545001277087850146931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15081453336738900933725149 5655545001277087850146931)
                ·
                  refine ⟨8483317501915631775220397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5655545001277087850146931 8483317501915631775220397)
                  ·
                    refine ⟨3181244063218361915707649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8483317501915631775220397 3181244063218361915707649)
                    ·
                      refine ⟨2385933047413771436780737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3181244063218361915707649 2385933047413771436780737)
                      ·
                        rfl

theorem cell23_4646588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 3, 1, 3, 2].length) (baseStart_4646588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4646588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4646588 prefixEnd_4646588 := by exact prefixLift 4646588
  have htrace : WordTrace (prefixWord ++ tailWord_4646588) baseStart_4646588 baseEnd_4646588 := by
    simpa [prefixWord, tailWord_4646588, baseEnd_4646588] using wordTrace_append hprefix tailTrace_4646588
  have hstable : (prefixWord ++ tailWord_4646588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4646588).length < 2 ^ (prefixWord ++ tailWord_4646588).sum := by decide
  have hdescent : baseEnd_4646588 < baseStart_4646588 := by decide
  rcases family_descends (prefixWord ++ tailWord_4646588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4646612 : List Nat := [2, 4, 1, 3, 1, 3, 2, 1, 2, 1, 3]
def baseStart_4646612 : Nat := 118140960795 + 4646612 * 2 ^ 59
def prefixEnd_4646612 : Nat := 4983230072969 + 3 ^ 40 * 4646612 * 2
def baseEnd_4646612 : Nat := 2385945370949479342880627

theorem tailTrace_4646612 : CollatzResearch.WordTrace tailWord_4646612 prefixEnd_4646612 2385945370949479342880627 := by
  unfold tailWord_4646612
  simp only [CollatzResearch.WordTrace]
  refine ⟨84737931321062888497363045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112983908428083851329817393 84737931321062888497363045)
  ·
    refine ⟨15888362122699291593255571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84737931321062888497363045 15888362122699291593255571)
    ·
      refine ⟨23832543184048937389883357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15888362122699291593255571 23832543184048937389883357)
      ·
        refine ⟨8937203694018351521206259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23832543184048937389883357 8937203694018351521206259)
        ·
          refine ⟨13405805541027527281809389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8937203694018351521206259 13405805541027527281809389)
          ·
            refine ⟨5027177077885322730678521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13405805541027527281809389 5027177077885322730678521)
            ·
              refine ⟨3770382808413992048008891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5027177077885322730678521 3770382808413992048008891)
              ·
                refine ⟨5655574212620988072013337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3770382808413992048008891 5655574212620988072013337)
                ·
                  refine ⟨4241680659465741054010003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5655574212620988072013337 4241680659465741054010003)
                  ·
                    refine ⟨6362520989198611581015005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4241680659465741054010003 6362520989198611581015005)
                    ·
                      refine ⟨2385945370949479342880627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6362520989198611581015005 2385945370949479342880627)
                      ·
                        rfl

theorem cell23_4646612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 2, 1, 2, 1, 3].length) (baseStart_4646612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4646612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4646612 prefixEnd_4646612 := by exact prefixLift 4646612
  have htrace : WordTrace (prefixWord ++ tailWord_4646612) baseStart_4646612 baseEnd_4646612 := by
    simpa [prefixWord, tailWord_4646612, baseEnd_4646612] using wordTrace_append hprefix tailTrace_4646612
  have hstable : (prefixWord ++ tailWord_4646612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4646612).length < 2 ^ (prefixWord ++ tailWord_4646612).sum := by decide
  have hdescent : baseEnd_4646612 < baseStart_4646612 := by decide
  rcases family_descends (prefixWord ++ tailWord_4646612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4646658 : List Nat := [3, 4, 1, 1, 1, 1, 3, 4, 5]
def baseStart_4646658 : Nat := 118140960795 + 4646658 * 2 ^ 59
def prefixEnd_4646658 : Nat := 4983230072969 + 3 ^ 40 * 4646658 * 2
def baseEnd_4646658 : Nat := 265107665673287351433935

theorem tailTrace_4646658 : CollatzResearch.WordTrace tailWord_4646658 prefixEnd_4646658 265107665673287351433935 := by
  unfold tailWord_4646658
  simp only [CollatzResearch.WordTrace]
  refine ⟨42369385099989781712725157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112985026933306084567267085 42369385099989781712725157)
  ·
    refine ⟨7944259706248084071135967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42369385099989781712725157 7944259706248084071135967)
    ·
      refine ⟨11916389559372126106703951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7944259706248084071135967 11916389559372126106703951)
      ·
        refine ⟨17874584339058189160055927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11916389559372126106703951 17874584339058189160055927)
        ·
          refine ⟨26811876508587283740083891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17874584339058189160055927 26811876508587283740083891)
          ·
            refine ⟨40217814762880925610125837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26811876508587283740083891 40217814762880925610125837)
            ·
              refine ⟨15081680536080347103797189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40217814762880925610125837 15081680536080347103797189)
              ·
                refine ⟨2827815100515065081961973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15081680536080347103797189 2827815100515065081961973)
                ·
                  refine ⟨265107665673287351433935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2827815100515065081961973 265107665673287351433935)
                  ·
                    rfl

theorem cell23_4646658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 4, 5].length) (baseStart_4646658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4646658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4646658 prefixEnd_4646658 := by exact prefixLift 4646658
  have htrace : WordTrace (prefixWord ++ tailWord_4646658) baseStart_4646658 baseEnd_4646658 := by
    simpa [prefixWord, tailWord_4646658, baseEnd_4646658] using wordTrace_append hprefix tailTrace_4646658
  have hstable : (prefixWord ++ tailWord_4646658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4646658).length < 2 ^ (prefixWord ++ tailWord_4646658).sum := by decide
  have hdescent : baseEnd_4646658 < baseStart_4646658 := by decide
  rcases family_descends (prefixWord ++ tailWord_4646658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4646664 : List Nat := [2, 1, 3, 2, 2, 1, 1, 3, 1, 2, 5]
def baseStart_4646664 : Nat := 118140960795 + 4646664 * 2 ^ 59
def prefixEnd_4646664 : Nat := 4983230072969 + 3 ^ 40 * 4646664 * 2
def baseEnd_4646664 : Nat := 2385972071943513139430387

theorem tailTrace_4646664 : CollatzResearch.WordTrace tailWord_4646664 prefixEnd_4646664 2385972071943513139430387 := by
  unfold tailWord_4646664
  simp only [CollatzResearch.WordTrace]
  refine ⟨84738879618968694937809523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112985172825291593250412697 84738879618968694937809523)
  ·
    refine ⟨127108319428453042406714285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84738879618968694937809523 127108319428453042406714285)
    ·
      refine ⟨47665619785669890902517857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 127108319428453042406714285 47665619785669890902517857)
      ·
        refine ⟨35749214839252418176888393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47665619785669890902517857 35749214839252418176888393)
        ·
          refine ⟨26811911129439313632666295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35749214839252418176888393 26811911129439313632666295)
          ·
            refine ⟨40217866694158970448999443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26811911129439313632666295 40217866694158970448999443)
            ·
              refine ⟨60326800041238455673499165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40217866694158970448999443 60326800041238455673499165)
              ·
                refine ⟨22622550015464420877562187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60326800041238455673499165 22622550015464420877562187)
                ·
                  refine ⟨33933825023196631316343281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22622550015464420877562187 33933825023196631316343281)
                  ·
                    refine ⟨25450368767397473487257461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33933825023196631316343281 25450368767397473487257461)
                    ·
                      refine ⟨2385972071943513139430387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25450368767397473487257461 2385972071943513139430387)
                      ·
                        rfl

theorem cell23_4646664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 3, 1, 2, 5].length) (baseStart_4646664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4646664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4646664 prefixEnd_4646664 := by exact prefixLift 4646664
  have htrace : WordTrace (prefixWord ++ tailWord_4646664) baseStart_4646664 baseEnd_4646664 := by
    simpa [prefixWord, tailWord_4646664, baseEnd_4646664] using wordTrace_append hprefix tailTrace_4646664
  have hstable : (prefixWord ++ tailWord_4646664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4646664).length < 2 ^ (prefixWord ++ tailWord_4646664).sum := by decide
  have hdescent : baseEnd_4646664 < baseStart_4646664 := by decide
  rcases family_descends (prefixWord ++ tailWord_4646664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4646691 : List Nat := [1, 1, 1, 4, 2, 1, 5, 1, 2, 1, 4]
def baseStart_4646691 : Nat := 118140960795 + 4646691 * 2 ^ 59
def prefixEnd_4646691 : Nat := 4983230072969 + 3 ^ 40 * 4646691 * 2
def baseEnd_4646691 : Nat := 2385985935921184533792763

theorem tailTrace_4646691 : CollatzResearch.WordTrace tailWord_4646691 prefixEnd_4646691 2385985935921184533792763 := by
  unfold tailWord_4646691
  simp only [CollatzResearch.WordTrace]
  refine ⟨169478744008839573486851927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112985829339226382324567951 169478744008839573486851927)
  ·
    refine ⟨254218116013259360230277891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169478744008839573486851927 254218116013259360230277891)
    ·
      refine ⟨381327174019889040345416837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 254218116013259360230277891 381327174019889040345416837)
      ·
        refine ⟨71498845128729195064765657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 381327174019889040345416837 71498845128729195064765657)
        ·
          refine ⟨53624133846546896298574243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71498845128729195064765657 53624133846546896298574243)
          ·
            refine ⟨80436200769820344447861365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53624133846546896298574243 80436200769820344447861365)
            ·
              refine ⟨7540893822170657291987003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 80436200769820344447861365 7540893822170657291987003)
              ·
                refine ⟨11311340733255985937980505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7540893822170657291987003 11311340733255985937980505)
                ·
                  refine ⟨8483505549941989453485379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11311340733255985937980505 8483505549941989453485379)
                  ·
                    refine ⟨12725258324912984180228069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8483505549941989453485379 12725258324912984180228069)
                    ·
                      refine ⟨2385985935921184533792763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12725258324912984180228069 2385985935921184533792763)
                      ·
                        rfl

theorem cell23_4646691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 5, 1, 2, 1, 4].length) (baseStart_4646691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4646691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4646691 prefixEnd_4646691 := by exact prefixLift 4646691
  have htrace : WordTrace (prefixWord ++ tailWord_4646691) baseStart_4646691 baseEnd_4646691 := by
    simpa [prefixWord, tailWord_4646691, baseEnd_4646691] using wordTrace_append hprefix tailTrace_4646691
  have hstable : (prefixWord ++ tailWord_4646691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4646691).length < 2 ^ (prefixWord ++ tailWord_4646691).sum := by decide
  have hdescent : baseEnd_4646691 < baseStart_4646691 := by decide
  rcases family_descends (prefixWord ++ tailWord_4646691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4646718 : List Nat := [4, 2, 1, 2, 2, 1, 1, 3, 3, 4]
def baseStart_4646718 : Nat := 118140960795 + 4646718 * 2 ^ 59
def prefixEnd_4646718 : Nat := 4983230072969 + 3 ^ 40 * 4646718 * 2
def baseEnd_4646718 : Nat := 795333266632951976051713

theorem tailTrace_4646718 : CollatzResearch.WordTrace tailWord_4646718 prefixEnd_4646718 795333266632951976051713 := by
  unfold tailWord_4646718
  simp only [CollatzResearch.WordTrace]
  refine ⟨21184966097467719637260601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112986485853161171398723205 21184966097467719637260601)
  ·
    refine ⟨15888724573100789727945451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21184966097467719637260601 15888724573100789727945451)
    ·
      refine ⟨23833086859651184591918177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15888724573100789727945451 23833086859651184591918177)
      ·
        refine ⟨17874815144738388443938633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23833086859651184591918177 17874815144738388443938633)
        ·
          refine ⟨13406111358553791332953975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17874815144738388443938633 13406111358553791332953975)
          ·
            refine ⟨20109167037830686999430963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13406111358553791332953975 20109167037830686999430963)
            ·
              refine ⟨30163750556746030499146445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20109167037830686999430963 30163750556746030499146445)
              ·
                refine ⟨11311406458779761437179917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30163750556746030499146445 11311406458779761437179917)
                ·
                  refine ⟨4241777422042410538942469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11311406458779761437179917 4241777422042410538942469)
                  ·
                    refine ⟨795333266632951976051713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4241777422042410538942469 795333266632951976051713)
                    ·
                      rfl

theorem cell23_4646718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 3, 3, 4].length) (baseStart_4646718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4646718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4646718 prefixEnd_4646718 := by exact prefixLift 4646718
  have htrace : WordTrace (prefixWord ++ tailWord_4646718) baseStart_4646718 baseEnd_4646718 := by
    simpa [prefixWord, tailWord_4646718, baseEnd_4646718] using wordTrace_append hprefix tailTrace_4646718
  have hstable : (prefixWord ++ tailWord_4646718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4646718).length < 2 ^ (prefixWord ++ tailWord_4646718).sum := by decide
  have hdescent : baseEnd_4646718 < baseStart_4646718 := by decide
  rcases family_descends (prefixWord ++ tailWord_4646718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4646781 : List Nat := [1, 4, 1, 1, 2, 1, 1, 4, 3, 1, 4]
def baseStart_4646781 : Nat := 118140960795 + 4646781 * 2 ^ 59
def prefixEnd_4646781 : Nat := 4983230072969 + 3 ^ 40 * 4646781 * 2
def baseEnd_4646781 : Nat := 2386032149180089181667349

theorem tailTrace_4646781 : CollatzResearch.WordTrace tailWord_4646781 prefixEnd_4646781 2386032149180089181667349 := by
  unfold tailWord_4646781
  simp only [CollatzResearch.WordTrace]
  refine ⟨169482026578513518857628197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112988017719009012571752131 169482026578513518857628197)
  ·
    refine ⟨31777879983471284785805287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 169482026578513518857628197 31777879983471284785805287)
    ·
      refine ⟨47666819975206927178707931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31777879983471284785805287 47666819975206927178707931)
      ·
        refine ⟨71500229962810390768061897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47666819975206927178707931 71500229962810390768061897)
        ·
          refine ⟨53625172472107793076046423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71500229962810390768061897 53625172472107793076046423)
          ·
            refine ⟨80437758708161689614069635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53625172472107793076046423 80437758708161689614069635)
            ·
              refine ⟨120656638062242534421104453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80437758708161689614069635 120656638062242534421104453)
              ·
                refine ⟨22623119636670475203957085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 120656638062242534421104453 22623119636670475203957085)
                ·
                  refine ⟨8483669863751428201483907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22623119636670475203957085 8483669863751428201483907)
                  ·
                    refine ⟨12725504795627142302225861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8483669863751428201483907 12725504795627142302225861)
                    ·
                      refine ⟨2386032149180089181667349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12725504795627142302225861 2386032149180089181667349)
                      ·
                        rfl

theorem cell23_4646781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 4, 3, 1, 4].length) (baseStart_4646781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4646781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4646781 prefixEnd_4646781 := by exact prefixLift 4646781
  have htrace : WordTrace (prefixWord ++ tailWord_4646781) baseStart_4646781 baseEnd_4646781 := by
    simpa [prefixWord, tailWord_4646781, baseEnd_4646781] using wordTrace_append hprefix tailTrace_4646781
  have hstable : (prefixWord ++ tailWord_4646781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4646781).length < 2 ^ (prefixWord ++ tailWord_4646781).sum := by decide
  have hdescent : baseEnd_4646781 < baseStart_4646781 := by decide
  rcases family_descends (prefixWord ++ tailWord_4646781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4646782 : List Nat := [4, 2, 3, 1, 1, 3, 2, 1, 6]
def baseStart_4646782 : Nat := 118140960795 + 4646782 * 2 ^ 59
def prefixEnd_4646782 : Nat := 4983230072969 + 3 ^ 40 * 4646782 * 2
def baseEnd_4646782 : Nat := 265114740295638186417205

theorem tailTrace_4646782 : CollatzResearch.WordTrace tailWord_4646782 prefixEnd_4646782 265114740295638186417205 := by
  unfold tailWord_4646782
  simp only [CollatzResearch.WordTrace]
  refine ⟨21185257881438737003551825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112988042034339930685609733 21185257881438737003551825)
  ·
    refine ⟨15888943411079052752663869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21185257881438737003551825 15888943411079052752663869)
    ·
      refine ⟨5958353779154644782248951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15888943411079052752663869 5958353779154644782248951)
      ·
        refine ⟨8937530668731967173373427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5958353779154644782248951 8937530668731967173373427)
        ·
          refine ⟨13406296003097950760060141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8937530668731967173373427 13406296003097950760060141)
          ·
            refine ⟨5027361001161731535022553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13406296003097950760060141 5027361001161731535022553)
            ·
              refine ⟨3770520750871298651266915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5027361001161731535022553 3770520750871298651266915)
              ·
                refine ⟨5655781126306947976900373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3770520750871298651266915 5655781126306947976900373)
                ·
                  refine ⟨265114740295638186417205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5655781126306947976900373 265114740295638186417205)
                  ·
                    rfl

theorem cell23_4646782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 2, 1, 6].length) (baseStart_4646782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4646782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4646782 prefixEnd_4646782 := by exact prefixLift 4646782
  have htrace : WordTrace (prefixWord ++ tailWord_4646782) baseStart_4646782 baseEnd_4646782 := by
    simpa [prefixWord, tailWord_4646782, baseEnd_4646782] using wordTrace_append hprefix tailTrace_4646782
  have hstable : (prefixWord ++ tailWord_4646782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4646782).length < 2 ^ (prefixWord ++ tailWord_4646782).sum := by decide
  have hdescent : baseEnd_4646782 < baseStart_4646782 := by decide
  rcases family_descends (prefixWord ++ tailWord_4646782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4646802 : List Nat := [3, 2, 3, 2, 1, 2, 2, 1, 2, 3, 2]
def baseStart_4646802 : Nat := 118140960795 + 4646802 * 2 ^ 59
def prefixEnd_4646802 : Nat := 4983230072969 + 3 ^ 40 * 4646802 * 2
def baseEnd_4646802 : Nat := 2386042932273833599504753

theorem tailTrace_4646802 : CollatzResearch.WordTrace tailWord_4646802 prefixEnd_4646802 2386042932273833599504753 := by
  unfold tailWord_4646802
  simp only [CollatzResearch.WordTrace]
  refine ⟨42370698127859359861035665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112988528340958292962761773 42370698127859359861035665)
  ·
    refine ⟨31778023595894519895776749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42370698127859359861035665 31778023595894519895776749)
    ·
      refine ⟨11916758848460444960916281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31778023595894519895776749 11916758848460444960916281)
      ·
        refine ⟨8937569136345333720687211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11916758848460444960916281 8937569136345333720687211)
        ·
          refine ⟨13406353704518000581030817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8937569136345333720687211 13406353704518000581030817)
          ·
            refine ⟨10054765278388500435773113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13406353704518000581030817 10054765278388500435773113)
            ·
              refine ⟨7541073958791375326829835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10054765278388500435773113 7541073958791375326829835)
              ·
                refine ⟨11311610938187062990244753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7541073958791375326829835 11311610938187062990244753)
                ·
                  refine ⟨8483708203640297242683565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11311610938187062990244753 8483708203640297242683565)
                  ·
                    refine ⟨3181390576365111466006337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8483708203640297242683565 3181390576365111466006337)
                    ·
                      refine ⟨2386042932273833599504753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3181390576365111466006337 2386042932273833599504753)
                      ·
                        rfl

theorem cell23_4646802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 2, 1, 2, 3, 2].length) (baseStart_4646802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4646802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4646802 prefixEnd_4646802 := by exact prefixLift 4646802
  have htrace : WordTrace (prefixWord ++ tailWord_4646802) baseStart_4646802 baseEnd_4646802 := by
    simpa [prefixWord, tailWord_4646802, baseEnd_4646802] using wordTrace_append hprefix tailTrace_4646802
  have hstable : (prefixWord ++ tailWord_4646802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4646802).length < 2 ^ (prefixWord ++ tailWord_4646802).sum := by decide
  have hdescent : baseEnd_4646802 < baseStart_4646802 := by decide
  rcases family_descends (prefixWord ++ tailWord_4646802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4646831 : List Nat := [1, 1, 2, 1, 2, 2, 3, 2, 3, 3, 3]
def baseStart_4646831 : Nat := 118140960795 + 4646831 * 2 ^ 59
def prefixEnd_4646831 : Nat := 4983230072969 + 3 ^ 40 * 4646831 * 2
def baseEnd_4646831 : Nat := 2386057823212813986042119

theorem tailTrace_4646831 : CollatzResearch.WordTrace tailWord_4646831 prefixEnd_4646831 2386057823212813986042119 := by
  unfold tailWord_4646831
  simp only [CollatzResearch.WordTrace]
  refine ⟨169483850228332377396948347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112989233485554918264632231 169483850228332377396948347)
  ·
    refine ⟨254225775342498566095422521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169483850228332377396948347 254225775342498566095422521)
    ·
      refine ⟨190669331506873924571566891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 254225775342498566095422521 190669331506873924571566891)
      ·
        refine ⟨286003997260310886857350337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190669331506873924571566891 286003997260310886857350337)
        ·
          refine ⟨214502997945233165143012753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 286003997260310886857350337 214502997945233165143012753)
          ·
            refine ⟨160877248458924873857259565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 214502997945233165143012753 160877248458924873857259565)
            ·
              refine ⟨60328968172096827696472337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 160877248458924873857259565 60328968172096827696472337)
              ·
                refine ⟨45246726129072620772354253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60328968172096827696472337 45246726129072620772354253)
                ·
                  refine ⟨16967522298402232789632845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45246726129072620772354253 16967522298402232789632845)
                  ·
                    refine ⟨6362820861900837296112317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16967522298402232789632845 6362820861900837296112317)
                    ·
                      refine ⟨2386057823212813986042119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6362820861900837296112317 2386057823212813986042119)
                      ·
                        rfl

theorem cell23_4646831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 2, 3, 3, 3].length) (baseStart_4646831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4646831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4646831 prefixEnd_4646831 := by exact prefixLift 4646831
  have htrace : WordTrace (prefixWord ++ tailWord_4646831) baseStart_4646831 baseEnd_4646831 := by
    simpa [prefixWord, tailWord_4646831, baseEnd_4646831] using wordTrace_append hprefix tailTrace_4646831
  have hstable : (prefixWord ++ tailWord_4646831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4646831).length < 2 ^ (prefixWord ++ tailWord_4646831).sum := by decide
  have hdescent : baseEnd_4646831 < baseStart_4646831 := by decide
  rcases family_descends (prefixWord ++ tailWord_4646831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4646848 : List Nat := [2, 1, 1, 2, 3, 2, 4, 1, 1, 3, 3]
def baseStart_4646848 : Nat := 118140960795 + 4646848 * 2 ^ 59
def prefixEnd_4646848 : Nat := 4983230072969 + 3 ^ 40 * 4646848 * 2
def baseEnd_4646848 : Nat := 2386066552383940419529541

theorem tailTrace_4646848 : CollatzResearch.WordTrace tailWord_4646848 prefixEnd_4646848 2386066552383940419529541 := by
  unfold tailWord_4646848
  simp only [CollatzResearch.WordTrace]
  refine ⟨84742235134635394650158599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112989646846180526200211465 84742235134635394650158599)
  ·
    refine ⟨127113352701953091975237899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84742235134635394650158599 127113352701953091975237899)
    ·
      refine ⟨190670029052929637962856849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127113352701953091975237899 190670029052929637962856849)
      ·
        refine ⟨143002521789697228472142637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 190670029052929637962856849 143002521789697228472142637)
        ·
          refine ⟨53625945671136460677053489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 143002521789697228472142637 53625945671136460677053489)
          ·
            refine ⟨40219459253352345507790117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53625945671136460677053489 40219459253352345507790117)
            ·
              refine ⟨7541148610003564782710647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40219459253352345507790117 7541148610003564782710647)
              ·
                refine ⟨11311722915005347174065971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7541148610003564782710647 11311722915005347174065971)
                ·
                  refine ⟨16967584372508020761098957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11311722915005347174065971 16967584372508020761098957)
                  ·
                    refine ⟨6362844139690507785412109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16967584372508020761098957 6362844139690507785412109)
                    ·
                      refine ⟨2386066552383940419529541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6362844139690507785412109 2386066552383940419529541)
                      ·
                        rfl

theorem cell23_4646848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 4, 1, 1, 3, 3].length) (baseStart_4646848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4646848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4646848 prefixEnd_4646848 := by exact prefixLift 4646848
  have htrace : WordTrace (prefixWord ++ tailWord_4646848) baseStart_4646848 baseEnd_4646848 := by
    simpa [prefixWord, tailWord_4646848, baseEnd_4646848] using wordTrace_append hprefix tailTrace_4646848
  have hstable : (prefixWord ++ tailWord_4646848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4646848).length < 2 ^ (prefixWord ++ tailWord_4646848).sum := by decide
  have hdescent : baseEnd_4646848 < baseStart_4646848 := by decide
  rcases family_descends (prefixWord ++ tailWord_4646848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4646866 : List Nat := [3, 2, 2, 3, 2, 1, 2, 3, 1, 2, 2]
def baseStart_4646866 : Nat := 118140960795 + 4646866 * 2 ^ 59
def prefixEnd_4646866 : Nat := 4983230072969 + 3 ^ 40 * 4646866 * 2
def baseEnd_4646866 : Nat := 2386075795035721349104459

theorem tailTrace_4646866 : CollatzResearch.WordTrace tailWord_4646866 prefixEnd_4646866 2386075795035721349104459 := by
  unfold tailWord_4646866
  simp only [CollatzResearch.WordTrace]
  refine ⟨42371281695801394593618113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112990084522137052249648301 42371281695801394593618113)
  ·
    refine ⟨31778461271851045945213585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42371281695801394593618113 31778461271851045945213585)
    ·
      refine ⟨23833845953888284458910189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31778461271851045945213585 23833845953888284458910189)
      ·
        refine ⟨8937692232708106672091321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23833845953888284458910189 8937692232708106672091321)
        ·
          refine ⟨6703269174531080004068491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8937692232708106672091321 6703269174531080004068491)
          ·
            refine ⟨10054903761796620006102737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6703269174531080004068491 10054903761796620006102737)
            ·
              refine ⟨7541177821347465004577053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10054903761796620006102737 7541177821347465004577053)
              ·
                refine ⟨2827941683005299376716395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7541177821347465004577053 2827941683005299376716395)
                ·
                  refine ⟨4241912524507949065074593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2827941683005299376716395 4241912524507949065074593)
                  ·
                    refine ⟨3181434393380961798805945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4241912524507949065074593 3181434393380961798805945)
                    ·
                      refine ⟨2386075795035721349104459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3181434393380961798805945 2386075795035721349104459)
                      ·
                        rfl

theorem cell23_4646866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 2, 3, 1, 2, 2].length) (baseStart_4646866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4646866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4646866 prefixEnd_4646866 := by exact prefixLift 4646866
  have htrace : WordTrace (prefixWord ++ tailWord_4646866) baseStart_4646866 baseEnd_4646866 := by
    simpa [prefixWord, tailWord_4646866, baseEnd_4646866] using wordTrace_append hprefix tailTrace_4646866
  have hstable : (prefixWord ++ tailWord_4646866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4646866).length < 2 ^ (prefixWord ++ tailWord_4646866).sum := by decide
  have hdescent : baseEnd_4646866 < baseStart_4646866 := by decide
  rcases family_descends (prefixWord ++ tailWord_4646866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4646876 : List Nat := [2, 2, 6, 1, 1, 2, 1, 2, 2, 4]
def baseStart_4646876 : Nat := 118140960795 + 4646876 * 2 ^ 59
def prefixEnd_4646876 : Nat := 4983230072969 + 3 ^ 40 * 4646876 * 2
def baseEnd_4646876 : Nat := 795360309947422103326471

theorem tailTrace_4646876 : CollatzResearch.WordTrace tailWord_4646876 prefixEnd_4646876 795360309947422103326471 := by
  unfold tailWord_4646876
  simp only [CollatzResearch.WordTrace]
  refine ⟨84742745756584675041168241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112990327675446233388224321 84742745756584675041168241)
  ·
    refine ⟨63557059317438506280876181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84742745756584675041168241 63557059317438506280876181)
    ·
      refine ⟨2979237155504929981916071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 63557059317438506280876181 2979237155504929981916071)
      ·
        refine ⟨4468855733257394972874107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2979237155504929981916071 4468855733257394972874107)
        ·
          refine ⟨6703283599886092459311161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4468855733257394972874107 6703283599886092459311161)
          ·
            refine ⟨5027462699914569344483371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6703283599886092459311161 5027462699914569344483371)
            ·
              refine ⟨7541194049871854016725057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5027462699914569344483371 7541194049871854016725057)
              ·
                refine ⟨5655895537403890512543793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7541194049871854016725057 5655895537403890512543793)
                ·
                  refine ⟨4241921653052917884407845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5655895537403890512543793 4241921653052917884407845)
                  ·
                    refine ⟨795360309947422103326471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4241921653052917884407845 795360309947422103326471)
                    ·
                      rfl

theorem cell23_4646876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_4646876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4646876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4646876 prefixEnd_4646876 := by exact prefixLift 4646876
  have htrace : WordTrace (prefixWord ++ tailWord_4646876) baseStart_4646876 baseEnd_4646876 := by
    simpa [prefixWord, tailWord_4646876, baseEnd_4646876] using wordTrace_append hprefix tailTrace_4646876
  have hstable : (prefixWord ++ tailWord_4646876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4646876).length < 2 ^ (prefixWord ++ tailWord_4646876).sum := by decide
  have hdescent : baseEnd_4646876 < baseStart_4646876 := by decide
  rcases family_descends (prefixWord ++ tailWord_4646876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4646881 : List Nat := [1, 2, 3, 1, 2, 1, 3, 2, 2, 6]
def baseStart_4646881 : Nat := 118140960795 + 4646881 * 2 ^ 59
def prefixEnd_4646881 : Nat := 4983230072969 + 3 ^ 40 * 4646881 * 2
def baseEnd_4646881 : Nat := 795361165748512930138963

theorem tailTrace_4646881 : CollatzResearch.WordTrace tailWord_4646881 prefixEnd_4646881 795361165748512930138963 := by
  unfold tailWord_4646881
  simp only [CollatzResearch.WordTrace]
  refine ⟨169485673878151235936268497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112990449252100823957512331 169485673878151235936268497)
  ·
    refine ⟨127114255408613426952201373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169485673878151235936268497 127114255408613426952201373)
    ·
      refine ⟨47667845778230035107075515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 127114255408613426952201373 47667845778230035107075515)
      ·
        refine ⟨71501768667345052660613273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47667845778230035107075515 71501768667345052660613273)
        ·
          refine ⟨53626326500508789495459955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71501768667345052660613273 53626326500508789495459955)
          ·
            refine ⟨80439489750763184243189933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53626326500508789495459955 80439489750763184243189933)
            ·
              refine ⟨30164808656536194091196225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80439489750763184243189933 30164808656536194091196225)
              ·
                refine ⟨22623606492402145568397169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30164808656536194091196225 22623606492402145568397169)
                ·
                  refine ⟨16967704869301609176297877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22623606492402145568397169 16967704869301609176297877)
                  ·
                    refine ⟨795361165748512930138963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16967704869301609176297877 795361165748512930138963)
                    ·
                      rfl

theorem cell23_4646881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 2, 2, 6].length) (baseStart_4646881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4646881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4646881 prefixEnd_4646881 := by exact prefixLift 4646881
  have htrace : WordTrace (prefixWord ++ tailWord_4646881) baseStart_4646881 baseEnd_4646881 := by
    simpa [prefixWord, tailWord_4646881, baseEnd_4646881] using wordTrace_append hprefix tailTrace_4646881
  have hstable : (prefixWord ++ tailWord_4646881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4646881).length < 2 ^ (prefixWord ++ tailWord_4646881).sum := by decide
  have hdescent : baseEnd_4646881 < baseStart_4646881 := by decide
  rcases family_descends (prefixWord ++ tailWord_4646881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4646891 : List Nat := [1, 1, 1, 1, 2, 3, 1, 3, 1, 6, 3]
def baseStart_4646891 : Nat := 118140960795 + 4646891 * 2 ^ 59
def prefixEnd_4646891 : Nat := 4983230072969 + 3 ^ 40 * 4646891 * 2
def baseEnd_4646891 : Nat := 2386088632052083751291843

theorem tailTrace_4646891 : CollatzResearch.WordTrace tailWord_4646891 prefixEnd_4646891 2386088632052083751291843 := by
  unfold tailWord_4646891
  simp only [CollatzResearch.WordTrace]
  refine ⟨169486038608115007644132527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112990692405410005096088351 169486038608115007644132527)
  ·
    refine ⟨254229057912172511466198791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169486038608115007644132527 254229057912172511466198791)
    ·
      refine ⟨381343586868258767199298187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 254229057912172511466198791 381343586868258767199298187)
      ·
        refine ⟨572015380302388150798947281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 381343586868258767199298187 572015380302388150798947281)
        ·
          refine ⟨429011535226791113099210461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 572015380302388150798947281 429011535226791113099210461)
          ·
            refine ⟨160879325710046667412203923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 429011535226791113099210461 160879325710046667412203923)
            ·
              refine ⟨241318988565070001118305885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 160879325710046667412203923 241318988565070001118305885)
              ·
                refine ⟨90494620711901250419364707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 241318988565070001118305885 90494620711901250419364707)
                ·
                  refine ⟨135741931067851875629047061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 90494620711901250419364707 135741931067851875629047061)
                  ·
                    refine ⟨6362903018805556670111581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 135741931067851875629047061 6362903018805556670111581)
                    ·
                      refine ⟨2386088632052083751291843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6362903018805556670111581 2386088632052083751291843)
                      ·
                        rfl

theorem cell23_4646891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 6, 3].length) (baseStart_4646891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4646891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4646891 prefixEnd_4646891 := by exact prefixLift 4646891
  have htrace : WordTrace (prefixWord ++ tailWord_4646891) baseStart_4646891 baseEnd_4646891 := by
    simpa [prefixWord, tailWord_4646891, baseEnd_4646891] using wordTrace_append hprefix tailTrace_4646891
  have hstable : (prefixWord ++ tailWord_4646891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4646891).length < 2 ^ (prefixWord ++ tailWord_4646891).sum := by decide
  have hdescent : baseEnd_4646891 < baseStart_4646891 := by decide
  rcases family_descends (prefixWord ++ tailWord_4646891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4646905 : List Nat := [1, 2, 1, 3, 1, 4, 3, 1, 1, 4, 2]
def baseStart_4646905 : Nat := 118140960795 + 4646905 * 2 ^ 59
def prefixEnd_4646905 : Nat := 4983230072969 + 3 ^ 40 * 4646905 * 2
def baseEnd_4646905 : Nat := 2386095820781246696516779

theorem tailTrace_4646905 : CollatzResearch.WordTrace tailWord_4646905 prefixEnd_4646905 2386095820781246696516779 := by
  unfold tailWord_4646905
  simp only [CollatzResearch.WordTrace]
  refine ⟨169486549230064288035142169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112991032820042858690094779 169486549230064288035142169)
  ·
    refine ⟨127114911922548216026356627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169486549230064288035142169 127114911922548216026356627)
    ·
      refine ⟨190672367883822324039534941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127114911922548216026356627 190672367883822324039534941)
      ·
        refine ⟨71502137956433371514825603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 190672367883822324039534941 71502137956433371514825603)
        ·
          refine ⟨107253206934650057272238405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71502137956433371514825603 107253206934650057272238405)
          ·
            refine ⟨20109976300246885738544701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 107253206934650057272238405 20109976300246885738544701)
            ·
              refine ⟨7541241112592582151954263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20109976300246885738544701 7541241112592582151954263)
              ·
                refine ⟨11311861668888873227931395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7541241112592582151954263 11311861668888873227931395)
                ·
                  refine ⟨16967792503333309841897093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11311861668888873227931395 16967792503333309841897093)
                  ·
                    refine ⟨3181461094374995595355705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16967792503333309841897093 3181461094374995595355705)
                    ·
                      refine ⟨2386095820781246696516779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3181461094374995595355705 2386095820781246696516779)
                      ·
                        rfl

theorem cell23_4646905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 3, 1, 1, 4, 2].length) (baseStart_4646905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4646905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4646905 prefixEnd_4646905 := by exact prefixLift 4646905
  have htrace : WordTrace (prefixWord ++ tailWord_4646905) baseStart_4646905 baseEnd_4646905 := by
    simpa [prefixWord, tailWord_4646905, baseEnd_4646905] using wordTrace_append hprefix tailTrace_4646905
  have hstable : (prefixWord ++ tailWord_4646905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4646905).length < 2 ^ (prefixWord ++ tailWord_4646905).sum := by decide
  have hdescent : baseEnd_4646905 < baseStart_4646905 := by decide
  rcases family_descends (prefixWord ++ tailWord_4646905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4646945 : List Nat := [1, 2, 3, 2, 4, 2, 1, 1, 7]
def baseStart_4646945 : Nat := 118140960795 + 4646945 * 2 ^ 59
def prefixEnd_4646945 : Nat := 4983230072969 + 3 ^ 40 * 4646945 * 2
def baseEnd_4646945 : Nat := 265124040000825171112955

theorem tailTrace_4646945 : CollatzResearch.WordTrace tailWord_4646945 prefixEnd_4646945 265124040000825171112955 := by
  unfold tailWord_4646945
  simp only [CollatzResearch.WordTrace]
  refine ⟨169488008149919374866598289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112992005433279583244398859 169488008149919374866598289)
  ·
    refine ⟨127116006112439531149948717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169488008149919374866598289 127116006112439531149948717)
    ·
      refine ⟨47668502292164824181230769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 127116006112439531149948717 47668502292164824181230769)
      ·
        refine ⟨35751376719123618135923077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47668502292164824181230769 35751376719123618135923077)
        ·
          refine ⟨6703383134835678400485577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35751376719123618135923077 6703383134835678400485577)
          ·
            refine ⟨5027537351126758800364183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6703383134835678400485577 5027537351126758800364183)
            ·
              refine ⟨7541306026690138200546275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5027537351126758800364183 7541306026690138200546275)
              ·
                refine ⟨11311959040035207300819413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7541306026690138200546275 11311959040035207300819413)
                ·
                  refine ⟨265124040000825171112955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11311959040035207300819413 265124040000825171112955)
                  ·
                    rfl

theorem cell23_4646945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 1, 1, 7].length) (baseStart_4646945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4646945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4646945 prefixEnd_4646945 := by exact prefixLift 4646945
  have htrace : WordTrace (prefixWord ++ tailWord_4646945) baseStart_4646945 baseEnd_4646945 := by
    simpa [prefixWord, tailWord_4646945, baseEnd_4646945] using wordTrace_append hprefix tailTrace_4646945
  have hstable : (prefixWord ++ tailWord_4646945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4646945).length < 2 ^ (prefixWord ++ tailWord_4646945).sum := by decide
  have hdescent : baseEnd_4646945 < baseStart_4646945 := by decide
  rcases family_descends (prefixWord ++ tailWord_4646945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4646991 : List Nat := [1, 1, 2, 1, 1, 2, 2, 3, 1, 3, 6]
def baseStart_4646991 : Nat := 118140960795 + 4646991 * 2 ^ 59
def prefixEnd_4646991 : Nat := 4983230072969 + 3 ^ 40 * 4646991 * 2
def baseEnd_4646991 : Nat := 2386139980117533360041383

theorem tailTrace_4646991 : CollatzResearch.WordTrace tailWord_4646991 prefixEnd_4646991 2386139980117533360041383 := by
  unfold tailWord_4646991
  simp only [CollatzResearch.WordTrace]
  refine ⟨169489685907752724722772827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112993123938501816481848551 169489685907752724722772827)
  ·
    refine ⟨254234528861629087084159241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169489685907752724722772827 254234528861629087084159241)
    ·
      refine ⟨190675896646221815313119431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 254234528861629087084159241 190675896646221815313119431)
      ·
        refine ⟨286013844969332722969679147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190675896646221815313119431 286013844969332722969679147)
        ·
          refine ⟨429020767453999084454518721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 286013844969332722969679147 429020767453999084454518721)
          ·
            refine ⟨321765575590499313340889041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 429020767453999084454518721 321765575590499313340889041)
            ·
              refine ⟨241324181692874485005666781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 321765575590499313340889041 241324181692874485005666781)
              ·
                refine ⟨90496568134827931877125043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 241324181692874485005666781 90496568134827931877125043)
                ·
                  refine ⟨135744852202241897815687565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 90496568134827931877125043 135744852202241897815687565)
                  ·
                    refine ⟨50904319575840711680882837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 135744852202241897815687565 50904319575840711680882837)
                    ·
                      refine ⟨2386139980117533360041383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50904319575840711680882837 2386139980117533360041383)
                      ·
                        rfl

theorem cell23_4646991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 3, 6].length) (baseStart_4646991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4646991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4646991 prefixEnd_4646991 := by exact prefixLift 4646991
  have htrace : WordTrace (prefixWord ++ tailWord_4646991) baseStart_4646991 baseEnd_4646991 := by
    simpa [prefixWord, tailWord_4646991, baseEnd_4646991] using wordTrace_append hprefix tailTrace_4646991
  have hstable : (prefixWord ++ tailWord_4646991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4646991).length < 2 ^ (prefixWord ++ tailWord_4646991).sum := by decide
  have hdescent : baseEnd_4646991 < baseStart_4646991 := by decide
  rcases family_descends (prefixWord ++ tailWord_4646991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4647095 : List Nat := [1, 1, 3, 1, 4, 2, 1, 2, 4, 4]
def baseStart_4647095 : Nat := 118140960795 + 4647095 * 2 ^ 59
def prefixEnd_4647095 : Nat := 4983230072969 + 3 ^ 40 * 4647095 * 2
def baseEnd_4647095 : Nat := 795397794035200317713635

theorem tailTrace_4647095 : CollatzResearch.WordTrace tailWord_4647095 prefixEnd_4647095 795397794035200317713635 := by
  unfold tailWord_4647095
  simp only [CollatzResearch.WordTrace]
  refine ⟨169493479099375950484558739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112995652732917300323039159 169493479099375950484558739)
  ·
    refine ⟨254240218649063925726838109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169493479099375950484558739 254240218649063925726838109)
    ·
      refine ⟨95340081993398972147564291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 254240218649063925726838109 95340081993398972147564291)
      ·
        refine ⟨143010122990098458221346437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95340081993398972147564291 143010122990098458221346437)
        ·
          refine ⟨26814398060643460916502457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 143010122990098458221346437 26814398060643460916502457)
          ·
            refine ⟨20110798545482595687376843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26814398060643460916502457 20110798545482595687376843)
            ·
              refine ⟨30166197818223893531065265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20110798545482595687376843 30166197818223893531065265)
              ·
                refine ⟨22624648363667920148298949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30166197818223893531065265 22624648363667920148298949)
                ·
                  refine ⟨4242121568187735027806053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22624648363667920148298949 4242121568187735027806053)
                  ·
                    refine ⟨795397794035200317713635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4242121568187735027806053 795397794035200317713635)
                    ·
                      rfl

theorem cell23_4647095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 2, 4, 4].length) (baseStart_4647095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4647095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4647095 prefixEnd_4647095 := by exact prefixLift 4647095
  have htrace : WordTrace (prefixWord ++ tailWord_4647095) baseStart_4647095 baseEnd_4647095 := by
    simpa [prefixWord, tailWord_4647095, baseEnd_4647095] using wordTrace_append hprefix tailTrace_4647095
  have hstable : (prefixWord ++ tailWord_4647095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4647095).length < 2 ^ (prefixWord ++ tailWord_4647095).sum := by decide
  have hdescent : baseEnd_4647095 < baseStart_4647095 := by decide
  rcases family_descends (prefixWord ++ tailWord_4647095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4647106 : List Nat := [3, 5, 1, 1, 1, 1, 1, 1, 4, 3, 2]
def baseStart_4647106 : Nat := 118140960795 + 4647106 * 2 ^ 59
def prefixEnd_4647106 : Nat := 4983230072969 + 3 ^ 40 * 4647106 * 2
def baseEnd_4647106 : Nat := 2386199030392800410103355

theorem tailTrace_4647106 : CollatzResearch.WordTrace tailWord_4647106 prefixEnd_4647106 2386199030392800410103355 := by
  unfold tailWord_4647106
  simp only [CollatzResearch.WordTrace]
  refine ⟨42373470075584024840802293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112995920201557399575472781 42373470075584024840802293)
  ·
    refine ⟨3972512819586002328825215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 42373470075584024840802293 3972512819586002328825215)
    ·
      refine ⟨5958769229379003493237823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3972512819586002328825215 5958769229379003493237823)
      ·
        refine ⟨8938153844068505239856735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5958769229379003493237823 8938153844068505239856735)
        ·
          refine ⟨13407230766102757859785103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8938153844068505239856735 13407230766102757859785103)
          ·
            refine ⟨20110846149154136789677655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13407230766102757859785103 20110846149154136789677655)
            ·
              refine ⟨30166269223731205184516483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20110846149154136789677655 30166269223731205184516483)
              ·
                refine ⟨45249403835596807776774725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30166269223731205184516483 45249403835596807776774725)
                ·
                  refine ⟨8484263219174401458145261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45249403835596807776774725 8484263219174401458145261)
                  ·
                    refine ⟨3181598707190400546804473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8484263219174401458145261 3181598707190400546804473)
                    ·
                      refine ⟨2386199030392800410103355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3181598707190400546804473 2386199030392800410103355)
                      ·
                        rfl

theorem cell23_4647106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 1, 4, 3, 2].length) (baseStart_4647106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4647106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4647106 prefixEnd_4647106 := by exact prefixLift 4647106
  have htrace : WordTrace (prefixWord ++ tailWord_4647106) baseStart_4647106 baseEnd_4647106 := by
    simpa [prefixWord, tailWord_4647106, baseEnd_4647106] using wordTrace_append hprefix tailTrace_4647106
  have hstable : (prefixWord ++ tailWord_4647106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4647106).length < 2 ^ (prefixWord ++ tailWord_4647106).sum := by decide
  have hdescent : baseEnd_4647106 < baseStart_4647106 := by decide
  rcases family_descends (prefixWord ++ tailWord_4647106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4647135 : List Nat := [1, 1, 2, 3, 2, 1, 1, 5, 1, 3, 3]
def baseStart_4647135 : Nat := 118140960795 + 4647135 * 2 ^ 59
def prefixEnd_4647135 : Nat := 4983230072969 + 3 ^ 40 * 4647135 * 2
def baseEnd_4647135 : Nat := 2386213921331780796640721

theorem tailTrace_4647135 : CollatzResearch.WordTrace tailWord_4647135 prefixEnd_4647135 2386213921331780796640721 := by
  unfold tailWord_4647135
  simp only [CollatzResearch.WordTrace]
  refine ⟨169494938019231037316014859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112996625346154024877343239 169494938019231037316014859)
  ·
    refine ⟨254242407028846555974022289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169494938019231037316014859 254242407028846555974022289)
    ·
      refine ⟨190681805271634916980516717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 254242407028846555974022289 190681805271634916980516717)
      ·
        refine ⟨71505676976863093867693769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 190681805271634916980516717 71505676976863093867693769)
        ·
          refine ⟨53629257732647320400770327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71505676976863093867693769 53629257732647320400770327)
          ·
            refine ⟨80443886598970980601155491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53629257732647320400770327 80443886598970980601155491)
            ·
              refine ⟨120665829898456470901733237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80443886598970980601155491 120665829898456470901733237)
              ·
                refine ⟨11312421552980294147037491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 120665829898456470901733237 11312421552980294147037491)
                ·
                  refine ⟨16968632329470441220556237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11312421552980294147037491 16968632329470441220556237)
                  ·
                    refine ⟨6363237123551415457708589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16968632329470441220556237 6363237123551415457708589)
                    ·
                      refine ⟨2386213921331780796640721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6363237123551415457708589 2386213921331780796640721)
                      ·
                        rfl

theorem cell23_4647135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 5, 1, 3, 3].length) (baseStart_4647135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4647135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4647135 prefixEnd_4647135 := by exact prefixLift 4647135
  have htrace : WordTrace (prefixWord ++ tailWord_4647135) baseStart_4647135 baseEnd_4647135 := by
    simpa [prefixWord, tailWord_4647135, baseEnd_4647135] using wordTrace_append hprefix tailTrace_4647135
  have hstable : (prefixWord ++ tailWord_4647135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4647135).length < 2 ^ (prefixWord ++ tailWord_4647135).sum := by decide
  have hdescent : baseEnd_4647135 < baseStart_4647135 := by decide
  rcases family_descends (prefixWord ++ tailWord_4647135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4647139 : List Nat := [1, 1, 1, 8, 1, 1, 1, 1, 3, 2, 3]
def baseStart_4647139 : Nat := 118140960795 + 4647139 * 2 ^ 59
def prefixEnd_4647139 : Nat := 4983230072969 + 3 ^ 40 * 4647139 * 2
def baseEnd_4647139 : Nat := 2386215975254398780990703

theorem tailTrace_4647139 : CollatzResearch.WordTrace tailWord_4647139 prefixEnd_4647139 2386215975254398780990703 := by
  unfold tailWord_4647139
  simp only [CollatzResearch.WordTrace]
  refine ⟨169495083911216545999160471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112996722607477697332773647 169495083911216545999160471)
  ·
    refine ⟨254242625866824818998740707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169495083911216545999160471 254242625866824818998740707)
    ·
      refine ⟨381363938800237228498111061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 254242625866824818998740707 381363938800237228498111061)
      ·
        refine ⟨4469108657815280021462239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 381363938800237228498111061 4469108657815280021462239)
        ·
          refine ⟨6703662986722920032193359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4469108657815280021462239 6703662986722920032193359)
          ·
            refine ⟨10055494480084380048290039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6703662986722920032193359 10055494480084380048290039)
            ·
              refine ⟨15083241720126570072435059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10055494480084380048290039 15083241720126570072435059)
              ·
                refine ⟨22624862580189855108652589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15083241720126570072435059 22624862580189855108652589)
                ·
                  refine ⟨8484323467571195665744721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22624862580189855108652589 8484323467571195665744721)
                  ·
                    refine ⟨6363242600678396749308541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8484323467571195665744721 6363242600678396749308541)
                    ·
                      refine ⟨2386215975254398780990703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6363242600678396749308541 2386215975254398780990703)
                      ·
                        rfl

theorem cell23_4647139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_4647139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4647139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4647139 prefixEnd_4647139 := by exact prefixLift 4647139
  have htrace : WordTrace (prefixWord ++ tailWord_4647139) baseStart_4647139 baseEnd_4647139 := by
    simpa [prefixWord, tailWord_4647139, baseEnd_4647139] using wordTrace_append hprefix tailTrace_4647139
  have hstable : (prefixWord ++ tailWord_4647139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4647139).length < 2 ^ (prefixWord ++ tailWord_4647139).sum := by decide
  have hdescent : baseEnd_4647139 < baseStart_4647139 := by decide
  rcases family_descends (prefixWord ++ tailWord_4647139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4647145 : List Nat := [1, 2, 1, 1, 1, 2, 2, 2, 2, 7, 2]
def baseStart_4647145 : Nat := 118140960795 + 4647145 * 2 ^ 59
def prefixEnd_4647145 : Nat := 4983230072969 + 3 ^ 40 * 4647145 * 2
def baseEnd_4647145 : Nat := 2386219056138325757515675

theorem tailTrace_4647145 : CollatzResearch.WordTrace tailWord_4647145 prefixEnd_4647145 2386219056138325757515675 := by
  unfold tailWord_4647145
  simp only [CollatzResearch.WordTrace]
  refine ⟨169495302749194809023878889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112996868499463206015919259 169495302749194809023878889)
  ·
    refine ⟨127121477061896106767909167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169495302749194809023878889 127121477061896106767909167)
    ·
      refine ⟨190682215592844160151863751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127121477061896106767909167 190682215592844160151863751)
      ·
        refine ⟨286023323389266240227795627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190682215592844160151863751 286023323389266240227795627)
        ·
          refine ⟨429034985083899360341693441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 286023323389266240227795627 429034985083899360341693441)
          ·
            refine ⟨321776238812924520256270081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 429034985083899360341693441 321776238812924520256270081)
            ·
              refine ⟨241332179109693390192202561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 321776238812924520256270081 241332179109693390192202561)
              ·
                refine ⟨180999134332270042644151921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 241332179109693390192202561 180999134332270042644151921)
                ·
                  refine ⟨135749350749202531983113941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 180999134332270042644151921 135749350749202531983113941)
                  ·
                    refine ⟨3181625408184434343354233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 135749350749202531983113941 3181625408184434343354233)
                    ·
                      refine ⟨2386219056138325757515675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3181625408184434343354233 2386219056138325757515675)
                      ·
                        rfl

theorem cell23_4647145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 7, 2].length) (baseStart_4647145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4647145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4647145 prefixEnd_4647145 := by exact prefixLift 4647145
  have htrace : WordTrace (prefixWord ++ tailWord_4647145) baseStart_4647145 baseEnd_4647145 := by
    simpa [prefixWord, tailWord_4647145, baseEnd_4647145] using wordTrace_append hprefix tailTrace_4647145
  have hstable : (prefixWord ++ tailWord_4647145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4647145).length < 2 ^ (prefixWord ++ tailWord_4647145).sum := by decide
  have hdescent : baseEnd_4647145 < baseStart_4647145 := by decide
  rcases family_descends (prefixWord ++ tailWord_4647145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4647169 : List Nat := [1, 2, 4, 1, 1, 2, 4, 2, 2, 1, 3]
def baseStart_4647169 : Nat := 118140960795 + 4647169 * 2 ^ 59
def prefixEnd_4647169 : Nat := 4983230072969 + 3 ^ 40 * 4647169 * 2
def baseEnd_4647169 : Nat := 2386231379674033663615565

theorem tailTrace_4647169 : CollatzResearch.WordTrace tailWord_4647169 prefixEnd_4647169 2386231379674033663615565 := by
  unfold tailWord_4647169
  simp only [CollatzResearch.WordTrace]
  refine ⟨169496178101107861122752561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112997452067405240748501707 169496178101107861122752561)
  ·
    refine ⟨127122133575830895842064421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169496178101107861122752561 127122133575830895842064421)
    ·
      refine ⟨23835400045468292970387079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 127122133575830895842064421 23835400045468292970387079)
      ·
        refine ⟨35753100068202439455580619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23835400045468292970387079 35753100068202439455580619)
        ·
          refine ⟨53629650102303659183370929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35753100068202439455580619 53629650102303659183370929)
          ·
            refine ⟨40222237576727744387528197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53629650102303659183370929 40222237576727744387528197)
            ·
              refine ⟨7541669545636452072661537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40222237576727744387528197 7541669545636452072661537)
              ·
                refine ⟨5656252159227339054496153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7541669545636452072661537 5656252159227339054496153)
                ·
                  refine ⟨4242189119420504290872115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5656252159227339054496153 4242189119420504290872115)
                  ·
                    refine ⟨6363283679130756436308173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4242189119420504290872115 6363283679130756436308173)
                    ·
                      refine ⟨2386231379674033663615565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6363283679130756436308173 2386231379674033663615565)
                      ·
                        rfl

theorem cell23_4647169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 4, 2, 2, 1, 3].length) (baseStart_4647169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4647169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4647169 prefixEnd_4647169 := by exact prefixLift 4647169
  have htrace : WordTrace (prefixWord ++ tailWord_4647169) baseStart_4647169 baseEnd_4647169 := by
    simpa [prefixWord, tailWord_4647169, baseEnd_4647169] using wordTrace_append hprefix tailTrace_4647169
  have hstable : (prefixWord ++ tailWord_4647169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4647169).length < 2 ^ (prefixWord ++ tailWord_4647169).sum := by decide
  have hdescent : baseEnd_4647169 < baseStart_4647169 := by decide
  rcases family_descends (prefixWord ++ tailWord_4647169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4647170 : List Nat := [3, 4, 1, 1, 2, 1, 4, 2, 1, 2, 2]
def baseStart_4647170 : Nat := 118140960795 + 4647170 * 2 ^ 59
def prefixEnd_4647170 : Nat := 4983230072969 + 3 ^ 40 * 4647170 * 2
def baseEnd_4647170 : Nat := 2386231893154688159703061

theorem tailTrace_4647170 : CollatzResearch.WordTrace tailWord_4647170 prefixEnd_4647170 2386231893154688159703061 := by
  unfold tailWord_4647170
  simp only [CollatzResearch.WordTrace]
  refine ⟨42374053643526059573384741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112997476382736158862359309 42374053643526059573384741)
  ·
    refine ⟨7945135058161136170009639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42374053643526059573384741 7945135058161136170009639)
    ·
      refine ⟨11917702587241704255014459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7945135058161136170009639 11917702587241704255014459)
      ·
        refine ⟨17876553880862556382521689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11917702587241704255014459 17876553880862556382521689)
        ·
          refine ⟨13407415410646917286891267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17876553880862556382521689 13407415410646917286891267)
          ·
            refine ⟨20111123115970375930336901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13407415410646917286891267 20111123115970375930336901)
            ·
              refine ⟨3770835584244445486938169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20111123115970375930336901 3770835584244445486938169)
              ·
                refine ⟨2828126688183334115203627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3770835584244445486938169 2828126688183334115203627)
                ·
                  refine ⟨4242190032275001172805441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2828126688183334115203627 4242190032275001172805441)
                  ·
                    refine ⟨3181642524206250879604081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4242190032275001172805441 3181642524206250879604081)
                    ·
                      refine ⟨2386231893154688159703061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3181642524206250879604081 2386231893154688159703061)
                      ·
                        rfl

theorem cell23_4647170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 4, 2, 1, 2, 2].length) (baseStart_4647170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4647170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4647170 prefixEnd_4647170 := by exact prefixLift 4647170
  have htrace : WordTrace (prefixWord ++ tailWord_4647170) baseStart_4647170 baseEnd_4647170 := by
    simpa [prefixWord, tailWord_4647170, baseEnd_4647170] using wordTrace_append hprefix tailTrace_4647170
  have hstable : (prefixWord ++ tailWord_4647170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4647170).length < 2 ^ (prefixWord ++ tailWord_4647170).sum := by decide
  have hdescent : baseEnd_4647170 < baseStart_4647170 := by decide
  rcases family_descends (prefixWord ++ tailWord_4647170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4647185 : List Nat := [1, 2, 2, 1, 1, 6, 1, 1, 2, 6]
def baseStart_4647185 : Nat := 118140960795 + 4647185 * 2 ^ 59
def prefixEnd_4647185 : Nat := 4983230072969 + 3 ^ 40 * 4647185 * 2
def baseEnd_4647185 : Nat := 795413198454835200338497

theorem tailTrace_4647185 : CollatzResearch.WordTrace tailWord_4647185 prefixEnd_4647185 795413198454835200338497 := by
  unfold tailWord_4647185
  simp only [CollatzResearch.WordTrace]
  refine ⟨169496761669049895855335009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112997841112699930570223339 169496761669049895855335009)
  ·
    refine ⟨127122571251787421891501257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169496761669049895855335009 127122571251787421891501257)
    ·
      refine ⟨95341928438840566418625943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127122571251787421891501257 95341928438840566418625943)
      ·
        refine ⟨143012892658260849627938915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95341928438840566418625943 143012892658260849627938915)
        ·
          refine ⟨214519338987391274441908373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143012892658260849627938915 214519338987391274441908373)
          ·
            refine ⟨10055594015033965989464455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 214519338987391274441908373 10055594015033965989464455)
            ·
              refine ⟨15083391022550948984196683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10055594015033965989464455 15083391022550948984196683)
              ·
                refine ⟨22625086533826423476295025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15083391022550948984196683 22625086533826423476295025)
                ·
                  refine ⟨16968814900369817607221269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22625086533826423476295025 16968814900369817607221269)
                  ·
                    refine ⟨795413198454835200338497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16968814900369817607221269 795413198454835200338497)
                    ·
                      rfl

theorem cell23_4647185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 6].length) (baseStart_4647185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4647185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4647185 prefixEnd_4647185 := by exact prefixLift 4647185
  have htrace : WordTrace (prefixWord ++ tailWord_4647185) baseStart_4647185 baseEnd_4647185 := by
    simpa [prefixWord, tailWord_4647185, baseEnd_4647185] using wordTrace_append hprefix tailTrace_4647185
  have hstable : (prefixWord ++ tailWord_4647185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4647185).length < 2 ^ (prefixWord ++ tailWord_4647185).sum := by decide
  have hdescent : baseEnd_4647185 < baseStart_4647185 := by decide
  rcases family_descends (prefixWord ++ tailWord_4647185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4647207 : List Nat := [1, 1, 8, 1, 2, 1, 2, 1, 1, 2, 3]
def baseStart_4647207 : Nat := 118140960795 + 4647207 * 2 ^ 59
def prefixEnd_4647207 : Nat := 4983230072969 + 3 ^ 40 * 4647207 * 2
def baseEnd_4647207 : Nat := 2386250891938904514940391

theorem tailTrace_4647207 : CollatzResearch.WordTrace tailWord_4647207 prefixEnd_4647207 2386250891938904514940391 := by
  unfold tailWord_4647207
  simp only [CollatzResearch.WordTrace]
  refine ⟨169497564074970193612635875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112998376049980129075090583 169497564074970193612635875)
  ·
    refine ⟨254246346112455290418953813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169497564074970193612635875 254246346112455290418953813)
    ·
      refine ⟨2979449368505335434597115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 254246346112455290418953813 2979449368505335434597115)
      ·
        refine ⟨4469174052758003151895673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2979449368505335434597115 4469174052758003151895673)
        ·
          refine ⟨3351880539568502363921755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4469174052758003151895673 3351880539568502363921755)
          ·
            refine ⟨5027820809352753545882633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3351880539568502363921755 5027820809352753545882633)
            ·
              refine ⟨3770865607014565159411975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5027820809352753545882633 3770865607014565159411975)
              ·
                refine ⟨5656298410521847739117963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3770865607014565159411975 5656298410521847739117963)
                ·
                  refine ⟨8484447615782771608676945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5656298410521847739117963 8484447615782771608676945)
                  ·
                    refine ⟨6363335711837078706507709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8484447615782771608676945 6363335711837078706507709)
                    ·
                      refine ⟨2386250891938904514940391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6363335711837078706507709 2386250891938904514940391)
                      ·
                        rfl

theorem cell23_4647207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_4647207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4647207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4647207 prefixEnd_4647207 := by exact prefixLift 4647207
  have htrace : WordTrace (prefixWord ++ tailWord_4647207) baseStart_4647207 baseEnd_4647207 := by
    simpa [prefixWord, tailWord_4647207, baseEnd_4647207] using wordTrace_append hprefix tailTrace_4647207
  have hstable : (prefixWord ++ tailWord_4647207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4647207).length < 2 ^ (prefixWord ++ tailWord_4647207).sum := by decide
  have hdescent : baseEnd_4647207 < baseStart_4647207 := by decide
  rcases family_descends (prefixWord ++ tailWord_4647207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4647213 : List Nat := [1, 5, 3, 1, 2, 1, 1, 3, 1, 3, 2]
def baseStart_4647213 : Nat := 118140960795 + 4647213 * 2 ^ 59
def prefixEnd_4647213 : Nat := 4983230072969 + 3 ^ 40 * 4647213 * 2
def baseEnd_4647213 : Nat := 2386253972822831491465363

theorem tailTrace_4647213 : CollatzResearch.WordTrace tailWord_4647213 prefixEnd_4647213 2386253972822831491465363 := by
  unfold tailWord_4647213
  simp only [CollatzResearch.WordTrace]
  refine ⟨169497782912948456637354293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112998521941965637758236195 169497782912948456637354293)
  ·
    refine ⟨15890417148088917809751965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 169497782912948456637354293 15890417148088917809751965)
    ·
      refine ⟨5958906430533344178656987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15890417148088917809751965 5958906430533344178656987)
      ·
        refine ⟨8938359645800016267985481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5958906430533344178656987 8938359645800016267985481)
        ·
          refine ⟨6703769734350012200989111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8938359645800016267985481 6703769734350012200989111)
          ·
            refine ⟨10055654601525018301483667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6703769734350012200989111 10055654601525018301483667)
            ·
              refine ⟨15083481902287527452225501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10055654601525018301483667 15083481902287527452225501)
              ·
                refine ⟨5656305713357822794584563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15083481902287527452225501 5656305713357822794584563)
                ·
                  refine ⟨8484458570036734191876845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5656305713357822794584563 8484458570036734191876845)
                  ·
                    refine ⟨3181671963763775321953817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8484458570036734191876845 3181671963763775321953817)
                    ·
                      refine ⟨2386253972822831491465363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3181671963763775321953817 2386253972822831491465363)
                      ·
                        rfl

theorem cell23_4647213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 3, 1, 3, 2].length) (baseStart_4647213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4647213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4647213 prefixEnd_4647213 := by exact prefixLift 4647213
  have htrace : WordTrace (prefixWord ++ tailWord_4647213) baseStart_4647213 baseEnd_4647213 := by
    simpa [prefixWord, tailWord_4647213, baseEnd_4647213] using wordTrace_append hprefix tailTrace_4647213
  have hstable : (prefixWord ++ tailWord_4647213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4647213).length < 2 ^ (prefixWord ++ tailWord_4647213).sum := by decide
  have hdescent : baseEnd_4647213 < baseStart_4647213 := by decide
  rcases family_descends (prefixWord ++ tailWord_4647213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4647226 : List Nat := [3, 1, 1, 1, 4, 2, 3, 2, 2, 2, 2]
def baseStart_4647226 : Nat := 118140960795 + 4647226 * 2 ^ 59
def prefixEnd_4647226 : Nat := 4983230072969 + 3 ^ 40 * 4647226 * 2
def baseEnd_4647226 : Nat := 2386260648071339940602803

theorem tailTrace_4647226 : CollatzResearch.WordTrace tailWord_4647226 prefixEnd_4647226 2386260648071339940602803 := by
  unfold tailWord_4647226
  simp only [CollatzResearch.WordTrace]
  refine ⟨42374564265475339964394383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112998838041267573238385021 42374564265475339964394383)
  ·
    refine ⟨63561846398213009946591575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42374564265475339964394383 63561846398213009946591575)
    ·
      refine ⟨95342769597319514919887363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63561846398213009946591575 95342769597319514919887363)
      ·
        refine ⟨143014154395979272379831045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95342769597319514919887363 143014154395979272379831045)
        ·
          refine ⟨26815153949246113571218321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 143014154395979272379831045 26815153949246113571218321)
          ·
            refine ⟨20111365461934585178413741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26815153949246113571218321 20111365461934585178413741)
            ·
              refine ⟨7541762048225469441905153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20111365461934585178413741 7541762048225469441905153)
              ·
                refine ⟨5656321536169102081428865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7541762048225469441905153 5656321536169102081428865)
                ·
                  refine ⟨4242241152126826561071649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5656321536169102081428865 4242241152126826561071649)
                  ·
                    refine ⟨3181680864095119920803737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4242241152126826561071649 3181680864095119920803737)
                    ·
                      refine ⟨2386260648071339940602803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3181680864095119920803737 2386260648071339940602803)
                      ·
                        rfl

theorem cell23_4647226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 3, 2, 2, 2, 2].length) (baseStart_4647226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4647226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4647226 prefixEnd_4647226 := by exact prefixLift 4647226
  have htrace : WordTrace (prefixWord ++ tailWord_4647226) baseStart_4647226 baseEnd_4647226 := by
    simpa [prefixWord, tailWord_4647226, baseEnd_4647226] using wordTrace_append hprefix tailTrace_4647226
  have hstable : (prefixWord ++ tailWord_4647226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4647226).length < 2 ^ (prefixWord ++ tailWord_4647226).sum := by decide
  have hdescent : baseEnd_4647226 < baseStart_4647226 := by decide
  rcases family_descends (prefixWord ++ tailWord_4647226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4647266 : List Nat := [3, 3, 2, 1, 1, 4, 1, 3, 5]
def baseStart_4647266 : Nat := 118140960795 + 4647266 * 2 ^ 59
def prefixEnd_4647266 : Nat := 4983230072969 + 3 ^ 40 * 4647266 * 2
def baseEnd_4647266 : Nat := 265142354144168864900291

theorem tailTrace_4647266 : CollatzResearch.WordTrace tailWord_4647266 prefixEnd_4647266 265142354144168864900291 := by
  unfold tailWord_4647266
  simp only [CollatzResearch.WordTrace]
  refine ⟨42374928995439111672258413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112999810654504297792689101 42374928995439111672258413)
  ·
    refine ⟨15890598373289666877096905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42374928995439111672258413 15890598373289666877096905)
    ·
      refine ⟨11917948779967250157822679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15890598373289666877096905 11917948779967250157822679)
      ·
        refine ⟨17876923169950875236734019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11917948779967250157822679 17876923169950875236734019)
        ·
          refine ⟨26815384754926312855101029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17876923169950875236734019 26815384754926312855101029)
          ·
            refine ⟨5027884641548683660331443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26815384754926312855101029 5027884641548683660331443)
            ·
              refine ⟨7541826962323025490497165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5027884641548683660331443 7541826962323025490497165)
              ·
                refine ⟨2828185110871134558936437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7541826962323025490497165 2828185110871134558936437)
                ·
                  refine ⟨265142354144168864900291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2828185110871134558936437 265142354144168864900291)
                  ·
                    rfl

theorem cell23_4647266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 1, 3, 5].length) (baseStart_4647266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4647266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4647266 prefixEnd_4647266 := by exact prefixLift 4647266
  have htrace : WordTrace (prefixWord ++ tailWord_4647266) baseStart_4647266 baseEnd_4647266 := by
    simpa [prefixWord, tailWord_4647266, baseEnd_4647266] using wordTrace_append hprefix tailTrace_4647266
  have hstable : (prefixWord ++ tailWord_4647266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4647266).length < 2 ^ (prefixWord ++ tailWord_4647266).sum := by decide
  have hdescent : baseEnd_4647266 < baseStart_4647266 := by decide
  rcases family_descends (prefixWord ++ tailWord_4647266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4647282 : List Nat := [3, 2, 1, 2, 1, 3, 1, 1, 4, 1, 4]
def baseStart_4647282 : Nat := 118140960795 + 4647282 * 2 ^ 59
def prefixEnd_4647282 : Nat := 4983230072969 + 3 ^ 40 * 4647282 * 2
def baseEnd_4647282 : Nat := 2386289402987991721502545

theorem tailTrace_4647282 : CollatzResearch.WordTrace tailWord_4647282 prefixEnd_4647282 2386289402987991721502545 := by
  unfold tailWord_4647282
  simp only [CollatzResearch.WordTrace]
  refine ⟨42375074887424620355404025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113000199699798987614410733 42375074887424620355404025)
  ·
    refine ⟨31781306165568465266553019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42375074887424620355404025 31781306165568465266553019)
    ·
      refine ⟨47671959248352697899829529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31781306165568465266553019 47671959248352697899829529)
      ·
        refine ⟨35753969436264523424872147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47671959248352697899829529 35753969436264523424872147)
        ·
          refine ⟨53630954154396785137308221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35753969436264523424872147 53630954154396785137308221)
          ·
            refine ⟨20111607807898794426490583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53630954154396785137308221 20111607807898794426490583)
            ·
              refine ⟨30167411711848191639735875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20111607807898794426490583 30167411711848191639735875)
              ·
                refine ⟨45251117567772287459603813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30167411711848191639735875 45251117567772287459603813)
                ·
                  refine ⟨8484584543957303898675715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45251117567772287459603813 8484584543957303898675715)
                  ·
                    refine ⟨12726876815935955848013573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8484584543957303898675715 12726876815935955848013573)
                    ·
                      refine ⟨2386289402987991721502545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12726876815935955848013573 2386289402987991721502545)
                      ·
                        rfl

theorem cell23_4647282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 1, 4, 1, 4].length) (baseStart_4647282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4647282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4647282 prefixEnd_4647282 := by exact prefixLift 4647282
  have htrace : WordTrace (prefixWord ++ tailWord_4647282) baseStart_4647282 baseEnd_4647282 := by
    simpa [prefixWord, tailWord_4647282, baseEnd_4647282] using wordTrace_append hprefix tailTrace_4647282
  have hstable : (prefixWord ++ tailWord_4647282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4647282).length < 2 ^ (prefixWord ++ tailWord_4647282).sum := by decide
  have hdescent : baseEnd_4647282 < baseStart_4647282 := by decide
  rcases family_descends (prefixWord ++ tailWord_4647282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4647292 : List Nat := [2, 2, 2, 1, 1, 1, 2, 5, 3, 4]
def baseStart_4647292 : Nat := 118140960795 + 4647292 * 2 ^ 59
def prefixEnd_4647292 : Nat := 4983230072969 + 3 ^ 40 * 4647292 * 2
def baseEnd_4647292 : Nat := 795431512598178894125833

theorem tailTrace_4647292 : CollatzResearch.WordTrace tailWord_4647292 prefixEnd_4647292 795431512598178894125833 := by
  unfold tailWord_4647292
  simp only [CollatzResearch.WordTrace]
  refine ⟨84750332139831126564740065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113000442853108168752986753 84750332139831126564740065)
  ·
    refine ⟨63562749104873344923555049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84750332139831126564740065 63562749104873344923555049)
    ·
      refine ⟨47672061828655008692666287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63562749104873344923555049 47672061828655008692666287)
      ·
        refine ⟨71508092742982513038999431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47672061828655008692666287 71508092742982513038999431)
        ·
          refine ⟨107262139114473769558499147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71508092742982513038999431 107262139114473769558499147)
          ·
            refine ⟨160893208671710654337748721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107262139114473769558499147 160893208671710654337748721)
            ·
              refine ⟨120669906503782990753311541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 160893208671710654337748721 120669906503782990753311541)
              ·
                refine ⟨11312803734729655383122957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 120669906503782990753311541 11312803734729655383122957)
                ·
                  refine ⟨4242301400523620768671109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11312803734729655383122957 4242301400523620768671109)
                  ·
                    refine ⟨795431512598178894125833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4242301400523620768671109 795431512598178894125833)
                    ·
                      rfl

theorem cell23_4647292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 5, 3, 4].length) (baseStart_4647292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4647292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4647292 prefixEnd_4647292 := by exact prefixLift 4647292
  have htrace : WordTrace (prefixWord ++ tailWord_4647292) baseStart_4647292 baseEnd_4647292 := by
    simpa [prefixWord, tailWord_4647292, baseEnd_4647292] using wordTrace_append hprefix tailTrace_4647292
  have hstable : (prefixWord ++ tailWord_4647292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4647292).length < 2 ^ (prefixWord ++ tailWord_4647292).sum := by decide
  have hdescent : baseEnd_4647292 < baseStart_4647292 := by decide
  rcases family_descends (prefixWord ++ tailWord_4647292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4647316 : List Nat := [2, 4, 2, 1, 3, 1, 2, 1, 2, 1, 4]
def baseStart_4647316 : Nat := 118140960795 + 4647316 * 2 ^ 59
def prefixEnd_4647316 : Nat := 4983230072969 + 3 ^ 40 * 4647316 * 2
def baseEnd_4647316 : Nat := 2386306861330244588477389

theorem tailTrace_4647316 : CollatzResearch.WordTrace tailWord_4647316 prefixEnd_4647316 2386306861330244588477389 := by
  unfold tailWord_4647316
  simp only [CollatzResearch.WordTrace]
  refine ⟨84750769815787652614176901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113001026421050203485569201 84750769815787652614176901)
  ·
    refine ⟨15890769340460184865158169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84750769815787652614176901 15890769340460184865158169)
    ·
      refine ⟨11918077005345138648868627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15890769340460184865158169 11918077005345138648868627)
      ·
        refine ⟨17877115508017707973302941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11918077005345138648868627 17877115508017707973302941)
        ·
          refine ⟨6703918315506640489988603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17877115508017707973302941 6703918315506640489988603)
          ·
            refine ⟨10055877473259960734982905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6703918315506640489988603 10055877473259960734982905)
            ·
              refine ⟨7541908104944970551237179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10055877473259960734982905 7541908104944970551237179)
              ·
                refine ⟨11312862157417455826855769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7541908104944970551237179 11312862157417455826855769)
                ·
                  refine ⟨8484646618063091870141827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11312862157417455826855769 8484646618063091870141827)
                  ·
                    refine ⟨12726969927094637805212741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8484646618063091870141827 12726969927094637805212741)
                    ·
                      refine ⟨2386306861330244588477389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12726969927094637805212741 2386306861330244588477389)
                      ·
                        rfl

theorem cell23_4647316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 2, 1, 2, 1, 4].length) (baseStart_4647316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4647316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4647316 prefixEnd_4647316 := by exact prefixLift 4647316
  have htrace : WordTrace (prefixWord ++ tailWord_4647316) baseStart_4647316 baseEnd_4647316 := by
    simpa [prefixWord, tailWord_4647316, baseEnd_4647316] using wordTrace_append hprefix tailTrace_4647316
  have hstable : (prefixWord ++ tailWord_4647316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4647316).length < 2 ^ (prefixWord ++ tailWord_4647316).sum := by decide
  have hdescent : baseEnd_4647316 < baseStart_4647316 := by decide
  rcases family_descends (prefixWord ++ tailWord_4647316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4647336 : List Nat := [2, 1, 6, 1, 1, 1, 2, 2, 2, 2, 3]
def baseStart_4647336 : Nat := 118140960795 + 4647336 * 2 ^ 59
def prefixEnd_4647336 : Nat := 4983230072969 + 3 ^ 40 * 4647336 * 2
def baseEnd_4647336 : Nat := 2386317130943334510227297

theorem tailTrace_4647336 : CollatzResearch.WordTrace tailWord_4647336 prefixEnd_4647336 2386317130943334510227297 := by
  unfold tailWord_4647336
  simp only [CollatzResearch.WordTrace]
  refine ⟨84751134545751424322040931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113001512727668565762721241 84751134545751424322040931)
  ·
    refine ⟨127126701818627136483061397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84751134545751424322040931 127126701818627136483061397)
    ·
      refine ⟨5959064147748147022643503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 127126701818627136483061397 5959064147748147022643503)
      ·
        refine ⟨8938596221622220533965255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5959064147748147022643503 8938596221622220533965255)
        ·
          refine ⟨13407894332433330800947883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8938596221622220533965255 13407894332433330800947883)
          ·
            refine ⟨20111841498649996201421825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13407894332433330800947883 20111841498649996201421825)
            ·
              refine ⟨15083881123987497151066369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20111841498649996201421825 15083881123987497151066369)
              ·
                refine ⟨11312910842990622863299777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15083881123987497151066369 11312910842990622863299777)
                ·
                  refine ⟨8484683132242967147474833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11312910842990622863299777 8484683132242967147474833)
                  ·
                    refine ⟨6363512349182225360606125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8484683132242967147474833 6363512349182225360606125)
                    ·
                      refine ⟨2386317130943334510227297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6363512349182225360606125 2386317130943334510227297)
                      ·
                        rfl

theorem cell23_4647336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_4647336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4647336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4647336 prefixEnd_4647336 := by exact prefixLift 4647336
  have htrace : WordTrace (prefixWord ++ tailWord_4647336) baseStart_4647336 baseEnd_4647336 := by
    simpa [prefixWord, tailWord_4647336, baseEnd_4647336] using wordTrace_append hprefix tailTrace_4647336
  have hstable : (prefixWord ++ tailWord_4647336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4647336).length < 2 ^ (prefixWord ++ tailWord_4647336).sum := by decide
  have hdescent : baseEnd_4647336 < baseStart_4647336 := by decide
  rcases family_descends (prefixWord ++ tailWord_4647336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4647392 : List Nat := [2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 5]
def baseStart_4647392 : Nat := 118140960795 + 4647392 * 2 ^ 59
def prefixEnd_4647392 : Nat := 4983230072969 + 3 ^ 40 * 4647392 * 2
def baseEnd_4647392 : Nat := 2386345885859986291127039

theorem tailTrace_4647392 : CollatzResearch.WordTrace tailWord_4647392 prefixEnd_4647392 2386345885859986291127039 := by
  unfold tailWord_4647392
  simp only [CollatzResearch.WordTrace]
  refine ⟨84752155789649985104060215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113002874386199980138746953 84752155789649985104060215)
  ·
    refine ⟨127128233684474977656090323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84752155789649985104060215 127128233684474977656090323)
    ·
      refine ⟨190692350526712466484135485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127128233684474977656090323 190692350526712466484135485)
      ·
        refine ⟨71509631447517174931550807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 190692350526712466484135485 71509631447517174931550807)
        ·
          refine ⟨107264447171275762397326211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71509631447517174931550807 107264447171275762397326211)
          ·
            refine ⟨160896670756913643595989317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107264447171275762397326211 160896670756913643595989317)
            ·
              refine ⟨30168125766921308174247997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 160896670756913643595989317 30168125766921308174247997)
              ·
                refine ⟨11313047162595490565342999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30168125766921308174247997 11313047162595490565342999)
                ·
                  refine ⟨16969570743893235848014499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11313047162595490565342999 16969570743893235848014499)
                  ·
                    refine ⟨25454356115839853772021749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16969570743893235848014499 25454356115839853772021749)
                    ·
                      refine ⟨2386345885859986291127039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25454356115839853772021749 2386345885859986291127039)
                      ·
                        rfl

theorem cell23_4647392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 5].length) (baseStart_4647392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4647392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4647392 prefixEnd_4647392 := by exact prefixLift 4647392
  have htrace : WordTrace (prefixWord ++ tailWord_4647392) baseStart_4647392 baseEnd_4647392 := by
    simpa [prefixWord, tailWord_4647392, baseEnd_4647392] using wordTrace_append hprefix tailTrace_4647392
  have hstable : (prefixWord ++ tailWord_4647392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4647392).length < 2 ^ (prefixWord ++ tailWord_4647392).sum := by decide
  have hdescent : baseEnd_4647392 < baseStart_4647392 := by decide
  rcases family_descends (prefixWord ++ tailWord_4647392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4647399 : List Nat := [1, 1, 5, 2, 1, 1, 3, 1, 4, 4]
def baseStart_4647399 : Nat := 118140960795 + 4647399 * 2 ^ 59
def prefixEnd_4647399 : Nat := 4983230072969 + 3 ^ 40 * 4647399 * 2
def baseEnd_4647399 : Nat := 795449826741522587913169

theorem tailTrace_4647399 : CollatzResearch.WordTrace tailWord_4647399 prefixEnd_4647399 795449826741522587913169 := by
  unfold tailWord_4647399
  simp only [CollatzResearch.WordTrace]
  refine ⟨169504566890274610403625251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113003044593516406935750167 169504566890274610403625251)
  ·
    refine ⟨254256850335411915605437877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169504566890274610403625251 254256850335411915605437877)
    ·
      refine ⟨23836579718944867088009801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 254256850335411915605437877 23836579718944867088009801)
      ·
        refine ⟨17877434789208650316007351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23836579718944867088009801 17877434789208650316007351)
        ·
          refine ⟨26816152183812975474011027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17877434789208650316007351 26816152183812975474011027)
          ·
            refine ⟨40224228275719463211016541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26816152183812975474011027 40224228275719463211016541)
            ·
              refine ⟨15084085603394798704131203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40224228275719463211016541 15084085603394798704131203)
              ·
                refine ⟨22626128405092198056196805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15084085603394798704131203 22626128405092198056196805)
                ·
                  refine ⟨4242399075954787135536901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22626128405092198056196805 4242399075954787135536901)
                  ·
                    refine ⟨795449826741522587913169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4242399075954787135536901 795449826741522587913169)
                    ·
                      rfl

theorem cell23_4647399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 1, 4, 4].length) (baseStart_4647399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4647399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4647399 prefixEnd_4647399 := by exact prefixLift 4647399
  have htrace : WordTrace (prefixWord ++ tailWord_4647399) baseStart_4647399 baseEnd_4647399 := by
    simpa [prefixWord, tailWord_4647399, baseEnd_4647399] using wordTrace_append hprefix tailTrace_4647399
  have hstable : (prefixWord ++ tailWord_4647399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4647399).length < 2 ^ (prefixWord ++ tailWord_4647399).sum := by decide
  have hdescent : baseEnd_4647399 < baseStart_4647399 := by decide
  rcases family_descends (prefixWord ++ tailWord_4647399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4647416 : List Nat := [2, 1, 2, 1, 1, 4, 5, 1, 2, 4]
def baseStart_4647416 : Nat := 118140960795 + 4647416 * 2 ^ 59
def prefixEnd_4647416 : Nat := 4983230072969 + 3 ^ 40 * 4647416 * 2
def baseEnd_4647416 : Nat := 795452736465231399075643

theorem tailTrace_4647416 : CollatzResearch.WordTrace tailWord_4647416 prefixEnd_4647416 795452736465231399075643 := by
  unfold tailWord_4647416
  simp only [CollatzResearch.WordTrace]
  refine ⟨84752593465606511153497051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113003457954142014871329401 84752593465606511153497051)
  ·
    refine ⟨127128890198409766730245577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84752593465606511153497051 127128890198409766730245577)
    ·
      refine ⟨95346667648807325047684183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127128890198409766730245577 95346667648807325047684183)
      ·
        refine ⟨143020001473210987571526275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95346667648807325047684183 143020001473210987571526275)
        ·
          refine ⟨214530002209816481357289413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143020001473210987571526275 214530002209816481357289413)
          ·
            refine ⟨40224375414340590254491765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 214530002209816481357289413 40224375414340590254491765)
            ·
              refine ⟨3771035195094430336358603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40224375414340590254491765 3771035195094430336358603)
              ·
                refine ⟨5656552792641645504537905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3771035195094430336358603 5656552792641645504537905)
                ·
                  refine ⟨4242414594481234128403429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5656552792641645504537905 4242414594481234128403429)
                  ·
                    refine ⟨795452736465231399075643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4242414594481234128403429 795452736465231399075643)
                    ·
                      rfl

theorem cell23_4647416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 5, 1, 2, 4].length) (baseStart_4647416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4647416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4647416 prefixEnd_4647416 := by exact prefixLift 4647416
  have htrace : WordTrace (prefixWord ++ tailWord_4647416) baseStart_4647416 baseEnd_4647416 := by
    simpa [prefixWord, tailWord_4647416, baseEnd_4647416] using wordTrace_append hprefix tailTrace_4647416
  have hstable : (prefixWord ++ tailWord_4647416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4647416).length < 2 ^ (prefixWord ++ tailWord_4647416).sum := by decide
  have hdescent : baseEnd_4647416 < baseStart_4647416 := by decide
  rcases family_descends (prefixWord ++ tailWord_4647416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4647439 : List Nat := [1, 1, 2, 1, 1, 1, 2, 6, 4, 1, 3]
def baseStart_4647439 : Nat := 118140960795 + 4647439 * 2 ^ 59
def prefixEnd_4647439 : Nat := 4983230072969 + 3 ^ 40 * 4647439 * 2
def baseEnd_4647439 : Nat := 2386370019450747607239323

theorem tailTrace_4647439 : CollatzResearch.WordTrace tailWord_4647439 prefixEnd_4647439 2386370019450747607239323 := by
  unfold tailWord_4647439
  simp only [CollatzResearch.WordTrace]
  refine ⟨169506025810129697235081371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113004017206753131490054247 169506025810129697235081371)
  ·
    refine ⟨254259038715194545852622057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169506025810129697235081371 254259038715194545852622057)
    ·
      refine ⟨190694279036395909389466543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 254259038715194545852622057 190694279036395909389466543)
      ·
        refine ⟨286041418554593864084199815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190694279036395909389466543 286041418554593864084199815)
        ·
          refine ⟨429062127831890796126299723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 286041418554593864084199815 429062127831890796126299723)
          ·
            refine ⟨643593191747836194189449585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 429062127831890796126299723 643593191747836194189449585)
            ·
              refine ⟨482694893810877145642087189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 643593191747836194189449585 482694893810877145642087189)
              ·
                refine ⟨22626323147384866201972837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 482694893810877145642087189 22626323147384866201972837)
                ·
                  refine ⟨4242435590134662412869907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22626323147384866201972837 4242435590134662412869907)
                  ·
                    refine ⟨6363653385201993619304861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4242435590134662412869907 6363653385201993619304861)
                    ·
                      refine ⟨2386370019450747607239323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6363653385201993619304861 2386370019450747607239323)
                      ·
                        rfl

theorem cell23_4647439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 6, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 6, 4, 1, 3].length) (baseStart_4647439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4647439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4647439 prefixEnd_4647439 := by exact prefixLift 4647439
  have htrace : WordTrace (prefixWord ++ tailWord_4647439) baseStart_4647439 baseEnd_4647439 := by
    simpa [prefixWord, tailWord_4647439, baseEnd_4647439] using wordTrace_append hprefix tailTrace_4647439
  have hstable : (prefixWord ++ tailWord_4647439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4647439).length < 2 ^ (prefixWord ++ tailWord_4647439).sum := by decide
  have hdescent : baseEnd_4647439 < baseStart_4647439 := by decide
  rcases family_descends (prefixWord ++ tailWord_4647439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4647472 : List Nat := [2, 1, 1, 1, 2, 3, 2, 3, 2, 6]
def baseStart_4647472 : Nat := 118140960795 + 4647472 * 2 ^ 59
def prefixEnd_4647472 : Nat := 4983230072969 + 3 ^ 40 * 4647472 * 2
def baseEnd_4647472 : Nat := 795462321437448659375557

theorem tailTrace_4647472 : CollatzResearch.WordTrace tailWord_4647472 prefixEnd_4647472 795462321437448659375557 := by
  unfold tailWord_4647472
  simp only [CollatzResearch.WordTrace]
  refine ⟨84753614709505071935516335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113004819612673429247355113 84753614709505071935516335)
  ·
    refine ⟨127130422064257607903274503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84753614709505071935516335 127130422064257607903274503)
    ·
      refine ⟨190695633096386411854911755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127130422064257607903274503 190695633096386411854911755)
      ·
        refine ⟨286043449644579617782367633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190695633096386411854911755 286043449644579617782367633)
        ·
          refine ⟨214532587233434713336775725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 286043449644579617782367633 214532587233434713336775725)
          ·
            refine ⟨80449720212538017501290897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 214532587233434713336775725 80449720212538017501290897)
            ·
              refine ⟨60337290159403513125968173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80449720212538017501290897 60337290159403513125968173)
              ·
                refine ⟨22626483809776317422238065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60337290159403513125968173 22626483809776317422238065)
                ·
                  refine ⟨16969862857332238066678549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22626483809776317422238065 16969862857332238066678549)
                  ·
                    refine ⟨795462321437448659375557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16969862857332238066678549 795462321437448659375557)
                    ·
                      rfl

theorem cell23_4647472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 3, 2, 6].length) (baseStart_4647472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4647472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4647472 prefixEnd_4647472 := by exact prefixLift 4647472
  have htrace : WordTrace (prefixWord ++ tailWord_4647472) baseStart_4647472 baseEnd_4647472 := by
    simpa [prefixWord, tailWord_4647472, baseEnd_4647472] using wordTrace_append hprefix tailTrace_4647472
  have hstable : (prefixWord ++ tailWord_4647472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4647472).length < 2 ^ (prefixWord ++ tailWord_4647472).sum := by decide
  have hdescent : baseEnd_4647472 < baseStart_4647472 := by decide
  rcases family_descends (prefixWord ++ tailWord_4647472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4647473 : List Nat := [1, 2, 2, 3, 1, 1, 6, 1, 2, 1, 3]
def baseStart_4647473 : Nat := 118140960795 + 4647473 * 2 ^ 59
def prefixEnd_4647473 : Nat := 4983230072969 + 3 ^ 40 * 4647473 * 2
def baseEnd_4647473 : Nat := 2386387477793000474214167

theorem tailTrace_4647473 : CollatzResearch.WordTrace tailWord_4647473 prefixEnd_4647473 2386387477793000474214167 := by
  unfold tailWord_4647473
  simp only [CollatzResearch.WordTrace]
  refine ⟨169507265892006521041819073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113004843928004347361212715 169507265892006521041819073)
  ·
    refine ⟨127130449419004890781364305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169507265892006521041819073 127130449419004890781364305)
    ·
      refine ⟨95347837064253668086023229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127130449419004890781364305 95347837064253668086023229)
      ·
        refine ⟨35755438899095125532258711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95347837064253668086023229 35755438899095125532258711)
        ·
          refine ⟨53633158348642688298388067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35755438899095125532258711 53633158348642688298388067)
          ·
            refine ⟨80449737522964032447582101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53633158348642688298388067 80449737522964032447582101)
            ·
              refine ⟨3771081446388939020980411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 80449737522964032447582101 3771081446388939020980411)
              ·
                refine ⟨5656622169583408531470617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3771081446388939020980411 5656622169583408531470617)
                ·
                  refine ⟨4242466627187556398602963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5656622169583408531470617 4242466627187556398602963)
                  ·
                    refine ⟨6363699940781334597904445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4242466627187556398602963 6363699940781334597904445)
                    ·
                      refine ⟨2386387477793000474214167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6363699940781334597904445 2386387477793000474214167)
                      ·
                        rfl

theorem cell23_4647473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 6, 1, 2, 1, 3].length) (baseStart_4647473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4647473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4647473 prefixEnd_4647473 := by exact prefixLift 4647473
  have htrace : WordTrace (prefixWord ++ tailWord_4647473) baseStart_4647473 baseEnd_4647473 := by
    simpa [prefixWord, tailWord_4647473, baseEnd_4647473] using wordTrace_append hprefix tailTrace_4647473
  have hstable : (prefixWord ++ tailWord_4647473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4647473).length < 2 ^ (prefixWord ++ tailWord_4647473).sum := by decide
  have hdescent : baseEnd_4647473 < baseStart_4647473 := by decide
  rcases family_descends (prefixWord ++ tailWord_4647473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4647496 : List Nat := [2, 1, 3, 1, 1, 1, 1, 3, 6, 2, 2]
def baseStart_4647496 : Nat := 118140960795 + 4647496 * 2 ^ 59
def prefixEnd_4647496 : Nat := 4983230072969 + 3 ^ 40 * 4647496 * 2
def baseEnd_4647496 : Nat := 2386399287848053884226561

theorem tailTrace_4647496 : CollatzResearch.WordTrace tailWord_4647496 prefixEnd_4647496 2386399287848053884226561 := by
  unfold tailWord_4647496
  simp only [CollatzResearch.WordTrace]
  refine ⟨84754052385461597984953171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113005403180615463979937561 84754052385461597984953171)
  ·
    refine ⟨127131078578192396977429757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84754052385461597984953171 127131078578192396977429757)
    ·
      refine ⟨47674154466822148866536159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 127131078578192396977429757 47674154466822148866536159)
      ·
        refine ⟨71511231700233223299804239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47674154466822148866536159 71511231700233223299804239)
        ·
          refine ⟨107266847550349834949706359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71511231700233223299804239 107266847550349834949706359)
          ·
            refine ⟨160900271325524752424559539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107266847550349834949706359 160900271325524752424559539)
            ·
              refine ⟨241350406988287128636839309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 160900271325524752424559539 241350406988287128636839309)
              ·
                refine ⟨90506402620607673238814741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 241350406988287128636839309 90506402620607673238814741)
                ·
                  refine ⟨4242487622840984683069441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 90506402620607673238814741 4242487622840984683069441)
                  ·
                    refine ⟨3181865717130738512302081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4242487622840984683069441 3181865717130738512302081)
                    ·
                      refine ⟨2386399287848053884226561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3181865717130738512302081 2386399287848053884226561)
                      ·
                        rfl

theorem cell23_4647496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 6, 2, 2].length) (baseStart_4647496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4647496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4647496 prefixEnd_4647496 := by exact prefixLift 4647496
  have htrace : WordTrace (prefixWord ++ tailWord_4647496) baseStart_4647496 baseEnd_4647496 := by
    simpa [prefixWord, tailWord_4647496, baseEnd_4647496] using wordTrace_append hprefix tailTrace_4647496
  have hstable : (prefixWord ++ tailWord_4647496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4647496).length < 2 ^ (prefixWord ++ tailWord_4647496).sum := by decide
  have hdescent : baseEnd_4647496 < baseStart_4647496 := by decide
  rcases family_descends (prefixWord ++ tailWord_4647496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4647512 : List Nat := [2, 1, 2, 2, 1, 2, 2, 1, 1, 2, 7]
def baseStart_4647512 : Nat := 118140960795 + 4647512 * 2 ^ 59
def prefixEnd_4647512 : Nat := 4983230072969 + 3 ^ 40 * 4647512 * 2
def baseEnd_4647512 : Nat := 2386407503538525821626487

theorem tailTrace_4647512 : CollatzResearch.WordTrace tailWord_4647512 prefixEnd_4647512 2386407503538525821626487 := by
  unfold tailWord_4647512
  simp only [CollatzResearch.WordTrace]
  refine ⟨84754344169432615351244395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113005792225910153801659193 84754344169432615351244395)
  ·
    refine ⟨127131516254148923026866593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84754344169432615351244395 127131516254148923026866593)
    ·
      refine ⟨95348637190611692270149945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127131516254148923026866593 95348637190611692270149945)
      ·
        refine ⟨71511477892958769202612459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95348637190611692270149945 71511477892958769202612459)
        ·
          refine ⟨107267216839438153803918689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71511477892958769202612459 107267216839438153803918689)
          ·
            refine ⟨80450412629578615352939017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107267216839438153803918689 80450412629578615352939017)
            ·
              refine ⟨60337809472183961514704263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80450412629578615352939017 60337809472183961514704263)
              ·
                refine ⟨90506714208275942272056395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60337809472183961514704263 90506714208275942272056395)
                ·
                  refine ⟨135760071312413913408084593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 90506714208275942272056395 135760071312413913408084593)
                  ·
                    refine ⟨101820053484310435056063445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 135760071312413913408084593 101820053484310435056063445)
                    ·
                      refine ⟨2386407503538525821626487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 101820053484310435056063445 2386407503538525821626487)
                      ·
                        rfl

theorem cell23_4647512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 1, 2, 7].length) (baseStart_4647512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4647512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4647512 prefixEnd_4647512 := by exact prefixLift 4647512
  have htrace : WordTrace (prefixWord ++ tailWord_4647512) baseStart_4647512 baseEnd_4647512 := by
    simpa [prefixWord, tailWord_4647512, baseEnd_4647512] using wordTrace_append hprefix tailTrace_4647512
  have hstable : (prefixWord ++ tailWord_4647512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4647512).length < 2 ^ (prefixWord ++ tailWord_4647512).sum := by decide
  have hdescent : baseEnd_4647512 < baseStart_4647512 := by decide
  rcases family_descends (prefixWord ++ tailWord_4647512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4647663 : List Nat := [1, 1, 2, 1, 5, 2, 1, 3, 2, 3, 2]
def baseStart_4647663 : Nat := 118140960795 + 4647663 * 2 ^ 59
def prefixEnd_4647663 : Nat := 4983230072969 + 3 ^ 40 * 4647663 * 2
def baseEnd_4647663 : Nat := 2386485039117354730838293

theorem tailTrace_4647663 : CollatzResearch.WordTrace tailWord_4647663 prefixEnd_4647663 2386485039117354730838293 := by
  unfold tailWord_4647663
  simp only [CollatzResearch.WordTrace]
  refine ⟨169514195761318183491235643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113009463840878788994157095 169514195761318183491235643)
  ·
    refine ⟨254271293641977275236853465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169514195761318183491235643 254271293641977275236853465)
    ·
      refine ⟨190703470231482956427640099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 254271293641977275236853465 190703470231482956427640099)
      ·
        refine ⟨286055205347224434641460149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190703470231482956427640099 286055205347224434641460149)
        ·
          refine ⟨26817675501302290747636889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 286055205347224434641460149 26817675501302290747636889)
          ·
            refine ⟨20113256625976718060727667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26817675501302290747636889 20113256625976718060727667)
            ·
              refine ⟨30169884938965077091091501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20113256625976718060727667 30169884938965077091091501)
              ·
                refine ⟨11313706852111903909159313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30169884938965077091091501 11313706852111903909159313)
                ·
                  refine ⟨8485280139083927931869485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11313706852111903909159313 8485280139083927931869485)
                  ·
                    refine ⟨3181980052156472974451057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8485280139083927931869485 3181980052156472974451057)
                    ·
                      refine ⟨2386485039117354730838293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3181980052156472974451057 2386485039117354730838293)
                      ·
                        rfl

theorem cell23_4647663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 3, 2, 3, 2].length) (baseStart_4647663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4647663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4647663 prefixEnd_4647663 := by exact prefixLift 4647663
  have htrace : WordTrace (prefixWord ++ tailWord_4647663) baseStart_4647663 baseEnd_4647663 := by
    simpa [prefixWord, tailWord_4647663, baseEnd_4647663] using wordTrace_append hprefix tailTrace_4647663
  have hstable : (prefixWord ++ tailWord_4647663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4647663).length < 2 ^ (prefixWord ++ tailWord_4647663).sum := by decide
  have hdescent : baseEnd_4647663 < baseStart_4647663 := by decide
  rcases family_descends (prefixWord ++ tailWord_4647663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4647687 : List Nat := [1, 1, 4, 4, 1, 2, 1, 4, 1, 1, 3]
def baseStart_4647687 : Nat := 118140960795 + 4647687 * 2 ^ 59
def prefixEnd_4647687 : Nat := 4983230072969 + 3 ^ 40 * 4647687 * 2
def baseEnd_4647687 : Nat := 2386497362653062636938183

theorem tailTrace_4647687 : CollatzResearch.WordTrace tailWord_4647687 prefixEnd_4647687 2386497362653062636938183 := by
  unfold tailWord_4647687
  simp only [CollatzResearch.WordTrace]
  refine ⟨169515071113231235590109315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113010047408820823726739543 169515071113231235590109315)
  ·
    refine ⟨254272606669846853385163973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169515071113231235590109315 254272606669846853385163973)
    ·
      refine ⟨47676113750596285009718245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 254272606669846853385163973 47676113750596285009718245)
      ·
        refine ⟨8939271328236803439322171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47676113750596285009718245 8939271328236803439322171)
        ·
          refine ⟨13408906992355205158983257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8939271328236803439322171 13408906992355205158983257)
          ·
            refine ⟨10056680244266403869237443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13408906992355205158983257 10056680244266403869237443)
            ·
              refine ⟨15085020366399605803856165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10056680244266403869237443 15085020366399605803856165)
              ·
                refine ⟨2828441318699926088223031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15085020366399605803856165 2828441318699926088223031)
                ·
                  refine ⟨4242661978049889132334547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2828441318699926088223031 4242661978049889132334547)
                  ·
                    refine ⟨6363992967074833698501821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4242661978049889132334547 6363992967074833698501821)
                    ·
                      refine ⟨2386497362653062636938183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6363992967074833698501821 2386497362653062636938183)
                      ·
                        rfl

theorem cell23_4647687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 4, 1, 1, 3].length) (baseStart_4647687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4647687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4647687 prefixEnd_4647687 := by exact prefixLift 4647687
  have htrace : WordTrace (prefixWord ++ tailWord_4647687) baseStart_4647687 baseEnd_4647687 := by
    simpa [prefixWord, tailWord_4647687, baseEnd_4647687] using wordTrace_append hprefix tailTrace_4647687
  have hstable : (prefixWord ++ tailWord_4647687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4647687).length < 2 ^ (prefixWord ++ tailWord_4647687).sum := by decide
  have hdescent : baseEnd_4647687 < baseStart_4647687 := by decide
  rcases family_descends (prefixWord ++ tailWord_4647687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4647689 : List Nat := [1, 2, 1, 1, 3, 2, 2, 1, 3, 1, 6]
def baseStart_4647689 : Nat := 118140960795 + 4647689 * 2 ^ 59
def prefixEnd_4647689 : Nat := 4983230072969 + 3 ^ 40 * 4647689 * 2
def baseEnd_4647689 : Nat := 2386498389614371629113173

theorem tailTrace_4647689 : CollatzResearch.WordTrace tailWord_4647689 prefixEnd_4647689 2386498389614371629113173 := by
  unfold tailWord_4647689
  simp only [CollatzResearch.WordTrace]
  refine ⟨169515144059223989931682121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113010096039482659954454747 169515144059223989931682121)
  ·
    refine ⟨127136358044417992448761591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169515144059223989931682121 127136358044417992448761591)
    ·
      refine ⟨190704537066626988673142387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127136358044417992448761591 190704537066626988673142387)
      ·
        refine ⟨286056805599940483009713581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190704537066626988673142387 286056805599940483009713581)
        ·
          refine ⟨107271302099977681128642593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 286056805599940483009713581 107271302099977681128642593)
          ·
            refine ⟨80453476574983260846481945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107271302099977681128642593 80453476574983260846481945)
            ·
              refine ⟨60340107431237445634861459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80453476574983260846481945 60340107431237445634861459)
              ·
                refine ⟨90510161146856168452292189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60340107431237445634861459 90510161146856168452292189)
                ·
                  refine ⟨33941310430071063169609571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 90510161146856168452292189 33941310430071063169609571)
                  ·
                    refine ⟨50911965645106594754414357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33941310430071063169609571 50911965645106594754414357)
                    ·
                      refine ⟨2386498389614371629113173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50911965645106594754414357 2386498389614371629113173)
                      ·
                        rfl

theorem cell23_4647689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 3, 1, 6].length) (baseStart_4647689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4647689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4647689 prefixEnd_4647689 := by exact prefixLift 4647689
  have htrace : WordTrace (prefixWord ++ tailWord_4647689) baseStart_4647689 baseEnd_4647689 := by
    simpa [prefixWord, tailWord_4647689, baseEnd_4647689] using wordTrace_append hprefix tailTrace_4647689
  have hstable : (prefixWord ++ tailWord_4647689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4647689).length < 2 ^ (prefixWord ++ tailWord_4647689).sum := by decide
  have hdescent : baseEnd_4647689 < baseStart_4647689 := by decide
  rcases family_descends (prefixWord ++ tailWord_4647689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4647703 : List Nat := [1, 1, 3, 4, 3, 1, 2, 1, 1, 6]
def baseStart_4647703 : Nat := 118140960795 + 4647703 * 2 ^ 59
def prefixEnd_4647703 : Nat := 4983230072969 + 3 ^ 40 * 4647703 * 2
def baseEnd_4647703 : Nat := 795501859447844858112703

theorem tailTrace_4647703 : CollatzResearch.WordTrace tailWord_4647703 prefixEnd_4647703 795501859447844858112703 := by
  unfold tailWord_4647703
  simp only [CollatzResearch.WordTrace]
  refine ⟨169515654681173270322691763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113010436454115513548461175 169515654681173270322691763)
  ·
    refine ⟨254273482021759905484037645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169515654681173270322691763 254273482021759905484037645)
    ·
      refine ⟨95352555758159964556514117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 254273482021759905484037645 95352555758159964556514117)
      ·
        refine ⟨17878604204654993354346397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 95352555758159964556514117 17878604204654993354346397)
        ·
          refine ⟨6704476576745622507879899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17878604204654993354346397 6704476576745622507879899)
          ·
            refine ⟨10056714865118433761819849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6704476576745622507879899 10056714865118433761819849)
            ·
              refine ⟨7542536148838825321364887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10056714865118433761819849 7542536148838825321364887)
              ·
                refine ⟨11313804223258237982047331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7542536148838825321364887 11313804223258237982047331)
                ·
                  refine ⟨16970706334887356973070997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11313804223258237982047331 16970706334887356973070997)
                  ·
                    refine ⟨795501859447844858112703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16970706334887356973070997 795501859447844858112703)
                    ·
                      rfl

theorem cell23_4647703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 2, 1, 1, 6].length) (baseStart_4647703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4647703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4647703 prefixEnd_4647703 := by exact prefixLift 4647703
  have htrace : WordTrace (prefixWord ++ tailWord_4647703) baseStart_4647703 baseEnd_4647703 := by
    simpa [prefixWord, tailWord_4647703, baseEnd_4647703] using wordTrace_append hprefix tailTrace_4647703
  have hstable : (prefixWord ++ tailWord_4647703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4647703).length < 2 ^ (prefixWord ++ tailWord_4647703).sum := by decide
  have hdescent : baseEnd_4647703 < baseStart_4647703 := by decide
  rcases family_descends (prefixWord ++ tailWord_4647703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4647713 : List Nat := [1, 2, 3, 2, 1, 2, 2, 4, 1, 2, 3]
def baseStart_4647713 : Nat := 118140960795 + 4647713 * 2 ^ 59
def prefixEnd_4647713 : Nat := 4983230072969 + 3 ^ 40 * 4647713 * 2
def baseEnd_4647713 : Nat := 2386510713150079535213063

theorem tailTrace_4647713 : CollatzResearch.WordTrace tailWord_4647713 prefixEnd_4647713 2386510713150079535213063 := by
  unfold tailWord_4647713
  simp only [CollatzResearch.WordTrace]
  refine ⟨169516019411137042030555793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113010679607424694687037195 169516019411137042030555793)
  ·
    refine ⟨127137014558352781522916845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169516019411137042030555793 127137014558352781522916845)
    ·
      refine ⟨47676380459382293071093817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 127137014558352781522916845 47676380459382293071093817)
      ·
        refine ⟨35757285344536719803320363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47676380459382293071093817 35757285344536719803320363)
        ·
          refine ⟨53635928016805079704980545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35757285344536719803320363 53635928016805079704980545)
          ·
            refine ⟨40226946012603809778735409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53635928016805079704980545 40226946012603809778735409)
            ·
              refine ⟨30170209509452857334051557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40226946012603809778735409 30170209509452857334051557)
              ·
                refine ⟨5656914283022410750134667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30170209509452857334051557 5656914283022410750134667)
                ·
                  refine ⟨8485371424533616125202001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5656914283022410750134667 8485371424533616125202001)
                  ·
                    refine ⟨6364028568400212093901501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8485371424533616125202001 6364028568400212093901501)
                    ·
                      refine ⟨2386510713150079535213063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6364028568400212093901501 2386510713150079535213063)
                      ·
                        rfl

theorem cell23_4647713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 4, 1, 2, 3].length) (baseStart_4647713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4647713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4647713 prefixEnd_4647713 := by exact prefixLift 4647713
  have htrace : WordTrace (prefixWord ++ tailWord_4647713) baseStart_4647713 baseEnd_4647713 := by
    simpa [prefixWord, tailWord_4647713, baseEnd_4647713] using wordTrace_append hprefix tailTrace_4647713
  have hstable : (prefixWord ++ tailWord_4647713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4647713).length < 2 ^ (prefixWord ++ tailWord_4647713).sum := by decide
  have hdescent : baseEnd_4647713 < baseStart_4647713 := by decide
  rcases family_descends (prefixWord ++ tailWord_4647713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4647757 : List Nat := [1, 6, 1, 2, 2, 2, 1, 1, 1, 2, 4]
def baseStart_4647757 : Nat := 118140960795 + 4647757 * 2 ^ 59
def prefixEnd_4647757 : Nat := 4983230072969 + 3 ^ 40 * 4647757 * 2
def baseEnd_4647757 : Nat := 2386533306298877363062861

theorem tailTrace_4647757 : CollatzResearch.WordTrace tailWord_4647757 prefixEnd_4647757 2386533306298877363062861 := by
  unfold tailWord_4647757
  simp only [CollatzResearch.WordTrace]
  refine ⟨169517624222977637545157525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113011749481985091696771683 169517624222977637545157525)
  ·
    refine ⟨7946138635452076759929259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 169517624222977637545157525 7946138635452076759929259)
    ·
      refine ⟨11919207953178115139893889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7946138635452076759929259 11919207953178115139893889)
      ·
        refine ⟨8939405964883586354920417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11919207953178115139893889 8939405964883586354920417)
        ·
          refine ⟨6704554473662689766190313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8939405964883586354920417 6704554473662689766190313)
          ·
            refine ⟨5028415855247017324642735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6704554473662689766190313 5028415855247017324642735)
            ·
              refine ⟨7542623782870525986964103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5028415855247017324642735 7542623782870525986964103)
              ·
                refine ⟨11313935674305788980446155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7542623782870525986964103 11313935674305788980446155)
                ·
                  refine ⟨16970903511458683470669233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11313935674305788980446155 16970903511458683470669233)
                  ·
                    refine ⟨12728177633594012603001925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16970903511458683470669233 12728177633594012603001925)
                    ·
                      refine ⟨2386533306298877363062861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12728177633594012603001925 2386533306298877363062861)
                      ·
                        rfl

theorem cell23_4647757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_4647757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4647757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4647757 prefixEnd_4647757 := by exact prefixLift 4647757
  have htrace : WordTrace (prefixWord ++ tailWord_4647757) baseStart_4647757 baseEnd_4647757 := by
    simpa [prefixWord, tailWord_4647757, baseEnd_4647757] using wordTrace_append hprefix tailTrace_4647757
  have hstable : (prefixWord ++ tailWord_4647757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4647757).length < 2 ^ (prefixWord ++ tailWord_4647757).sum := by decide
  have hdescent : baseEnd_4647757 < baseStart_4647757 := by decide
  rcases family_descends (prefixWord ++ tailWord_4647757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4647770 : List Nat := [3, 1, 1, 2, 1, 4, 1, 4, 1, 3, 2]
def baseStart_4647770 : Nat := 118140960795 + 4647770 * 2 ^ 59
def prefixEnd_4647770 : Nat := 4983230072969 + 3 ^ 40 * 4647770 * 2
def baseEnd_4647770 : Nat := 2386539981547385812200301

theorem tailTrace_4647770 : CollatzResearch.WordTrace tailWord_4647770 prefixEnd_4647770 2386539981547385812200301 := by
  unfold tailWord_4647770
  simp only [CollatzResearch.WordTrace]
  refine ⟨42379524592982635191345191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113012065581287027176920509 42379524592982635191345191)
  ·
    refine ⟨63569286889473952787017787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42379524592982635191345191 63569286889473952787017787)
    ·
      refine ⟨95353930334210929180526681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63569286889473952787017787 95353930334210929180526681)
      ·
        refine ⟨71515447750658196885395011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95353930334210929180526681 71515447750658196885395011)
        ·
          refine ⟨107273171625987295328092517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71515447750658196885395011 107273171625987295328092517)
          ·
            refine ⟨20113719679872617874017347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 107273171625987295328092517 20113719679872617874017347)
            ·
              refine ⟨30170579519808926811026021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20113719679872617874017347 30170579519808926811026021)
              ·
                refine ⟨5656983659964173777067379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30170579519808926811026021 5656983659964173777067379)
                ·
                  refine ⟨8485475489946260665601069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5656983659964173777067379 8485475489946260665601069)
                  ·
                    refine ⟨3182053308729847749600401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8485475489946260665601069 3182053308729847749600401)
                    ·
                      refine ⟨2386539981547385812200301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3182053308729847749600401 2386539981547385812200301)
                      ·
                        rfl

theorem cell23_4647770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 4, 1, 3, 2].length) (baseStart_4647770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4647770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4647770 prefixEnd_4647770 := by exact prefixLift 4647770
  have htrace : WordTrace (prefixWord ++ tailWord_4647770) baseStart_4647770 baseEnd_4647770 := by
    simpa [prefixWord, tailWord_4647770, baseEnd_4647770] using wordTrace_append hprefix tailTrace_4647770
  have hstable : (prefixWord ++ tailWord_4647770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4647770).length < 2 ^ (prefixWord ++ tailWord_4647770).sum := by decide
  have hdescent : baseEnd_4647770 < baseStart_4647770 := by decide
  rcases family_descends (prefixWord ++ tailWord_4647770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4647778 : List Nat := [3, 3, 2, 1, 4, 1, 1, 3, 1, 2, 2]
def baseStart_4647778 : Nat := 118140960795 + 4647778 * 2 ^ 59
def prefixEnd_4647778 : Nat := 4983230072969 + 3 ^ 40 * 4647778 * 2
def baseEnd_4647778 : Nat := 2386544089392621780900265

theorem tailTrace_4647778 : CollatzResearch.WordTrace tailWord_4647778 prefixEnd_4647778 2386544089392621780900265 := by
  unfold tailWord_4647778
  simp only [CollatzResearch.WordTrace]
  refine ⟨42379597538975389532917997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113012260103934372087781325 42379597538975389532917997)
  ·
    refine ⟨15892349077115771074844249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42379597538975389532917997 15892349077115771074844249)
    ·
      refine ⟨11919261807836828306133187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15892349077115771074844249 11919261807836828306133187)
      ·
        refine ⟨17878892711755242459199781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11919261807836828306133187 17878892711755242459199781)
        ·
          refine ⟨3352292383454107961099959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17878892711755242459199781 3352292383454107961099959)
          ·
            refine ⟨5028438575181161941649939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3352292383454107961099959 5028438575181161941649939)
            ·
              refine ⟨7542657862771742912474909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5028438575181161941649939 7542657862771742912474909)
              ·
                refine ⟨2828496698539403592178091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7542657862771742912474909 2828496698539403592178091)
                ·
                  refine ⟨4242745047809105388267137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2828496698539403592178091 4242745047809105388267137)
                  ·
                    refine ⟨3182058785856829041200353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4242745047809105388267137 3182058785856829041200353)
                    ·
                      refine ⟨2386544089392621780900265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3182058785856829041200353 2386544089392621780900265)
                      ·
                        rfl

theorem cell23_4647778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 1, 3, 1, 2, 2].length) (baseStart_4647778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4647778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4647778 prefixEnd_4647778 := by exact prefixLift 4647778
  have htrace : WordTrace (prefixWord ++ tailWord_4647778) baseStart_4647778 baseEnd_4647778 := by
    simpa [prefixWord, tailWord_4647778, baseEnd_4647778] using wordTrace_append hprefix tailTrace_4647778
  have hstable : (prefixWord ++ tailWord_4647778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4647778).length < 2 ^ (prefixWord ++ tailWord_4647778).sum := by decide
  have hdescent : baseEnd_4647778 < baseStart_4647778 := by decide
  rcases family_descends (prefixWord ++ tailWord_4647778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4647817 : List Nat := [1, 2, 1, 1, 5, 3, 1, 3, 2, 2, 2]
def baseStart_4647817 : Nat := 118140960795 + 4647817 * 2 ^ 59
def prefixEnd_4647817 : Nat := 4983230072969 + 3 ^ 40 * 4647817 * 2
def baseEnd_4647817 : Nat := 2386564115138147128312585

theorem tailTrace_4647817 : CollatzResearch.WordTrace tailWord_4647817 prefixEnd_4647817 2386564115138147128312585 := by
  unfold tailWord_4647817
  simp only [CollatzResearch.WordTrace]
  refine ⟨169519812602760267792341705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113013208401840178528227803 169519812602760267792341705)
  ·
    refine ⟨127139859452070200844256279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169519812602760267792341705 127139859452070200844256279)
    ·
      refine ⟨190709789178105301266384419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127139859452070200844256279 190709789178105301266384419)
      ·
        refine ⟨286064683767157951899576629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190709789178105301266384419 286064683767157951899576629)
        ·
          refine ⟨26818564103171057990585309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 286064683767157951899576629 26818564103171057990585309)
          ·
            refine ⟨10056961538689146746469491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26818564103171057990585309 10056961538689146746469491)
            ·
              refine ⟨15085442308033720119704237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10056961538689146746469491 15085442308033720119704237)
              ·
                refine ⟨5657040865512645044889089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15085442308033720119704237 5657040865512645044889089)
                ·
                  refine ⟨4242780649134483783666817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5657040865512645044889089 4242780649134483783666817)
                  ·
                    refine ⟨3182085486850862837750113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4242780649134483783666817 3182085486850862837750113)
                    ·
                      refine ⟨2386564115138147128312585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3182085486850862837750113 2386564115138147128312585)
                      ·
                        rfl

theorem cell23_4647817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 3, 2, 2, 2].length) (baseStart_4647817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4647817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4647817 prefixEnd_4647817 := by exact prefixLift 4647817
  have htrace : WordTrace (prefixWord ++ tailWord_4647817) baseStart_4647817 baseEnd_4647817 := by
    simpa [prefixWord, tailWord_4647817, baseEnd_4647817] using wordTrace_append hprefix tailTrace_4647817
  have hstable : (prefixWord ++ tailWord_4647817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4647817).length < 2 ^ (prefixWord ++ tailWord_4647817).sum := by decide
  have hdescent : baseEnd_4647817 < baseStart_4647817 := by decide
  rcases family_descends (prefixWord ++ tailWord_4647817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4647883 : List Nat := [1, 1, 1, 1, 3, 5, 1, 1, 5, 4]
def baseStart_4647883 : Nat := 118140960795 + 4647883 * 2 ^ 59
def prefixEnd_4647883 : Nat := 4983230072969 + 3 ^ 40 * 4647883 * 2
def baseEnd_4647883 : Nat := 795532668287114623362427

theorem tailTrace_4647883 : CollatzResearch.WordTrace tailWord_4647883 prefixEnd_4647883 795532668287114623362427 := by
  unfold tailWord_4647883
  simp only [CollatzResearch.WordTrace]
  refine ⟨169522219820521161064244303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113014813213680774042829535 169522219820521161064244303)
  ·
    refine ⟨254283329730781741596366455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169522219820521161064244303 254283329730781741596366455)
    ·
      refine ⟨381424994596172612394549683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 254283329730781741596366455 381424994596172612394549683)
      ·
        refine ⟨572137491894258918591824525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 381424994596172612394549683 572137491894258918591824525)
        ·
          refine ⟨214551559460347094471934197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 572137491894258918591824525 214551559460347094471934197)
          ·
            refine ⟨20114208699407540106743831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 214551559460347094471934197 20114208699407540106743831)
            ·
              refine ⟨30171313049111310160115747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20114208699407540106743831 30171313049111310160115747)
              ·
                refine ⟨45256969573666965240173621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30171313049111310160115747 45256969573666965240173621)
                ·
                  refine ⟨4242840897531277991266277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45256969573666965240173621 4242840897531277991266277)
                  ·
                    refine ⟨795532668287114623362427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4242840897531277991266277 795532668287114623362427)
                    ·
                      rfl

theorem cell23_4647883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 1, 5, 4].length) (baseStart_4647883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4647883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4647883 prefixEnd_4647883 := by exact prefixLift 4647883
  have htrace : WordTrace (prefixWord ++ tailWord_4647883) baseStart_4647883 baseEnd_4647883 := by
    simpa [prefixWord, tailWord_4647883, baseEnd_4647883] using wordTrace_append hprefix tailTrace_4647883
  have hstable : (prefixWord ++ tailWord_4647883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4647883).length < 2 ^ (prefixWord ++ tailWord_4647883).sum := by decide
  have hdescent : baseEnd_4647883 < baseStart_4647883 := by decide
  rcases family_descends (prefixWord ++ tailWord_4647883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4647890 : List Nat := [3, 2, 2, 3, 1, 2, 1, 1, 1, 3, 4]
def baseStart_4647890 : Nat := 118140960795 + 4647890 * 2 ^ 59
def prefixEnd_4647890 : Nat := 4983230072969 + 3 ^ 40 * 4647890 * 2
def baseEnd_4647890 : Nat := 2386601599225925342699749

theorem tailTrace_4647890 : CollatzResearch.WordTrace tailWord_4647890 prefixEnd_4647890 2386601599225925342699749 := by
  unfold tailWord_4647890
  simp only [CollatzResearch.WordTrace]
  refine ⟨42380618782873950314937281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113014983420997200839832749 42380618782873950314937281)
  ·
    refine ⟨31785464087155462736202961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42380618782873950314937281 31785464087155462736202961)
    ·
      refine ⟨23839098065366597052152221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31785464087155462736202961 23839098065366597052152221)
      ·
        refine ⟨8939661774512473894557083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23839098065366597052152221 8939661774512473894557083)
        ·
          refine ⟨13409492661768710841835625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8939661774512473894557083 13409492661768710841835625)
          ·
            refine ⟨10057119496326533131376719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13409492661768710841835625 10057119496326533131376719)
            ·
              refine ⟨15085679244489799697065079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10057119496326533131376719 15085679244489799697065079)
              ·
                refine ⟨22628518866734699545597619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15085679244489799697065079 22628518866734699545597619)
                ·
                  refine ⟨33942778300102049318396429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22628518866734699545597619 33942778300102049318396429)
                  ·
                    refine ⟨12728541862538268494398661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33942778300102049318396429 12728541862538268494398661)
                    ·
                      refine ⟨2386601599225925342699749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12728541862538268494398661 2386601599225925342699749)
                      ·
                        rfl

theorem cell23_4647890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_4647890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4647890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4647890 prefixEnd_4647890 := by exact prefixLift 4647890
  have htrace : WordTrace (prefixWord ++ tailWord_4647890) baseStart_4647890 baseEnd_4647890 := by
    simpa [prefixWord, tailWord_4647890, baseEnd_4647890] using wordTrace_append hprefix tailTrace_4647890
  have hstable : (prefixWord ++ tailWord_4647890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4647890).length < 2 ^ (prefixWord ++ tailWord_4647890).sum := by decide
  have hdescent : baseEnd_4647890 < baseStart_4647890 := by decide
  rcases family_descends (prefixWord ++ tailWord_4647890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4647960 : List Nat := [2, 1, 2, 3, 2, 2, 2, 3, 1, 5]
def baseStart_4647960 : Nat := 118140960795 + 4647960 * 2 ^ 59
def prefixEnd_4647960 : Nat := 4983230072969 + 3 ^ 40 * 4647960 * 2
def baseEnd_4647960 : Nat := 795545847623913356274809

theorem tailTrace_4647960 : CollatzResearch.WordTrace tailWord_4647960 prefixEnd_4647960 795545847623913356274809 := by
  unfold tailWord_4647960
  simp only [CollatzResearch.WordTrace]
  refine ⟨84762514120621101607398667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113016685494161468809864889 84762514120621101607398667)
  ·
    refine ⟨127143771180931652411098001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84762514120621101607398667 127143771180931652411098001)
    ·
      refine ⟨95357828385698739308323501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127143771180931652411098001 95357828385698739308323501)
      ·
        refine ⟨35759185644637027240621313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95357828385698739308323501 35759185644637027240621313)
        ·
          refine ⟨26819389233477770430465985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35759185644637027240621313 26819389233477770430465985)
          ·
            refine ⟨20114541925108327822849489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26819389233477770430465985 20114541925108327822849489)
            ·
              refine ⟨15085906443831245867137117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20114541925108327822849489 15085906443831245867137117)
              ·
                refine ⟨5657214916436717200176419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15085906443831245867137117 5657214916436717200176419)
                ·
                  refine ⟨8485822374655075800264629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5657214916436717200176419 8485822374655075800264629)
                  ·
                    refine ⟨795545847623913356274809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8485822374655075800264629 795545847623913356274809)
                    ·
                      rfl

theorem cell23_4647960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 3, 1, 5].length) (baseStart_4647960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4647960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4647960 prefixEnd_4647960 := by exact prefixLift 4647960
  have htrace : WordTrace (prefixWord ++ tailWord_4647960) baseStart_4647960 baseEnd_4647960 := by
    simpa [prefixWord, tailWord_4647960, baseEnd_4647960] using wordTrace_append hprefix tailTrace_4647960
  have hstable : (prefixWord ++ tailWord_4647960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4647960).length < 2 ^ (prefixWord ++ tailWord_4647960).sum := by decide
  have hdescent : baseEnd_4647960 < baseStart_4647960 := by decide
  rcases family_descends (prefixWord ++ tailWord_4647960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4647967 : List Nat := [1, 1, 2, 4, 1, 4, 1, 2, 2, 3, 2]
def baseStart_4647967 : Nat := 118140960795 + 4647967 * 2 ^ 59
def prefixEnd_4647967 : Nat := 4983230072969 + 3 ^ 40 * 4647967 * 2
def baseEnd_4647967 : Nat := 2386641137236321541436895

theorem tailTrace_4647967 : CollatzResearch.WordTrace tailWord_4647967 prefixEnd_4647967 2386641137236321541436895 := by
  unfold tailWord_4647967
  simp only [CollatzResearch.WordTrace]
  refine ⟨169525283552216843410302155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113016855701477895606868103 169525283552216843410302155)
  ·
    refine ⟨254287925328325265115453233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169525283552216843410302155 254287925328325265115453233)
    ·
      refine ⟨190715943996243948836589925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 254287925328325265115453233 190715943996243948836589925)
      ·
        refine ⟨35759239499295740406860611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 190715943996243948836589925 35759239499295740406860611)
        ·
          refine ⟨53638859248943610610290917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35759239499295740406860611 53638859248943610610290917)
          ·
            refine ⟨10057286109176926989429547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53638859248943610610290917 10057286109176926989429547)
            ·
              refine ⟨15085929163765390484144321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10057286109176926989429547 15085929163765390484144321)
              ·
                refine ⟨11314446872824042863108241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15085929163765390484144321 11314446872824042863108241)
                ·
                  refine ⟨8485835154618032147331181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11314446872824042863108241 8485835154618032147331181)
                  ·
                    refine ⟨3182188182981762055249193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8485835154618032147331181 3182188182981762055249193)
                    ·
                      refine ⟨2386641137236321541436895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3182188182981762055249193 2386641137236321541436895)
                      ·
                        rfl

theorem cell23_4647967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 2, 2, 3, 2].length) (baseStart_4647967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4647967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4647967 prefixEnd_4647967 := by exact prefixLift 4647967
  have htrace : WordTrace (prefixWord ++ tailWord_4647967) baseStart_4647967 baseEnd_4647967 := by
    simpa [prefixWord, tailWord_4647967, baseEnd_4647967] using wordTrace_append hprefix tailTrace_4647967
  have hstable : (prefixWord ++ tailWord_4647967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4647967).length < 2 ^ (prefixWord ++ tailWord_4647967).sum := by decide
  have hdescent : baseEnd_4647967 < baseStart_4647967 := by decide
  rcases family_descends (prefixWord ++ tailWord_4647967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4647997 : List Nat := [1, 4, 1, 3, 1, 2, 3, 2, 1, 1, 4]
def baseStart_4647997 : Nat := 118140960795 + 4647997 * 2 ^ 59
def prefixEnd_4647997 : Nat := 4983230072969 + 3 ^ 40 * 4647997 * 2
def baseEnd_4647997 : Nat := 2386656541655956424061757

theorem tailTrace_4647997 : CollatzResearch.WordTrace tailWord_4647997 prefixEnd_4647997 2386656541655956424061757 := by
  unfold tailWord_4647997
  simp only [CollatzResearch.WordTrace]
  refine ⟨169526377742108158533894245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113017585161405439022596163 169526377742108158533894245)
  ·
    refine ⟨31786195826645279725105171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 169526377742108158533894245 31786195826645279725105171)
    ·
      refine ⟨47679293739967919587657757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31786195826645279725105171 47679293739967919587657757)
      ·
        refine ⟨17879735152487969845371659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47679293739967919587657757 17879735152487969845371659)
        ·
          refine ⟨26819602728731954768057489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17879735152487969845371659 26819602728731954768057489)
          ·
            refine ⟨20114702046548966076043117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26819602728731954768057489 20114702046548966076043117)
            ·
              refine ⟨7543013267455862278516169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20114702046548966076043117 7543013267455862278516169)
              ·
                refine ⟨5657259950591896708887127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7543013267455862278516169 5657259950591896708887127)
                ·
                  refine ⟨8485889925887845063330691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5657259950591896708887127 8485889925887845063330691)
                  ·
                    refine ⟨12728834888831767594996037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8485889925887845063330691 12728834888831767594996037)
                    ·
                      refine ⟨2386656541655956424061757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12728834888831767594996037 2386656541655956424061757)
                      ·
                        rfl

theorem cell23_4647997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 3, 2, 1, 1, 4].length) (baseStart_4647997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4647997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4647997 prefixEnd_4647997 := by exact prefixLift 4647997
  have htrace : WordTrace (prefixWord ++ tailWord_4647997) baseStart_4647997 baseEnd_4647997 := by
    simpa [prefixWord, tailWord_4647997, baseEnd_4647997] using wordTrace_append hprefix tailTrace_4647997
  have hstable : (prefixWord ++ tailWord_4647997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4647997).length < 2 ^ (prefixWord ++ tailWord_4647997).sum := by decide
  have hdescent : baseEnd_4647997 < baseStart_4647997 := by decide
  rcases family_descends (prefixWord ++ tailWord_4647997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4648000 : List Nat := [2, 1, 1, 2, 2, 3, 3, 1, 3, 2, 3]
def baseStart_4648000 : Nat := 118140960795 + 4648000 * 2 ^ 59
def prefixEnd_4648000 : Nat := 4983230072969 + 3 ^ 40 * 4648000 * 2
def baseEnd_4648000 : Nat := 2386658082097919912324243

theorem tailTrace_4648000 : CollatzResearch.WordTrace tailWord_4648000 prefixEnd_4648000 2386658082097919912324243 := by
  unfold tailWord_4648000
  simp only [CollatzResearch.WordTrace]
  refine ⟨84763243580548645023126727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113017658107398193364168969 84763243580548645023126727)
  ·
    refine ⟨127144865370822967534690091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84763243580548645023126727 127144865370822967534690091)
    ·
      refine ⟨190717298056234451302035137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127144865370822967534690091 190717298056234451302035137)
      ·
        refine ⟨143037973542175838476526353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 190717298056234451302035137 143037973542175838476526353)
        ·
          refine ⟨107278480156631878857394765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 143037973542175838476526353 107278480156631878857394765)
          ·
            refine ⟨40229430058736954571523037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 107278480156631878857394765 40229430058736954571523037)
            ·
              refine ⟨15086036272026357964321139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40229430058736954571523037 15086036272026357964321139)
              ·
                refine ⟨22629054408039536946481709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15086036272026357964321139 22629054408039536946481709)
                ·
                  refine ⟨8485895403014826354930641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22629054408039536946481709 8485895403014826354930641)
                  ·
                    refine ⟨6364421552261119766197981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8485895403014826354930641 6364421552261119766197981)
                    ·
                      refine ⟨2386658082097919912324243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6364421552261119766197981 2386658082097919912324243)
                      ·
                        rfl

theorem cell23_4648000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 1, 3, 2, 3].length) (baseStart_4648000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4648000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4648000 prefixEnd_4648000 := by exact prefixLift 4648000
  have htrace : WordTrace (prefixWord ++ tailWord_4648000) baseStart_4648000 baseEnd_4648000 := by
    simpa [prefixWord, tailWord_4648000, baseEnd_4648000] using wordTrace_append hprefix tailTrace_4648000
  have hstable : (prefixWord ++ tailWord_4648000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4648000).length < 2 ^ (prefixWord ++ tailWord_4648000).sum := by decide
  have hdescent : baseEnd_4648000 < baseStart_4648000 := by decide
  rcases family_descends (prefixWord ++ tailWord_4648000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4648033 : List Nat := [1, 2, 3, 1, 1, 2, 3, 1, 2, 7]
def baseStart_4648033 : Nat := 118140960795 + 4648033 * 2 ^ 59
def prefixEnd_4648033 : Nat := 4983230072969 + 3 ^ 40 * 4648033 * 2
def baseEnd_4648033 : Nat := 795558342319839427737197

theorem tailTrace_4648033 : CollatzResearch.WordTrace tailWord_4648033 prefixEnd_4648033 795558342319839427737197 := by
  unfold tailWord_4648033
  simp only [CollatzResearch.WordTrace]
  refine ⟨169527690769977736682204753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113018460513318491121469835 169527690769977736682204753)
  ·
    refine ⟨127145768077483302511653565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169527690769977736682204753 127145768077483302511653565)
    ·
      refine ⟨47679663029056238441870087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 127145768077483302511653565 47679663029056238441870087)
      ·
        refine ⟨71519494543584357662805131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47679663029056238441870087 71519494543584357662805131)
        ·
          refine ⟨107279241815376536494207697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71519494543584357662805131 107279241815376536494207697)
          ·
            refine ⟨80459431361532402370655773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107279241815376536494207697 80459431361532402370655773)
            ·
              refine ⟨30172286760574650888995915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80459431361532402370655773 30172286760574650888995915)
              ·
                refine ⟨45258430140861976333493873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30172286760574650888995915 45258430140861976333493873)
                ·
                  refine ⟨33943822605646482250120405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45258430140861976333493873 33943822605646482250120405)
                  ·
                    refine ⟨795558342319839427737197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33943822605646482250120405 795558342319839427737197)
                    ·
                      rfl

theorem cell23_4648033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 1, 2, 7].length) (baseStart_4648033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4648033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4648033 prefixEnd_4648033 := by exact prefixLift 4648033
  have htrace : WordTrace (prefixWord ++ tailWord_4648033) baseStart_4648033 baseEnd_4648033 := by
    simpa [prefixWord, tailWord_4648033, baseEnd_4648033] using wordTrace_append hprefix tailTrace_4648033
  have hstable : (prefixWord ++ tailWord_4648033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4648033).length < 2 ^ (prefixWord ++ tailWord_4648033).sum := by decide
  have hdescent : baseEnd_4648033 < baseStart_4648033 := by decide
  rcases family_descends (prefixWord ++ tailWord_4648033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4648047 : List Nat := [1, 1, 2, 1, 3, 3, 1, 5, 2, 1, 3]
def baseStart_4648047 : Nat := 118140960795 + 4648047 * 2 ^ 59
def prefixEnd_4648047 : Nat := 4983230072969 + 3 ^ 40 * 4648047 * 2
def baseEnd_4648047 : Nat := 2386682215688681228436527

theorem tailTrace_4648047 : CollatzResearch.WordTrace tailWord_4648047 prefixEnd_4648047 2386682215688681228436527 := by
  unfold tailWord_4648047
  simp only [CollatzResearch.WordTrace]
  refine ⟨169528201391927017073214395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113018800927951344715476263 169528201391927017073214395)
  ·
    refine ⟨254292302087890525609821593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169528201391927017073214395 254292302087890525609821593)
    ·
      refine ⟨190719226565917894207366195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 254292302087890525609821593 190719226565917894207366195)
      ·
        refine ⟨286078839848876841311049293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190719226565917894207366195 286078839848876841311049293)
        ·
          refine ⟨107279564943328815491643485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 286078839848876841311049293 107279564943328815491643485)
          ·
            refine ⟨40229836853748305809366307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 107279564943328815491643485 40229836853748305809366307)
            ·
              refine ⟨60344755280622458714049461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40229836853748305809366307 60344755280622458714049461)
              ·
                refine ⟨5657320807558355504442137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 60344755280622458714049461 5657320807558355504442137)
                ·
                  refine ⟨4242990605668766628331603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5657320807558355504442137 4242990605668766628331603)
                  ·
                    refine ⟨6364485908503149942497405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4242990605668766628331603 6364485908503149942497405)
                    ·
                      refine ⟨2386682215688681228436527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6364485908503149942497405 2386682215688681228436527)
                      ·
                        rfl

theorem cell23_4648047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 5, 2, 1, 3].length) (baseStart_4648047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4648047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4648047 prefixEnd_4648047 := by exact prefixLift 4648047
  have htrace : WordTrace (prefixWord ++ tailWord_4648047) baseStart_4648047 baseEnd_4648047 := by
    simpa [prefixWord, tailWord_4648047, baseEnd_4648047] using wordTrace_append hprefix tailTrace_4648047
  have hstable : (prefixWord ++ tailWord_4648047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4648047).length < 2 ^ (prefixWord ++ tailWord_4648047).sum := by decide
  have hdescent : baseEnd_4648047 < baseStart_4648047 := by decide
  rcases family_descends (prefixWord ++ tailWord_4648047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4648074 : List Nat := [3, 1, 2, 3, 1, 1, 3, 3, 1, 3, 2]
def baseStart_4648074 : Nat := 118140960795 + 4648074 * 2 ^ 59
def prefixEnd_4648074 : Nat := 4983230072969 + 3 ^ 40 * 4648074 * 2
def baseEnd_4648074 : Nat := 2386696079666352622798903

theorem tailTrace_4648074 : CollatzResearch.WordTrace tailWord_4648074 prefixEnd_4648074 2386696079666352622798903 := by
  unfold tailWord_4648074
  simp only [CollatzResearch.WordTrace]
  refine ⟨42382296540707300171111819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113019457441886133789631517 42382296540707300171111819)
  ·
    refine ⟨63573444811060950256667729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42382296540707300171111819 63573444811060950256667729)
    ·
      refine ⟨47680083608295712692500797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63573444811060950256667729 47680083608295712692500797)
      ·
        refine ⟨17880031353110892259687799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47680083608295712692500797 17880031353110892259687799)
        ·
          refine ⟨26820047029666338389531699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17880031353110892259687799 26820047029666338389531699)
          ·
            refine ⟨40230070544499507584297549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26820047029666338389531699 40230070544499507584297549)
            ·
              refine ⟨15086276454187315344111581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40230070544499507584297549 15086276454187315344111581)
              ·
                refine ⟨5657353670320243254041843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15086276454187315344111581 5657353670320243254041843)
                ·
                  refine ⟨8486030505480364881062765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5657353670320243254041843 8486030505480364881062765)
                  ·
                    refine ⟨3182261439555136830398537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8486030505480364881062765 3182261439555136830398537)
                    ·
                      refine ⟨2386696079666352622798903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3182261439555136830398537 2386696079666352622798903)
                      ·
                        rfl

theorem cell23_4648074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 3, 1, 3, 2].length) (baseStart_4648074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4648074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4648074 prefixEnd_4648074 := by exact prefixLift 4648074
  have htrace : WordTrace (prefixWord ++ tailWord_4648074) baseStart_4648074 baseEnd_4648074 := by
    simpa [prefixWord, tailWord_4648074, baseEnd_4648074] using wordTrace_append hprefix tailTrace_4648074
  have hstable : (prefixWord ++ tailWord_4648074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4648074).length < 2 ^ (prefixWord ++ tailWord_4648074).sum := by decide
  have hdescent : baseEnd_4648074 < baseStart_4648074 := by decide
  rcases family_descends (prefixWord ++ tailWord_4648074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4648098 : List Nat := [3, 3, 1, 3, 2, 1, 3, 1, 2, 1, 3]
def baseStart_4648098 : Nat := 118140960795 + 4648098 * 2 ^ 59
def prefixEnd_4648098 : Nat := 4983230072969 + 3 ^ 40 * 4648098 * 2
def baseEnd_4648098 : Nat := 2386708403202060528898793

theorem tailTrace_4648098 : CollatzResearch.WordTrace tailWord_4648098 prefixEnd_4648098 2386708403202060528898793 := by
  unfold tailWord_4648098
  simp only [CollatzResearch.WordTrace]
  refine ⟨42382515378685563195830237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113020041009828168522213965 42382515378685563195830237)
  ·
    refine ⟨15893443267007086198436339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42382515378685563195830237 15893443267007086198436339)
    ·
      refine ⟨23840164900510629297654509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15893443267007086198436339 23840164900510629297654509)
      ·
        refine ⟨8940061837691485986620441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23840164900510629297654509 8940061837691485986620441)
        ·
          refine ⟨6705046378268614489965331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8940061837691485986620441 6705046378268614489965331)
          ·
            refine ⟨10057569567402921734947997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6705046378268614489965331 10057569567402921734947997)
            ·
              refine ⟨3771588587776095650605499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10057569567402921734947997 3771588587776095650605499)
              ·
                refine ⟨5657382881664143475908249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3771588587776095650605499 5657382881664143475908249)
                ·
                  refine ⟨4243037161248107606931187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5657382881664143475908249 4243037161248107606931187)
                  ·
                    refine ⟨6364555741872161410396781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4243037161248107606931187 6364555741872161410396781)
                    ·
                      refine ⟨2386708403202060528898793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6364555741872161410396781 2386708403202060528898793)
                      ·
                        rfl

theorem cell23_4648098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 3, 1, 2, 1, 3].length) (baseStart_4648098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4648098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4648098 prefixEnd_4648098 := by exact prefixLift 4648098
  have htrace : WordTrace (prefixWord ++ tailWord_4648098) baseStart_4648098 baseEnd_4648098 := by
    simpa [prefixWord, tailWord_4648098, baseEnd_4648098] using wordTrace_append hprefix tailTrace_4648098
  have hstable : (prefixWord ++ tailWord_4648098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4648098).length < 2 ^ (prefixWord ++ tailWord_4648098).sum := by decide
  have hdescent : baseEnd_4648098 < baseStart_4648098 := by decide
  rcases family_descends (prefixWord ++ tailWord_4648098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4648120 : List Nat := [2, 1, 2, 1, 2, 1, 2, 2, 4, 3, 3]
def baseStart_4648120 : Nat := 118140960795 + 4648120 * 2 ^ 59
def prefixEnd_4648120 : Nat := 4983230072969 + 3 ^ 40 * 4648120 * 2
def baseEnd_4648120 : Nat := 2386719699776459442823691

theorem tailTrace_4648120 : CollatzResearch.WordTrace tailWord_4648120 prefixEnd_4648120 2386719699776459442823691 := by
  unfold tailWord_4648120
  simp only [CollatzResearch.WordTrace]
  refine ⟨84765431960331275270310907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113020575947108367027081209 84765431960331275270310907)
  ·
    refine ⟨127148147940496912905466361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84765431960331275270310907 127148147940496912905466361)
    ·
      refine ⟨95361110955372684679099771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127148147940496912905466361 95361110955372684679099771)
      ·
        refine ⟨143041666433059027018649657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95361110955372684679099771 143041666433059027018649657)
        ·
          refine ⟨107281249824794270263987243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 143041666433059027018649657 107281249824794270263987243)
          ·
            refine ⟨160921874737191405395980865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107281249824794270263987243 160921874737191405395980865)
            ·
              refine ⟨120691406052893554046985649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 160921874737191405395980865 120691406052893554046985649)
              ·
                refine ⟨90518554539670165535239237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 120691406052893554046985649 90518554539670165535239237)
                ·
                  refine ⟨16972228976188156037857357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 90518554539670165535239237 16972228976188156037857357)
                  ·
                    refine ⟨6364585866070558514196509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16972228976188156037857357 6364585866070558514196509)
                    ·
                      refine ⟨2386719699776459442823691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6364585866070558514196509 2386719699776459442823691)
                      ·
                        rfl

theorem cell23_4648120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 4, 3, 3].length) (baseStart_4648120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4648120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4648120 prefixEnd_4648120 := by exact prefixLift 4648120
  have htrace : WordTrace (prefixWord ++ tailWord_4648120) baseStart_4648120 baseEnd_4648120 := by
    simpa [prefixWord, tailWord_4648120, baseEnd_4648120] using wordTrace_append hprefix tailTrace_4648120
  have hstable : (prefixWord ++ tailWord_4648120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4648120).length < 2 ^ (prefixWord ++ tailWord_4648120).sum := by decide
  have hdescent : baseEnd_4648120 < baseStart_4648120 := by decide
  rcases family_descends (prefixWord ++ tailWord_4648120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4648127 : List Nat := [1, 1, 2, 2, 2, 2, 5, 3, 5]
def baseStart_4648127 : Nat := 118140960795 + 4648127 * 2 ^ 59
def prefixEnd_4648127 : Nat := 4983230072969 + 3 ^ 40 * 4648127 * 2
def baseEnd_4648127 : Nat := 265191477126782323937351

theorem tailTrace_4648127 : CollatzResearch.WordTrace tailWord_4648127 prefixEnd_4648127 265191477126782323937351 := by
  unfold tailWord_4648127
  simp only [CollatzResearch.WordTrace]
  refine ⟨169531119231637190736126635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113020746154424793824084423 169531119231637190736126635)
  ·
    refine ⟨254296678847455786104189953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169531119231637190736126635 254296678847455786104189953)
    ·
      refine ⟨190722509135591839578142465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 254296678847455786104189953 190722509135591839578142465)
      ·
        refine ⟨143041881851693879683606849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 190722509135591839578142465 143041881851693879683606849)
        ·
          refine ⟨107281411388770409762705137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 143041881851693879683606849 107281411388770409762705137)
          ·
            refine ⟨80461058541577807322028853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107281411388770409762705137 80461058541577807322028853)
            ·
              refine ⟨7543224238272919436440205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 80461058541577807322028853 7543224238272919436440205)
              ·
                refine ⟨2828709089352344788665077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7543224238272919436440205 2828709089352344788665077)
                ·
                  refine ⟨265191477126782323937351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2828709089352344788665077 265191477126782323937351)
                  ·
                    rfl

theorem cell23_4648127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 5, 3, 5].length) (baseStart_4648127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4648127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4648127 prefixEnd_4648127 := by exact prefixLift 4648127
  have htrace : WordTrace (prefixWord ++ tailWord_4648127) baseStart_4648127 baseEnd_4648127 := by
    simpa [prefixWord, tailWord_4648127, baseEnd_4648127] using wordTrace_append hprefix tailTrace_4648127
  have hstable : (prefixWord ++ tailWord_4648127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4648127).length < 2 ^ (prefixWord ++ tailWord_4648127).sum := by decide
  have hdescent : baseEnd_4648127 < baseStart_4648127 := by decide
  rcases family_descends (prefixWord ++ tailWord_4648127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4648177 : List Nat := [1, 2, 2, 2, 2, 1, 1, 2, 4, 4, 2]
def baseStart_4648177 : Nat := 118140960795 + 4648177 * 2 ^ 59
def prefixEnd_4648177 : Nat := 4983230072969 + 3 ^ 40 * 4648177 * 2
def baseEnd_4648177 : Nat := 2386748968173765719810929

theorem tailTrace_4648177 : CollatzResearch.WordTrace tailWord_4648177 prefixEnd_4648177 2386748968173765719810929 := by
  unfold tailWord_4648177
  simp only [CollatzResearch.WordTrace]
  refine ⟨169532942881456049275446785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113021961920970699516964523 169532942881456049275446785)
  ·
    refine ⟨127149707161092036956585089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169532942881456049275446785 127149707161092036956585089)
    ·
      refine ⟨95362280370819027717438817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127149707161092036956585089 95362280370819027717438817)
      ·
        refine ⟨71521710278114270788079113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95362280370819027717438817 71521710278114270788079113)
        ·
          refine ⟨53641282708585703091059335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71521710278114270788079113 53641282708585703091059335)
          ·
            refine ⟨80461924062878554636589003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53641282708585703091059335 80461924062878554636589003)
            ·
              refine ⟨120692886094317831954883505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80461924062878554636589003 120692886094317831954883505)
              ·
                refine ⟨90519664570738373966162629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 120692886094317831954883505 90519664570738373966162629)
                ·
                  refine ⟨16972437107013445118655493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 90519664570738373966162629 16972437107013445118655493)
                  ·
                    refine ⟨3182331957565020959747905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16972437107013445118655493 3182331957565020959747905)
                    ·
                      refine ⟨2386748968173765719810929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3182331957565020959747905 2386748968173765719810929)
                      ·
                        rfl

theorem cell23_4648177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 4, 4, 2].length) (baseStart_4648177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4648177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4648177 prefixEnd_4648177 := by exact prefixLift 4648177
  have htrace : WordTrace (prefixWord ++ tailWord_4648177) baseStart_4648177 baseEnd_4648177 := by
    simpa [prefixWord, tailWord_4648177, baseEnd_4648177] using wordTrace_append hprefix tailTrace_4648177
  have hstable : (prefixWord ++ tailWord_4648177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4648177).length < 2 ^ (prefixWord ++ tailWord_4648177).sum := by decide
  have hdescent : baseEnd_4648177 < baseStart_4648177 := by decide
  rcases family_descends (prefixWord ++ tailWord_4648177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4648197 : List Nat := [1, 3, 1, 1, 2, 1, 3, 4, 2, 2, 3]
def baseStart_4648197 : Nat := 118140960795 + 4648197 * 2 ^ 59
def prefixEnd_4648197 : Nat := 4983230072969 + 3 ^ 40 * 4648197 * 2
def baseEnd_4648197 : Nat := 2386759237786855641560837

theorem tailTrace_4648197 : CollatzResearch.WordTrace tailWord_4648197 prefixEnd_4648197 2386759237786855641560837 := by
  unfold tailWord_4648197
  simp only [CollatzResearch.WordTrace]
  refine ⟨169533672341383592691174845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113022448227589061794116563 169533672341383592691174845)
  ·
    refine ⟨63575127128018847259190567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 169533672341383592691174845 63575127128018847259190567)
    ·
      refine ⟨95362690692028270888785851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63575127128018847259190567 95362690692028270888785851)
      ·
        refine ⟨143044036038042406333178777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95362690692028270888785851 143044036038042406333178777)
        ·
          refine ⟨107283027028531804749884083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 143044036038042406333178777 107283027028531804749884083)
          ·
            refine ⟨160924540542797707124826125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107283027028531804749884083 160924540542797707124826125)
            ·
              refine ⟨60346702703549140171809797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 160924540542797707124826125 60346702703549140171809797)
              ·
                refine ⟨11315006756915463782214337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60346702703549140171809797 11315006756915463782214337)
                ·
                  refine ⟨8486255067686597836660753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11315006756915463782214337 8486255067686597836660753)
                  ·
                    refine ⟨6364691300764948377495565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8486255067686597836660753 6364691300764948377495565)
                    ·
                      refine ⟨2386759237786855641560837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6364691300764948377495565 2386759237786855641560837)
                      ·
                        rfl

theorem cell23_4648197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 4, 2, 2, 3].length) (baseStart_4648197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4648197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4648197 prefixEnd_4648197 := by exact prefixLift 4648197
  have htrace : WordTrace (prefixWord ++ tailWord_4648197) baseStart_4648197 baseEnd_4648197 := by
    simpa [prefixWord, tailWord_4648197, baseEnd_4648197] using wordTrace_append hprefix tailTrace_4648197
  have hstable : (prefixWord ++ tailWord_4648197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4648197).length < 2 ^ (prefixWord ++ tailWord_4648197).sum := by decide
  have hdescent : baseEnd_4648197 < baseStart_4648197 := by decide
  rcases family_descends (prefixWord ++ tailWord_4648197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4648295 : List Nat := [1, 1, 5, 1, 4, 2, 1, 3, 1, 1, 3]
def baseStart_4648295 : Nat := 118140960795 + 4648295 * 2 ^ 59
def prefixEnd_4648295 : Nat := 4983230072969 + 3 ^ 40 * 4648295 * 2
def baseEnd_4648295 : Nat := 2386809558890996258135387

theorem tailTrace_4648295 : CollatzResearch.WordTrace tailWord_4648295 prefixEnd_4648295 2386809558890996258135387 := by
  unfold tailWord_4648295
  simp only [CollatzResearch.WordTrace]
  refine ⟨169537246695028555428242339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113024831130019036952161559 169537246695028555428242339)
  ·
    refine ⟨254305870042542833142363509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169537246695028555428242339 254305870042542833142363509)
    ·
      refine ⟨23841175316488390607096579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 254305870042542833142363509 23841175316488390607096579)
      ·
        refine ⟨35761762974732585910644869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23841175316488390607096579 35761762974732585910644869)
        ·
          refine ⟨6705330557762359858245913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35761762974732585910644869 6705330557762359858245913)
          ·
            refine ⟨5028997918321769893684435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6705330557762359858245913 5028997918321769893684435)
            ·
              refine ⟨7543496877482654840526653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5028997918321769893684435 7543496877482654840526653)
              ·
                refine ⟨2828811329055995565197495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7543496877482654840526653 2828811329055995565197495)
                ·
                  refine ⟨4243216993583993347796243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2828811329055995565197495 4243216993583993347796243)
                  ·
                    refine ⟨6364825490375990021694365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4243216993583993347796243 6364825490375990021694365)
                    ·
                      refine ⟨2386809558890996258135387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6364825490375990021694365 2386809558890996258135387)
                      ·
                        rfl

theorem cell23_4648295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 1, 3, 1, 1, 3].length) (baseStart_4648295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4648295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4648295 prefixEnd_4648295 := by exact prefixLift 4648295
  have htrace : WordTrace (prefixWord ++ tailWord_4648295) baseStart_4648295 baseEnd_4648295 := by
    simpa [prefixWord, tailWord_4648295, baseEnd_4648295] using wordTrace_append hprefix tailTrace_4648295
  have hstable : (prefixWord ++ tailWord_4648295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4648295).length < 2 ^ (prefixWord ++ tailWord_4648295).sum := by decide
  have hdescent : baseEnd_4648295 < baseStart_4648295 := by decide
  rcases family_descends (prefixWord ++ tailWord_4648295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4648304 : List Nat := [2, 1, 1, 1, 4, 2, 1, 5, 1, 2, 3]
def baseStart_4648304 : Nat := 118140960795 + 4648304 * 2 ^ 59
def prefixEnd_4648304 : Nat := 4983230072969 + 3 ^ 40 * 4648304 * 2
def baseEnd_4648304 : Nat := 2386814180216886722922845

theorem tailTrace_4648304 : CollatzResearch.WordTrace tailWord_4648304 prefixEnd_4648304 2386814180216886722922845 := by
  unfold tailWord_4648304
  simp only [CollatzResearch.WordTrace]
  refine ⟨84768787475997974982659983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113025049967997299976879977 84768787475997974982659983)
  ·
    refine ⟨127153181213996962473989975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84768787475997974982659983 127153181213996962473989975)
    ·
      refine ⟨190729771820995443710984963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127153181213996962473989975 190729771820995443710984963)
      ·
        refine ⟨286094657731493165566477445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190729771820995443710984963 286094657731493165566477445)
        ·
          refine ⟨53642748324654968543714521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 286094657731493165566477445 53642748324654968543714521)
          ·
            refine ⟨40232061243491226407785891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53642748324654968543714521 40232061243491226407785891)
            ·
              refine ⟨60348091865236839611678837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40232061243491226407785891 60348091865236839611678837)
              ·
                refine ⟨5657633612365953713594891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 60348091865236839611678837 5657633612365953713594891)
                ·
                  refine ⟨8486450418548930570392337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5657633612365953713594891 8486450418548930570392337)
                  ·
                    refine ⟨6364837813911697927794253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8486450418548930570392337 6364837813911697927794253)
                    ·
                      refine ⟨2386814180216886722922845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6364837813911697927794253 2386814180216886722922845)
                      ·
                        rfl

theorem cell23_4648304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 5, 1, 2, 3].length) (baseStart_4648304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4648304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4648304 prefixEnd_4648304 := by exact prefixLift 4648304
  have htrace : WordTrace (prefixWord ++ tailWord_4648304) baseStart_4648304 baseEnd_4648304 := by
    simpa [prefixWord, tailWord_4648304, baseEnd_4648304] using wordTrace_append hprefix tailTrace_4648304
  have hstable : (prefixWord ++ tailWord_4648304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4648304).length < 2 ^ (prefixWord ++ tailWord_4648304).sum := by decide
  have hdescent : baseEnd_4648304 < baseStart_4648304 := by decide
  rcases family_descends (prefixWord ++ tailWord_4648304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4648328 : List Nat := [2, 1, 3, 3, 1, 4, 2, 1, 2, 4]
def baseStart_4648328 : Nat := 118140960795 + 4648328 * 2 ^ 59
def prefixEnd_4648328 : Nat := 4983230072969 + 3 ^ 40 * 4648328 * 2
def baseEnd_4648328 : Nat := 795608834584198209674245

theorem tailTrace_4648328 : CollatzResearch.WordTrace tailWord_4648328 prefixEnd_4648328 795608834584198209674245 := by
  unfold tailWord_4648328
  simp only [CollatzResearch.WordTrace]
  refine ⟨84769225151954501032096819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113025633535939334709462425 84769225151954501032096819)
  ·
    refine ⟨127153837727931751548145229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84769225151954501032096819 127153837727931751548145229)
    ·
      refine ⟨47682689147974406830554461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 127153837727931751548145229 47682689147974406830554461)
      ·
        refine ⟨17881008430490402561457923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47682689147974406830554461 17881008430490402561457923)
        ·
          refine ⟨26821512645735603842186885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17881008430490402561457923 26821512645735603842186885)
          ·
            refine ⟨5029033621075425720410041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26821512645735603842186885 5029033621075425720410041)
            ·
              refine ⟨3771775215806569290307531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5029033621075425720410041 3771775215806569290307531)
              ·
                refine ⟨5657662823709853935461297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3771775215806569290307531 5657662823709853935461297)
                ·
                  refine ⟨4243247117782390451595973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5657662823709853935461297 4243247117782390451595973)
                  ·
                    refine ⟨795608834584198209674245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4243247117782390451595973 795608834584198209674245)
                    ·
                      rfl

theorem cell23_4648328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 2, 1, 2, 4].length) (baseStart_4648328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4648328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4648328 prefixEnd_4648328 := by exact prefixLift 4648328
  have htrace : WordTrace (prefixWord ++ tailWord_4648328) baseStart_4648328 baseEnd_4648328 := by
    simpa [prefixWord, tailWord_4648328, baseEnd_4648328] using wordTrace_append hprefix tailTrace_4648328
  have hstable : (prefixWord ++ tailWord_4648328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4648328).length < 2 ^ (prefixWord ++ tailWord_4648328).sum := by decide
  have hdescent : baseEnd_4648328 < baseStart_4648328 := by decide
  rcases family_descends (prefixWord ++ tailWord_4648328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4648338 : List Nat := [3, 2, 3, 3, 1, 1, 1, 1, 3, 2, 3]
def baseStart_4648338 : Nat := 118140960795 + 4648338 * 2 ^ 59
def prefixEnd_4648338 : Nat := 4983230072969 + 3 ^ 40 * 4648338 * 2
def baseEnd_4648338 : Nat := 2386831638559139589897689

theorem tailTrace_4648338 : CollatzResearch.WordTrace tailWord_4648338 prefixEnd_4648338 2386831638559139589897689 := by
  unfold tailWord_4648338
  simp only [CollatzResearch.WordTrace]
  refine ⟨42384703758468193443014417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113025876689248515848038445 42384703758468193443014417)
  ·
    refine ⟨31788527818851145082260813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42384703758468193443014417 31788527818851145082260813)
    ·
      refine ⟨11920697932069179405847805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31788527818851145082260813 11920697932069179405847805)
      ·
        refine ⟨4470261724525942277192927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11920697932069179405847805 4470261724525942277192927)
        ·
          refine ⟨6705392586788913415789391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4470261724525942277192927 6705392586788913415789391)
          ·
            refine ⟨10058088880183370123684087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6705392586788913415789391 10058088880183370123684087)
            ·
              refine ⟨15087133320275055185526131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10058088880183370123684087 15087133320275055185526131)
              ·
                refine ⟨22630699980412582778289197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15087133320275055185526131 22630699980412582778289197)
                ·
                  refine ⟨8486512492654718541858449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22630699980412582778289197 8486512492654718541858449)
                  ·
                    refine ⟨6364884369491038906393837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8486512492654718541858449 6364884369491038906393837)
                    ·
                      refine ⟨2386831638559139589897689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6364884369491038906393837 2386831638559139589897689)
                      ·
                        rfl

theorem cell23_4648338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_4648338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4648338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4648338 prefixEnd_4648338 := by exact prefixLift 4648338
  have htrace : WordTrace (prefixWord ++ tailWord_4648338) baseStart_4648338 baseEnd_4648338 := by
    simpa [prefixWord, tailWord_4648338, baseEnd_4648338] using wordTrace_append hprefix tailTrace_4648338
  have hstable : (prefixWord ++ tailWord_4648338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4648338).length < 2 ^ (prefixWord ++ tailWord_4648338).sum := by decide
  have hdescent : baseEnd_4648338 < baseStart_4648338 := by decide
  rcases family_descends (prefixWord ++ tailWord_4648338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4648387 : List Nat := [1, 1, 1, 3, 1, 1, 5, 1, 1, 4, 4]
def baseStart_4648387 : Nat := 118140960795 + 4648387 * 2 ^ 59
def prefixEnd_4648387 : Nat := 4983230072969 + 3 ^ 40 * 4648387 * 2
def baseEnd_4648387 : Nat := 2386856799111209898184963

theorem tailTrace_4648387 : CollatzResearch.WordTrace tailWord_4648387 prefixEnd_4648387 2386856799111209898184963 := by
  unfold tailWord_4648387
  simp only [CollatzResearch.WordTrace]
  refine ⟨169540602210695255140591415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113027068140463503427060943 169540602210695255140591415)
  ·
    refine ⟨254310903316042882710887123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169540602210695255140591415 254310903316042882710887123)
    ·
      refine ⟨381466354974064324066330685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 254310903316042882710887123 381466354974064324066330685)
      ·
        refine ⟨143049883115274121524874007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 381466354974064324066330685 143049883115274121524874007)
        ·
          refine ⟨214574824672911182287311011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143049883115274121524874007 214574824672911182287311011)
          ·
            refine ⟨321862237009366773430966517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 214574824672911182287311011 321862237009366773430966517)
            ·
              refine ⟨30174584719628135009153111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 321862237009366773430966517 30174584719628135009153111)
              ·
                refine ⟨45261877079442202513729667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30174584719628135009153111 45261877079442202513729667)
                ·
                  refine ⟨67892815619163303770594501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45261877079442202513729667 67892815619163303770594501)
                  ·
                    refine ⟨12729902928593119456986469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 67892815619163303770594501 12729902928593119456986469)
                    ·
                      refine ⟨2386856799111209898184963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12729902928593119456986469 2386856799111209898184963)
                      ·
                        rfl

theorem cell23_4648387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 1, 1, 4, 4].length) (baseStart_4648387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4648387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4648387 prefixEnd_4648387 := by exact prefixLift 4648387
  have htrace : WordTrace (prefixWord ++ tailWord_4648387) baseStart_4648387 baseEnd_4648387 := by
    simpa [prefixWord, tailWord_4648387, baseEnd_4648387] using wordTrace_append hprefix tailTrace_4648387
  have hstable : (prefixWord ++ tailWord_4648387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4648387).length < 2 ^ (prefixWord ++ tailWord_4648387).sum := by decide
  have hdescent : baseEnd_4648387 < baseStart_4648387 := by decide
  rcases family_descends (prefixWord ++ tailWord_4648387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4648391 : List Nat := [1, 1, 4, 1, 1, 3, 4, 1, 1, 4, 2]
def baseStart_4648391 : Nat := 118140960795 + 4648391 * 2 ^ 59
def prefixEnd_4648391 : Nat := 4983230072969 + 3 ^ 40 * 4648391 * 2
def baseEnd_4648391 : Nat := 2386858853033827882534945

theorem tailTrace_4648391 : CollatzResearch.WordTrace tailWord_4648391 prefixEnd_4648391 2386858853033827882534945 := by
  unfold tailWord_4648391
  simp only [CollatzResearch.WordTrace]
  refine ⟨169540748102680763823737027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113027165401787175882491351 169540748102680763823737027)
  ·
    refine ⟨254311122154021145735605541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169540748102680763823737027 254311122154021145735605541)
    ·
      refine ⟨47683335403878964825426039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 254311122154021145735605541 47683335403878964825426039)
      ·
        refine ⟨71525003105818447238139059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47683335403878964825426039 71525003105818447238139059)
        ·
          refine ⟨107287504658727670857208589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71525003105818447238139059 107287504658727670857208589)
          ·
            refine ⟨40232814247022876571453221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 107287504658727670857208589 40232814247022876571453221)
            ·
              refine ⟨7543652671316789357147479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40232814247022876571453221 7543652671316789357147479)
              ·
                refine ⟨11315479006975184035721219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7543652671316789357147479 11315479006975184035721219)
                ·
                  refine ⟨16973218510462776053581829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11315479006975184035721219 16973218510462776053581829)
                  ·
                    refine ⟨3182478470711770510046593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16973218510462776053581829 3182478470711770510046593)
                    ·
                      refine ⟨2386858853033827882534945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3182478470711770510046593 2386858853033827882534945)
                      ·
                        rfl

theorem cell23_4648391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 4, 1, 1, 4, 2].length) (baseStart_4648391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4648391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4648391 prefixEnd_4648391 := by exact prefixLift 4648391
  have htrace : WordTrace (prefixWord ++ tailWord_4648391) baseStart_4648391 baseEnd_4648391 := by
    simpa [prefixWord, tailWord_4648391, baseEnd_4648391] using wordTrace_append hprefix tailTrace_4648391
  have hstable : (prefixWord ++ tailWord_4648391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4648391).length < 2 ^ (prefixWord ++ tailWord_4648391).sum := by decide
  have hdescent : baseEnd_4648391 < baseStart_4648391 := by decide
  rcases family_descends (prefixWord ++ tailWord_4648391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4648424 : List Nat := [2, 1, 4, 1, 1, 2, 1, 1, 4, 3, 3]
def baseStart_4648424 : Nat := 118140960795 + 4648424 * 2 ^ 59
def prefixEnd_4648424 : Nat := 4983230072969 + 3 ^ 40 * 4648424 * 2
def baseEnd_4648424 : Nat := 2386875797895426253422293

theorem tailTrace_4648424 : CollatzResearch.WordTrace tailWord_4648424 prefixEnd_4648424 2386875797895426253422293 := by
  unfold tailWord_4648424
  simp only [CollatzResearch.WordTrace]
  refine ⟨84770975855780605229844163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113027967807707473639792217 84770975855780605229844163)
  ·
    refine ⟨127156463783670907844766245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84770975855780605229844163 127156463783670907844766245)
    ·
      refine ⟨23841836959438295220893671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 127156463783670907844766245 23841836959438295220893671)
      ·
        refine ⟨35762755439157442831340507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23841836959438295220893671 35762755439157442831340507)
        ·
          refine ⟨53644133158736164247010761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35762755439157442831340507 53644133158736164247010761)
          ·
            refine ⟨40233099869052123185258071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53644133158736164247010761 40233099869052123185258071)
            ·
              refine ⟨60349649803578184777887107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40233099869052123185258071 60349649803578184777887107)
              ·
                refine ⟨90524474705367277166830661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60349649803578184777887107 90524474705367277166830661)
                ·
                  refine ⟨16973339007256364468780749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 90524474705367277166830661 16973339007256364468780749)
                  ·
                    refine ⟨6365002127721136675792781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16973339007256364468780749 6365002127721136675792781)
                    ·
                      refine ⟨2386875797895426253422293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6365002127721136675792781 2386875797895426253422293)
                      ·
                        rfl

theorem cell23_4648424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 4, 3, 3].length) (baseStart_4648424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4648424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4648424 prefixEnd_4648424 := by exact prefixLift 4648424
  have htrace : WordTrace (prefixWord ++ tailWord_4648424) baseStart_4648424 baseEnd_4648424 := by
    simpa [prefixWord, tailWord_4648424, baseEnd_4648424] using wordTrace_append hprefix tailTrace_4648424
  have hstable : (prefixWord ++ tailWord_4648424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4648424).length < 2 ^ (prefixWord ++ tailWord_4648424).sum := by decide
  have hdescent : baseEnd_4648424 < baseStart_4648424 := by decide
  rcases family_descends (prefixWord ++ tailWord_4648424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4648457 : List Nat := [1, 2, 1, 1, 3, 1, 3, 1, 2, 8]
def baseStart_4648457 : Nat := 118140960795 + 4648457 * 2 ^ 59
def prefixEnd_4648457 : Nat := 4983230072969 + 3 ^ 40 * 4648457 * 2
def baseEnd_4648457 : Nat := 795630914252341541436547

theorem tailTrace_4648457 : CollatzResearch.WordTrace tailWord_4648457 prefixEnd_4648457 795630914252341541436547 := by
  unfold tailWord_4648457
  simp only [CollatzResearch.WordTrace]
  refine ⟨169543155320441657095639625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113028770213627771397093083 169543155320441657095639625)
  ·
    refine ⟨127157366490331242821729719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169543155320441657095639625 127157366490331242821729719)
    ·
      refine ⟨190736049735496864232594579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127157366490331242821729719 190736049735496864232594579)
      ·
        refine ⟨286104074603245296348891869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190736049735496864232594579 286104074603245296348891869)
        ·
          refine ⟨107289027976216986130834451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 286104074603245296348891869 107289027976216986130834451)
          ·
            refine ⟨160933541964325479196251677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107289027976216986130834451 160933541964325479196251677)
            ·
              refine ⟨60350078236622054698594379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 160933541964325479196251677 60350078236622054698594379)
              ·
                refine ⟨90525117354933082047891569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60350078236622054698594379 90525117354933082047891569)
                ·
                  refine ⟨67893838016199811535918677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 90525117354933082047891569 67893838016199811535918677)
                  ·
                    refine ⟨795630914252341541436547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 67893838016199811535918677 795630914252341541436547)
                    ·
                      rfl

theorem cell23_4648457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 2, 8].length) (baseStart_4648457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4648457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4648457 prefixEnd_4648457 := by exact prefixLift 4648457
  have htrace : WordTrace (prefixWord ++ tailWord_4648457) baseStart_4648457 baseEnd_4648457 := by
    simpa [prefixWord, tailWord_4648457, baseEnd_4648457] using wordTrace_append hprefix tailTrace_4648457
  have hstable : (prefixWord ++ tailWord_4648457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4648457).length < 2 ^ (prefixWord ++ tailWord_4648457).sum := by decide
  have hdescent : baseEnd_4648457 < baseStart_4648457 := by decide
  rcases family_descends (prefixWord ++ tailWord_4648457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4648481 : List Nat := [1, 2, 3, 2, 2, 3, 1, 2, 2, 1, 4]
def baseStart_4648481 : Nat := 118140960795 + 4648481 * 2 ^ 59
def prefixEnd_4648481 : Nat := 4983230072969 + 3 ^ 40 * 4648481 * 2
def baseEnd_4648481 : Nat := 2386905066292732530409531

theorem tailTrace_4648481 : CollatzResearch.WordTrace tailWord_4648481 prefixEnd_4648481 2386905066292732530409531 := by
  unfold tailWord_4648481
  simp only [CollatzResearch.WordTrace]
  refine ⟨169544030672354709194513297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113029353781569806129675531 169544030672354709194513297)
  ·
    refine ⟨127158023004266031895884973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169544030672354709194513297 127158023004266031895884973)
    ·
      refine ⟨47684258626599761960956865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 127158023004266031895884973 47684258626599761960956865)
      ·
        refine ⟨35763193969949821470717649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47684258626599761960956865 35763193969949821470717649)
        ·
          refine ⟨26822395477462366103038237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35763193969949821470717649 26822395477462366103038237)
          ·
            refine ⟨10058398304048387288639339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26822395477462366103038237 10058398304048387288639339)
            ·
              refine ⟨15087597456072580932959009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10058398304048387288639339 15087597456072580932959009)
              ·
                refine ⟨11315698092054435699719257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15087597456072580932959009 11315698092054435699719257)
                ·
                  refine ⟨8486773569040826774789443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11315698092054435699719257 8486773569040826774789443)
                  ·
                    refine ⟨12730160353561240162184165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8486773569040826774789443 12730160353561240162184165)
                    ·
                      refine ⟨2386905066292732530409531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12730160353561240162184165 2386905066292732530409531)
                      ·
                        rfl

theorem cell23_4648481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 2, 2, 1, 4].length) (baseStart_4648481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4648481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4648481 prefixEnd_4648481 := by exact prefixLift 4648481
  have htrace : WordTrace (prefixWord ++ tailWord_4648481) baseStart_4648481 baseEnd_4648481 := by
    simpa [prefixWord, tailWord_4648481, baseEnd_4648481] using wordTrace_append hprefix tailTrace_4648481
  have hstable : (prefixWord ++ tailWord_4648481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4648481).length < 2 ^ (prefixWord ++ tailWord_4648481).sum := by decide
  have hdescent : baseEnd_4648481 < baseStart_4648481 := by decide
  rcases family_descends (prefixWord ++ tailWord_4648481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4648565 : List Nat := [1, 3, 4, 2, 1, 2, 1, 2, 3, 1, 3]
def baseStart_4648565 : Nat := 118140960795 + 4648565 * 2 ^ 59
def prefixEnd_4648565 : Nat := 4983230072969 + 3 ^ 40 * 4648565 * 2
def baseEnd_4648565 : Nat := 2386948198667710201759145

theorem tailTrace_4648565 : CollatzResearch.WordTrace tailWord_4648565 prefixEnd_4648565 2386948198667710201759145 := by
  unfold tailWord_4648565
  simp only [CollatzResearch.WordTrace]
  refine ⟨169547094404050391540571149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113031396269366927693714099 169547094404050391540571149)
  ·
    refine ⟨63580160401518896827714181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 169547094404050391540571149 63580160401518896827714181)
    ·
      refine ⟨11921280075284793155196409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63580160401518896827714181 11921280075284793155196409)
      ·
        refine ⟨8940960056463594866397307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11921280075284793155196409 8940960056463594866397307)
        ·
          refine ⟨13411440084695392299595961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8940960056463594866397307 13411440084695392299595961)
          ·
            refine ⟨10058580063521544224696971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13411440084695392299595961 10058580063521544224696971)
            ·
              refine ⟨15087870095282316337045457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10058580063521544224696971 15087870095282316337045457)
              ·
                refine ⟨11315902571461737252784093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15087870095282316337045457 11315902571461737252784093)
                ·
                  refine ⟨4243463464298151469794035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11315902571461737252784093 4243463464298151469794035)
                  ·
                    refine ⟨6365195196447227204691053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4243463464298151469794035 6365195196447227204691053)
                    ·
                      refine ⟨2386948198667710201759145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6365195196447227204691053 2386948198667710201759145)
                      ·
                        rfl

theorem cell23_4648565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_4648565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4648565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4648565 prefixEnd_4648565 := by exact prefixLift 4648565
  have htrace : WordTrace (prefixWord ++ tailWord_4648565) baseStart_4648565 baseEnd_4648565 := by
    simpa [prefixWord, tailWord_4648565, baseEnd_4648565] using wordTrace_append hprefix tailTrace_4648565
  have hstable : (prefixWord ++ tailWord_4648565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4648565).length < 2 ^ (prefixWord ++ tailWord_4648565).sum := by decide
  have hdescent : baseEnd_4648565 < baseStart_4648565 := by decide
  rcases family_descends (prefixWord ++ tailWord_4648565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4648571 : List Nat := [1, 1, 1, 1, 1, 4, 4, 4, 1, 1, 4]
def baseStart_4648571 : Nat := 118140960795 + 4648571 * 2 ^ 59
def prefixEnd_4648571 : Nat := 4983230072969 + 3 ^ 40 * 4648571 * 2
def baseEnd_4648571 : Nat := 2386951279551637178284117

theorem tailTrace_4648571 : CollatzResearch.WordTrace tailWord_4648571 prefixEnd_4648571 2386951279551637178284117 := by
  unfold tailWord_4648571
  simp only [CollatzResearch.WordTrace]
  refine ⟨169547313242028654565289567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113031542161352436376859711 169547313242028654565289567)
  ·
    refine ⟨254320969863042981847934351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169547313242028654565289567 254320969863042981847934351)
    ·
      refine ⟨381481454794564472771901527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 254320969863042981847934351 381481454794564472771901527)
      ·
        refine ⟨572222182191846709157852291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 381481454794564472771901527 572222182191846709157852291)
        ·
          refine ⟨858333273287770063736778437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 572222182191846709157852291 858333273287770063736778437)
          ·
            refine ⟨160937488741456886950645957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 858333273287770063736778437 160937488741456886950645957)
            ·
              refine ⟨30175779139023166303246117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 160937488741456886950645957 30175779139023166303246117)
              ·
                refine ⟨5657958588566843681858647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30175779139023166303246117 5657958588566843681858647)
                ·
                  refine ⟨8486937882850265522787971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5657958588566843681858647 8486937882850265522787971)
                  ·
                    refine ⟨12730406824275398284181957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8486937882850265522787971 12730406824275398284181957)
                    ·
                      refine ⟨2386951279551637178284117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12730406824275398284181957 2386951279551637178284117)
                      ·
                        rfl

theorem cell23_4648571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 4, 1, 1, 4].length) (baseStart_4648571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4648571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4648571 prefixEnd_4648571 := by exact prefixLift 4648571
  have htrace : WordTrace (prefixWord ++ tailWord_4648571) baseStart_4648571 baseEnd_4648571 := by
    simpa [prefixWord, tailWord_4648571, baseEnd_4648571] using wordTrace_append hprefix tailTrace_4648571
  have hstable : (prefixWord ++ tailWord_4648571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4648571).length < 2 ^ (prefixWord ++ tailWord_4648571).sum := by decide
  have hdescent : baseEnd_4648571 < baseStart_4648571 := by decide
  rcases family_descends (prefixWord ++ tailWord_4648571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4648581 : List Nat := [1, 3, 1, 1, 4, 1, 2, 2, 4, 4]
def baseStart_4648581 : Nat := 118140960795 + 4648581 * 2 ^ 59
def prefixEnd_4648581 : Nat := 4983230072969 + 3 ^ 40 * 4648581 * 2
def baseEnd_4648581 : Nat := 795652138119394046386357

theorem tailTrace_4648581 : CollatzResearch.WordTrace tailWord_4648581 prefixEnd_4648581 795652138119394046386357 := by
  unfold tailWord_4648581
  simp only [CollatzResearch.WordTrace]
  refine ⟨169547677971992426273153597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113031785314661617515435731 169547677971992426273153597)
  ·
    refine ⟨63580379239497159852432599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 169547677971992426273153597 63580379239497159852432599)
    ·
      refine ⟨95370568859245739778648899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63580379239497159852432599 95370568859245739778648899)
      ·
        refine ⟨143055853288868609667973349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95370568859245739778648899 143055853288868609667973349)
        ·
          refine ⟨26822972491662864312745003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 143055853288868609667973349 26822972491662864312745003)
          ·
            refine ⟨40234458737494296469117505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26822972491662864312745003 40234458737494296469117505)
            ·
              refine ⟨30175844053120722351838129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40234458737494296469117505 30175844053120722351838129)
              ·
                refine ⟨22631883039840541763878597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30175844053120722351838129 22631883039840541763878597)
                ·
                  refine ⟨4243478069970101580727237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22631883039840541763878597 4243478069970101580727237)
                  ·
                    refine ⟨795652138119394046386357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4243478069970101580727237 795652138119394046386357)
                    ·
                      rfl

theorem cell23_4648581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 2, 4, 4].length) (baseStart_4648581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4648581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4648581 prefixEnd_4648581 := by exact prefixLift 4648581
  have htrace : WordTrace (prefixWord ++ tailWord_4648581) baseStart_4648581 baseEnd_4648581 := by
    simpa [prefixWord, tailWord_4648581, baseEnd_4648581] using wordTrace_append hprefix tailTrace_4648581
  have hstable : (prefixWord ++ tailWord_4648581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4648581).length < 2 ^ (prefixWord ++ tailWord_4648581).sum := by decide
  have hdescent : baseEnd_4648581 < baseStart_4648581 := by decide
  rcases family_descends (prefixWord ++ tailWord_4648581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4648588 : List Nat := [2, 2, 1, 2, 1, 1, 3, 2, 5, 2, 2]
def baseStart_4648588 : Nat := 118140960795 + 4648588 * 2 ^ 59
def prefixEnd_4648588 : Nat := 4983230072969 + 3 ^ 40 * 4648588 * 2
def baseEnd_4648588 : Nat := 2386960008722763611771539

theorem tailTrace_4648588 : CollatzResearch.WordTrace tailWord_4648588 prefixEnd_4648588 2386960008722763611771539 := by
  unfold tailWord_4648588
  simp only [CollatzResearch.WordTrace]
  refine ⟨84773966641483533234329209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113031955521978044312438945 84773966641483533234329209)
  ·
    refine ⟨63580474981112649925746907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84773966641483533234329209 63580474981112649925746907)
    ·
      refine ⟨95370712471668974888620361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63580474981112649925746907 95370712471668974888620361)
      ·
        refine ⟨71528034353751731166465271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95370712471668974888620361 71528034353751731166465271)
        ·
          refine ⟨107292051530627596749697907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71528034353751731166465271 107292051530627596749697907)
          ·
            refine ⟨160938077295941395124546861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107292051530627596749697907 160938077295941395124546861)
            ·
              refine ⟨60351778985978023171705073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 160938077295941395124546861 60351778985978023171705073)
              ·
                refine ⟨45263834239483517378778805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60351778985978023171705073 45263834239483517378778805)
                ·
                  refine ⟨4243484459951579754260513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45263834239483517378778805 4243484459951579754260513)
                  ·
                    refine ⟨3182613344963684815695385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4243484459951579754260513 3182613344963684815695385)
                    ·
                      refine ⟨2386960008722763611771539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3182613344963684815695385 2386960008722763611771539)
                      ·
                        rfl

theorem cell23_4648588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 5, 2, 2].length) (baseStart_4648588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4648588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4648588 prefixEnd_4648588 := by exact prefixLift 4648588
  have htrace : WordTrace (prefixWord ++ tailWord_4648588) baseStart_4648588 baseEnd_4648588 := by
    simpa [prefixWord, tailWord_4648588, baseEnd_4648588] using wordTrace_append hprefix tailTrace_4648588
  have hstable : (prefixWord ++ tailWord_4648588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4648588).length < 2 ^ (prefixWord ++ tailWord_4648588).sum := by decide
  have hdescent : baseEnd_4648588 < baseStart_4648588 := by decide
  rcases family_descends (prefixWord ++ tailWord_4648588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4648622 : List Nat := [4, 1, 4, 1, 2, 1, 2, 2, 1, 1, 4]
def baseStart_4648622 : Nat := 118140960795 + 4648622 * 2 ^ 59
def prefixEnd_4648622 : Nat := 4983230072969 + 3 ^ 40 * 4648622 * 2
def baseEnd_4648622 : Nat := 2386977467065016478746383

theorem tailTrace_4648622 : CollatzResearch.WordTrace tailWord_4648622 prefixEnd_4648622 2386977467065016478746383 := by
  unfold tailWord_4648622
  simp only [CollatzResearch.WordTrace]
  refine ⟨21193646670605486284424515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113032782243229260183597413 21193646670605486284424515)
  ·
    refine ⟨31790470005908229426636773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21193646670605486284424515 31790470005908229426636773)
    ·
      refine ⟨5960713126107793017494395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31790470005908229426636773 5960713126107793017494395)
      ·
        refine ⟨8941069689161689526241593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5960713126107793017494395 8941069689161689526241593)
        ·
          refine ⟨6705802266871267144681195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8941069689161689526241593 6705802266871267144681195)
          ·
            refine ⟨10058703400306900717021793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6705802266871267144681195 10058703400306900717021793)
            ·
              refine ⟨7544027550230175537766345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10058703400306900717021793 7544027550230175537766345)
              ·
                refine ⟨5658020662672631653324759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7544027550230175537766345 5658020662672631653324759)
                ·
                  refine ⟨8487030994008947479987139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5658020662672631653324759 8487030994008947479987139)
                  ·
                    refine ⟨12730546491013421219980709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8487030994008947479987139 12730546491013421219980709)
                    ·
                      refine ⟨2386977467065016478746383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12730546491013421219980709 2386977467065016478746383)
                      ·
                        rfl

theorem cell23_4648622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_4648622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4648622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4648622 prefixEnd_4648622 := by exact prefixLift 4648622
  have htrace : WordTrace (prefixWord ++ tailWord_4648622) baseStart_4648622 baseEnd_4648622 := by
    simpa [prefixWord, tailWord_4648622, baseEnd_4648622] using wordTrace_append hprefix tailTrace_4648622
  have hstable : (prefixWord ++ tailWord_4648622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4648622).length < 2 ^ (prefixWord ++ tailWord_4648622).sum := by decide
  have hdescent : baseEnd_4648622 < baseStart_4648622 := by decide
  rcases family_descends (prefixWord ++ tailWord_4648622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4648624 : List Nat := [2, 1, 1, 1, 2, 1, 4, 2, 2, 7]
def baseStart_4648624 : Nat := 118140960795 + 4648624 * 2 ^ 59
def prefixEnd_4648624 : Nat := 4983230072969 + 3 ^ 40 * 4648624 * 2
def baseEnd_4648624 : Nat := 795659498008775156973791

theorem tailTrace_4648624 : CollatzResearch.WordTrace tailWord_4648624 prefixEnd_4648624 795659498008775156973791 := by
  unfold tailWord_4648624
  simp only [CollatzResearch.WordTrace]
  refine ⟨84774623155418322308484463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113032830873891096411312617 84774623155418322308484463)
  ·
    refine ⟨127161934733127483462726695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84774623155418322308484463 127161934733127483462726695)
    ·
      refine ⟨190742902099691225194090043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127161934733127483462726695 190742902099691225194090043)
      ·
        refine ⟨286114353149536837791135065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190742902099691225194090043 286114353149536837791135065)
        ·
          refine ⟨214585764862152628343351299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 286114353149536837791135065 214585764862152628343351299)
          ·
            refine ⟨321878647293228942515026949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 214585764862152628343351299 321878647293228942515026949)
            ·
              refine ⟨60352246367480426721567553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 321878647293228942515026949 60352246367480426721567553)
              ·
                refine ⟨45264184775610320041175665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60352246367480426721567553 45264184775610320041175665)
                ·
                  refine ⟨33948138581707740030881749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45264184775610320041175665 33948138581707740030881749)
                  ·
                    refine ⟨795659498008775156973791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33948138581707740030881749 795659498008775156973791)
                    ·
                      rfl

theorem cell23_4648624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 2, 2, 7].length) (baseStart_4648624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4648624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4648624 prefixEnd_4648624 := by exact prefixLift 4648624
  have htrace : WordTrace (prefixWord ++ tailWord_4648624) baseStart_4648624 baseEnd_4648624 := by
    simpa [prefixWord, tailWord_4648624, baseEnd_4648624] using wordTrace_append hprefix tailTrace_4648624
  have hstable : (prefixWord ++ tailWord_4648624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4648624).length < 2 ^ (prefixWord ++ tailWord_4648624).sum := by decide
  have hdescent : baseEnd_4648624 < baseStart_4648624 := by decide
  rcases family_descends (prefixWord ++ tailWord_4648624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4648712 : List Nat := [2, 1, 3, 2, 2, 1, 4, 2, 2, 2, 2]
def baseStart_4648712 : Nat := 118140960795 + 4648712 * 2 ^ 59
def prefixEnd_4648712 : Nat := 4983230072969 + 3 ^ 40 * 4648712 * 2
def baseEnd_4648712 : Nat := 2387023680323921126620969

theorem tailTrace_4648712 : CollatzResearch.WordTrace tailWord_4648712 prefixEnd_4648712 2387023680323921126620969 := by
  unfold tailWord_4648712
  simp only [CollatzResearch.WordTrace]
  refine ⟨84776227967258917823086195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113034970623011890430781593 84776227967258917823086195)
  ·
    refine ⟨127164341950888376734629293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84776227967258917823086195 127164341950888376734629293)
    ·
      refine ⟨47686628231583141275485985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 127164341950888376734629293 47686628231583141275485985)
      ·
        refine ⟨35764971173687355956614489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47686628231583141275485985 35764971173687355956614489)
        ·
          refine ⟨26823728380265516967460867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35764971173687355956614489 26823728380265516967460867)
          ·
            refine ⟨40235592570398275451191301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26823728380265516967460867 40235592570398275451191301)
            ·
              refine ⟨7544173606949676647098369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40235592570398275451191301 7544173606949676647098369)
              ·
                refine ⟨5658130205212257485323777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7544173606949676647098369 5658130205212257485323777)
                ·
                  refine ⟨4243597653909193113992833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5658130205212257485323777 4243597653909193113992833)
                  ·
                    refine ⟨3182698240431894835494625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4243597653909193113992833 3182698240431894835494625)
                    ·
                      refine ⟨2387023680323921126620969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3182698240431894835494625 2387023680323921126620969)
                      ·
                        rfl

theorem cell23_4648712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 4, 2, 2, 2, 2].length) (baseStart_4648712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4648712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4648712 prefixEnd_4648712 := by exact prefixLift 4648712
  have htrace : WordTrace (prefixWord ++ tailWord_4648712) baseStart_4648712 baseEnd_4648712 := by
    simpa [prefixWord, tailWord_4648712, baseEnd_4648712] using wordTrace_append hprefix tailTrace_4648712
  have hstable : (prefixWord ++ tailWord_4648712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4648712).length < 2 ^ (prefixWord ++ tailWord_4648712).sum := by decide
  have hdescent : baseEnd_4648712 < baseStart_4648712 := by decide
  rcases family_descends (prefixWord ++ tailWord_4648712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4648748 : List Nat := [2, 2, 1, 1, 1, 5, 3, 1, 2, 5]
def baseStart_4648748 : Nat := 118140960795 + 4648748 * 2 ^ 59
def prefixEnd_4648748 : Nat := 4983230072969 + 3 ^ 40 * 4648748 * 2
def baseEnd_4648748 : Nat := 795680721875827661923601

theorem tailTrace_4648748 : CollatzResearch.WordTrace tailWord_4648748 prefixEnd_4648748 795680721875827661923601 := by
  unfold tailWord_4648748
  simp only [CollatzResearch.WordTrace]
  refine ⟨84776884481193706897241449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113035845974924942529655265 84776884481193706897241449)
  ·
    refine ⟨63582663360895280172931087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84776884481193706897241449 63582663360895280172931087)
    ·
      refine ⟨95373995041342920259396631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63582663360895280172931087 95373995041342920259396631)
      ·
        refine ⟨143060992562014380389094947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95373995041342920259396631 143060992562014380389094947)
        ·
          refine ⟨214591488843021570583642421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143060992562014380389094947 214591488843021570583642421)
          ·
            refine ⟨20117952079033272242216477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 214591488843021570583642421 20117952079033272242216477)
            ·
              refine ⟨7544232029637477090831179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20117952079033272242216477 7544232029637477090831179)
              ·
                refine ⟨11316348044456215636246769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7544232029637477090831179 11316348044456215636246769)
                ·
                  refine ⟨8487261033342161727185077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11316348044456215636246769 8487261033342161727185077)
                  ·
                    refine ⟨795680721875827661923601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8487261033342161727185077 795680721875827661923601)
                    ·
                      rfl

theorem cell23_4648748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 5].length) (baseStart_4648748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4648748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4648748 prefixEnd_4648748 := by exact prefixLift 4648748
  have htrace : WordTrace (prefixWord ++ tailWord_4648748) baseStart_4648748 baseEnd_4648748 := by
    simpa [prefixWord, tailWord_4648748, baseEnd_4648748] using wordTrace_append hprefix tailTrace_4648748
  have hstable : (prefixWord ++ tailWord_4648748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4648748).length < 2 ^ (prefixWord ++ tailWord_4648748).sum := by decide
  have hdescent : baseEnd_4648748 < baseStart_4648748 := by decide
  rcases family_descends (prefixWord ++ tailWord_4648748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4648751 : List Nat := [1, 1, 2, 1, 2, 1, 2, 5, 1, 3, 4]
def baseStart_4648751 : Nat := 118140960795 + 4648751 * 2 ^ 59
def prefixEnd_4648751 : Nat := 4983230072969 + 3 ^ 40 * 4648751 * 2
def baseEnd_4648751 : Nat := 2387043706069446474033289

theorem tailTrace_4648751 : CollatzResearch.WordTrace tailWord_4648751 prefixEnd_4648751 2387043706069446474033289 := by
  unfold tailWord_4648751
  simp only [CollatzResearch.WordTrace]
  refine ⟨169553878381376545306842107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113035918920917696871228071 169553878381376545306842107)
  ·
    refine ⟨254330817572064817960263161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169553878381376545306842107 254330817572064817960263161)
    ·
      refine ⟨190748113179048613470197371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 254330817572064817960263161 190748113179048613470197371)
      ·
        refine ⟨286122169768572920205296057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190748113179048613470197371 286122169768572920205296057)
        ·
          refine ⟨214591627326429690153972043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 286122169768572920205296057 214591627326429690153972043)
          ·
            refine ⟨321887440989644535230958065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 214591627326429690153972043 321887440989644535230958065)
            ·
              refine ⟨241415580742233401423218549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 321887440989644535230958065 241415580742233401423218549)
              ·
                refine ⟨22632710694584381383426739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 241415580742233401423218549 22632710694584381383426739)
                ·
                  refine ⟨33949066041876572075140109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22632710694584381383426739 33949066041876572075140109)
                  ·
                    refine ⟨12730899765703714528177541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33949066041876572075140109 12730899765703714528177541)
                    ·
                      refine ⟨2387043706069446474033289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12730899765703714528177541 2387043706069446474033289)
                      ·
                        rfl

theorem cell23_4648751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 5, 1, 3, 4].length) (baseStart_4648751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4648751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4648751 prefixEnd_4648751 := by exact prefixLift 4648751
  have htrace : WordTrace (prefixWord ++ tailWord_4648751) baseStart_4648751 baseEnd_4648751 := by
    simpa [prefixWord, tailWord_4648751, baseEnd_4648751] using wordTrace_append hprefix tailTrace_4648751
  have hstable : (prefixWord ++ tailWord_4648751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4648751).length < 2 ^ (prefixWord ++ tailWord_4648751).sum := by decide
  have hdescent : baseEnd_4648751 < baseStart_4648751 := by decide
  rcases family_descends (prefixWord ++ tailWord_4648751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4648785 : List Nat := [1, 2, 2, 1, 5, 1, 2, 1, 2, 4, 2]
def baseStart_4648785 : Nat := 118140960795 + 4648785 * 2 ^ 59
def prefixEnd_4648785 : Nat := 4983230072969 + 3 ^ 40 * 4648785 * 2
def baseEnd_4648785 : Nat := 2387061164411699341008133

theorem tailTrace_4648785 : CollatzResearch.WordTrace tailWord_4648785 prefixEnd_4648785 2387061164411699341008133 := by
  unfold tailWord_4648785
  simp only [CollatzResearch.WordTrace]
  refine ⟨169555118463253369113579809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113036745642168912742386539 169555118463253369113579809)
  ·
    refine ⟨127166338847440026835184857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169555118463253369113579809 127166338847440026835184857)
    ·
      refine ⟨95374754135580020126388643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127166338847440026835184857 95374754135580020126388643)
      ·
        refine ⟨143062131203370030189582965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95374754135580020126388643 143062131203370030189582965)
        ·
          refine ⟨13412074800315940330273403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 143062131203370030189582965 13412074800315940330273403)
          ·
            refine ⟨20118112200473910495410105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13412074800315940330273403 20118112200473910495410105)
            ·
              refine ⟨15088584150355432871557579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20118112200473910495410105 15088584150355432871557579)
              ·
                refine ⟨22632876225533149307336369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15088584150355432871557579 22632876225533149307336369)
                ·
                  refine ⟨16974657169149861980502277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22632876225533149307336369 16974657169149861980502277)
                  ·
                    refine ⟨3182748219215599121344177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16974657169149861980502277 3182748219215599121344177)
                    ·
                      refine ⟨2387061164411699341008133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3182748219215599121344177 2387061164411699341008133)
                      ·
                        rfl

theorem cell23_4648785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 1, 2, 4, 2].length) (baseStart_4648785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4648785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4648785 prefixEnd_4648785 := by exact prefixLift 4648785
  have htrace : WordTrace (prefixWord ++ tailWord_4648785) baseStart_4648785 baseEnd_4648785 := by
    simpa [prefixWord, tailWord_4648785, baseEnd_4648785] using wordTrace_append hprefix tailTrace_4648785
  have hstable : (prefixWord ++ tailWord_4648785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4648785).length < 2 ^ (prefixWord ++ tailWord_4648785).sum := by decide
  have hdescent : baseEnd_4648785 < baseStart_4648785 := by decide
  rcases family_descends (prefixWord ++ tailWord_4648785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4648812 : List Nat := [2, 2, 1, 1, 4, 2, 3, 3, 1, 4]
def baseStart_4648812 : Nat := 118140960795 + 4648812 * 2 ^ 59
def prefixEnd_4648812 : Nat := 4983230072969 + 3 ^ 40 * 4648812 * 2
def baseEnd_4648812 : Nat := 795691676129790245123503

theorem tailTrace_4648812 : CollatzResearch.WordTrace tailWord_4648812 prefixEnd_4648812 795691676129790245123503 := by
  unfold tailWord_4648812
  simp only [CollatzResearch.WordTrace]
  refine ⟨84778051617077776362406345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113037402156103701816541793 84778051617077776362406345)
  ·
    refine ⟨63583538712808332271804759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84778051617077776362406345 63583538712808332271804759)
    ·
      refine ⟨95375308069212498407707139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63583538712808332271804759 95375308069212498407707139)
      ·
        refine ⟨143062962103818747611560709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95375308069212498407707139 143062962103818747611560709)
        ·
          refine ⟨26824305394466015177167633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 143062962103818747611560709 26824305394466015177167633)
          ·
            refine ⟨20118229045849511382875725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26824305394466015177167633 20118229045849511382875725)
            ·
              refine ⟨7544335892193566768578397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20118229045849511382875725 7544335892193566768578397)
              ·
                refine ⟨2829125959572587538216899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7544335892193566768578397 2829125959572587538216899)
                ·
                  refine ⟨4243688939358881307325349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2829125959572587538216899 4243688939358881307325349)
                  ·
                    refine ⟨795691676129790245123503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4243688939358881307325349 795691676129790245123503)
                    ·
                      rfl

theorem cell23_4648812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 3, 3, 1, 4].length) (baseStart_4648812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4648812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4648812 prefixEnd_4648812 := by exact prefixLift 4648812
  have htrace : WordTrace (prefixWord ++ tailWord_4648812) baseStart_4648812 baseEnd_4648812 := by
    simpa [prefixWord, tailWord_4648812, baseEnd_4648812] using wordTrace_append hprefix tailTrace_4648812
  have hstable : (prefixWord ++ tailWord_4648812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4648812).length < 2 ^ (prefixWord ++ tailWord_4648812).sum := by decide
  have hdescent : baseEnd_4648812 < baseStart_4648812 := by decide
  rcases family_descends (prefixWord ++ tailWord_4648812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4648831 : List Nat := [1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 7]
def baseStart_4648831 : Nat := 118140960795 + 4648831 * 2 ^ 59
def prefixEnd_4648831 : Nat := 4983230072969 + 3 ^ 40 * 4648831 * 2
def baseEnd_4648831 : Nat := 2387084784521806161032921

theorem tailTrace_4648831 : CollatzResearch.WordTrace tailWord_4648831 prefixEnd_4648831 2387084784521806161032921 := by
  unfold tailWord_4648831
  simp only [CollatzResearch.WordTrace]
  refine ⟨169556796221086718969754347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113037864147391145979836231 169556796221086718969754347)
  ·
    refine ⟨254335194331630078454631521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169556796221086718969754347 254335194331630078454631521)
    ·
      refine ⟨190751395748722558840973641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 254335194331630078454631521 190751395748722558840973641)
      ·
        refine ⟨143063546811541919130730231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 190751395748722558840973641 143063546811541919130730231)
        ·
          refine ⟨214595320217312878696095347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143063546811541919130730231 214595320217312878696095347)
          ·
            refine ⟨321892980325969318044143021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 214595320217312878696095347 321892980325969318044143021)
            ·
              refine ⟨120709867622238494266553633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 321892980325969318044143021 120709867622238494266553633)
              ·
                refine ⟨90532400716678870699915225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 120709867622238494266553633 90532400716678870699915225)
                ·
                  refine ⟨67899300537509153024936419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 90532400716678870699915225 67899300537509153024936419)
                  ·
                    refine ⟨101848950806263729537404629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 67899300537509153024936419 101848950806263729537404629)
                    ·
                      refine ⟨2387084784521806161032921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 101848950806263729537404629 2387084784521806161032921)
                      ·
                        rfl

theorem cell23_4648831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 7].length) (baseStart_4648831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4648831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4648831 prefixEnd_4648831 := by exact prefixLift 4648831
  have htrace : WordTrace (prefixWord ++ tailWord_4648831) baseStart_4648831 baseEnd_4648831 := by
    simpa [prefixWord, tailWord_4648831, baseEnd_4648831] using wordTrace_append hprefix tailTrace_4648831
  have hstable : (prefixWord ++ tailWord_4648831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4648831).length < 2 ^ (prefixWord ++ tailWord_4648831).sum := by decide
  have hdescent : baseEnd_4648831 < baseStart_4648831 := by decide
  rcases family_descends (prefixWord ++ tailWord_4648831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4648855 : List Nat := [1, 1, 3, 3, 1, 3, 3, 2, 1, 5]
def baseStart_4648855 : Nat := 118140960795 + 4648855 * 2 ^ 59
def prefixEnd_4648855 : Nat := 4983230072969 + 3 ^ 40 * 4648855 * 2
def baseEnd_4648855 : Nat := 795699036019171355710937

theorem tailTrace_4648855 : CollatzResearch.WordTrace tailWord_4648855 prefixEnd_4648855 795699036019171355710937 := by
  unfold tailWord_4648855
  simp only [CollatzResearch.WordTrace]
  refine ⟨169557671572999771068628019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113038447715333180712418679 169557671572999771068628019)
  ·
    refine ⟨254336507359499656602942029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169557671572999771068628019 254336507359499656602942029)
    ·
      refine ⟨95376190259812371226103261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 254336507359499656602942029 95376190259812371226103261)
      ·
        refine ⟨35766071347429639209788723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95376190259812371226103261 35766071347429639209788723)
        ·
          refine ⟨53649107021144458814683085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35766071347429639209788723 53649107021144458814683085)
          ·
            refine ⟨20118415132929172055506157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53649107021144458814683085 20118415132929172055506157)
            ·
              refine ⟨7544405674848439520814809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20118415132929172055506157 7544405674848439520814809)
              ·
                refine ⟨5658304256136329640611107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7544405674848439520814809 5658304256136329640611107)
                ·
                  refine ⟨8487456384204494460916661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5658304256136329640611107 8487456384204494460916661)
                  ·
                    refine ⟨795699036019171355710937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8487456384204494460916661 795699036019171355710937)
                    ·
                      rfl

theorem cell23_4648855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 3, 2, 1, 5].length) (baseStart_4648855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4648855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4648855 prefixEnd_4648855 := by exact prefixLift 4648855
  have htrace : WordTrace (prefixWord ++ tailWord_4648855) baseStart_4648855 baseEnd_4648855 := by
    simpa [prefixWord, tailWord_4648855, baseEnd_4648855] using wordTrace_append hprefix tailTrace_4648855
  have hstable : (prefixWord ++ tailWord_4648855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4648855).length < 2 ^ (prefixWord ++ tailWord_4648855).sum := by decide
  have hdescent : baseEnd_4648855 < baseStart_4648855 := by decide
  rcases family_descends (prefixWord ++ tailWord_4648855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4648868 : List Nat := [2, 3, 1, 2, 1, 3, 1, 1, 3, 6]
def baseStart_4648868 : Nat := 118140960795 + 4648868 * 2 ^ 59
def prefixEnd_4648868 : Nat := 4983230072969 + 3 ^ 40 * 4648868 * 2
def baseEnd_4648868 : Nat := 795701261102007505423417

theorem tailTrace_4648868 : CollatzResearch.WordTrace tailWord_4648868 prefixEnd_4648868 795701261102007505423417 := by
  unfold tailWord_4648868
  simp only [CollatzResearch.WordTrace]
  refine ⟨84779072860976337144425629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113038763814635116192567505 84779072860976337144425629)
  ·
    refine ⟨31792152322866126429159611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84779072860976337144425629 31792152322866126429159611)
    ·
      refine ⟨47688228484299189643739417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31792152322866126429159611 47688228484299189643739417)
      ·
        refine ⟨35766171363224392232804563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47688228484299189643739417 35766171363224392232804563)
        ·
          refine ⟨53649257044836588349206845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35766171363224392232804563 53649257044836588349206845)
          ·
            refine ⟨20118471391813720630952567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53649257044836588349206845 20118471391813720630952567)
            ·
              refine ⟨30177707087720580946428851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20118471391813720630952567 30177707087720580946428851)
              ·
                refine ⟨45266560631580871419643277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30177707087720580946428851 45266560631580871419643277)
                ·
                  refine ⟨16974960236842826782366229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45266560631580871419643277 16974960236842826782366229)
                  ·
                    refine ⟨795701261102007505423417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16974960236842826782366229 795701261102007505423417)
                    ·
                      rfl

theorem cell23_4648868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 1, 3, 6].length) (baseStart_4648868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4648868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4648868 prefixEnd_4648868 := by exact prefixLift 4648868
  have htrace : WordTrace (prefixWord ++ tailWord_4648868) baseStart_4648868 baseEnd_4648868 := by
    simpa [prefixWord, tailWord_4648868, baseEnd_4648868] using wordTrace_append hprefix tailTrace_4648868
  have hstable : (prefixWord ++ tailWord_4648868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4648868).length < 2 ^ (prefixWord ++ tailWord_4648868).sum := by decide
  have hdescent : baseEnd_4648868 < baseStart_4648868 := by decide
  rcases family_descends (prefixWord ++ tailWord_4648868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4648888 : List Nat := [2, 1, 2, 1, 2, 3, 1, 2, 3, 2, 4]
def baseStart_4648888 : Nat := 118140960795 + 4648888 * 2 ^ 59
def prefixEnd_4648888 : Nat := 4983230072969 + 3 ^ 40 * 4648888 * 2
def baseEnd_4648888 : Nat := 2387114052919112438020159

theorem tailTrace_4648888 : CollatzResearch.WordTrace tailWord_4648888 prefixEnd_4648888 2387114052919112438020159 := by
  unfold tailWord_4648888
  simp only [CollatzResearch.WordTrace]
  refine ⟨84779437590940108852289659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113039250121253478469719545 84779437590940108852289659)
  ·
    refine ⟨127169156386410163278434489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84779437590940108852289659 127169156386410163278434489)
    ·
      refine ⟨95376867289807622458825867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127169156386410163278434489 95376867289807622458825867)
      ·
        refine ⟨143065300934711433688238801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95376867289807622458825867 143065300934711433688238801)
        ·
          refine ⟨107298975701033575266179101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 143065300934711433688238801 107298975701033575266179101)
          ·
            refine ⟨40237115887887590724817163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 107298975701033575266179101 40237115887887590724817163)
            ·
              refine ⟨60355673831831386087225745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40237115887887590724817163 60355673831831386087225745)
              ·
                refine ⟨45266755373873539565419309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60355673831831386087225745 45266755373873539565419309)
                ·
                  refine ⟨16975033265202577337032241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45266755373873539565419309 16975033265202577337032241)
                  ·
                    refine ⟨12731274948901933002774181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16975033265202577337032241 12731274948901933002774181)
                    ·
                      refine ⟨2387114052919112438020159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12731274948901933002774181 2387114052919112438020159)
                      ·
                        rfl

theorem cell23_4648888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 2, 3, 2, 4].length) (baseStart_4648888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4648888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4648888 prefixEnd_4648888 := by exact prefixLift 4648888
  have htrace : WordTrace (prefixWord ++ tailWord_4648888) baseStart_4648888 baseEnd_4648888 := by
    simpa [prefixWord, tailWord_4648888, baseEnd_4648888] using wordTrace_append hprefix tailTrace_4648888
  have hstable : (prefixWord ++ tailWord_4648888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4648888).length < 2 ^ (prefixWord ++ tailWord_4648888).sum := by decide
  have hdescent : baseEnd_4648888 < baseStart_4648888 := by decide
  rcases family_descends (prefixWord ++ tailWord_4648888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4648966 : List Nat := [6, 2, 1, 2, 1, 1, 1, 9]
def baseStart_4648966 : Nat := 118140960795 + 4648966 * 2 ^ 59
def prefixEnd_4648966 : Nat := 4983230072969 + 3 ^ 40 * 4648966 * 2
def baseEnd_4648966 : Nat := 88413114978154190105363

theorem tailTrace_4648966 : CollatzResearch.WordTrace tailWord_4648966 prefixEnd_4648966 88413114978154190105363 := by
  unfold tailWord_4648966
  simp only [CollatzResearch.WordTrace]
  refine ⟨5298803752362426157059961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 113041146717065091350612501 5298803752362426157059961)
  ·
    refine ⟨3974102814271819617794971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5298803752362426157059961 3974102814271819617794971)
    ·
      refine ⟨5961154221407729426692457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3974102814271819617794971 5961154221407729426692457)
      ·
        refine ⟨4470865666055797070019343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5961154221407729426692457 4470865666055797070019343)
        ·
          refine ⟨6706298499083695605029015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4470865666055797070019343 6706298499083695605029015)
          ·
            refine ⟨10059447748625543407543523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6706298499083695605029015 10059447748625543407543523)
            ·
              refine ⟨15089171622938315111315285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10059447748625543407543523 15089171622938315111315285)
              ·
                refine ⟨88413114978154190105363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15089171622938315111315285 88413114978154190105363)
                ·
                  rfl

theorem cell23_4648966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 9].length) (baseStart_4648966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4648966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4648966 prefixEnd_4648966 := by exact prefixLift 4648966
  have htrace : WordTrace (prefixWord ++ tailWord_4648966) baseStart_4648966 baseEnd_4648966 := by
    simpa [prefixWord, tailWord_4648966, baseEnd_4648966] using wordTrace_append hprefix tailTrace_4648966
  have hstable : (prefixWord ++ tailWord_4648966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4648966).length < 2 ^ (prefixWord ++ tailWord_4648966).sum := by decide
  have hdescent : baseEnd_4648966 < baseStart_4648966 := by decide
  rcases family_descends (prefixWord ++ tailWord_4648966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4649015 : List Nat := [1, 1, 3, 1, 2, 2, 2, 3, 2, 3, 3]
def baseStart_4649015 : Nat := 118140960795 + 4649015 * 2 ^ 59
def prefixEnd_4649015 : Nat := 4983230072969 + 3 ^ 40 * 4649015 * 2
def baseEnd_4649015 : Nat := 2387179264962233441132075

theorem tailTrace_4649015 : CollatzResearch.WordTrace tailWord_4649015 prefixEnd_4649015 2387179264962233441132075 := by
  unfold tailWord_4649015
  simp only [CollatzResearch.WordTrace]
  refine ⟨169563507252420118394452499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113042338168280078929634999 169563507252420118394452499)
  ·
    refine ⟨254345260878630177591678749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169563507252420118394452499 254345260878630177591678749)
    ·
      refine ⟨95379472829486316596879531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 254345260878630177591678749 95379472829486316596879531)
      ·
        refine ⟨143069209244229474895319297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95379472829486316596879531 143069209244229474895319297)
        ·
          refine ⟨107301906933172106171489473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 143069209244229474895319297 107301906933172106171489473)
          ·
            refine ⟨80476430199879079628617105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107301906933172106171489473 80476430199879079628617105)
            ·
              refine ⟨60357322649909309721462829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80476430199879079628617105 60357322649909309721462829)
              ·
                refine ⟨22633995993715991145548561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60357322649909309721462829 22633995993715991145548561)
                ·
                  refine ⟨16975496995286993359161421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22633995993715991145548561 16975496995286993359161421)
                  ·
                    refine ⟨6365811373232622509685533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16975496995286993359161421 6365811373232622509685533)
                    ·
                      refine ⟨2387179264962233441132075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6365811373232622509685533 2387179264962233441132075)
                      ·
                        rfl

theorem cell23_4649015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 3, 2, 3, 3].length) (baseStart_4649015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4649015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4649015 prefixEnd_4649015 := by exact prefixLift 4649015
  have htrace : WordTrace (prefixWord ++ tailWord_4649015) baseStart_4649015 baseEnd_4649015 := by
    simpa [prefixWord, tailWord_4649015, baseEnd_4649015] using wordTrace_append hprefix tailTrace_4649015
  have hstable : (prefixWord ++ tailWord_4649015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4649015).length < 2 ^ (prefixWord ++ tailWord_4649015).sum := by decide
  have hdescent : baseEnd_4649015 < baseStart_4649015 := by decide
  rcases family_descends (prefixWord ++ tailWord_4649015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4649016 : List Nat := [2, 1, 2, 1, 6, 1, 1, 3, 2, 2, 2]
def baseStart_4649016 : Nat := 118140960795 + 4649016 * 2 ^ 59
def prefixEnd_4649016 : Nat := 4983230072969 + 3 ^ 40 * 4649016 * 2
def baseEnd_4649016 : Nat := 2387179778442887937219571

theorem tailTrace_4649016 : CollatzResearch.WordTrace tailWord_4649016 prefixEnd_4649016 2387179778442887937219571 := by
  unfold tailWord_4649016
  simp only [CollatzResearch.WordTrace]
  refine ⟨84781771862708247782619451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113042362483610997043492601 84781771862708247782619451)
  ·
    refine ⟨127172657794062371673929177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84781771862708247782619451 127172657794062371673929177)
    ·
      refine ⟨95379493345546778755446883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127172657794062371673929177 95379493345546778755446883)
      ·
        refine ⟨143069240018320168133170325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95379493345546778755446883 143069240018320168133170325)
        ·
          refine ⟨6706370625858757881242359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 143069240018320168133170325 6706370625858757881242359)
          ·
            refine ⟨10059555938788136821863539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6706370625858757881242359 10059555938788136821863539)
            ·
              refine ⟨15089333908182205232795309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10059555938788136821863539 15089333908182205232795309)
              ·
                refine ⟨5658500215568326962298241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15089333908182205232795309 5658500215568326962298241)
                ·
                  refine ⟨4243875161676245221723681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5658500215568326962298241 4243875161676245221723681)
                  ·
                    refine ⟨3182906371257183916292761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4243875161676245221723681 3182906371257183916292761)
                    ·
                      refine ⟨2387179778442887937219571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3182906371257183916292761 2387179778442887937219571)
                      ·
                        rfl

theorem cell23_4649016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 3, 2, 2, 2].length) (baseStart_4649016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4649016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4649016 prefixEnd_4649016 := by exact prefixLift 4649016
  have htrace : WordTrace (prefixWord ++ tailWord_4649016) baseStart_4649016 baseEnd_4649016 := by
    simpa [prefixWord, tailWord_4649016, baseEnd_4649016] using wordTrace_append hprefix tailTrace_4649016
  have hstable : (prefixWord ++ tailWord_4649016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4649016).length < 2 ^ (prefixWord ++ tailWord_4649016).sum := by decide
  have hdescent : baseEnd_4649016 < baseStart_4649016 := by decide
  rcases family_descends (prefixWord ++ tailWord_4649016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4649045 : List Nat := [1, 3, 2, 2, 1, 3, 1, 2, 1, 2, 5]
def baseStart_4649045 : Nat := 118140960795 + 4649045 * 2 ^ 59
def prefixEnd_4649045 : Nat := 4983230072969 + 3 ^ 40 * 4649045 * 2
def baseEnd_4649045 : Nat := 2387194669381868323756937

theorem tailTrace_4649045 : CollatzResearch.WordTrace tailWord_4649045 prefixEnd_4649045 2387194669381868323756937 := by
  unfold tailWord_4649045
  simp only [CollatzResearch.WordTrace]
  refine ⟨169564601442311433518044589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113043067628207622345363059 169564601442311433518044589)
  ·
    refine ⟨63586725540866787569266721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 169564601442311433518044589 63586725540866787569266721)
    ·
      refine ⟨47690044155650090676950041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63586725540866787569266721 47690044155650090676950041)
      ·
        refine ⟨35767533116737568007712531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47690044155650090676950041 35767533116737568007712531)
        ·
          refine ⟨53651299675106352011568797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35767533116737568007712531 53651299675106352011568797)
          ·
            refine ⟨20119237378164882004338299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53651299675106352011568797 20119237378164882004338299)
            ·
              refine ⟨30178856067247323006507449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20119237378164882004338299 30178856067247323006507449)
              ·
                refine ⟨22634142050435492254880587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30178856067247323006507449 22634142050435492254880587)
                ·
                  refine ⟨33951213075653238382320881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22634142050435492254880587 33951213075653238382320881)
                  ·
                    refine ⟨25463409806739928786740661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33951213075653238382320881 25463409806739928786740661)
                    ·
                      refine ⟨2387194669381868323756937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25463409806739928786740661 2387194669381868323756937)
                      ·
                        rfl

theorem cell23_4649045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 2, 1, 2, 5].length) (baseStart_4649045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4649045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4649045 prefixEnd_4649045 := by exact prefixLift 4649045
  have htrace : WordTrace (prefixWord ++ tailWord_4649045) baseStart_4649045 baseEnd_4649045 := by
    simpa [prefixWord, tailWord_4649045, baseEnd_4649045] using wordTrace_append hprefix tailTrace_4649045
  have hstable : (prefixWord ++ tailWord_4649045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4649045).length < 2 ^ (prefixWord ++ tailWord_4649045).sum := by decide
  have hdescent : baseEnd_4649045 < baseStart_4649045 := by decide
  rcases family_descends (prefixWord ++ tailWord_4649045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4649052 : List Nat := [2, 2, 4, 1, 1, 2, 2, 2, 2, 5]
def baseStart_4649052 : Nat := 118140960795 + 4649052 * 2 ^ 59
def prefixEnd_4649052 : Nat := 4983230072969 + 3 ^ 40 * 4649052 * 2
def baseEnd_4649052 : Nat := 795732754582149932123135

theorem tailTrace_4649052 : CollatzResearch.WordTrace tailWord_4649052 prefixEnd_4649052 795732754582149932123135 := by
  unfold tailWord_4649052
  simp only [CollatzResearch.WordTrace]
  refine ⟨84782428376643036856774705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113043237835524049142366273 84782428376643036856774705)
  ·
    refine ⟨63586821282482277642581029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84782428376643036856774705 63586821282482277642581029)
    ·
      refine ⟨11922528990465427057983943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63586821282482277642581029 11922528990465427057983943)
      ·
        refine ⟨17883793485698140586975915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11922528990465427057983943 17883793485698140586975915)
        ·
          refine ⟨26825690228547210880463873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17883793485698140586975915 26825690228547210880463873)
          ·
            refine ⟨20119267671410408160347905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26825690228547210880463873 20119267671410408160347905)
            ·
              refine ⟨15089450753557806120260929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20119267671410408160347905 15089450753557806120260929)
              ·
                refine ⟨11317088065168354590195697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15089450753557806120260929 11317088065168354590195697)
                ·
                  refine ⟨8487816048876265942646773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11317088065168354590195697 8487816048876265942646773)
                  ·
                    refine ⟨795732754582149932123135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8487816048876265942646773 795732754582149932123135)
                    ·
                      rfl

theorem cell23_4649052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 2, 2, 5].length) (baseStart_4649052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4649052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4649052 prefixEnd_4649052 := by exact prefixLift 4649052
  have htrace : WordTrace (prefixWord ++ tailWord_4649052) baseStart_4649052 baseEnd_4649052 := by
    simpa [prefixWord, tailWord_4649052, baseEnd_4649052] using wordTrace_append hprefix tailTrace_4649052
  have hstable : (prefixWord ++ tailWord_4649052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4649052).length < 2 ^ (prefixWord ++ tailWord_4649052).sum := by decide
  have hdescent : baseEnd_4649052 < baseStart_4649052 := by decide
  rcases family_descends (prefixWord ++ tailWord_4649052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4649055 : List Nat := [1, 1, 2, 3, 1, 1, 2, 3, 4, 1, 4]
def baseStart_4649055 : Nat := 118140960795 + 4649055 * 2 ^ 59
def prefixEnd_4649055 : Nat := 4983230072969 + 3 ^ 40 * 4649055 * 2
def baseEnd_4649055 : Nat := 2387199804188413284631891

theorem tailTrace_4649055 : CollatzResearch.WordTrace tailWord_4649055 prefixEnd_4649055 2387199804188413284631891 := by
  unfold tailWord_4649055
  simp only [CollatzResearch.WordTrace]
  refine ⟨169564966172275205225908619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113043310781516803483939079 169564966172275205225908619)
  ·
    refine ⟨254347449258412807838862929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169564966172275205225908619 254347449258412807838862929)
    ·
      refine ⟨190760586943809605879147197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 254347449258412807838862929 190760586943809605879147197)
      ·
        refine ⟨71535220103928602204680199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 190760586943809605879147197 71535220103928602204680199)
        ·
          refine ⟨107302830155892903307020299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71535220103928602204680199 107302830155892903307020299)
          ·
            refine ⟨160954245233839354960530449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107302830155892903307020299 160954245233839354960530449)
            ·
              refine ⟨120715683925379516220397837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 160954245233839354960530449 120715683925379516220397837)
              ·
                refine ⟨45268381472017318582649189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 120715683925379516220397837 45268381472017318582649189)
                ·
                  refine ⟨8487821526003247234246723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45268381472017318582649189 8487821526003247234246723)
                  ·
                    refine ⟨12731732289004870851370085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8487821526003247234246723 12731732289004870851370085)
                    ·
                      refine ⟨2387199804188413284631891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12731732289004870851370085 2387199804188413284631891)
                      ·
                        rfl

theorem cell23_4649055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 3, 4, 1, 4].length) (baseStart_4649055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4649055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4649055 prefixEnd_4649055 := by exact prefixLift 4649055
  have htrace : WordTrace (prefixWord ++ tailWord_4649055) baseStart_4649055 baseEnd_4649055 := by
    simpa [prefixWord, tailWord_4649055, baseEnd_4649055] using wordTrace_append hprefix tailTrace_4649055
  have hstable : (prefixWord ++ tailWord_4649055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4649055).length < 2 ^ (prefixWord ++ tailWord_4649055).sum := by decide
  have hdescent : baseEnd_4649055 < baseStart_4649055 := by decide
  rcases family_descends (prefixWord ++ tailWord_4649055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
