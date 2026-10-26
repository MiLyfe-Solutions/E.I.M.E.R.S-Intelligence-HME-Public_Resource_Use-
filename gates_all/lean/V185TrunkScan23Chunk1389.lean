import V185TrunkScan23Chunk1388

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_8226858 : List Nat := [3, 1, 4, 1, 2, 1, 1, 1, 5, 2, 2]
def baseStart_8226858 : Nat := 118140960795 + 8226858 * 2 ^ 59
def prefixEnd_8226858 : Nat := 4983230072969 + 3 ^ 40 * 8226858 * 2
def baseEnd_8226858 : Nat := 4224332430286478613940375

theorem tailTrace_8226858 : CollatzResearch.WordTrace tailWord_8226858 prefixEnd_8226858 4224332430286478613940375 := by
  unfold tailWord_8226858
  simp only [CollatzResearch.WordTrace]
  refine ⟨75014540507376494082730307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200038774686337317553947485 75014540507376494082730307)
  ·
    refine ⟨112521810761064741124095461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75014540507376494082730307 112521810761064741124095461)
    ·
      refine ⟨21097839517699638960767899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112521810761064741124095461 21097839517699638960767899)
      ·
        refine ⟨31646759276549458441151849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21097839517699638960767899 31646759276549458441151849)
        ·
          refine ⟨23735069457412093830863887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31646759276549458441151849 23735069457412093830863887)
          ·
            refine ⟨35602604186118140746295831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23735069457412093830863887 35602604186118140746295831)
            ·
              refine ⟨53403906279177211119443747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35602604186118140746295831 53403906279177211119443747)
              ·
                refine ⟨80105859418765816679165621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53403906279177211119443747 80105859418765816679165621)
                ·
                  refine ⟨7509924320509295313671777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80105859418765816679165621 7509924320509295313671777)
                  ·
                    refine ⟨5632443240381971485253833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7509924320509295313671777 5632443240381971485253833)
                    ·
                      refine ⟨4224332430286478613940375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5632443240381971485253833 4224332430286478613940375)
                      ·
                        rfl

theorem cell23_8226858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 1, 5, 2, 2].length) (baseStart_8226858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8226858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8226858 prefixEnd_8226858 := by exact prefixLift 8226858
  have htrace : WordTrace (prefixWord ++ tailWord_8226858) baseStart_8226858 baseEnd_8226858 := by
    simpa [prefixWord, tailWord_8226858, baseEnd_8226858] using wordTrace_append hprefix tailTrace_8226858
  have hstable : (prefixWord ++ tailWord_8226858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8226858).length < 2 ^ (prefixWord ++ tailWord_8226858).sum := by decide
  have hdescent : baseEnd_8226858 < baseStart_8226858 := by decide
  rcases family_descends (prefixWord ++ tailWord_8226858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8226864 : List Nat := [2, 1, 1, 1, 2, 6, 3, 7]
def baseStart_8226864 : Nat := 118140960795 + 8226864 * 2 ^ 59
def prefixEnd_8226864 : Nat := 4983230072969 + 3 ^ 40 * 8226864 * 2
def baseEnd_8226864 : Nat := 156456870784089095943161

theorem tailTrace_8226864 : CollatzResearch.WordTrace tailWord_8226864 prefixEnd_8226864 156456870784089095943161 := by
  unfold tailWord_8226864
  simp only [CollatzResearch.WordTrace]
  refine ⟨150029190433742119677819823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200038920578322826237093097 150029190433742119677819823)
  ·
    refine ⟨225043785650613179516729735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150029190433742119677819823 225043785650613179516729735)
    ·
      refine ⟨337565678475919769275094603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225043785650613179516729735 337565678475919769275094603)
      ·
        refine ⟨506348517713879653912641905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337565678475919769275094603 506348517713879653912641905)
        ·
          refine ⟨379761388285409740434481429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 506348517713879653912641905 379761388285409740434481429)
          ·
            refine ⟨17801315075878581582866317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 379761388285409740434481429 17801315075878581582866317)
            ·
              refine ⟨6675493153454468093574869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17801315075878581582866317 6675493153454468093574869)
              ·
                refine ⟨156456870784089095943161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6675493153454468093574869 156456870784089095943161)
                ·
                  rfl

theorem cell23_8226864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 3, 7].length) (baseStart_8226864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8226864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8226864 prefixEnd_8226864 := by exact prefixLift 8226864
  have htrace : WordTrace (prefixWord ++ tailWord_8226864) baseStart_8226864 baseEnd_8226864 := by
    simpa [prefixWord, tailWord_8226864, baseEnd_8226864] using wordTrace_append hprefix tailTrace_8226864
  have hstable : (prefixWord ++ tailWord_8226864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8226864).length < 2 ^ (prefixWord ++ tailWord_8226864).sum := by decide
  have hdescent : baseEnd_8226864 < baseStart_8226864 := by decide
  rcases family_descends (prefixWord ++ tailWord_8226864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8226902 : List Nat := [5, 2, 2, 1, 1, 2, 3, 1, 2, 4]
def baseStart_8226902 : Nat := 118140960795 + 8226902 * 2 ^ 59
def prefixEnd_8226902 : Nat := 4983230072969 + 3 ^ 40 * 8226902 * 2
def baseEnd_8226902 : Nat := 1408118341145092147263391

theorem tailTrace_8226902 : CollatzResearch.WordTrace tailWord_8226902 prefixEnd_8226902 1408118341145092147263391 := by
  unfold tailWord_8226902
  simp only [CollatzResearch.WordTrace]
  refine ⟨18753735427584160740345185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 200039844560897714563681973 18753735427584160740345185)
  ·
    refine ⟨14065301570688120555258889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18753735427584160740345185 14065301570688120555258889)
    ·
      refine ⟨10548976178016090416444167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14065301570688120555258889 10548976178016090416444167)
      ·
        refine ⟨15823464267024135624666251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10548976178016090416444167 15823464267024135624666251)
        ·
          refine ⟨23735196400536203436999377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15823464267024135624666251 23735196400536203436999377)
          ·
            refine ⟨17801397300402152577749533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23735196400536203436999377 17801397300402152577749533)
            ·
              refine ⟨6675523987650807216656075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17801397300402152577749533 6675523987650807216656075)
              ·
                refine ⟨10013285981476210824984113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6675523987650807216656075 10013285981476210824984113)
                ·
                  refine ⟨7509964486107158118738085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10013285981476210824984113 7509964486107158118738085)
                  ·
                    refine ⟨1408118341145092147263391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7509964486107158118738085 1408118341145092147263391)
                    ·
                      rfl

theorem cell23_8226902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_8226902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8226902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8226902 prefixEnd_8226902 := by exact prefixLift 8226902
  have htrace : WordTrace (prefixWord ++ tailWord_8226902) baseStart_8226902 baseEnd_8226902 := by
    simpa [prefixWord, tailWord_8226902, baseEnd_8226902] using wordTrace_append hprefix tailTrace_8226902
  have hstable : (prefixWord ++ tailWord_8226902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8226902).length < 2 ^ (prefixWord ++ tailWord_8226902).sum := by decide
  have hdescent : baseEnd_8226902 < baseStart_8226902 := by decide
  rcases family_descends (prefixWord ++ tailWord_8226902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8226908 : List Nat := [2, 2, 4, 1, 1, 4, 1, 1, 1, 3, 3]
def baseStart_8226908 : Nat := 118140960795 + 8226908 * 2 ^ 59
def prefixEnd_8226908 : Nat := 4983230072969 + 3 ^ 40 * 8226908 * 2
def baseEnd_8226908 : Nat := 4224358104319203418315145

theorem tailTrace_8226908 : CollatzResearch.WordTrace tailWord_8226908 prefixEnd_8226908 4224358104319203418315145 := by
  unfold tailWord_8226908
  simp only [CollatzResearch.WordTrace]
  refine ⟨150029992839662417435120689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200039990452883223246827585 150029992839662417435120689)
  ·
    refine ⟨112522494629746813076340517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150029992839662417435120689 112522494629746813076340517)
    ·
      refine ⟨21097967743077527451813847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112522494629746813076340517 21097967743077527451813847)
      ·
        refine ⟨31646951614616291177720771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21097967743077527451813847 31646951614616291177720771)
        ·
          refine ⟨47470427421924436766581157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31646951614616291177720771 47470427421924436766581157)
          ·
            refine ⟨8900705141610831893733967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47470427421924436766581157 8900705141610831893733967)
            ·
              refine ⟨13351057712416247840600951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8900705141610831893733967 13351057712416247840600951)
              ·
                refine ⟨20026586568624371760901427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13351057712416247840600951 20026586568624371760901427)
                ·
                  refine ⟨30039879852936557641352141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20026586568624371760901427 30039879852936557641352141)
                  ·
                    refine ⟨11264954944851209115507053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30039879852936557641352141 11264954944851209115507053)
                    ·
                      refine ⟨4224358104319203418315145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11264954944851209115507053 4224358104319203418315145)
                      ·
                        rfl

theorem cell23_8226908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 1, 1, 1, 3, 3].length) (baseStart_8226908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8226908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8226908 prefixEnd_8226908 := by exact prefixLift 8226908
  have htrace : WordTrace (prefixWord ++ tailWord_8226908) baseStart_8226908 baseEnd_8226908 := by
    simpa [prefixWord, tailWord_8226908, baseEnd_8226908] using wordTrace_append hprefix tailTrace_8226908
  have hstable : (prefixWord ++ tailWord_8226908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8226908).length < 2 ^ (prefixWord ++ tailWord_8226908).sum := by decide
  have hdescent : baseEnd_8226908 < baseStart_8226908 := by decide
  rcases family_descends (prefixWord ++ tailWord_8226908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8226948 : List Nat := [2, 3, 2, 1, 2, 1, 1, 3, 4, 2, 2]
def baseStart_8226948 : Nat := 118140960795 + 8226948 * 2 ^ 59
def prefixEnd_8226948 : Nat := 4983230072969 + 3 ^ 40 * 8226948 * 2
def baseEnd_8226948 : Nat := 4224378643545383261814961

theorem tailTrace_8226948 : CollatzResearch.WordTrace tailWord_8226948 prefixEnd_8226948 4224378643545383261814961 := by
  unfold tailWord_8226948
  simp only [CollatzResearch.WordTrace]
  refine ⟨150030722299589960850848749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200040963066119947801131665 150030722299589960850848749)
  ·
    refine ⟨56261520862346235319068281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150030722299589960850848749 56261520862346235319068281)
    ·
      refine ⟨42196140646759676489301211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56261520862346235319068281 42196140646759676489301211)
      ·
        refine ⟨63294210970139514733951817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42196140646759676489301211 63294210970139514733951817)
        ·
          refine ⟨47470658227604636050463863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63294210970139514733951817 47470658227604636050463863)
          ·
            refine ⟨71205987341406954075695795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47470658227604636050463863 71205987341406954075695795)
            ·
              refine ⟨106808981012110431113543693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71205987341406954075695795 106808981012110431113543693)
              ·
                refine ⟨40053367879541411667578885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106808981012110431113543693 40053367879541411667578885)
                ·
                  refine ⟨7510006477414014687671041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40053367879541411667578885 7510006477414014687671041)
                  ·
                    refine ⟨5632504858060511015753281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7510006477414014687671041 5632504858060511015753281)
                    ·
                      refine ⟨4224378643545383261814961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5632504858060511015753281 4224378643545383261814961)
                      ·
                        rfl

theorem cell23_8226948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 3, 4, 2, 2].length) (baseStart_8226948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8226948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8226948 prefixEnd_8226948 := by exact prefixLift 8226948
  have htrace : WordTrace (prefixWord ++ tailWord_8226948) baseStart_8226948 baseEnd_8226948 := by
    simpa [prefixWord, tailWord_8226948, baseEnd_8226948] using wordTrace_append hprefix tailTrace_8226948
  have hstable : (prefixWord ++ tailWord_8226948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8226948).length < 2 ^ (prefixWord ++ tailWord_8226948).sum := by decide
  have hdescent : baseEnd_8226948 < baseStart_8226948 := by decide
  rcases family_descends (prefixWord ++ tailWord_8226948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8226994 : List Nat := [3, 2, 1, 1, 1, 3, 1, 1, 3, 2, 5]
def baseStart_8226994 : Nat := 118140960795 + 8226994 * 2 ^ 59
def prefixEnd_8226994 : Nat := 4983230072969 + 3 ^ 40 * 8226994 * 2
def baseEnd_8226994 : Nat := 4224402263655490081839749

theorem tailTrace_8226994 : CollatzResearch.WordTrace tailWord_8226994 prefixEnd_8226994 4224402263655490081839749 := by
  unfold tailWord_8226994
  simp only [CollatzResearch.WordTrace]
  refine ⟨75015780589253317889468009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200042081571342181038581357 75015780589253317889468009)
  ·
    refine ⟨56261835441939988417101007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75015780589253317889468009 56261835441939988417101007)
    ·
      refine ⟨84392753162909982625651511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56261835441939988417101007 84392753162909982625651511)
      ·
        refine ⟨126589129744364973938477267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84392753162909982625651511 126589129744364973938477267)
        ·
          refine ⟨189883694616547460907715901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126589129744364973938477267 189883694616547460907715901)
          ·
            refine ⟨71206385481205297840393463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 189883694616547460907715901 71206385481205297840393463)
            ·
              refine ⟨106809578221807946760590195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71206385481205297840393463 106809578221807946760590195)
              ·
                refine ⟨160214367332711920140885293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106809578221807946760590195 160214367332711920140885293)
                ·
                  refine ⟨60080387749766970052831985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 160214367332711920140885293 60080387749766970052831985)
                  ·
                    refine ⟨45060290812325227539623989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60080387749766970052831985 45060290812325227539623989)
                    ·
                      refine ⟨4224402263655490081839749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45060290812325227539623989 4224402263655490081839749)
                      ·
                        rfl

theorem cell23_8226994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 3, 2, 5].length) (baseStart_8226994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8226994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8226994 prefixEnd_8226994 := by exact prefixLift 8226994
  have htrace : WordTrace (prefixWord ++ tailWord_8226994) baseStart_8226994 baseEnd_8226994 := by
    simpa [prefixWord, tailWord_8226994, baseEnd_8226994] using wordTrace_append hprefix tailTrace_8226994
  have hstable : (prefixWord ++ tailWord_8226994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8226994).length < 2 ^ (prefixWord ++ tailWord_8226994).sum := by decide
  have hdescent : baseEnd_8226994 < baseStart_8226994 := by decide
  rcases family_descends (prefixWord ++ tailWord_8226994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8227041 : List Nat := [1, 2, 3, 1, 3, 1, 3, 1, 1, 4, 3]
def baseStart_8227041 : Nat := 118140960795 + 8227041 * 2 ^ 59
def prefixEnd_8227041 : Nat := 4983230072969 + 3 ^ 40 * 8227041 * 2
def baseEnd_8227041 : Nat := 4224426397246251397952033

theorem tailTrace_8227041 : CollatzResearch.WordTrace tailWord_8227041 prefixEnd_8227041 4224426397246251397952033 := by
  unfold tailWord_8227041
  simp only [CollatzResearch.WordTrace]
  refine ⟨300064836587842998584832977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200043224391895332389888651 300064836587842998584832977)
  ·
    refine ⟨225048627440882248938624733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300064836587842998584832977 225048627440882248938624733)
    ·
      refine ⟨84393235290330843351984275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225048627440882248938624733 84393235290330843351984275)
      ·
        refine ⟨126589852935496265027976413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84393235290330843351984275 126589852935496265027976413)
        ·
          refine ⟨47471194850811099385491155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126589852935496265027976413 47471194850811099385491155)
          ·
            refine ⟨71206792276216649078236733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47471194850811099385491155 71206792276216649078236733)
            ·
              refine ⟨26702547103581243404338775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71206792276216649078236733 26702547103581243404338775)
              ·
                refine ⟨40053820655371865106508163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26702547103581243404338775 40053820655371865106508163)
                ·
                  refine ⟨60080730983057797659762245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40053820655371865106508163 60080730983057797659762245)
                  ·
                    refine ⟨11265137059323337061205421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60080730983057797659762245 11265137059323337061205421)
                    ·
                      refine ⟨4224426397246251397952033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11265137059323337061205421 4224426397246251397952033)
                      ·
                        rfl

theorem cell23_8227041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 1, 1, 4, 3].length) (baseStart_8227041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8227041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8227041 prefixEnd_8227041 := by exact prefixLift 8227041
  have htrace : WordTrace (prefixWord ++ tailWord_8227041) baseStart_8227041 baseEnd_8227041 := by
    simpa [prefixWord, tailWord_8227041, baseEnd_8227041] using wordTrace_append hprefix tailTrace_8227041
  have hstable : (prefixWord ++ tailWord_8227041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8227041).length < 2 ^ (prefixWord ++ tailWord_8227041).sum := by decide
  have hdescent : baseEnd_8227041 < baseStart_8227041 := by decide
  rcases family_descends (prefixWord ++ tailWord_8227041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8227044 : List Nat := [2, 3, 1, 1, 1, 2, 1, 4, 8]
def baseStart_8227044 : Nat := 118140960795 + 8227044 * 2 ^ 59
def prefixEnd_8227044 : Nat := 4983230072969 + 3 ^ 40 * 8227044 * 2
def baseEnd_8227044 : Nat := 469380881965357209579391

theorem tailTrace_8227044 : CollatzResearch.WordTrace tailWord_8227044 prefixEnd_8227044 469380881965357209579391 := by
  unfold tailWord_8227044
  simp only [CollatzResearch.WordTrace]
  refine ⟨150032473003416065048596093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200043297337888086731461457 150032473003416065048596093)
  ·
    refine ⟨56262177376281024393223535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150032473003416065048596093 56262177376281024393223535)
    ·
      refine ⟨84393266064421536589835303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56262177376281024393223535 84393266064421536589835303)
      ·
        refine ⟨126589899096632304884752955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84393266064421536589835303 126589899096632304884752955)
        ·
          refine ⟨189884848644948457327129433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126589899096632304884752955 189884848644948457327129433)
          ·
            refine ⟨142413636483711342995347075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189884848644948457327129433 142413636483711342995347075)
            ·
              refine ⟨213620454725567014493020613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142413636483711342995347075 213620454725567014493020613)
              ·
                refine ⟨40053835261043815217441365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 213620454725567014493020613 40053835261043815217441365)
                ·
                  refine ⟨469380881965357209579391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40053835261043815217441365 469380881965357209579391)
                  ·
                    rfl

theorem cell23_8227044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 4, 8].length) (baseStart_8227044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8227044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8227044 prefixEnd_8227044 := by exact prefixLift 8227044
  have htrace : WordTrace (prefixWord ++ tailWord_8227044) baseStart_8227044 baseEnd_8227044 := by
    simpa [prefixWord, tailWord_8227044, baseEnd_8227044] using wordTrace_append hprefix tailTrace_8227044
  have hstable : (prefixWord ++ tailWord_8227044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8227044).length < 2 ^ (prefixWord ++ tailWord_8227044).sum := by decide
  have hdescent : baseEnd_8227044 < baseStart_8227044 := by decide
  rcases family_descends (prefixWord ++ tailWord_8227044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8227108 : List Nat := [2, 3, 1, 3, 1, 2, 2, 3, 1, 5]
def baseStart_8227108 : Nat := 118140960795 + 8227108 * 2 ^ 59
def prefixEnd_8227108 : Nat := 4983230072969 + 3 ^ 40 * 8227108 * 2
def baseEnd_8227108 : Nat := 1408153600150034211938075

theorem tailTrace_8227108 : CollatzResearch.WordTrace tailWord_8227108 prefixEnd_8227108 1408153600150034211938075 := by
  unfold tailWord_8227108
  simp only [CollatzResearch.WordTrace]
  refine ⟨150033640139300134513760989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200044853519066846018347985 150033640139300134513760989)
  ·
    refine ⟨56262615052237550442660371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150033640139300134513760989 56262615052237550442660371)
    ·
      refine ⟨84393922578356325663990557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56262615052237550442660371 84393922578356325663990557)
      ·
        refine ⟨31647720966883622123996459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84393922578356325663990557 31647720966883622123996459)
        ·
          refine ⟨47471581450325433185994689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31647720966883622123996459 47471581450325433185994689)
          ·
            refine ⟨35603686087744074889496017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47471581450325433185994689 35603686087744074889496017)
            ·
              refine ⟨26702764565808056167122013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35603686087744074889496017 26702764565808056167122013)
              ·
                refine ⟨10013536712178021062670755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26702764565808056167122013 10013536712178021062670755)
                ·
                  refine ⟨15020305068267031594006133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10013536712178021062670755 15020305068267031594006133)
                  ·
                    refine ⟨1408153600150034211938075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15020305068267031594006133 1408153600150034211938075)
                    ·
                      rfl

theorem cell23_8227108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 3, 1, 5].length) (baseStart_8227108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8227108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8227108 prefixEnd_8227108 := by exact prefixLift 8227108
  have htrace : WordTrace (prefixWord ++ tailWord_8227108) baseStart_8227108 baseEnd_8227108 := by
    simpa [prefixWord, tailWord_8227108, baseEnd_8227108] using wordTrace_append hprefix tailTrace_8227108
  have hstable : (prefixWord ++ tailWord_8227108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8227108).length < 2 ^ (prefixWord ++ tailWord_8227108).sum := by decide
  have hdescent : baseEnd_8227108 < baseStart_8227108 := by decide
  rcases family_descends (prefixWord ++ tailWord_8227108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8227122 : List Nat := [3, 2, 1, 1, 5, 2, 1, 1, 3, 1, 3]
def baseStart_8227122 : Nat := 118140960795 + 8227122 * 2 ^ 59
def prefixEnd_8227122 : Nat := 4983230072969 + 3 ^ 40 * 8227122 * 2
def baseEnd_8227122 : Nat := 4224467989179265581039161

theorem tailTrace_8227122 : CollatzResearch.WordTrace tailWord_8227122 prefixEnd_8227122 4224467989179265581039161 := by
  unfold tailWord_8227122
  simp only [CollatzResearch.WordTrace]
  refine ⟨75016947725137387354632905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200045193933699699612354413 75016947725137387354632905)
  ·
    refine ⟨56262710793853040515974679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75016947725137387354632905 56262710793853040515974679)
    ·
      refine ⟨84394066190779560773962019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56262710793853040515974679 84394066190779560773962019)
      ·
        refine ⟨126591099286169341160943029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84394066190779560773962019 126591099286169341160943029)
        ·
          refine ⟨11867915558078375733838409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 126591099286169341160943029 11867915558078375733838409)
          ·
            refine ⟨8900936668558781800378807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11867915558078375733838409 8900936668558781800378807)
            ·
              refine ⟨13351405002838172700568211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8900936668558781800378807 13351405002838172700568211)
              ·
                refine ⟨20027107504257259050852317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13351405002838172700568211 20027107504257259050852317)
                ·
                  refine ⟨7510165314096472144069619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20027107504257259050852317 7510165314096472144069619)
                  ·
                    refine ⟨11265247971144708216104429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7510165314096472144069619 11265247971144708216104429)
                    ·
                      refine ⟨4224467989179265581039161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11265247971144708216104429 4224467989179265581039161)
                      ·
                        rfl

theorem cell23_8227122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 1, 1, 3, 1, 3].length) (baseStart_8227122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8227122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8227122 prefixEnd_8227122 := by exact prefixLift 8227122
  have htrace : WordTrace (prefixWord ++ tailWord_8227122) baseStart_8227122 baseEnd_8227122 := by
    simpa [prefixWord, tailWord_8227122, baseEnd_8227122] using wordTrace_append hprefix tailTrace_8227122
  have hstable : (prefixWord ++ tailWord_8227122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8227122).length < 2 ^ (prefixWord ++ tailWord_8227122).sum := by decide
  have hdescent : baseEnd_8227122 < baseStart_8227122 := by decide
  rcases family_descends (prefixWord ++ tailWord_8227122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8227148 : List Nat := [2, 2, 1, 3, 2, 1, 3, 1, 3, 2, 3]
def baseStart_8227148 : Nat := 118140960795 + 8227148 * 2 ^ 59
def prefixEnd_8227148 : Nat := 4983230072969 + 3 ^ 40 * 8227148 * 2
def baseEnd_8227148 : Nat := 4224481339676282479314041

theorem tailTrace_8227148 : CollatzResearch.WordTrace tailWord_8227148 prefixEnd_8227148 4224481339676282479314041 := by
  unfold tailWord_8227148
  simp only [CollatzResearch.WordTrace]
  refine ⟨150034369599227677929489049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200045826132303570572652065 150034369599227677929489049)
  ·
    refine ⟨112525777199420758447116787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150034369599227677929489049 112525777199420758447116787)
    ·
      refine ⟨168788665799131137670675181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112525777199420758447116787 168788665799131137670675181)
      ·
        refine ⟨63295749674674176626503193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168788665799131137670675181 63295749674674176626503193)
        ·
          refine ⟨47471812256005632469877395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63295749674674176626503193 47471812256005632469877395)
          ·
            refine ⟨71207718384008448704816093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47471812256005632469877395 71207718384008448704816093)
            ·
              refine ⟨26702894394003168264306035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71207718384008448704816093 26702894394003168264306035)
              ·
                refine ⟨40054341591004752396459053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26702894394003168264306035 40054341591004752396459053)
                ·
                  refine ⟨15020378096626782148672145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40054341591004752396459053 15020378096626782148672145)
                  ·
                    refine ⟨11265283572470086611504109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15020378096626782148672145 11265283572470086611504109)
                    ·
                      refine ⟨4224481339676282479314041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11265283572470086611504109 4224481339676282479314041)
                      ·
                        rfl

theorem cell23_8227148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 1, 3, 2, 3].length) (baseStart_8227148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8227148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8227148 prefixEnd_8227148 := by exact prefixLift 8227148
  have htrace : WordTrace (prefixWord ++ tailWord_8227148) baseStart_8227148 baseEnd_8227148 := by
    simpa [prefixWord, tailWord_8227148, baseEnd_8227148] using wordTrace_append hprefix tailTrace_8227148
  have hstable : (prefixWord ++ tailWord_8227148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8227148).length < 2 ^ (prefixWord ++ tailWord_8227148).sum := by decide
  have hdescent : baseEnd_8227148 < baseStart_8227148 := by decide
  rcases family_descends (prefixWord ++ tailWord_8227148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8227162 : List Nat := [3, 1, 1, 2, 1, 2, 1, 7, 1, 2, 2]
def baseStart_8227162 : Nat := 118140960795 + 8227162 * 2 ^ 59
def prefixEnd_8227162 : Nat := 4983230072969 + 3 ^ 40 * 8227162 * 2
def baseEnd_8227162 : Nat := 4224488528405445424538977

theorem tailTrace_8227162 : CollatzResearch.WordTrace tailWord_8227162 prefixEnd_8227162 4224488528405445424538977 := by
  unfold tailWord_8227162
  simp only [CollatzResearch.WordTrace]
  refine ⟨75017312455101159062496935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200046166546936424166658493 75017312455101159062496935)
  ·
    refine ⟨112525968682651738593745403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75017312455101159062496935 112525968682651738593745403)
    ·
      refine ⟨168788953023977607890618105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112525968682651738593745403 168788953023977607890618105)
      ·
        refine ⟨126591714767983205917963579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168788953023977607890618105 126591714767983205917963579)
        ·
          refine ⟨189887572151974808876945369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126591714767983205917963579 189887572151974808876945369)
          ·
            refine ⟨142415679113981106657709027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189887572151974808876945369 142415679113981106657709027)
            ·
              refine ⟨213623518670971659986563541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142415679113981106657709027 213623518670971659986563541)
              ·
                refine ⟨5006801218850898280935083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 213623518670971659986563541 5006801218850898280935083)
                ·
                  refine ⟨7510201828276347421402625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5006801218850898280935083 7510201828276347421402625)
                  ·
                    refine ⟨5632651371207260566051969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7510201828276347421402625 5632651371207260566051969)
                    ·
                      refine ⟨4224488528405445424538977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5632651371207260566051969 4224488528405445424538977)
                      ·
                        rfl

theorem cell23_8227162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 7, 1, 2, 2].length) (baseStart_8227162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8227162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8227162 prefixEnd_8227162 := by exact prefixLift 8227162
  have htrace : WordTrace (prefixWord ++ tailWord_8227162) baseStart_8227162 baseEnd_8227162 := by
    simpa [prefixWord, tailWord_8227162, baseEnd_8227162] using wordTrace_append hprefix tailTrace_8227162
  have hstable : (prefixWord ++ tailWord_8227162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8227162).length < 2 ^ (prefixWord ++ tailWord_8227162).sum := by decide
  have hdescent : baseEnd_8227162 < baseStart_8227162 := by decide
  rcases family_descends (prefixWord ++ tailWord_8227162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8227181 : List Nat := [1, 5, 1, 1, 1, 2, 1, 1, 1, 9]
def baseStart_8227181 : Nat := 118140960795 + 8227181 * 2 ^ 59
def prefixEnd_8227181 : Nat := 4983230072969 + 3 ^ 40 * 8227181 * 2
def baseEnd_8227181 : Nat := 1408166094845960283400463

theorem tailTrace_8227181 : CollatzResearch.WordTrace tailWord_8227181 prefixEnd_8227181 1408166094845960283400463 := by
  unfold tailWord_8227181
  simp only [CollatzResearch.WordTrace]
  refine ⟨300069942807335802494929397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200046628538223868329952931 300069942807335802494929397)
  ·
    refine ⟨28131557138187731483899631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 300069942807335802494929397 28131557138187731483899631)
    ·
      refine ⟨42197335707281597225849447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28131557138187731483899631 42197335707281597225849447)
      ·
        refine ⟨63296003560922395838774171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42197335707281597225849447 63296003560922395838774171)
        ·
          refine ⟨94944005341383593758161257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63296003560922395838774171 94944005341383593758161257)
          ·
            refine ⟨71208004006037695318620943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94944005341383593758161257 71208004006037695318620943)
            ·
              refine ⟨106812006009056542977931415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71208004006037695318620943 106812006009056542977931415)
              ·
                refine ⟨160218009013584814466897123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106812006009056542977931415 160218009013584814466897123)
                ·
                  refine ⟨240327013520377221700345685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 160218009013584814466897123 240327013520377221700345685)
                  ·
                    refine ⟨1408166094845960283400463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 240327013520377221700345685 1408166094845960283400463)
                    ·
                      rfl

theorem cell23_8227181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 9].length) (baseStart_8227181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8227181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8227181 prefixEnd_8227181 := by exact prefixLift 8227181
  have htrace : WordTrace (prefixWord ++ tailWord_8227181) baseStart_8227181 baseEnd_8227181 := by
    simpa [prefixWord, tailWord_8227181, baseEnd_8227181] using wordTrace_append hprefix tailTrace_8227181
  have hstable : (prefixWord ++ tailWord_8227181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8227181).length < 2 ^ (prefixWord ++ tailWord_8227181).sum := by decide
  have hdescent : baseEnd_8227181 < baseStart_8227181 := by decide
  rcases family_descends (prefixWord ++ tailWord_8227181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8227195 : List Nat := [1, 1, 1, 1, 1, 7, 2, 3, 2, 1, 3]
def baseStart_8227195 : Nat := 118140960795 + 8227195 * 2 ^ 59
def prefixEnd_8227195 : Nat := 4983230072969 + 3 ^ 40 * 8227195 * 2
def baseEnd_8227195 : Nat := 4224505473267043795426325

theorem tailTrace_8227195 : CollatzResearch.WordTrace tailWord_8227195 prefixEnd_8227195 4224505473267043795426325 := by
  unfold tailWord_8227195
  simp only [CollatzResearch.WordTrace]
  refine ⟨300070453429285082885939039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200046968952856721923959359 300070453429285082885939039)
  ·
    refine ⟨450105680143927624328908559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300070453429285082885939039 450105680143927624328908559)
    ·
      refine ⟨675158520215891436493362839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 450105680143927624328908559 675158520215891436493362839)
      ·
        refine ⟨1012737780323837154740044259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 675158520215891436493362839 1012737780323837154740044259)
        ·
          refine ⟨1519106670485755732110066389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1012737780323837154740044259 1519106670485755732110066389)
          ·
            refine ⟨35604062589509899971329681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 1519106670485755732110066389 35604062589509899971329681)
            ·
              refine ⟨26703046942132424978497261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35604062589509899971329681 26703046942132424978497261)
              ·
                refine ⟨10013642603299659366936473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26703046942132424978497261 10013642603299659366936473)
                ·
                  refine ⟨7510231952474744525202355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10013642603299659366936473 7510231952474744525202355)
                  ·
                    refine ⟨11265347928712116787803533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7510231952474744525202355 11265347928712116787803533)
                    ·
                      refine ⟨4224505473267043795426325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11265347928712116787803533 4224505473267043795426325)
                      ·
                        rfl

theorem cell23_8227195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 3, 2, 1, 3].length) (baseStart_8227195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8227195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8227195 prefixEnd_8227195 := by exact prefixLift 8227195
  have htrace : WordTrace (prefixWord ++ tailWord_8227195) baseStart_8227195 baseEnd_8227195 := by
    simpa [prefixWord, tailWord_8227195, baseEnd_8227195] using wordTrace_append hprefix tailTrace_8227195
  have hstable : (prefixWord ++ tailWord_8227195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8227195).length < 2 ^ (prefixWord ++ tailWord_8227195).sum := by decide
  have hdescent : baseEnd_8227195 < baseStart_8227195 := by decide
  rcases family_descends (prefixWord ++ tailWord_8227195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8227202 : List Nat := [3, 4, 2, 1, 2, 1, 3, 7]
def baseStart_8227202 : Nat := 118140960795 + 8227202 * 2 ^ 59
def prefixEnd_8227202 : Nat := 4983230072969 + 3 ^ 40 * 8227202 * 2
def baseEnd_8227202 : Nat := 156463298801171306223659

theorem tailTrace_8227202 : CollatzResearch.WordTrace tailWord_8227202 prefixEnd_8227202 156463298801171306223659 := by
  unfold tailWord_8227202
  simp only [CollatzResearch.WordTrace]
  refine ⟨75017677185064930770360965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200047139160173148720962573 75017677185064930770360965)
  ·
    refine ⟨14065814472199674519442681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75017677185064930770360965 14065814472199674519442681)
    ·
      refine ⟨10549360854149755889582011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14065814472199674519442681 10549360854149755889582011)
      ·
        refine ⟨15824041281224633834373017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10549360854149755889582011 15824041281224633834373017)
        ·
          refine ⟨11868030960918475375779763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15824041281224633834373017 11868030960918475375779763)
          ·
            refine ⟨17802046441377713063669645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11868030960918475375779763 17802046441377713063669645)
            ·
              refine ⟨6675767415516642398876117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17802046441377713063669645 6675767415516642398876117)
              ·
                refine ⟨156463298801171306223659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6675767415516642398876117 156463298801171306223659)
                ·
                  rfl

theorem cell23_8227202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 3, 7].length) (baseStart_8227202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8227202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8227202 prefixEnd_8227202 := by exact prefixLift 8227202
  have htrace : WordTrace (prefixWord ++ tailWord_8227202) baseStart_8227202 baseEnd_8227202 := by
    simpa [prefixWord, tailWord_8227202, baseEnd_8227202] using wordTrace_append hprefix tailTrace_8227202
  have hstable : (prefixWord ++ tailWord_8227202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8227202).length < 2 ^ (prefixWord ++ tailWord_8227202).sum := by decide
  have hdescent : baseEnd_8227202 < baseStart_8227202 := by decide
  rcases family_descends (prefixWord ++ tailWord_8227202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8227205 : List Nat := [1, 3, 1, 1, 3, 1, 1, 6, 1, 3, 2]
def baseStart_8227205 : Nat := 118140960795 + 8227205 * 2 ^ 59
def prefixEnd_8227205 : Nat := 4983230072969 + 3 ^ 40 * 8227205 * 2
def baseEnd_8227205 : Nat := 4224510608073588756301279

theorem tailTrace_8227205 : CollatzResearch.WordTrace tailWord_8227205 prefixEnd_8227205 4224510608073588756301279 := by
  unfold tailWord_8227205
  simp only [CollatzResearch.WordTrace]
  refine ⟨300070818159248854593803069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200047212106165903062535379 300070818159248854593803069)
  ·
    refine ⟨112526556809718320472676151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 300070818159248854593803069 112526556809718320472676151)
    ·
      refine ⟨168789835214577480709014227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112526556809718320472676151 168789835214577480709014227)
      ·
        refine ⟨253184752821866221063521341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168789835214577480709014227 253184752821866221063521341)
        ·
          refine ⟨94944282308199832898820503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 253184752821866221063521341 94944282308199832898820503)
          ·
            refine ⟨142416423462299749348230755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94944282308199832898820503 142416423462299749348230755)
            ·
              refine ⟨213624635193449624022346133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142416423462299749348230755 213624635193449624022346133)
              ·
                refine ⟨10013654774692951126047475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 213624635193449624022346133 10013654774692951126047475)
                ·
                  refine ⟨15020482162039426689071213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10013654774692951126047475 15020482162039426689071213)
                  ·
                    refine ⟨5632680810764785008401705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15020482162039426689071213 5632680810764785008401705)
                    ·
                      refine ⟨4224510608073588756301279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5632680810764785008401705 4224510608073588756301279)
                      ·
                        rfl

theorem cell23_8227205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 6, 1, 3, 2].length) (baseStart_8227205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8227205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8227205 prefixEnd_8227205 := by exact prefixLift 8227205
  have htrace : WordTrace (prefixWord ++ tailWord_8227205) baseStart_8227205 baseEnd_8227205 := by
    simpa [prefixWord, tailWord_8227205, baseEnd_8227205] using wordTrace_append hprefix tailTrace_8227205
  have hstable : (prefixWord ++ tailWord_8227205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8227205).length < 2 ^ (prefixWord ++ tailWord_8227205).sum := by decide
  have hdescent : baseEnd_8227205 < baseStart_8227205 := by decide
  rcases family_descends (prefixWord ++ tailWord_8227205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8227221 : List Nat := [1, 3, 2, 1, 1, 2, 1, 3, 1, 3, 5]
def baseStart_8227221 : Nat := 118140960795 + 8227221 * 2 ^ 59
def prefixEnd_8227221 : Nat := 4983230072969 + 3 ^ 40 * 8227221 * 2
def baseEnd_8227221 : Nat := 4224518823764060693701205

theorem tailTrace_8227221 : CollatzResearch.WordTrace tailWord_8227221 prefixEnd_8227221 4224518823764060693701205 := by
  unfold tailWord_8227221
  simp only [CollatzResearch.WordTrace]
  refine ⟨300071401727190889326385517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200047601151460592884257011 300071401727190889326385517)
  ·
    refine ⟨112526775647696583497394569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 300071401727190889326385517 112526775647696583497394569)
    ·
      refine ⟨84395081735772437623045927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112526775647696583497394569 84395081735772437623045927)
      ·
        refine ⟨126592622603658656434568891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84395081735772437623045927 126592622603658656434568891)
        ·
          refine ⟨189888933905487984651853337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126592622603658656434568891 189888933905487984651853337)
          ·
            refine ⟨142416700429115988488890003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189888933905487984651853337 142416700429115988488890003)
            ·
              refine ⟨213625050643673982733335005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142416700429115988488890003 213625050643673982733335005)
              ·
                refine ⟨80109393991377743525000627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 213625050643673982733335005 80109393991377743525000627)
                ·
                  refine ⟨120164090987066615287500941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80109393991377743525000627 120164090987066615287500941)
                  ·
                    refine ⟨45061534120149980732812853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 120164090987066615287500941 45061534120149980732812853)
                    ·
                      refine ⟨4224518823764060693701205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45061534120149980732812853 4224518823764060693701205)
                      ·
                        rfl

theorem cell23_8227221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 3, 1, 3, 5].length) (baseStart_8227221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8227221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8227221 prefixEnd_8227221 := by exact prefixLift 8227221
  have htrace : WordTrace (prefixWord ++ tailWord_8227221) baseStart_8227221 baseEnd_8227221 := by
    simpa [prefixWord, tailWord_8227221, baseEnd_8227221] using wordTrace_append hprefix tailTrace_8227221
  have hstable : (prefixWord ++ tailWord_8227221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8227221).length < 2 ^ (prefixWord ++ tailWord_8227221).sum := by decide
  have hdescent : baseEnd_8227221 < baseStart_8227221 := by decide
  rcases family_descends (prefixWord ++ tailWord_8227221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8227229 : List Nat := [1, 4, 2, 1, 4, 2, 1, 2, 2, 1, 3]
def baseStart_8227229 : Nat := 118140960795 + 8227229 * 2 ^ 59
def prefixEnd_8227229 : Nat := 4983230072969 + 3 ^ 40 * 8227229 * 2
def baseEnd_8227229 : Nat := 4224522931609296662401169

theorem tailTrace_8227229 : CollatzResearch.WordTrace tailWord_8227229 prefixEnd_8227229 4224522931609296662401169 := by
  unfold tailWord_8227229
  simp only [CollatzResearch.WordTrace]
  refine ⟨300071693511161906692676741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200047795674107937795117827 300071693511161906692676741)
  ·
    refine ⟨56263442533342857504876889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 300071693511161906692676741 56263442533342857504876889)
    ·
      refine ⟨42197581900007143128657667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56263442533342857504876889 42197581900007143128657667)
      ·
        refine ⟨63296372850010714692986501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42197581900007143128657667 63296372850010714692986501)
        ·
          refine ⟨11868069909377009004934969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63296372850010714692986501 11868069909377009004934969)
          ·
            refine ⟨8901052432032756753701227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11868069909377009004934969 8901052432032756753701227)
            ·
              refine ⟨13351578648049135130551841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8901052432032756753701227 13351578648049135130551841)
              ·
                refine ⟨10013683986036851347913881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13351578648049135130551841 10013683986036851347913881)
                ·
                  refine ⟨7510262989527638510935411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10013683986036851347913881 7510262989527638510935411)
                  ·
                    refine ⟨11265394484291457766403117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7510262989527638510935411 11265394484291457766403117)
                    ·
                      refine ⟨4224522931609296662401169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11265394484291457766403117 4224522931609296662401169)
                      ·
                        rfl

theorem cell23_8227229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 1, 2, 2, 1, 3].length) (baseStart_8227229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8227229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8227229 prefixEnd_8227229 := by exact prefixLift 8227229
  have htrace : WordTrace (prefixWord ++ tailWord_8227229) baseStart_8227229 baseEnd_8227229 := by
    simpa [prefixWord, tailWord_8227229, baseEnd_8227229] using wordTrace_append hprefix tailTrace_8227229
  have hstable : (prefixWord ++ tailWord_8227229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8227229).length < 2 ^ (prefixWord ++ tailWord_8227229).sum := by decide
  have hdescent : baseEnd_8227229 < baseStart_8227229 := by decide
  rcases family_descends (prefixWord ++ tailWord_8227229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8227281 : List Nat := [1, 2, 2, 1, 2, 1, 1, 2, 3, 1, 7]
def baseStart_8227281 : Nat := 118140960795 + 8227281 * 2 ^ 59
def prefixEnd_8227281 : Nat := 4983230072969 + 3 ^ 40 * 8227281 * 2
def baseEnd_8227281 : Nat := 4224549632603330458950929

theorem tailTrace_8227281 : CollatzResearch.WordTrace tailWord_8227281 prefixEnd_8227281 4224549632603330458950929 := by
  unfold tailWord_8227281
  simp only [CollatzResearch.WordTrace]
  refine ⟨300073590106973519573569697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200049060071315679715713131 300073590106973519573569697)
  ·
    refine ⟨225055192580230139680177273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300073590106973519573569697 225055192580230139680177273)
    ·
      refine ⟨168791394435172604760132955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225055192580230139680177273 168791394435172604760132955)
      ·
        refine ⟨253187091652758907140199433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168791394435172604760132955 253187091652758907140199433)
        ·
          refine ⟨189890318739569180355149575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 253187091652758907140199433 189890318739569180355149575)
          ·
            refine ⟨284835478109353770532724363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189890318739569180355149575 284835478109353770532724363)
            ·
              refine ⟨427253217164030655799086545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 284835478109353770532724363 427253217164030655799086545)
              ·
                refine ⟨320439912873022991849314909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 427253217164030655799086545 320439912873022991849314909)
                ·
                  refine ⟨120164967327383621943493091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 320439912873022991849314909 120164967327383621943493091)
                  ·
                    refine ⟨180247450991075432915239637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 120164967327383621943493091 180247450991075432915239637)
                    ·
                      refine ⟨4224549632603330458950929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 180247450991075432915239637 4224549632603330458950929)
                      ·
                        rfl

theorem cell23_8227281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 1, 7].length) (baseStart_8227281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8227281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8227281 prefixEnd_8227281 := by exact prefixLift 8227281
  have htrace : WordTrace (prefixWord ++ tailWord_8227281) baseStart_8227281 baseEnd_8227281 := by
    simpa [prefixWord, tailWord_8227281, baseEnd_8227281] using wordTrace_append hprefix tailTrace_8227281
  have hstable : (prefixWord ++ tailWord_8227281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8227281).length < 2 ^ (prefixWord ++ tailWord_8227281).sum := by decide
  have hdescent : baseEnd_8227281 < baseStart_8227281 := by decide
  rcases family_descends (prefixWord ++ tailWord_8227281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8227308 : List Nat := [2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 4]
def baseStart_8227308 : Nat := 118140960795 + 8227308 * 2 ^ 59
def prefixEnd_8227308 : Nat := 4983230072969 + 3 ^ 40 * 8227308 * 2
def baseEnd_8227308 : Nat := 4224563496581001853313305

theorem tailTrace_8227308 : CollatzResearch.WordTrace tailWord_8227308 prefixEnd_8227308 4224563496581001853313305 := by
  unfold tailWord_8227308
  simp only [CollatzResearch.WordTrace]
  refine ⟨150037287438937851592401289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200049716585250468789868385 150037287438937851592401289)
  ·
    refine ⟨112527965579203388694300967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150037287438937851592401289 112527965579203388694300967)
    ·
      refine ⟨168791948368805083041451451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112527965579203388694300967 168791948368805083041451451)
      ·
        refine ⟨253187922553207624562177177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168791948368805083041451451 253187922553207624562177177)
        ·
          refine ⟨189890941914905718421632883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 253187922553207624562177177 189890941914905718421632883)
          ·
            refine ⟨284836412872358577632449325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189890941914905718421632883 284836412872358577632449325)
            ·
              refine ⟨106813654827134466612168497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 284836412872358577632449325 106813654827134466612168497)
              ·
                refine ⟨80110241120350849959126373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106813654827134466612168497 80110241120350849959126373)
                ·
                  refine ⟨15020670210065784367336195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80110241120350849959126373 15020670210065784367336195)
                  ·
                    refine ⟨22531005315098676551004293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15020670210065784367336195 22531005315098676551004293)
                    ·
                      refine ⟨4224563496581001853313305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22531005315098676551004293 4224563496581001853313305)
                      ·
                        rfl

theorem cell23_8227308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 4].length) (baseStart_8227308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8227308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8227308 prefixEnd_8227308 := by exact prefixLift 8227308
  have htrace : WordTrace (prefixWord ++ tailWord_8227308) baseStart_8227308 baseEnd_8227308 := by
    simpa [prefixWord, tailWord_8227308, baseEnd_8227308] using wordTrace_append hprefix tailTrace_8227308
  have hstable : (prefixWord ++ tailWord_8227308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8227308).length < 2 ^ (prefixWord ++ tailWord_8227308).sum := by decide
  have hdescent : baseEnd_8227308 < baseStart_8227308 := by decide
  rcases family_descends (prefixWord ++ tailWord_8227308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8227325 : List Nat := [1, 4, 1, 1, 1, 3, 4, 1, 2, 1, 4]
def baseStart_8227325 : Nat := 118140960795 + 8227325 * 2 ^ 59
def prefixEnd_8227325 : Nat := 4983230072969 + 3 ^ 40 * 8227325 * 2
def baseEnd_8227325 : Nat := 4224572225752128286800727

theorem tailTrace_8227325 : CollatzResearch.WordTrace tailWord_8227325 prefixEnd_8227325 4224572225752128286800727 := by
  unfold tailWord_8227325
  simp only [CollatzResearch.WordTrace]
  refine ⟨300075194918814115088171429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200050129945876076725447619 300075194918814115088171429)
  ·
    refine ⟨56264099047277646579032143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 300075194918814115088171429 56264099047277646579032143)
    ·
      refine ⟨84396148570916469868548215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56264099047277646579032143 84396148570916469868548215)
      ·
        refine ⟨126594222856374704802822323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84396148570916469868548215 126594222856374704802822323)
        ·
          refine ⟨189891334284562057204233485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126594222856374704802822323 189891334284562057204233485)
          ·
            refine ⟨71209250356710771451587557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 189891334284562057204233485 71209250356710771451587557)
            ·
              refine ⟨13351734441883269647172667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71209250356710771451587557 13351734441883269647172667)
              ·
                refine ⟨20027601662824904470759001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13351734441883269647172667 20027601662824904470759001)
                ·
                  refine ⟨15020701247118678353069251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20027601662824904470759001 15020701247118678353069251)
                  ·
                    refine ⟨22531051870678017529603877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15020701247118678353069251 22531051870678017529603877)
                    ·
                      refine ⟨4224572225752128286800727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22531051870678017529603877 4224572225752128286800727)
                      ·
                        rfl

theorem cell23_8227325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 4, 1, 2, 1, 4].length) (baseStart_8227325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8227325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8227325 prefixEnd_8227325 := by exact prefixLift 8227325
  have htrace : WordTrace (prefixWord ++ tailWord_8227325) baseStart_8227325 baseEnd_8227325 := by
    simpa [prefixWord, tailWord_8227325, baseEnd_8227325] using wordTrace_append hprefix tailTrace_8227325
  have hstable : (prefixWord ++ tailWord_8227325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8227325).length < 2 ^ (prefixWord ++ tailWord_8227325).sum := by decide
  have hdescent : baseEnd_8227325 < baseStart_8227325 := by decide
  rcases family_descends (prefixWord ++ tailWord_8227325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8227338 : List Nat := [3, 1, 2, 2, 2, 1, 2, 1, 2, 1, 6]
def baseStart_8227338 : Nat := 118140960795 + 8227338 * 2 ^ 59
def prefixEnd_8227338 : Nat := 4983230072969 + 3 ^ 40 * 8227338 * 2
def baseEnd_8227338 : Nat := 4224578901000636735938167

theorem tailTrace_8227338 : CollatzResearch.WordTrace tailWord_8227338 prefixEnd_8227338 4224578901000636735938167 := by
  unfold tailWord_8227338
  simp only [CollatzResearch.WordTrace]
  refine ⟨75018917266941754577098667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200050446045178012205596445 75018917266941754577098667)
  ·
    refine ⟨112528375900412631865648001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75018917266941754577098667 112528375900412631865648001)
    ·
      refine ⟨84396281925309473899236001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112528375900412631865648001 84396281925309473899236001)
      ·
        refine ⟨63297211443982105424427001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84396281925309473899236001 63297211443982105424427001)
        ·
          refine ⟨47472908582986579068320251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63297211443982105424427001 47472908582986579068320251)
          ·
            refine ⟨71209362874479868602480377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47472908582986579068320251 71209362874479868602480377)
            ·
              refine ⟨53407022155859901451860283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71209362874479868602480377 53407022155859901451860283)
              ·
                refine ⟨80110533233789852177790425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53407022155859901451860283 80110533233789852177790425)
                ·
                  refine ⟨60082899925342389133342819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80110533233789852177790425 60082899925342389133342819)
                  ·
                    refine ⟨90124349888013583700014229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60082899925342389133342819 90124349888013583700014229)
                    ·
                      refine ⟨4224578901000636735938167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90124349888013583700014229 4224578901000636735938167)
                      ·
                        rfl

theorem cell23_8227338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 1, 2, 1, 6].length) (baseStart_8227338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8227338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8227338 prefixEnd_8227338 := by exact prefixLift 8227338
  have htrace : WordTrace (prefixWord ++ tailWord_8227338) baseStart_8227338 baseEnd_8227338 := by
    simpa [prefixWord, tailWord_8227338, baseEnd_8227338] using wordTrace_append hprefix tailTrace_8227338
  have hstable : (prefixWord ++ tailWord_8227338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8227338).length < 2 ^ (prefixWord ++ tailWord_8227338).sum := by decide
  have hdescent : baseEnd_8227338 < baseStart_8227338 := by decide
  rcases family_descends (prefixWord ++ tailWord_8227338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8227373 : List Nat := [1, 5, 4, 1, 2, 1, 1, 1, 2, 5]
def baseStart_8227373 : Nat := 118140960795 + 8227373 * 2 ^ 59
def prefixEnd_8227373 : Nat := 4983230072969 + 3 ^ 40 * 8227373 * 2
def baseEnd_8227373 : Nat := 1408198957607848033000169

theorem tailTrace_8227373 : CollatzResearch.WordTrace tailWord_8227373 prefixEnd_8227373 1408198957607848033000169 := by
  unfold tailWord_8227373
  simp only [CollatzResearch.WordTrace]
  refine ⟨300076945622640219285918773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200051297081760146190612515 300076945622640219285918773)
  ·
    refine ⟨28132213652122520558054885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 300076945622640219285918773 28132213652122520558054885)
    ·
      refine ⟨5274790059772972604635291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28132213652122520558054885 5274790059772972604635291)
      ·
        refine ⟨7912185089659458906952937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5274790059772972604635291 7912185089659458906952937)
        ·
          refine ⟨5934138817244594180214703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7912185089659458906952937 5934138817244594180214703)
          ·
            refine ⟨8901208225866891270322055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5934138817244594180214703 8901208225866891270322055)
            ·
              refine ⟨13351812338800336905483083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8901208225866891270322055 13351812338800336905483083)
              ·
                refine ⟨20027718508200505358224625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13351812338800336905483083 20027718508200505358224625)
                ·
                  refine ⟨15020788881150379018668469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20027718508200505358224625 15020788881150379018668469)
                  ·
                    refine ⟨1408198957607848033000169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15020788881150379018668469 1408198957607848033000169)
                    ·
                      rfl

theorem cell23_8227373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_8227373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8227373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8227373 prefixEnd_8227373 := by exact prefixLift 8227373
  have htrace : WordTrace (prefixWord ++ tailWord_8227373) baseStart_8227373 baseEnd_8227373 := by
    simpa [prefixWord, tailWord_8227373, baseEnd_8227373] using wordTrace_append hprefix tailTrace_8227373
  have hstable : (prefixWord ++ tailWord_8227373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8227373).length < 2 ^ (prefixWord ++ tailWord_8227373).sum := by decide
  have hdescent : baseEnd_8227373 < baseStart_8227373 := by decide
  rcases family_descends (prefixWord ++ tailWord_8227373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8227409 : List Nat := [1, 2, 2, 1, 3, 3, 2, 4, 1, 1, 3]
def baseStart_8227409 : Nat := 118140960795 + 8227409 * 2 ^ 59
def prefixEnd_8227409 : Nat := 4983230072969 + 3 ^ 40 * 8227409 * 2
def baseEnd_8227409 : Nat := 4224615358127105958150341

theorem tailTrace_8227409 : CollatzResearch.WordTrace tailWord_8227409 prefixEnd_8227409 4224615358127105958150341 := by
  unfold tailWord_8227409
  simp only [CollatzResearch.WordTrace]
  refine ⟨300078258650509797434229281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200052172433673198289486187 300078258650509797434229281)
  ·
    refine ⟨225058693987882348075671961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300078258650509797434229281 225058693987882348075671961)
    ·
      refine ⟨168794020490911761056753971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225058693987882348075671961 168794020490911761056753971)
      ·
        refine ⟨253191030736367641585130957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168794020490911761056753971 253191030736367641585130957)
        ·
          refine ⟨94946636526137865594424109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 253191030736367641585130957 94946636526137865594424109)
          ·
            refine ⟨35604988697301699597909041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94946636526137865594424109 35604988697301699597909041)
            ·
              refine ⟨26703741522976274698431781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35604988697301699597909041 26703741522976274698431781)
              ·
                refine ⟨5006951535558051505955959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26703741522976274698431781 5006951535558051505955959)
                ·
                  refine ⟨7510427303337077258933939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5006951535558051505955959 7510427303337077258933939)
                  ·
                    refine ⟨11265640955005615888400909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7510427303337077258933939 11265640955005615888400909)
                    ·
                      refine ⟨4224615358127105958150341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11265640955005615888400909 4224615358127105958150341)
                      ·
                        rfl

theorem cell23_8227409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 4, 1, 1, 3].length) (baseStart_8227409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8227409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8227409 prefixEnd_8227409 := by exact prefixLift 8227409
  have htrace : WordTrace (prefixWord ++ tailWord_8227409) baseStart_8227409 baseEnd_8227409 := by
    simpa [prefixWord, tailWord_8227409, baseEnd_8227409] using wordTrace_append hprefix tailTrace_8227409
  have hstable : (prefixWord ++ tailWord_8227409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8227409).length < 2 ^ (prefixWord ++ tailWord_8227409).sum := by decide
  have hdescent : baseEnd_8227409 < baseStart_8227409 := by decide
  rcases family_descends (prefixWord ++ tailWord_8227409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8227425 : List Nat := [1, 2, 3, 1, 1, 4, 3, 1, 1, 6]
def baseStart_8227425 : Nat := 118140960795 + 8227425 * 2 ^ 59
def prefixEnd_8227425 : Nat := 4983230072969 + 3 ^ 40 * 8227425 * 2
def baseEnd_8227425 : Nat := 1408207857939192631850089

theorem tailTrace_8227425 : CollatzResearch.WordTrace tailWord_8227425 prefixEnd_8227425 1408207857939192631850089 := by
  unfold tailWord_8227425
  simp only [CollatzResearch.WordTrace]
  refine ⟨300078842218451832166811729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200052561478967888111207819 300078842218451832166811729)
  ·
    refine ⟨225059131663838874125108797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300078842218451832166811729 225059131663838874125108797)
    ·
      refine ⟨84397174373939577796915799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225059131663838874125108797 84397174373939577796915799)
      ·
        refine ⟨126595761560909366695373699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84397174373939577796915799 126595761560909366695373699)
        ·
          refine ⟨189893642341364050043060549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126595761560909366695373699 189893642341364050043060549)
          ·
            refine ⟨35605057939005759383073853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 189893642341364050043060549 35605057939005759383073853)
            ·
              refine ⟨13351896727127159768652695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35605057939005759383073853 13351896727127159768652695)
              ·
                refine ⟨20027845090690739652979043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13351896727127159768652695 20027845090690739652979043)
                ·
                  refine ⟨30041767636036109479468565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20027845090690739652979043 30041767636036109479468565)
                  ·
                    refine ⟨1408207857939192631850089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30041767636036109479468565 1408207857939192631850089)
                    ·
                      rfl

theorem cell23_8227425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 3, 1, 1, 6].length) (baseStart_8227425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8227425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8227425 prefixEnd_8227425 := by exact prefixLift 8227425
  have htrace : WordTrace (prefixWord ++ tailWord_8227425) baseStart_8227425 baseEnd_8227425 := by
    simpa [prefixWord, tailWord_8227425, baseEnd_8227425] using wordTrace_append hprefix tailTrace_8227425
  have hstable : (prefixWord ++ tailWord_8227425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8227425).length < 2 ^ (prefixWord ++ tailWord_8227425).sum := by decide
  have hdescent : baseEnd_8227425 < baseStart_8227425 := by decide
  rcases family_descends (prefixWord ++ tailWord_8227425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8227452 : List Nat := [2, 2, 2, 1, 1, 2, 4, 3, 1, 2, 3]
def baseStart_8227452 : Nat := 118140960795 + 8227452 * 2 ^ 59
def prefixEnd_8227452 : Nat := 4983230072969 + 3 ^ 40 * 8227452 * 2
def baseEnd_8227452 : Nat := 4224637437795249289912643

theorem tailTrace_8227452 : CollatzResearch.WordTrace tailWord_8227452 prefixEnd_8227452 4224637437795249289912643 := by
  unfold tailWord_8227452
  simp only [CollatzResearch.WordTrace]
  refine ⟨150039913494677007889022305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200053217992902677185363073 150039913494677007889022305)
  ·
    refine ⟨112529935121007755916766729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150039913494677007889022305 112529935121007755916766729)
    ·
      refine ⟨84397451340755816937575047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112529935121007755916766729 84397451340755816937575047)
      ·
        refine ⟨126596177011133725406362571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84397451340755816937575047 126596177011133725406362571)
        ·
          refine ⟨189894265516700588109543857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126596177011133725406362571 189894265516700588109543857)
          ·
            refine ⟨142420699137525441082157893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189894265516700588109543857 142420699137525441082157893)
            ·
              refine ⟨26703881088286020202904605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 142420699137525441082157893 26703881088286020202904605)
              ·
                refine ⟨10013955408107257576089227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26703881088286020202904605 10013955408107257576089227)
                ·
                  refine ⟨15020933112160886364133841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10013955408107257576089227 15020933112160886364133841)
                  ·
                    refine ⟨11265699834120664773100381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15020933112160886364133841 11265699834120664773100381)
                    ·
                      refine ⟨4224637437795249289912643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11265699834120664773100381 4224637437795249289912643)
                      ·
                        rfl

theorem cell23_8227452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 3, 1, 2, 3].length) (baseStart_8227452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8227452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8227452 prefixEnd_8227452 := by exact prefixLift 8227452
  have htrace : WordTrace (prefixWord ++ tailWord_8227452) baseStart_8227452 baseEnd_8227452 := by
    simpa [prefixWord, tailWord_8227452, baseEnd_8227452] using wordTrace_append hprefix tailTrace_8227452
  have hstable : (prefixWord ++ tailWord_8227452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8227452).length < 2 ^ (prefixWord ++ tailWord_8227452).sum := by decide
  have hdescent : baseEnd_8227452 < baseStart_8227452 := by decide
  rcases family_descends (prefixWord ++ tailWord_8227452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8227476 : List Nat := [2, 4, 2, 2, 1, 1, 4, 1, 2, 4]
def baseStart_8227476 : Nat := 118140960795 + 8227476 * 2 ^ 59
def prefixEnd_8227476 : Nat := 4983230072969 + 3 ^ 40 * 8227476 * 2
def baseEnd_8227476 : Nat := 1408216587110319065337511

theorem tailTrace_8227476 : CollatzResearch.WordTrace tailWord_8227476 prefixEnd_8227476 1408216587110319065337511 := by
  unfold tailWord_8227476
  simp only [CollatzResearch.WordTrace]
  refine ⟨150040351170633533938459141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200053801560844711917945521 150040351170633533938459141)
  ·
    refine ⟨28132565844493787613461089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150040351170633533938459141 28132565844493787613461089)
    ·
      refine ⟨21099424383370340710095817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28132565844493787613461089 21099424383370340710095817)
      ·
        refine ⟨15824568287527755532571863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21099424383370340710095817 15824568287527755532571863)
        ·
          refine ⟨23736852431291633298857795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15824568287527755532571863 23736852431291633298857795)
          ·
            refine ⟨35605278646937449948286693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23736852431291633298857795 35605278646937449948286693)
            ·
              refine ⟨6675989746300771865303755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35605278646937449948286693 6675989746300771865303755)
              ·
                refine ⟨10013984619451157797955633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6675989746300771865303755 10013984619451157797955633)
                ·
                  refine ⟨7510488464588368348466725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10013984619451157797955633 7510488464588368348466725)
                  ·
                    refine ⟨1408216587110319065337511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7510488464588368348466725 1408216587110319065337511)
                    ·
                      rfl

theorem cell23_8227476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 4, 1, 2, 4].length) (baseStart_8227476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8227476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8227476 prefixEnd_8227476 := by exact prefixLift 8227476
  have htrace : WordTrace (prefixWord ++ tailWord_8227476) baseStart_8227476 baseEnd_8227476 := by
    simpa [prefixWord, tailWord_8227476, baseEnd_8227476] using wordTrace_append hprefix tailTrace_8227476
  have hstable : (prefixWord ++ tailWord_8227476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8227476).length < 2 ^ (prefixWord ++ tailWord_8227476).sum := by decide
  have hdescent : baseEnd_8227476 < baseStart_8227476 := by decide
  rcases family_descends (prefixWord ++ tailWord_8227476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8227532 : List Nat := [2, 2, 1, 5, 1, 2, 1, 1, 2, 6]
def baseStart_8227532 : Nat := 118140960795 + 8227532 * 2 ^ 59
def prefixEnd_8227532 : Nat := 4983230072969 + 3 ^ 40 * 8227532 * 2
def baseEnd_8227532 : Nat := 1408226172082536325637425

theorem tailTrace_8227532 : CollatzResearch.WordTrace tailWord_8227532 prefixEnd_8227532 1408226172082536325637425 := by
  unfold tailWord_8227532
  simp only [CollatzResearch.WordTrace]
  refine ⟨150041372414532094720478425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200055163219376126293971233 150041372414532094720478425)
  ·
    refine ⟨112531029310899071040358819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150041372414532094720478425 112531029310899071040358819)
    ·
      refine ⟨168796543966348606560538229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112531029310899071040358819 168796543966348606560538229)
      ·
        refine ⟨15824675996845181865050459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 168796543966348606560538229 15824675996845181865050459)
        ·
          refine ⟨23737013995267772797575689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15824675996845181865050459 23737013995267772797575689)
          ·
            refine ⟨17802760496450829598181767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23737013995267772797575689 17802760496450829598181767)
            ·
              refine ⟨26704140744676244397272651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17802760496450829598181767 26704140744676244397272651)
              ·
                refine ⟨40056211117014366595908977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26704140744676244397272651 40056211117014366595908977)
                ·
                  refine ⟨30042158337760774946931733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40056211117014366595908977 30042158337760774946931733)
                  ·
                    refine ⟨1408226172082536325637425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30042158337760774946931733 1408226172082536325637425)
                    ·
                      rfl

theorem cell23_8227532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 1, 2, 6].length) (baseStart_8227532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8227532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8227532 prefixEnd_8227532 := by exact prefixLift 8227532
  have htrace : WordTrace (prefixWord ++ tailWord_8227532) baseStart_8227532 baseEnd_8227532 := by
    simpa [prefixWord, tailWord_8227532, baseEnd_8227532] using wordTrace_append hprefix tailTrace_8227532
  have hstable : (prefixWord ++ tailWord_8227532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8227532).length < 2 ^ (prefixWord ++ tailWord_8227532).sum := by decide
  have hdescent : baseEnd_8227532 < baseStart_8227532 := by decide
  rcases family_descends (prefixWord ++ tailWord_8227532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8227545 : List Nat := [1, 2, 1, 2, 3, 2, 3, 2, 7]
def baseStart_8227545 : Nat := 118140960795 + 8227545 * 2 ^ 59
def prefixEnd_8227545 : Nat := 4983230072969 + 3 ^ 40 * 8227545 * 2
def baseEnd_8227545 : Nat := 469409465721790825116635

theorem tailTrace_8227545 : CollatzResearch.WordTrace tailWord_8227545 prefixEnd_8227545 469409465721790825116635 := by
  unfold tailWord_8227545
  simp only [CollatzResearch.WordTrace]
  refine ⟨300083218978017092661180089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200055479318678061774120059 300083218978017092661180089)
  ·
    refine ⟨225062414233512819495885067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300083218978017092661180089 225062414233512819495885067)
    ·
      refine ⟨337593621350269229243827601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225062414233512819495885067 337593621350269229243827601)
      ·
        refine ⟨253195216012701921932870701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 337593621350269229243827601 253195216012701921932870701)
        ·
          refine ⟨94948206004763220724826513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 253195216012701921932870701 94948206004763220724826513)
          ·
            refine ⟨71211154503572415543619885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94948206004763220724826513 71211154503572415543619885)
            ·
              refine ⟨26704182938839655828857457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71211154503572415543619885 26704182938839655828857457)
              ·
                refine ⟨20028137204129741871643093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26704182938839655828857457 20028137204129741871643093)
                ·
                  refine ⟨469409465721790825116635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20028137204129741871643093 469409465721790825116635)
                  ·
                    rfl

theorem cell23_8227545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 2, 7].length) (baseStart_8227545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8227545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8227545 prefixEnd_8227545 := by exact prefixLift 8227545
  have htrace : WordTrace (prefixWord ++ tailWord_8227545) baseStart_8227545 baseEnd_8227545 := by
    simpa [prefixWord, tailWord_8227545, baseEnd_8227545] using wordTrace_append hprefix tailTrace_8227545
  have hstable : (prefixWord ++ tailWord_8227545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8227545).length < 2 ^ (prefixWord ++ tailWord_8227545).sum := by decide
  have hdescent : baseEnd_8227545 < baseStart_8227545 := by decide
  rcases family_descends (prefixWord ++ tailWord_8227545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8227560 : List Nat := [2, 1, 4, 1, 5, 1, 2, 1, 1, 3, 2]
def baseStart_8227560 : Nat := 118140960795 + 8227560 * 2 ^ 59
def prefixEnd_8227560 : Nat := 4983230072969 + 3 ^ 40 * 8227560 * 2
def baseEnd_8227560 : Nat := 4224692893705934867362147

theorem tailTrace_8227560 : CollatzResearch.WordTrace tailWord_8227560 prefixEnd_8227560 4224692893705934867362147 := by
  unfold tailWord_8227560
  simp only [CollatzResearch.WordTrace]
  refine ⟨150041883036481375111488067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200055844048641833481984089 150041883036481375111488067)
  ·
    refine ⟨225062824554722062667232101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150041883036481375111488067 225062824554722062667232101)
    ·
      refine ⟨42199279604010386750106019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 225062824554722062667232101 42199279604010386750106019)
      ·
        refine ⟨63298919406015580125159029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42199279604010386750106019 63298919406015580125159029)
        ·
          refine ⟨5934273694313960636733659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63298919406015580125159029 5934273694313960636733659)
          ·
            refine ⟨8901410541470940955100489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5934273694313960636733659 8901410541470940955100489)
            ·
              refine ⟨6676057906103205716325367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8901410541470940955100489 6676057906103205716325367)
              ·
                refine ⟨10014086859154808574488051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6676057906103205716325367 10014086859154808574488051)
                ·
                  refine ⟨15021130288732212861732077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10014086859154808574488051 15021130288732212861732077)
                  ·
                    refine ⟨5632923858274579823149529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15021130288732212861732077 5632923858274579823149529)
                    ·
                      refine ⟨4224692893705934867362147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5632923858274579823149529 4224692893705934867362147)
                      ·
                        rfl

theorem cell23_8227560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 2, 1, 1, 3, 2].length) (baseStart_8227560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8227560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8227560 prefixEnd_8227560 := by exact prefixLift 8227560
  have htrace : WordTrace (prefixWord ++ tailWord_8227560) baseStart_8227560 baseEnd_8227560 := by
    simpa [prefixWord, tailWord_8227560, baseEnd_8227560] using wordTrace_append hprefix tailTrace_8227560
  have hstable : (prefixWord ++ tailWord_8227560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8227560).length < 2 ^ (prefixWord ++ tailWord_8227560).sum := by decide
  have hdescent : baseEnd_8227560 < baseStart_8227560 := by decide
  rcases family_descends (prefixWord ++ tailWord_8227560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8227575 : List Nat := [1, 1, 3, 1, 1, 1, 3, 3, 4, 5]
def baseStart_8227575 : Nat := 118140960795 + 8227575 * 2 ^ 59
def prefixEnd_8227575 : Nat := 4983230072969 + 3 ^ 40 * 8227575 * 2
def baseEnd_8227575 : Nat := 1408233531971917436224859

theorem tailTrace_8227575 : CollatzResearch.WordTrace tailWord_8227575 prefixEnd_8227575 1408233531971917436224859 := by
  unfold tailWord_8227575
  simp only [CollatzResearch.WordTrace]
  refine ⟨300084313167908407784772179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200056208778605605189848119 300084313167908407784772179)
  ·
    refine ⟨450126469751862611677158269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300084313167908407784772179 450126469751862611677158269)
    ·
      refine ⟨168797426156948479378934351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 450126469751862611677158269 168797426156948479378934351)
      ·
        refine ⟨253196139235422719068401527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168797426156948479378934351 253196139235422719068401527)
        ·
          refine ⟨379794208853134078602602291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253196139235422719068401527 379794208853134078602602291)
          ·
            refine ⟨569691313279701117903903437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 379794208853134078602602291 569691313279701117903903437)
            ·
              refine ⟨213634242479887919213963789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 569691313279701117903903437 213634242479887919213963789)
              ·
                refine ⟨80112840929957969705236421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 213634242479887919213963789 80112840929957969705236421)
                ·
                  refine ⟨15021157674367119319731829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80112840929957969705236421 15021157674367119319731829)
                  ·
                    refine ⟨1408233531971917436224859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15021157674367119319731829 1408233531971917436224859)
                    ·
                      rfl

theorem cell23_8227575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 3, 4, 5].length) (baseStart_8227575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8227575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8227575 prefixEnd_8227575 := by exact prefixLift 8227575
  have htrace : WordTrace (prefixWord ++ tailWord_8227575) baseStart_8227575 baseEnd_8227575 := by
    simpa [prefixWord, tailWord_8227575, baseEnd_8227575] using wordTrace_append hprefix tailTrace_8227575
  have hstable : (prefixWord ++ tailWord_8227575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8227575).length < 2 ^ (prefixWord ++ tailWord_8227575).sum := by decide
  have hdescent : baseEnd_8227575 < baseStart_8227575 := by decide
  rcases family_descends (prefixWord ++ tailWord_8227575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8227585 : List Nat := [1, 2, 4, 1, 1, 1, 1, 3, 1, 1, 7]
def baseStart_8227585 : Nat := 118140960795 + 8227585 * 2 ^ 59
def prefixEnd_8227585 : Nat := 4983230072969 + 3 ^ 40 * 8227585 * 2
def baseEnd_8227585 : Nat := 4224705730722297269549531

theorem tailTrace_8227585 : CollatzResearch.WordTrace tailWord_8227585 prefixEnd_8227585 4224705730722297269549531 := by
  unfold tailWord_8227585
  simp only [CollatzResearch.WordTrace]
  refine ⟨300084677897872179492636209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200056451931914786328424139 300084677897872179492636209)
  ·
    refine ⟨225063508423404134619477157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300084677897872179492636209 225063508423404134619477157)
    ·
      refine ⟨42199407829388275241151967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 225063508423404134619477157 42199407829388275241151967)
      ·
        refine ⟨63299111744082412861727951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42199407829388275241151967 63299111744082412861727951)
        ·
          refine ⟨94948667616123619292591927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63299111744082412861727951 94948667616123619292591927)
          ·
            refine ⟨142423001424185428938887891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94948667616123619292591927 142423001424185428938887891)
            ·
              refine ⟨213634502136278143408331837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142423001424185428938887891 213634502136278143408331837)
              ·
                refine ⟨80112938301104303778124439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 213634502136278143408331837 80112938301104303778124439)
                ·
                  refine ⟨120169407451656455667186659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80112938301104303778124439 120169407451656455667186659)
                  ·
                    refine ⟨180254111177484683500779989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 120169407451656455667186659 180254111177484683500779989)
                    ·
                      refine ⟨4224705730722297269549531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 180254111177484683500779989 4224705730722297269549531)
                      ·
                        rfl

theorem cell23_8227585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 3, 1, 1, 7].length) (baseStart_8227585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8227585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8227585 prefixEnd_8227585 := by exact prefixLift 8227585
  have htrace : WordTrace (prefixWord ++ tailWord_8227585) baseStart_8227585 baseEnd_8227585 := by
    simpa [prefixWord, tailWord_8227585, baseEnd_8227585] using wordTrace_append hprefix tailTrace_8227585
  have hstable : (prefixWord ++ tailWord_8227585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8227585).length < 2 ^ (prefixWord ++ tailWord_8227585).sum := by decide
  have hdescent : baseEnd_8227585 < baseStart_8227585 := by decide
  rcases family_descends (prefixWord ++ tailWord_8227585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8227605 : List Nat := [1, 3, 2, 1, 2, 2, 1, 1, 2, 8]
def baseStart_8227605 : Nat := 118140960795 + 8227605 * 2 ^ 59
def prefixEnd_8227605 : Nat := 4983230072969 + 3 ^ 40 * 8227605 * 2
def baseEnd_8227605 : Nat := 1408238666778462397099813

theorem tailTrace_8227605 : CollatzResearch.WordTrace tailWord_8227605 prefixEnd_8227605 1408238666778462397099813 := by
  unfold tailWord_8227605
  simp only [CollatzResearch.WordTrace]
  refine ⟨300085407357799722908364269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200056938238533148605576179 300085407357799722908364269)
  ·
    refine ⟨112532027759174896090636601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 300085407357799722908364269 112532027759174896090636601)
    ·
      refine ⟨84399020819381172067977451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112532027759174896090636601 84399020819381172067977451)
      ·
        refine ⟨126598531229071758101966177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84399020819381172067977451 126598531229071758101966177)
        ·
          refine ⟨94948898421803818576474633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126598531229071758101966177 94948898421803818576474633)
          ·
            refine ⟨71211673816352863932355975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94948898421803818576474633 71211673816352863932355975)
            ·
              refine ⟨106817510724529295898533963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71211673816352863932355975 106817510724529295898533963)
              ·
                refine ⟨160226266086793943847800945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106817510724529295898533963 160226266086793943847800945)
                ·
                  refine ⟨120169699565095457885850709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 160226266086793943847800945 120169699565095457885850709)
                  ·
                    refine ⟨1408238666778462397099813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 120169699565095457885850709 1408238666778462397099813)
                    ·
                      rfl

theorem cell23_8227605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 2, 8].length) (baseStart_8227605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8227605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8227605 prefixEnd_8227605 := by exact prefixLift 8227605
  have htrace : WordTrace (prefixWord ++ tailWord_8227605) baseStart_8227605 baseEnd_8227605 := by
    simpa [prefixWord, tailWord_8227605, baseEnd_8227605] using wordTrace_append hprefix tailTrace_8227605
  have hstable : (prefixWord ++ tailWord_8227605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8227605).length < 2 ^ (prefixWord ++ tailWord_8227605).sum := by decide
  have hdescent : baseEnd_8227605 < baseStart_8227605 := by decide
  rcases family_descends (prefixWord ++ tailWord_8227605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8227612 : List Nat := [2, 2, 3, 1, 1, 3, 2, 1, 1, 3, 4]
def baseStart_8227612 : Nat := 118140960795 + 8227612 * 2 ^ 59
def prefixEnd_8227612 : Nat := 4983230072969 + 3 ^ 40 * 8227612 * 2
def baseEnd_8227612 : Nat := 4224719594699968663911907

theorem tailTrace_8227612 : CollatzResearch.WordTrace tailWord_8227612 prefixEnd_8227612 4224719594699968663911907 := by
  unfold tailWord_8227612
  simp only [CollatzResearch.WordTrace]
  refine ⟨150042831334387181551934545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200057108445849575402579393 150042831334387181551934545)
  ·
    refine ⟨112532123500790386163950909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150042831334387181551934545 112532123500790386163950909)
    ·
      refine ⟨42199546312796394811481591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112532123500790386163950909 42199546312796394811481591)
      ·
        refine ⟨63299319469194592217222387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42199546312796394811481591 63299319469194592217222387)
        ·
          refine ⟨94948979203791888325833581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63299319469194592217222387 94948979203791888325833581)
          ·
            refine ⟨35605867201421958122187593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94948979203791888325833581 35605867201421958122187593)
            ·
              refine ⟨26704400401066468591640695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35605867201421958122187593 26704400401066468591640695)
              ·
                refine ⟨40056600601599702887461043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26704400401066468591640695 40056600601599702887461043)
                ·
                  refine ⟨60084900902399554331191565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40056600601599702887461043 60084900902399554331191565)
                  ·
                    refine ⟨22531837838399832874196837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60084900902399554331191565 22531837838399832874196837)
                    ·
                      refine ⟨4224719594699968663911907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22531837838399832874196837 4224719594699968663911907)
                      ·
                        rfl

theorem cell23_8227612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 1, 1, 3, 4].length) (baseStart_8227612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8227612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8227612 prefixEnd_8227612 := by exact prefixLift 8227612
  have htrace : WordTrace (prefixWord ++ tailWord_8227612) baseStart_8227612 baseEnd_8227612 := by
    simpa [prefixWord, tailWord_8227612, baseEnd_8227612] using wordTrace_append hprefix tailTrace_8227612
  have hstable : (prefixWord ++ tailWord_8227612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8227612).length < 2 ^ (prefixWord ++ tailWord_8227612).sum := by decide
  have hdescent : baseEnd_8227612 < baseStart_8227612 := by decide
  rcases family_descends (prefixWord ++ tailWord_8227612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8227613 : List Nat := [1, 4, 2, 4, 1, 2, 1, 3, 5]
def baseStart_8227613 : Nat := 118140960795 + 8227613 * 2 ^ 59
def prefixEnd_8227613 : Nat := 4983230072969 + 3 ^ 40 * 8227613 * 2
def baseEnd_8227613 : Nat := 469413345353402573333267

theorem tailTrace_8227613 : CollatzResearch.WordTrace tailWord_8227613 prefixEnd_8227613 469413345353402573333267 := by
  unfold tailWord_8227613
  simp only [CollatzResearch.WordTrace]
  refine ⟨300085699141770740274655493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200057132761180493516436995 300085699141770740274655493)
  ·
    refine ⟨56266068589082013801497905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 300085699141770740274655493 56266068589082013801497905)
    ·
      refine ⟨42199551441811510351123429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56266068589082013801497905 42199551441811510351123429)
      ·
        refine ⟨7912415895339658190835643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42199551441811510351123429 7912415895339658190835643)
        ·
          refine ⟨11868623843009487286253465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7912415895339658190835643 11868623843009487286253465)
          ·
            refine ⟨8901467882257115464690099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11868623843009487286253465 8901467882257115464690099)
            ·
              refine ⟨13352201823385673197035149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8901467882257115464690099 13352201823385673197035149)
              ·
                refine ⟨5007075683769627448888181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13352201823385673197035149 5007075683769627448888181)
                ·
                  refine ⟨469413345353402573333267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5007075683769627448888181 469413345353402573333267)
                  ·
                    rfl

theorem cell23_8227613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 1, 3, 5].length) (baseStart_8227613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8227613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8227613 prefixEnd_8227613 := by exact prefixLift 8227613
  have htrace : WordTrace (prefixWord ++ tailWord_8227613) baseStart_8227613 baseEnd_8227613 := by
    simpa [prefixWord, tailWord_8227613, baseEnd_8227613] using wordTrace_append hprefix tailTrace_8227613
  have hstable : (prefixWord ++ tailWord_8227613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8227613).length < 2 ^ (prefixWord ++ tailWord_8227613).sum := by decide
  have hdescent : baseEnd_8227613 < baseStart_8227613 := by decide
  rcases family_descends (prefixWord ++ tailWord_8227613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8227625 : List Nat := [1, 2, 1, 1, 1, 1, 1, 4, 1, 6, 4]
def baseStart_8227625 : Nat := 118140960795 + 8227625 * 2 ^ 59
def prefixEnd_8227625 : Nat := 4983230072969 + 3 ^ 40 * 8227625 * 2
def baseEnd_8227625 : Nat := 4224726269948477113049347

theorem tailTrace_8227625 : CollatzResearch.WordTrace tailWord_8227625 prefixEnd_8227625 4224726269948477113049347 := by
  unfold tailWord_8227625
  simp only [CollatzResearch.WordTrace]
  refine ⟨300086136817727266324092329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200057424545151510882728219 300086136817727266324092329)
  ·
    refine ⟨225064602613295449743069247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300086136817727266324092329 225064602613295449743069247)
    ·
      refine ⟨337596903919943174614603871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225064602613295449743069247 337596903919943174614603871)
      ·
        refine ⟨506395355879914761921905807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337596903919943174614603871 506395355879914761921905807)
        ·
          refine ⟨759593033819872142882858711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 506395355879914761921905807 759593033819872142882858711)
          ·
            refine ⟨1139389550729808214324288067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 759593033819872142882858711 1139389550729808214324288067)
            ·
              refine ⟨1709084326094712321486432101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1139389550729808214324288067 1709084326094712321486432101)
              ·
                refine ⟨320453311142758560278706019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1709084326094712321486432101 320453311142758560278706019)
                ·
                  refine ⟨480679966714137840418059029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 320453311142758560278706019 480679966714137840418059029)
                  ·
                    refine ⟨22531873439725211269596517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 480679966714137840418059029 22531873439725211269596517)
                    ·
                      refine ⟨4224726269948477113049347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22531873439725211269596517 4224726269948477113049347)
                      ·
                        rfl

theorem cell23_8227625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 6, 4].length) (baseStart_8227625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8227625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8227625 prefixEnd_8227625 := by exact prefixLift 8227625
  have htrace : WordTrace (prefixWord ++ tailWord_8227625) baseStart_8227625 baseEnd_8227625 := by
    simpa [prefixWord, tailWord_8227625, baseEnd_8227625] using wordTrace_append hprefix tailTrace_8227625
  have hstable : (prefixWord ++ tailWord_8227625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8227625).length < 2 ^ (prefixWord ++ tailWord_8227625).sum := by decide
  have hdescent : baseEnd_8227625 < baseStart_8227625 := by decide
  rcases family_descends (prefixWord ++ tailWord_8227625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8227626 : List Nat := [3, 1, 4, 3, 1, 1, 1, 2, 2, 5]
def baseStart_8227626 : Nat := 118140960795 + 8227626 * 2 ^ 59
def prefixEnd_8227626 : Nat := 4983230072969 + 3 ^ 40 * 8227626 * 2
def baseEnd_8227626 : Nat := 1408242261143043869712281

theorem tailTrace_8227626 : CollatzResearch.WordTrace tailWord_8227626 prefixEnd_8227626 1408242261143043869712281 := by
  unfold tailWord_8227626
  simp only [CollatzResearch.WordTrace]
  refine ⟨75021543322680910873719683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200057448860482428996585821 75021543322680910873719683)
  ·
    refine ⟨112532314984021366310579525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75021543322680910873719683 112532314984021366310579525)
    ·
      refine ⟨21099809059504006183233661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112532314984021366310579525 21099809059504006183233661)
      ·
        refine ⟨7912428397314002318712623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21099809059504006183233661 7912428397314002318712623)
        ·
          refine ⟨11868642595971003478068935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7912428397314002318712623 11868642595971003478068935)
          ·
            refine ⟨17802963893956505217103403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11868642595971003478068935 17802963893956505217103403)
            ·
              refine ⟨26704445840934757825655105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17802963893956505217103403 26704445840934757825655105)
              ·
                refine ⟨20028334380701068369241329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26704445840934757825655105 20028334380701068369241329)
                ·
                  refine ⟨15021250785525801276930997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20028334380701068369241329 15021250785525801276930997)
                  ·
                    refine ⟨1408242261143043869712281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15021250785525801276930997 1408242261143043869712281)
                    ·
                      rfl

theorem cell23_8227626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 2, 2, 5].length) (baseStart_8227626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8227626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8227626 prefixEnd_8227626 := by exact prefixLift 8227626
  have htrace : WordTrace (prefixWord ++ tailWord_8227626) baseStart_8227626 baseEnd_8227626 := by
    simpa [prefixWord, tailWord_8227626, baseEnd_8227626] using wordTrace_append hprefix tailTrace_8227626
  have hstable : (prefixWord ++ tailWord_8227626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8227626).length < 2 ^ (prefixWord ++ tailWord_8227626).sum := by decide
  have hdescent : baseEnd_8227626 < baseStart_8227626 := by decide
  rcases family_descends (prefixWord ++ tailWord_8227626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8227662 : List Nat := [4, 1, 1, 1, 1, 1, 1, 3, 2, 5, 3]
def baseStart_8227662 : Nat := 118140960795 + 8227662 * 2 ^ 59
def prefixEnd_8227662 : Nat := 4983230072969 + 3 ^ 40 * 8227662 * 2
def baseEnd_8227662 : Nat := 4224745268732693468286677

theorem tailTrace_8227662 : CollatzResearch.WordTrace tailWord_8227662 prefixEnd_8227662 4224745268732693468286677 := by
  unfold tailWord_8227662
  simp only [CollatzResearch.WordTrace]
  refine ⟨37510935789824152705398655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200058324212395481095459493 37510935789824152705398655)
  ·
    refine ⟨56266403684736229058097983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37510935789824152705398655 56266403684736229058097983)
    ·
      refine ⟨84399605527104343587146975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56266403684736229058097983 84399605527104343587146975)
      ·
        refine ⟨126599408290656515380720463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84399605527104343587146975 126599408290656515380720463)
        ·
          refine ⟨189899112435984773071080695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126599408290656515380720463 189899112435984773071080695)
          ·
            refine ⟨284848668653977159606621043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189899112435984773071080695 284848668653977159606621043)
            ·
              refine ⟨427273002980965739409931565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 284848668653977159606621043 427273002980965739409931565)
              ·
                refine ⟨160227376117862152278724337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 427273002980965739409931565 160227376117862152278724337)
                ·
                  refine ⟨120170532088396614209043253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 160227376117862152278724337 120170532088396614209043253)
                  ·
                    refine ⟨11265987383287182582097805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 120170532088396614209043253 11265987383287182582097805)
                    ·
                      refine ⟨4224745268732693468286677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11265987383287182582097805 4224745268732693468286677)
                      ·
                        rfl

theorem cell23_8227662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 2, 5, 3].length) (baseStart_8227662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8227662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8227662 prefixEnd_8227662 := by exact prefixLift 8227662
  have htrace : WordTrace (prefixWord ++ tailWord_8227662) baseStart_8227662 baseEnd_8227662 := by
    simpa [prefixWord, tailWord_8227662, baseEnd_8227662] using wordTrace_append hprefix tailTrace_8227662
  have hstable : (prefixWord ++ tailWord_8227662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8227662).length < 2 ^ (prefixWord ++ tailWord_8227662).sum := by decide
  have hdescent : baseEnd_8227662 < baseStart_8227662 := by decide
  rcases family_descends (prefixWord ++ tailWord_8227662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8227719 : List Nat := [1, 1, 4, 2, 3, 1, 2, 1, 3, 1, 4]
def baseStart_8227719 : Nat := 118140960795 + 8227719 * 2 ^ 59
def prefixEnd_8227719 : Nat := 4983230072969 + 3 ^ 40 * 8227719 * 2
def baseEnd_8227719 : Nat := 4224774537129999745273915

theorem tailTrace_8227719 : CollatzResearch.WordTrace tailWord_8227719 prefixEnd_8227719 4224774537129999745273915 := by
  unfold tailWord_8227719
  simp only [CollatzResearch.WordTrace]
  refine ⟨300089565279386720378014211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200059710186257813585342807 300089565279386720378014211)
  ·
    refine ⟨450134347919080080567021317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300089565279386720378014211 450134347919080080567021317)
    ·
      refine ⟨84400190234827515106316497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 450134347919080080567021317 84400190234827515106316497)
      ·
        refine ⟨63300142676120636329737373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84400190234827515106316497 63300142676120636329737373)
        ·
          refine ⟨23737553503545238623651515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63300142676120636329737373 23737553503545238623651515)
          ·
            refine ⟨35606330255317857935477273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23737553503545238623651515 35606330255317857935477273)
            ·
              refine ⟨26704747691488393451607955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35606330255317857935477273 26704747691488393451607955)
              ·
                refine ⟨40057121537232590177411933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26704747691488393451607955 40057121537232590177411933)
                ·
                  refine ⟨15021420576462221316529475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40057121537232590177411933 15021420576462221316529475)
                  ·
                    refine ⟨22532130864693331974794213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15021420576462221316529475 22532130864693331974794213)
                    ·
                      refine ⟨4224774537129999745273915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22532130864693331974794213 4224774537129999745273915)
                      ·
                        rfl

theorem cell23_8227719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 1, 3, 1, 4].length) (baseStart_8227719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8227719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8227719 prefixEnd_8227719 := by exact prefixLift 8227719
  have htrace : WordTrace (prefixWord ++ tailWord_8227719) baseStart_8227719 baseEnd_8227719 := by
    simpa [prefixWord, tailWord_8227719, baseEnd_8227719] using wordTrace_append hprefix tailTrace_8227719
  have hstable : (prefixWord ++ tailWord_8227719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8227719).length < 2 ^ (prefixWord ++ tailWord_8227719).sum := by decide
  have hdescent : baseEnd_8227719 < baseStart_8227719 := by decide
  rcases family_descends (prefixWord ++ tailWord_8227719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8227746 : List Nat := [3, 3, 1, 2, 2, 2, 1, 1, 4, 4]
def baseStart_8227746 : Nat := 118140960795 + 8227746 * 2 ^ 59
def prefixEnd_8227746 : Nat := 4983230072969 + 3 ^ 40 * 8227746 * 2
def baseEnd_8227746 : Nat := 1408262800369223713212097

theorem tailTrace_8227746 : CollatzResearch.WordTrace tailWord_8227746 prefixEnd_8227746 1408262800369223713212097 := by
  unfold tailWord_8227746
  simp only [CollatzResearch.WordTrace]
  refine ⟨75022637512572225997311773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200060366700192602659498061 75022637512572225997311773)
  ·
    refine ⟨28133489067214584748991915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75022637512572225997311773 28133489067214584748991915)
    ·
      refine ⟨42200233600821877123487873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28133489067214584748991915 42200233600821877123487873)
      ·
        refine ⟨31650175200616407842615905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42200233600821877123487873 31650175200616407842615905)
        ·
          refine ⟨23737631400462305881961929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31650175200616407842615905 23737631400462305881961929)
          ·
            refine ⟨17803223550346729411471447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23737631400462305881961929 17803223550346729411471447)
            ·
              refine ⟨26704835325520094117207171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17803223550346729411471447 26704835325520094117207171)
              ·
                refine ⟨40057252988280141175810757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26704835325520094117207171 40057252988280141175810757)
                ·
                  refine ⟨7510734935302526470464517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40057252988280141175810757 7510734935302526470464517)
                  ·
                    refine ⟨1408262800369223713212097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7510734935302526470464517 1408262800369223713212097)
                    ·
                      rfl

theorem cell23_8227746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 1, 4, 4].length) (baseStart_8227746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8227746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8227746 prefixEnd_8227746 := by exact prefixLift 8227746
  have htrace : WordTrace (prefixWord ++ tailWord_8227746) baseStart_8227746 baseEnd_8227746 := by
    simpa [prefixWord, tailWord_8227746, baseEnd_8227746] using wordTrace_append hprefix tailTrace_8227746
  have hstable : (prefixWord ++ tailWord_8227746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8227746).length < 2 ^ (prefixWord ++ tailWord_8227746).sum := by decide
  have hdescent : baseEnd_8227746 < baseStart_8227746 := by decide
  rcases family_descends (prefixWord ++ tailWord_8227746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8227753 : List Nat := [1, 2, 1, 1, 1, 1, 5, 6, 1, 2, 2]
def baseStart_8227753 : Nat := 118140960795 + 8227753 * 2 ^ 59
def prefixEnd_8227753 : Nat := 4983230072969 + 3 ^ 40 * 8227753 * 2
def baseEnd_8227753 : Nat := 4224791995472252612248759

theorem tailTrace_8227753 : CollatzResearch.WordTrace tailWord_8227753 prefixEnd_8227753 4224791995472252612248759 := by
  unfold tailWord_8227753
  simp only [CollatzResearch.WordTrace]
  refine ⟨300090805361263544184751913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200060536907509029456501275 300090805361263544184751913)
  ·
    refine ⟨225068104020947658138563935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300090805361263544184751913 225068104020947658138563935)
    ·
      refine ⟨337602156031421487207845903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225068104020947658138563935 337602156031421487207845903)
      ·
        refine ⟨506403234047132230811768855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337602156031421487207845903 506403234047132230811768855)
        ·
          refine ⟨759604851070698346217653283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 506403234047132230811768855 759604851070698346217653283)
          ·
            refine ⟨1139407276606047519326479925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 759604851070698346217653283 1139407276606047519326479925)
            ·
              refine ⟨106819432181816954936857493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1139407276606047519326479925 106819432181816954936857493)
              ·
                refine ⟨5007160883522669762665195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 106819432181816954936857493 5007160883522669762665195)
                ·
                  refine ⟨7510741325284004643997793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5007160883522669762665195 7510741325284004643997793)
                  ·
                    refine ⟨5633055993963003482998345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7510741325284004643997793 5633055993963003482998345)
                    ·
                      refine ⟨4224791995472252612248759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5633055993963003482998345 4224791995472252612248759)
                      ·
                        rfl

theorem cell23_8227753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 6, 1, 2, 2].length) (baseStart_8227753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8227753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8227753 prefixEnd_8227753 := by exact prefixLift 8227753
  have htrace : WordTrace (prefixWord ++ tailWord_8227753) baseStart_8227753 baseEnd_8227753 := by
    simpa [prefixWord, tailWord_8227753, baseEnd_8227753] using wordTrace_append hprefix tailTrace_8227753
  have hstable : (prefixWord ++ tailWord_8227753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8227753).length < 2 ^ (prefixWord ++ tailWord_8227753).sum := by decide
  have hdescent : baseEnd_8227753 < baseStart_8227753 := by decide
  rcases family_descends (prefixWord ++ tailWord_8227753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8227773 : List Nat := [1, 4, 1, 2, 4, 1, 2, 2, 1, 2, 3]
def baseStart_8227773 : Nat := 118140960795 + 8227773 * 2 ^ 59
def prefixEnd_8227773 : Nat := 4983230072969 + 3 ^ 40 * 8227773 * 2
def baseEnd_8227773 : Nat := 4224802265085342533998667

theorem tailTrace_8227773 : CollatzResearch.WordTrace tailWord_8227773 prefixEnd_8227773 4224802265085342533998667 := by
  unfold tailWord_8227773
  simp only [CollatzResearch.WordTrace]
  refine ⟨300091534821191087600479973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200061023214127391733653315 300091534821191087600479973)
  ·
    refine ⟨56267162778973328925089995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 300091534821191087600479973 56267162778973328925089995)
    ·
      refine ⟨84400744168459993387634993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56267162778973328925089995 84400744168459993387634993)
      ·
        refine ⟨63300558126344995040726245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84400744168459993387634993 63300558126344995040726245)
        ·
          refine ⟨11868854648689686570136171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63300558126344995040726245 11868854648689686570136171)
          ·
            refine ⟨17803281973034529855204257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11868854648689686570136171 17803281973034529855204257)
            ·
              refine ⟨13352461479775897391403193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17803281973034529855204257 13352461479775897391403193)
              ·
                refine ⟨10014346109831923043552395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13352461479775897391403193 10014346109831923043552395)
                ·
                  refine ⟨15021519164747884565328593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10014346109831923043552395 15021519164747884565328593)
                  ·
                    refine ⟨11266139373560913423996445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15021519164747884565328593 11266139373560913423996445)
                    ·
                      refine ⟨4224802265085342533998667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11266139373560913423996445 4224802265085342533998667)
                      ·
                        rfl

theorem cell23_8227773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 2, 2, 1, 2, 3].length) (baseStart_8227773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8227773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8227773 prefixEnd_8227773 := by exact prefixLift 8227773
  have htrace : WordTrace (prefixWord ++ tailWord_8227773) baseStart_8227773 baseEnd_8227773 := by
    simpa [prefixWord, tailWord_8227773, baseEnd_8227773] using wordTrace_append hprefix tailTrace_8227773
  have hstable : (prefixWord ++ tailWord_8227773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8227773).length < 2 ^ (prefixWord ++ tailWord_8227773).sum := by decide
  have hdescent : baseEnd_8227773 < baseStart_8227773 := by decide
  rcases family_descends (prefixWord ++ tailWord_8227773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8227792 : List Nat := [2, 1, 1, 1, 1, 2, 3, 2, 1, 5, 4]
def baseStart_8227792 : Nat := 118140960795 + 8227792 * 2 ^ 59
def prefixEnd_8227792 : Nat := 4983230072969 + 3 ^ 40 * 8227792 * 2
def baseEnd_8227792 : Nat := 4224812021217777959661079

theorem tailTrace_8227792 : CollatzResearch.WordTrace tailWord_8227792 prefixEnd_8227792 4224812021217777959661079 := by
  unfold tailWord_8227792
  simp only [CollatzResearch.WordTrace]
  refine ⟨150046113904061126922710815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200061485205414835896947753 150046113904061126922710815)
  ·
    refine ⟨225069170856091690384066223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150046113904061126922710815 225069170856091690384066223)
    ·
      refine ⟨337603756284137535576099335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225069170856091690384066223 337603756284137535576099335)
      ·
        refine ⟨506405634426206303364149003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337603756284137535576099335 506405634426206303364149003)
        ·
          refine ⟨759608451639309455046223505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 506405634426206303364149003 759608451639309455046223505)
          ·
            refine ⟨569706338729482091284667629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 759608451639309455046223505 569706338729482091284667629)
            ·
              refine ⟨213639877023555784231750361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 569706338729482091284667629 213639877023555784231750361)
              ·
                refine ⟨160229907767666838173812771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 213639877023555784231750361 160229907767666838173812771)
                ·
                  refine ⟨240344861651500257260719157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 160229907767666838173812771 240344861651500257260719157)
                  ·
                    refine ⟨22532330779828149118192421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 240344861651500257260719157 22532330779828149118192421)
                    ·
                      refine ⟨4224812021217777959661079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22532330779828149118192421 4224812021217777959661079)
                      ·
                        rfl

theorem cell23_8227792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 1, 5, 4].length) (baseStart_8227792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8227792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8227792 prefixEnd_8227792 := by exact prefixLift 8227792
  have htrace : WordTrace (prefixWord ++ tailWord_8227792) baseStart_8227792 baseEnd_8227792 := by
    simpa [prefixWord, tailWord_8227792, baseEnd_8227792] using wordTrace_append hprefix tailTrace_8227792
  have hstable : (prefixWord ++ tailWord_8227792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8227792).length < 2 ^ (prefixWord ++ tailWord_8227792).sum := by decide
  have hdescent : baseEnd_8227792 < baseStart_8227792 := by decide
  rcases family_descends (prefixWord ++ tailWord_8227792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8227830 : List Nat := [5, 1, 1, 1, 3, 1, 3, 2, 1, 3, 2]
def baseStart_8227830 : Nat := 118140960795 + 8227830 * 2 ^ 59
def prefixEnd_8227830 : Nat := 4983230072969 + 3 ^ 40 * 8227830 * 2
def baseEnd_8227830 : Nat := 4224831533482648810985905

theorem tailTrace_8227830 : CollatzResearch.WordTrace tailWord_8227830 prefixEnd_8227830 4224831533482648810985905 := by
  unfold tailWord_8227830
  simp only [CollatzResearch.WordTrace]
  refine ⟨18755850861374036645956559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 200062409187989724223536629 18755850861374036645956559)
  ·
    refine ⟨28133776292061054968934839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18755850861374036645956559 28133776292061054968934839)
    ·
      refine ⟨42200664438091582453402259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28133776292061054968934839 42200664438091582453402259)
      ·
        refine ⟨63300996657137373680103389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42200664438091582453402259 63300996657137373680103389)
        ·
          refine ⟨23737873746426515130038771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63300996657137373680103389 23737873746426515130038771)
          ·
            refine ⟨35606810619639772695058157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23737873746426515130038771 35606810619639772695058157)
            ·
              refine ⟨13352553982364914760646809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35606810619639772695058157 13352553982364914760646809)
              ·
                refine ⟨10014415486773686070485107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13352553982364914760646809 10014415486773686070485107)
                ·
                  refine ⟨15021623230160529105727661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10014415486773686070485107 15021623230160529105727661)
                  ·
                    refine ⟨5633108711310198414647873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15021623230160529105727661 5633108711310198414647873)
                    ·
                      refine ⟨4224831533482648810985905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5633108711310198414647873 4224831533482648810985905)
                      ·
                        rfl

theorem cell23_8227830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 3, 2, 1, 3, 2].length) (baseStart_8227830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8227830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8227830 prefixEnd_8227830 := by exact prefixLift 8227830
  have htrace : WordTrace (prefixWord ++ tailWord_8227830) baseStart_8227830 baseEnd_8227830 := by
    simpa [prefixWord, tailWord_8227830, baseEnd_8227830] using wordTrace_append hprefix tailTrace_8227830
  have hstable : (prefixWord ++ tailWord_8227830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8227830).length < 2 ^ (prefixWord ++ tailWord_8227830).sum := by decide
  have hdescent : baseEnd_8227830 < baseStart_8227830 := by decide
  rcases family_descends (prefixWord ++ tailWord_8227830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8227832 : List Nat := [2, 1, 2, 1, 1, 3, 1, 3, 9]
def baseStart_8227832 : Nat := 118140960795 + 8227832 * 2 ^ 59
def prefixEnd_8227832 : Nat := 4983230072969 + 3 ^ 40 * 8227832 * 2
def baseEnd_8227832 : Nat := 469425840049328644795655

theorem tailTrace_8227832 : CollatzResearch.WordTrace tailWord_8227832 prefixEnd_8227832 469425840049328644795655 := by
  unfold tailWord_8227832
  simp only [CollatzResearch.WordTrace]
  refine ⟨150046843363988670338438875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200062457818651560451251833 150046843363988670338438875)
  ·
    refine ⟨225070265045983005507658313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150046843363988670338438875 225070265045983005507658313)
    ·
      refine ⟨168802698784487254130743735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225070265045983005507658313 168802698784487254130743735)
      ·
        refine ⟨253204048176730881196115603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168802698784487254130743735 253204048176730881196115603)
        ·
          refine ⟨379806072265096321794173405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253204048176730881196115603 379806072265096321794173405)
          ·
            refine ⟨142427277099411120672815027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 379806072265096321794173405 142427277099411120672815027)
            ·
              refine ⟨213640915649116681009222541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142427277099411120672815027 213640915649116681009222541)
              ·
                refine ⟨80115343368418755378458453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 213640915649116681009222541 80115343368418755378458453)
                ·
                  refine ⟨469425840049328644795655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 80115343368418755378458453 469425840049328644795655)
                  ·
                    rfl

theorem cell23_8227832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 3, 9].length) (baseStart_8227832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8227832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8227832 prefixEnd_8227832 := by exact prefixLift 8227832
  have htrace : WordTrace (prefixWord ++ tailWord_8227832) baseStart_8227832 baseEnd_8227832 := by
    simpa [prefixWord, tailWord_8227832, baseEnd_8227832] using wordTrace_append hprefix tailTrace_8227832
  have hstable : (prefixWord ++ tailWord_8227832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8227832).length < 2 ^ (prefixWord ++ tailWord_8227832).sum := by decide
  have hdescent : baseEnd_8227832 < baseStart_8227832 := by decide
  rcases family_descends (prefixWord ++ tailWord_8227832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8227859 : List Nat := [1, 1, 1, 2, 1, 4, 1, 4, 2, 3, 3]
def baseStart_8227859 : Nat := 118140960795 + 8227859 * 2 ^ 59
def prefixEnd_8227859 : Nat := 4983230072969 + 3 ^ 40 * 8227859 * 2
def baseEnd_8227859 : Nat := 4224846424421629197523271

theorem tailTrace_8227859 : CollatzResearch.WordTrace tailWord_8227859 prefixEnd_8227859 4224846424421629197523271 := by
  unfold tailWord_8227859
  simp only [CollatzResearch.WordTrace]
  refine ⟨300094671498879524288110631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200063114332586349525407087 300094671498879524288110631)
  ·
    refine ⟨450142007248319286432165947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300094671498879524288110631 450142007248319286432165947)
    ·
      refine ⟨675213010872478929648248921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 450142007248319286432165947 675213010872478929648248921)
      ·
        refine ⟨506409758154359197236186691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 675213010872478929648248921 506409758154359197236186691)
        ·
          refine ⟨759614637231538795854280037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 506409758154359197236186691 759614637231538795854280037)
          ·
            refine ⟨142427744480913524222677507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 759614637231538795854280037 142427744480913524222677507)
            ·
              refine ⟨213641616721370286334016261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142427744480913524222677507 213641616721370286334016261)
              ·
                refine ⟨40057803135256928687628049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 213641616721370286334016261 40057803135256928687628049)
                ·
                  refine ⟨30043352351442696515721037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40057803135256928687628049 30043352351442696515721037)
                  ·
                    refine ⟨11266257131791011193395389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30043352351442696515721037 11266257131791011193395389)
                    ·
                      refine ⟨4224846424421629197523271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11266257131791011193395389 4224846424421629197523271)
                      ·
                        rfl

theorem cell23_8227859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 4, 2, 3, 3].length) (baseStart_8227859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8227859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8227859 prefixEnd_8227859 := by exact prefixLift 8227859
  have htrace : WordTrace (prefixWord ++ tailWord_8227859) baseStart_8227859 baseEnd_8227859 := by
    simpa [prefixWord, tailWord_8227859, baseEnd_8227859] using wordTrace_append hprefix tailTrace_8227859
  have hstable : (prefixWord ++ tailWord_8227859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8227859).length < 2 ^ (prefixWord ++ tailWord_8227859).sum := by decide
  have hdescent : baseEnd_8227859 < baseStart_8227859 := by decide
  rcases family_descends (prefixWord ++ tailWord_8227859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8227866 : List Nat := [3, 1, 1, 3, 1, 2, 3, 4, 5]
def baseStart_8227866 : Nat := 118140960795 + 8227866 * 2 ^ 59
def prefixEnd_8227866 : Nat := 4983230072969 + 3 ^ 40 * 8227866 * 2
def baseEnd_8227866 : Nat := 469427779865134518903971

theorem tailTrace_8227866 : CollatzResearch.WordTrace tailWord_8227866 prefixEnd_8227866 469427779865134518903971 := by
  unfold tailWord_8227866
  simp only [CollatzResearch.WordTrace]
  refine ⟨75023731702463541120903863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200063284539902776322410301 75023731702463541120903863)
  ·
    refine ⟨112535597553695311681355795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75023731702463541120903863 112535597553695311681355795)
    ·
      refine ⟨168803396330542967522033693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112535597553695311681355795 168803396330542967522033693)
      ·
        refine ⟨63301273623953612820762635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168803396330542967522033693 63301273623953612820762635)
        ·
          refine ⟨94951910435930419231143953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63301273623953612820762635 94951910435930419231143953)
          ·
            refine ⟨71213932826947814423357965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94951910435930419231143953 71213932826947814423357965)
            ·
              refine ⟨26705224810105430408759237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71213932826947814423357965 26705224810105430408759237)
              ·
                refine ⟨5007229651894768201642357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26705224810105430408759237 5007229651894768201642357)
                ·
                  refine ⟨469427779865134518903971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5007229651894768201642357 469427779865134518903971)
                  ·
                    rfl

theorem cell23_8227866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 4, 5].length) (baseStart_8227866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8227866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8227866 prefixEnd_8227866 := by exact prefixLift 8227866
  have htrace : WordTrace (prefixWord ++ tailWord_8227866) baseStart_8227866 baseEnd_8227866 := by
    simpa [prefixWord, tailWord_8227866, baseEnd_8227866] using wordTrace_append hprefix tailTrace_8227866
  have hstable : (prefixWord ++ tailWord_8227866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8227866).length < 2 ^ (prefixWord ++ tailWord_8227866).sum := by decide
  have hdescent : baseEnd_8227866 < baseStart_8227866 := by decide
  rcases family_descends (prefixWord ++ tailWord_8227866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8227876 : List Nat := [2, 3, 1, 4, 1, 1, 1, 1, 1, 5, 3]
def baseStart_8227876 : Nat := 118140960795 + 8227876 * 2 ^ 59
def prefixEnd_8227876 : Nat := 4983230072969 + 3 ^ 40 * 8227876 * 2
def baseEnd_8227876 : Nat := 4224855153592755631010693

theorem tailTrace_8227876 : CollatzResearch.WordTrace tailWord_8227876 prefixEnd_8227876 4224855153592755631010693 := by
  unfold tailWord_8227876
  simp only [CollatzResearch.WordTrace]
  refine ⟨150047645769908968095739741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200063527693211957460986321 150047645769908968095739741)
  ·
    refine ⟨56267867163715863035902403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150047645769908968095739741 56267867163715863035902403)
    ·
      refine ⟨84401800745573794553853605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56267867163715863035902403 84401800745573794553853605)
      ·
        refine ⟨15825337639795086478847551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84401800745573794553853605 15825337639795086478847551)
        ·
          refine ⟨23738006459692629718271327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15825337639795086478847551 23738006459692629718271327)
          ·
            refine ⟨35607009689538944577406991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23738006459692629718271327 35607009689538944577406991)
            ·
              refine ⟨53410514534308416866110487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35607009689538944577406991 53410514534308416866110487)
              ·
                refine ⟨80115771801462625299165731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53410514534308416866110487 80115771801462625299165731)
                ·
                  refine ⟨120173657702193937948748597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80115771801462625299165731 120173657702193937948748597)
                  ·
                    refine ⟨11266280409580681682695181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 120173657702193937948748597 11266280409580681682695181)
                    ·
                      refine ⟨4224855153592755631010693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11266280409580681682695181 4224855153592755631010693)
                      ·
                        rfl

theorem cell23_8227876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_8227876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8227876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8227876 prefixEnd_8227876 := by exact prefixLift 8227876
  have htrace : WordTrace (prefixWord ++ tailWord_8227876) baseStart_8227876 baseEnd_8227876 := by
    simpa [prefixWord, tailWord_8227876, baseEnd_8227876] using wordTrace_append hprefix tailTrace_8227876
  have hstable : (prefixWord ++ tailWord_8227876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8227876).length < 2 ^ (prefixWord ++ tailWord_8227876).sum := by decide
  have hdescent : baseEnd_8227876 < baseStart_8227876 := by decide
  rcases family_descends (prefixWord ++ tailWord_8227876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8227896 : List Nat := [2, 1, 2, 1, 5, 1, 3, 1, 2, 5]
def baseStart_8227896 : Nat := 118140960795 + 8227896 * 2 ^ 59
def prefixEnd_8227896 : Nat := 4983230072969 + 3 ^ 40 * 8227896 * 2
def baseEnd_8227896 : Nat := 1408288474401948517586867

theorem tailTrace_8227896 : CollatzResearch.WordTrace tailWord_8227896 prefixEnd_8227896 1408288474401948517586867 := by
  unfold tailWord_8227896
  simp only [CollatzResearch.WordTrace]
  refine ⟨150048010499872739803603771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200064013999830319738138361 150048010499872739803603771)
  ·
    refine ⟨225072015749809109705405657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150048010499872739803603771 225072015749809109705405657)
    ·
      refine ⟨168804011812356832279054243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225072015749809109705405657 168804011812356832279054243)
      ·
        refine ⟨253206017718535248418581365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168804011812356832279054243 253206017718535248418581365)
        ·
          refine ⟨23738064161112679539242003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 253206017718535248418581365 23738064161112679539242003)
          ·
            refine ⟨35607096241669019308863005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23738064161112679539242003 35607096241669019308863005)
            ·
              refine ⟨13352661090625882240823627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35607096241669019308863005 13352661090625882240823627)
              ·
                refine ⟨20028991635938823361235441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13352661090625882240823627 20028991635938823361235441)
                ·
                  refine ⟨15021743726954117520926581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20028991635938823361235441 15021743726954117520926581)
                  ·
                    refine ⟨1408288474401948517586867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15021743726954117520926581 1408288474401948517586867)
                    ·
                      rfl

theorem cell23_8227896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 3, 1, 2, 5].length) (baseStart_8227896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8227896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8227896 prefixEnd_8227896 := by exact prefixLift 8227896
  have htrace : WordTrace (prefixWord ++ tailWord_8227896) baseStart_8227896 baseEnd_8227896 := by
    simpa [prefixWord, tailWord_8227896, baseEnd_8227896] using wordTrace_append hprefix tailTrace_8227896
  have hstable : (prefixWord ++ tailWord_8227896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8227896).length < 2 ^ (prefixWord ++ tailWord_8227896).sum := by decide
  have hdescent : baseEnd_8227896 < baseStart_8227896 := by decide
  rcases family_descends (prefixWord ++ tailWord_8227896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8227919 : List Nat := [1, 1, 2, 1, 1, 2, 2, 1, 5, 4, 3]
def baseStart_8227919 : Nat := 118140960795 + 8227919 * 2 ^ 59
def prefixEnd_8227919 : Nat := 4983230072969 + 3 ^ 40 * 8227919 * 2
def baseEnd_8227919 : Nat := 4224877233260898962772995

theorem tailTrace_8227919 : CollatzResearch.WordTrace tailWord_8227919 prefixEnd_8227919 4224877233260898962772995 := by
  unfold tailWord_8227919
  simp only [CollatzResearch.WordTrace]
  refine ⟨300096859878662154535294811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200064573252441436356863207 300096859878662154535294811)
  ·
    refine ⟨450145289817993231802942217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300096859878662154535294811 450145289817993231802942217)
    ·
      refine ⟨337608967363494923852206663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 450145289817993231802942217 337608967363494923852206663)
      ·
        refine ⟨506413451045242385778309995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337608967363494923852206663 506413451045242385778309995)
        ·
          refine ⟨759620176567863578667464993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 506413451045242385778309995 759620176567863578667464993)
          ·
            refine ⟨569715132425897684000598745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 759620176567863578667464993 569715132425897684000598745)
            ·
              refine ⟨427286349319423263000449059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 569715132425897684000598745 427286349319423263000449059)
              ·
                refine ⟨640929523979134894500673589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 427286349319423263000449059 640929523979134894500673589)
                ·
                  refine ⟨60087142873043896359438149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 640929523979134894500673589 60087142873043896359438149)
                  ·
                    refine ⟨11266339288695730567394653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60087142873043896359438149 11266339288695730567394653)
                    ·
                      refine ⟨4224877233260898962772995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11266339288695730567394653 4224877233260898962772995)
                      ·
                        rfl

theorem cell23_8227919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 5, 4, 3].length) (baseStart_8227919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8227919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8227919 prefixEnd_8227919 := by exact prefixLift 8227919
  have htrace : WordTrace (prefixWord ++ tailWord_8227919) baseStart_8227919 baseEnd_8227919 := by
    simpa [prefixWord, tailWord_8227919, baseEnd_8227919] using wordTrace_append hprefix tailTrace_8227919
  have hstable : (prefixWord ++ tailWord_8227919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8227919).length < 2 ^ (prefixWord ++ tailWord_8227919).sum := by decide
  have hdescent : baseEnd_8227919 < baseStart_8227919 := by decide
  rcases family_descends (prefixWord ++ tailWord_8227919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8228053 : List Nat := [1, 3, 2, 4, 1, 1, 1, 3, 1, 2, 4]
def baseStart_8228053 : Nat := 118140960795 + 8228053 * 2 ^ 59
def prefixEnd_8228053 : Nat := 4983230072969 + 3 ^ 40 * 8228053 * 2
def baseEnd_8228053 : Nat := 4224946039668601438497379

theorem tailTrace_8228053 : CollatzResearch.WordTrace tailWord_8228053 prefixEnd_8228053 4224946039668601438497379 := by
  unfold tailWord_8228053
  simp only [CollatzResearch.WordTrace]
  refine ⟨300101747260176695420672813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200067831506784463613781875 300101747260176695420672813)
  ·
    refine ⟨112538155222566260782752305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 300101747260176695420672813 112538155222566260782752305)
    ·
      refine ⟨84403616416924695587064229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112538155222566260782752305 84403616416924695587064229)
      ·
        refine ⟨15825678078173380422574543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84403616416924695587064229 15825678078173380422574543)
        ·
          refine ⟨23738517117260070633861815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15825678078173380422574543 23738517117260070633861815)
          ·
            refine ⟨35607775675890105950792723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23738517117260070633861815 35607775675890105950792723)
            ·
              refine ⟨53411663513835158926189085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35607775675890105950792723 53411663513835158926189085)
              ·
                refine ⟨20029373817688184597320907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53411663513835158926189085 20029373817688184597320907)
                ·
                  refine ⟨30044060726532276895981361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20029373817688184597320907 30044060726532276895981361)
                  ·
                    refine ⟨22533045544899207671986021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30044060726532276895981361 22533045544899207671986021)
                    ·
                      refine ⟨4224946039668601438497379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22533045544899207671986021 4224946039668601438497379)
                      ·
                        rfl

theorem cell23_8228053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_8228053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8228053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8228053 prefixEnd_8228053 := by exact prefixLift 8228053
  have htrace : WordTrace (prefixWord ++ tailWord_8228053) baseStart_8228053 baseEnd_8228053 := by
    simpa [prefixWord, tailWord_8228053, baseEnd_8228053] using wordTrace_append hprefix tailTrace_8228053
  have hstable : (prefixWord ++ tailWord_8228053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8228053).length < 2 ^ (prefixWord ++ tailWord_8228053).sum := by decide
  have hdescent : baseEnd_8228053 < baseStart_8228053 := by decide
  rcases family_descends (prefixWord ++ tailWord_8228053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8228059 : List Nat := [1, 1, 1, 1, 1, 1, 1, 4, 3, 9]
def baseStart_8228059 : Nat := 118140960795 + 8228059 * 2 ^ 59
def prefixEnd_8228059 : Nat := 4983230072969 + 3 ^ 40 * 8228059 * 2
def baseEnd_8228059 : Nat := 1408316373517509471674117

theorem tailTrace_8228059 : CollatzResearch.WordTrace tailWord_8228059 prefixEnd_8228059 1408316373517509471674117 := by
  unfold tailWord_8228059
  simp only [CollatzResearch.WordTrace]
  refine ⟨300101966098154958445391231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200067977398769972296927487 300101966098154958445391231)
  ·
    refine ⟨450152949147232437668086847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300101966098154958445391231 450152949147232437668086847)
    ·
      refine ⟨675229423720848656502130271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 450152949147232437668086847 675229423720848656502130271)
      ·
        refine ⟨1012844135581272984753195407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 675229423720848656502130271 1012844135581272984753195407)
        ·
          refine ⟨1519266203371909477129793111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1012844135581272984753195407 1519266203371909477129793111)
          ·
            refine ⟨2278899305057864215694689667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1519266203371909477129793111 2278899305057864215694689667)
            ·
              refine ⟨3418348957586796323542034501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2278899305057864215694689667 3418348957586796323542034501)
              ·
                refine ⟨640940429547524310664131469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3418348957586796323542034501 640940429547524310664131469)
                ·
                  refine ⟨240352661080321616499049301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 640940429547524310664131469 240352661080321616499049301)
                  ·
                    refine ⟨1408316373517509471674117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 240352661080321616499049301 1408316373517509471674117)
                    ·
                      rfl

theorem cell23_8228059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 9].length) (baseStart_8228059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8228059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8228059 prefixEnd_8228059 := by exact prefixLift 8228059
  have htrace : WordTrace (prefixWord ++ tailWord_8228059) baseStart_8228059 baseEnd_8228059 := by
    simpa [prefixWord, tailWord_8228059, baseEnd_8228059] using wordTrace_append hprefix tailTrace_8228059
  have hstable : (prefixWord ++ tailWord_8228059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8228059).length < 2 ^ (prefixWord ++ tailWord_8228059).sum := by decide
  have hdescent : baseEnd_8228059 < baseStart_8228059 := by decide
  rcases family_descends (prefixWord ++ tailWord_8228059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8228074 : List Nat := [3, 1, 3, 1, 1, 4, 2, 3, 1, 2, 2]
def baseStart_8228074 : Nat := 118140960795 + 8228074 * 2 ^ 59
def prefixEnd_8228074 : Nat := 4983230072969 + 3 ^ 40 * 8228074 * 2
def baseEnd_8228074 : Nat := 4224956822762345856334783

theorem tailTrace_8228074 : CollatzResearch.WordTrace tailWord_8228074 prefixEnd_8228074 4224956822762345856334783 := by
  unfold tailWord_8228074
  simp only [CollatzResearch.WordTrace]
  refine ⟨75025628298275154001796819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200068342128733744004791517 75025628298275154001796819)
  ·
    refine ⟨112538442447412731002695229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75025628298275154001796819 112538442447412731002695229)
    ·
      refine ⟨42201915917779774126010711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112538442447412731002695229 42201915917779774126010711)
      ·
        refine ⟨63302873876669661189016067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42201915917779774126010711 63302873876669661189016067)
        ·
          refine ⟨94954310815004491783524101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63302873876669661189016067 94954310815004491783524101)
          ·
            refine ⟨17803933277813342209410769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94954310815004491783524101 17803933277813342209410769)
            ·
              refine ⟨13352949958360006657058077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17803933277813342209410769 13352949958360006657058077)
              ·
                refine ⟨5007356234385002496396779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13352949958360006657058077 5007356234385002496396779)
                ·
                  refine ⟨7511034351577503744595169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5007356234385002496396779 7511034351577503744595169)
                  ·
                    refine ⟨5633275763683127808446377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7511034351577503744595169 5633275763683127808446377)
                    ·
                      refine ⟨4224956822762345856334783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5633275763683127808446377 4224956822762345856334783)
                      ·
                        rfl

theorem cell23_8228074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 2, 3, 1, 2, 2].length) (baseStart_8228074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8228074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8228074 prefixEnd_8228074 := by exact prefixLift 8228074
  have htrace : WordTrace (prefixWord ++ tailWord_8228074) baseStart_8228074 baseEnd_8228074 := by
    simpa [prefixWord, tailWord_8228074, baseEnd_8228074] using wordTrace_append hprefix tailTrace_8228074
  have hstable : (prefixWord ++ tailWord_8228074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8228074).length < 2 ^ (prefixWord ++ tailWord_8228074).sum := by decide
  have hdescent : baseEnd_8228074 < baseStart_8228074 := by decide
  rcases family_descends (prefixWord ++ tailWord_8228074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8228077 : List Nat := [1, 5, 1, 2, 2, 1, 4, 1, 1, 2, 3]
def baseStart_8228077 : Nat := 118140960795 + 8228077 * 2 ^ 59
def prefixEnd_8228077 : Nat := 4983230072969 + 3 ^ 40 * 8228077 * 2
def baseEnd_8228077 : Nat := 4224958363204309344597269

theorem tailTrace_8228077 : CollatzResearch.WordTrace tailWord_8228077 prefixEnd_8228077 4224958363204309344597269 := by
  unfold tailWord_8228077
  simp only [CollatzResearch.WordTrace]
  refine ⟨300102622612089747519546485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200068415074726498346364323 300102622612089747519546485)
  ·
    refine ⟨28134620869883413829957483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 300102622612089747519546485 28134620869883413829957483)
    ·
      refine ⟨42201931304825120744936225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28134620869883413829957483 42201931304825120744936225)
      ·
        refine ⟨31651448478618840558702169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42201931304825120744936225 31651448478618840558702169)
        ·
          refine ⟨23738586358964130419026627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31651448478618840558702169 23738586358964130419026627)
          ·
            refine ⟨35607879538446195628539941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23738586358964130419026627 35607879538446195628539941)
            ·
              refine ⟨6676477413458661680351239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35607879538446195628539941 6676477413458661680351239)
              ·
                refine ⟨10014716120187992520526859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6676477413458661680351239 10014716120187992520526859)
                ·
                  refine ⟨15022074180281988780790289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10014716120187992520526859 15022074180281988780790289)
                  ·
                    refine ⟨11266555635211491585592717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15022074180281988780790289 11266555635211491585592717)
                    ·
                      refine ⟨4224958363204309344597269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11266555635211491585592717 4224958363204309344597269)
                      ·
                        rfl

theorem cell23_8228077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 4, 1, 1, 2, 3].length) (baseStart_8228077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8228077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8228077 prefixEnd_8228077 := by exact prefixLift 8228077
  have htrace : WordTrace (prefixWord ++ tailWord_8228077) baseStart_8228077 baseEnd_8228077 := by
    simpa [prefixWord, tailWord_8228077, baseEnd_8228077] using wordTrace_append hprefix tailTrace_8228077
  have hstable : (prefixWord ++ tailWord_8228077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8228077).length < 2 ^ (prefixWord ++ tailWord_8228077).sum := by decide
  have hdescent : baseEnd_8228077 < baseStart_8228077 := by decide
  rcases family_descends (prefixWord ++ tailWord_8228077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8228084 : List Nat := [2, 6, 1, 2, 1, 1, 1, 1, 4, 4]
def baseStart_8228084 : Nat := 118140960795 + 8228084 * 2 ^ 59
def prefixEnd_8228084 : Nat := 4983230072969 + 3 ^ 40 * 8228084 * 2
def baseEnd_8228084 : Nat := 1408320652522963605736579

theorem tailTrace_8228084 : CollatzResearch.WordTrace tailWord_8228084 prefixEnd_8228084 1408320652522963605736579 := by
  unfold tailWord_8228084
  simp only [CollatzResearch.WordTrace]
  refine ⟨150051438961532193857525653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200068585282042925143367537 150051438961532193857525653)
  ·
    refine ⟨7033661201321821587071515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 150051438961532193857525653 7033661201321821587071515)
    ·
      refine ⟨10550491801982732380607273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7033661201321821587071515 10550491801982732380607273)
      ·
        refine ⟨7912868851487049285455455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10550491801982732380607273 7912868851487049285455455)
        ·
          refine ⟨11869303277230573928183183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7912868851487049285455455 11869303277230573928183183)
          ·
            refine ⟨17803954915845860892274775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11869303277230573928183183 17803954915845860892274775)
            ·
              refine ⟨26705932373768791338412163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17803954915845860892274775 26705932373768791338412163)
              ·
                refine ⟨40058898560653187007618245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26705932373768791338412163 40058898560653187007618245)
                ·
                  refine ⟨7511043480122472563928421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40058898560653187007618245 7511043480122472563928421)
                  ·
                    refine ⟨1408320652522963605736579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7511043480122472563928421 1408320652522963605736579)
                    ·
                      rfl

theorem cell23_8228084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_8228084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8228084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8228084 prefixEnd_8228084 := by exact prefixLift 8228084
  have htrace : WordTrace (prefixWord ++ tailWord_8228084) baseStart_8228084 baseEnd_8228084 := by
    simpa [prefixWord, tailWord_8228084, baseEnd_8228084] using wordTrace_append hprefix tailTrace_8228084
  have hstable : (prefixWord ++ tailWord_8228084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8228084).length < 2 ^ (prefixWord ++ tailWord_8228084).sum := by decide
  have hdescent : baseEnd_8228084 < baseStart_8228084 := by decide
  rcases family_descends (prefixWord ++ tailWord_8228084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8228107 : List Nat := [1, 1, 1, 1, 5, 4, 3, 1, 2, 1, 3]
def baseStart_8228107 : Nat := 118140960795 + 8228107 * 2 ^ 59
def prefixEnd_8228107 : Nat := 4983230072969 + 3 ^ 40 * 8228107 * 2
def baseEnd_8228107 : Nat := 4224973767623944227222131

theorem tailTrace_8228107 : CollatzResearch.WordTrace tailWord_8228107 prefixEnd_8228107 4224973767623944227222131 := by
  unfold tailWord_8228107
  simp only [CollatzResearch.WordTrace]
  refine ⟨300103716801981062643138575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200069144534654041762092383 300103716801981062643138575)
  ·
    refine ⟨450155575202971593964707863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300103716801981062643138575 450155575202971593964707863)
    ·
      refine ⟨675233362804457390947061795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 450155575202971593964707863 675233362804457390947061795)
      ·
        refine ⟨1012850044206686086420592693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 675233362804457390947061795 1012850044206686086420592693)
        ·
          refine ⟨94954691644376820601930565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1012850044206686086420592693 94954691644376820601930565)
          ·
            refine ⟨17804004683320653862861981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94954691644376820601930565 17804004683320653862861981)
            ·
              refine ⟨6676501756245245198573243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17804004683320653862861981 6676501756245245198573243)
              ·
                refine ⟨10014752634367867797859865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6676501756245245198573243 10014752634367867797859865)
                ·
                  refine ⟨7511064475775900848394899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10014752634367867797859865 7511064475775900848394899)
                  ·
                    refine ⟨11266596713663851272592349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7511064475775900848394899 11266596713663851272592349)
                    ·
                      refine ⟨4224973767623944227222131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11266596713663851272592349 4224973767623944227222131)
                      ·
                        rfl

theorem cell23_8228107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 3, 1, 2, 1, 3].length) (baseStart_8228107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8228107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8228107 prefixEnd_8228107 := by exact prefixLift 8228107
  have htrace : WordTrace (prefixWord ++ tailWord_8228107) baseStart_8228107 baseEnd_8228107 := by
    simpa [prefixWord, tailWord_8228107, baseEnd_8228107] using wordTrace_append hprefix tailTrace_8228107
  have hstable : (prefixWord ++ tailWord_8228107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8228107).length < 2 ^ (prefixWord ++ tailWord_8228107).sum := by decide
  have hdescent : baseEnd_8228107 < baseStart_8228107 := by decide
  rcases family_descends (prefixWord ++ tailWord_8228107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8228114 : List Nat := [3, 2, 4, 2, 2, 1, 2, 7]
def baseStart_8228114 : Nat := 118140960795 + 8228114 * 2 ^ 59
def prefixEnd_8228114 : Nat := 4983230072969 + 3 ^ 40 * 8228114 * 2
def baseEnd_8228114 : Nat := 156480643036612062956837

theorem tailTrace_8228114 : CollatzResearch.WordTrace tailWord_8228114 prefixEnd_8228114 156480643036612062956837 := by
  unfold tailWord_8228114
  simp only [CollatzResearch.WordTrace]
  refine ⟨75025993028238925709660849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200069314741970468559095597 75025993028238925709660849)
  ·
    refine ⟨56269494771179194282245637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75025993028238925709660849 56269494771179194282245637)
    ·
      refine ⟨10550530269596098927921057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56269494771179194282245637 10550530269596098927921057)
      ·
        refine ⟨7912897702197074195940793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10550530269596098927921057 7912897702197074195940793)
        ·
          refine ⟨5934673276647805646955595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7912897702197074195940793 5934673276647805646955595)
          ·
            refine ⟨8902009914971708470433393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5934673276647805646955595 8902009914971708470433393)
            ·
              refine ⟨6676507436228781352825045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8902009914971708470433393 6676507436228781352825045)
              ·
                refine ⟨156480643036612062956837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6676507436228781352825045 156480643036612062956837)
                ·
                  rfl

theorem cell23_8228114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 2, 7].length) (baseStart_8228114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8228114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8228114 prefixEnd_8228114 := by exact prefixLift 8228114
  have htrace : WordTrace (prefixWord ++ tailWord_8228114) baseStart_8228114 baseEnd_8228114 := by
    simpa [prefixWord, tailWord_8228114, baseEnd_8228114] using wordTrace_append hprefix tailTrace_8228114
  have hstable : (prefixWord ++ tailWord_8228114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8228114).length < 2 ^ (prefixWord ++ tailWord_8228114).sum := by decide
  have hdescent : baseEnd_8228114 < baseStart_8228114 := by decide
  rcases family_descends (prefixWord ++ tailWord_8228114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8228133 : List Nat := [1, 3, 1, 2, 4, 2, 1, 1, 2, 1, 5]
def baseStart_8228133 : Nat := 118140960795 + 8228133 * 2 ^ 59
def prefixEnd_8228133 : Nat := 4983230072969 + 3 ^ 40 * 8228133 * 2
def baseEnd_8228133 : Nat := 4224987118120961125497011

theorem tailTrace_8228133 : CollatzResearch.WordTrace tailWord_8228133 prefixEnd_8228133 4224987118120961125497011 := by
  unfold tailWord_8228133
  simp only [CollatzResearch.WordTrace]
  refine ⟨300104665099886869083585053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200069776733257912722390035 300104665099886869083585053)
  ·
    refine ⟨112539249412457575906344395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 300104665099886869083585053 112539249412457575906344395)
    ·
      refine ⟨168808874118686363859516593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112539249412457575906344395 168808874118686363859516593)
      ·
        refine ⟨126606655589014772894637445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168808874118686363859516593 126606655589014772894637445)
        ·
          refine ⟨23738747922940269917744521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 126606655589014772894637445 23738747922940269917744521)
          ·
            refine ⟨17804060942205202438308391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23738747922940269917744521 17804060942205202438308391)
            ·
              refine ⟨26706091413307803657462587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17804060942205202438308391 26706091413307803657462587)
              ·
                refine ⟨40059137119961705486193881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26706091413307803657462587 40059137119961705486193881)
                ·
                  refine ⟨30044352839971279114645411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40059137119961705486193881 30044352839971279114645411)
                  ·
                    refine ⟨45066529259956918671968117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30044352839971279114645411 45066529259956918671968117)
                    ·
                      refine ⟨4224987118120961125497011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45066529259956918671968117 4224987118120961125497011)
                      ·
                        rfl

theorem cell23_8228133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 1, 2, 1, 5].length) (baseStart_8228133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8228133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8228133 prefixEnd_8228133 := by exact prefixLift 8228133
  have htrace : WordTrace (prefixWord ++ tailWord_8228133) baseStart_8228133 baseEnd_8228133 := by
    simpa [prefixWord, tailWord_8228133, baseEnd_8228133] using wordTrace_append hprefix tailTrace_8228133
  have hstable : (prefixWord ++ tailWord_8228133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8228133).length < 2 ^ (prefixWord ++ tailWord_8228133).sum := by decide
  have hdescent : baseEnd_8228133 < baseStart_8228133 := by decide
  rcases family_descends (prefixWord ++ tailWord_8228133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8228176 : List Nat := [2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 7]
def baseStart_8228176 : Nat := 118140960795 + 8228176 * 2 ^ 59
def prefixEnd_8228176 : Nat := 4983230072969 + 3 ^ 40 * 8228176 * 2
def baseEnd_8228176 : Nat := 4225009197789104457259313

theorem tailTrace_8228176 : CollatzResearch.WordTrace tailWord_8228176 prefixEnd_8228176 4225009197789104457259313 := by
  unfold tailWord_8228176
  simp only [CollatzResearch.WordTrace]
  refine ⟨150053116719365543713700191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200070822292487391618266921 150053116719365543713700191)
  ·
    refine ⟨225079675079048315570550287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150053116719365543713700191 225079675079048315570550287)
    ·
      refine ⟨337619512618572473355825431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225079675079048315570550287 337619512618572473355825431)
      ·
        refine ⟨506429268927858710033738147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337619512618572473355825431 506429268927858710033738147)
        ·
          refine ⟨759643903391788065050607221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 506429268927858710033738147 759643903391788065050607221)
          ·
            refine ⟨71216615942980131098494427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 759643903391788065050607221 71216615942980131098494427)
            ·
              refine ⟨106824923914470196647741641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71216615942980131098494427 106824923914470196647741641)
              ·
                refine ⟨80118692935852647485806231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106824923914470196647741641 80118692935852647485806231)
                ·
                  refine ⟨120178039403778971228709347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80118692935852647485806231 120178039403778971228709347)
                  ·
                    refine ⟨180267059105668456843064021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 120178039403778971228709347 180267059105668456843064021)
                    ·
                      refine ⟨4225009197789104457259313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 180267059105668456843064021 4225009197789104457259313)
                      ·
                        rfl

theorem cell23_8228176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 7].length) (baseStart_8228176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8228176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8228176 prefixEnd_8228176 := by exact prefixLift 8228176
  have htrace : WordTrace (prefixWord ++ tailWord_8228176) baseStart_8228176 baseEnd_8228176 := by
    simpa [prefixWord, tailWord_8228176, baseEnd_8228176] using wordTrace_append hprefix tailTrace_8228176
  have hstable : (prefixWord ++ tailWord_8228176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8228176).length < 2 ^ (prefixWord ++ tailWord_8228176).sum := by decide
  have hdescent : baseEnd_8228176 < baseStart_8228176 := by decide
  rcases family_descends (prefixWord ++ tailWord_8228176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8228183 : List Nat := [1, 1, 3, 2, 3, 2, 1, 3, 2, 5]
def baseStart_8228183 : Nat := 118140960795 + 8228183 * 2 ^ 59
def prefixEnd_8228183 : Nat := 4983230072969 + 3 ^ 40 * 8228183 * 2
def baseEnd_8228183 : Nat := 1408337597384561976623927

theorem tailTrace_8228183 : CollatzResearch.WordTrace tailWord_8228183 prefixEnd_8228183 1408337597384561976623927 := by
  unfold tailWord_8228183
  simp only [CollatzResearch.WordTrace]
  refine ⟨300106488749705727622905203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200070992499803818415270135 300106488749705727622905203)
  ·
    refine ⟨450159733124558591434357805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300106488749705727622905203 450159733124558591434357805)
    ·
      refine ⟨168809899921709471787884177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 450159733124558591434357805 168809899921709471787884177)
      ·
        refine ⟨126607424941282103840913133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168809899921709471787884177 126607424941282103840913133)
        ·
          refine ⟨47477784352980788940342425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126607424941282103840913133 47477784352980788940342425)
          ·
            refine ⟨35608338264735591705256819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47477784352980788940342425 35608338264735591705256819)
            ·
              refine ⟨53412507397103387557885229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35608338264735591705256819 53412507397103387557885229)
              ·
                refine ⟨20029690273913770334206961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53412507397103387557885229 20029690273913770334206961)
                ·
                  refine ⟨15022267705435327750655221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20029690273913770334206961 15022267705435327750655221)
                  ·
                    refine ⟨1408337597384561976623927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15022267705435327750655221 1408337597384561976623927)
                    ·
                      rfl

theorem cell23_8228183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 3, 2, 5].length) (baseStart_8228183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8228183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8228183 prefixEnd_8228183 := by exact prefixLift 8228183
  have htrace : WordTrace (prefixWord ++ tailWord_8228183) baseStart_8228183 baseEnd_8228183 := by
    simpa [prefixWord, tailWord_8228183, baseEnd_8228183] using wordTrace_append hprefix tailTrace_8228183
  have hstable : (prefixWord ++ tailWord_8228183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8228183).length < 2 ^ (prefixWord ++ tailWord_8228183).sum := by decide
  have hdescent : baseEnd_8228183 < baseStart_8228183 := by decide
  rcases family_descends (prefixWord ++ tailWord_8228183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8228220 : List Nat := [2, 2, 2, 1, 1, 1, 5, 1, 2, 4, 2]
def baseStart_8228220 : Nat := 118140960795 + 8228220 * 2 ^ 59
def prefixEnd_8228220 : Nat := 4983230072969 + 3 ^ 40 * 8228220 * 2
def baseEnd_8228220 : Nat := 4225031790937902285109111

theorem tailTrace_8228220 : CollatzResearch.WordTrace tailWord_8228220 prefixEnd_8228220 4225031790937902285109111 := by
  unfold tailWord_8228220
  simp only [CollatzResearch.WordTrace]
  refine ⟨150053919125285841471001057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200071892167047788628001409 150053919125285841471001057)
  ·
    refine ⟨112540439343964381103250793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150053919125285841471001057 112540439343964381103250793)
    ·
      refine ⟨84405329507973285827438095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112540439343964381103250793 84405329507973285827438095)
      ·
        refine ⟨126607994261959928741157143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84405329507973285827438095 126607994261959928741157143)
        ·
          refine ⟨189911991392939893111735715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126607994261959928741157143 189911991392939893111735715)
          ·
            refine ⟨284867987089409839667603573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189911991392939893111735715 284867987089409839667603573)
            ·
              refine ⟨26706373789632172468837835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 284867987089409839667603573 26706373789632172468837835)
              ·
                refine ⟨40059560684448258703256753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26706373789632172468837835 40059560684448258703256753)
                ·
                  refine ⟨30044670513336194027442565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40059560684448258703256753 30044670513336194027442565)
                  ·
                    refine ⟨5633375721250536380145481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30044670513336194027442565 5633375721250536380145481)
                    ·
                      refine ⟨4225031790937902285109111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5633375721250536380145481 4225031790937902285109111)
                      ·
                        rfl

theorem cell23_8228220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 1, 2, 4, 2].length) (baseStart_8228220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8228220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8228220 prefixEnd_8228220 := by exact prefixLift 8228220
  have htrace : WordTrace (prefixWord ++ tailWord_8228220) baseStart_8228220 baseEnd_8228220 := by
    simpa [prefixWord, tailWord_8228220, baseEnd_8228220] using wordTrace_append hprefix tailTrace_8228220
  have hstable : (prefixWord ++ tailWord_8228220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8228220).length < 2 ^ (prefixWord ++ tailWord_8228220).sum := by decide
  have hdescent : baseEnd_8228220 < baseStart_8228220 := by decide
  rcases family_descends (prefixWord ++ tailWord_8228220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8228263 : List Nat := [1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 8]
def baseStart_8228263 : Nat := 118140960795 + 8228263 * 2 ^ 59
def prefixEnd_8228263 : Nat := 4983230072969 + 3 ^ 40 * 8228263 * 2
def baseEnd_8228263 : Nat := 4225053870606045616871413

theorem tailTrace_8228263 : CollatzResearch.WordTrace tailWord_8228263 prefixEnd_8228263 4225053870606045616871413 := by
  unfold tailWord_8228263
  simp only [CollatzResearch.WordTrace]
  refine ⟨300109406589415901285817443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200072937726277267523878295 300109406589415901285817443)
  ·
    refine ⟨450164109884123851928726165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300109406589415901285817443 450164109884123851928726165)
    ·
      refine ⟨21101442650818305559159039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 450164109884123851928726165 21101442650818305559159039)
      ·
        refine ⟨31652163976227458338738559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21101442650818305559159039 31652163976227458338738559)
        ·
          refine ⟨47478245964341187508107839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31652163976227458338738559 47478245964341187508107839)
          ·
            refine ⟨71217368946511781262161759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47478245964341187508107839 71217368946511781262161759)
            ·
              refine ⟨106826053419767671893242639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71217368946511781262161759 106826053419767671893242639)
              ·
                refine ⟨160239080129651507839863959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106826053419767671893242639 160239080129651507839863959)
                ·
                  refine ⟨240358620194477261759795939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 160239080129651507839863959 240358620194477261759795939)
                  ·
                    refine ⟨360537930291715892639693909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 240358620194477261759795939 360537930291715892639693909)
                    ·
                      refine ⟨4225053870606045616871413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 360537930291715892639693909 4225053870606045616871413)
                      ·
                        rfl

theorem cell23_8228263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_8228263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8228263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8228263 prefixEnd_8228263 := by exact prefixLift 8228263
  have htrace : WordTrace (prefixWord ++ tailWord_8228263) baseStart_8228263 baseEnd_8228263 := by
    simpa [prefixWord, tailWord_8228263, baseEnd_8228263] using wordTrace_append hprefix tailTrace_8228263
  have hstable : (prefixWord ++ tailWord_8228263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8228263).length < 2 ^ (prefixWord ++ tailWord_8228263).sum := by decide
  have hdescent : baseEnd_8228263 < baseStart_8228263 := by decide
  rcases family_descends (prefixWord ++ tailWord_8228263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8228264 : List Nat := [2, 1, 6, 1, 2, 1, 2, 1, 3, 4]
def baseStart_8228264 : Nat := 118140960795 + 8228264 * 2 ^ 59
def prefixEnd_8228264 : Nat := 4983230072969 + 3 ^ 40 * 8228264 * 2
def baseEnd_8228264 : Nat := 1408351461362233370986303

theorem tailTrace_8228264 : CollatzResearch.WordTrace tailWord_8228264 prefixEnd_8228264 1408351461362233370986303 := by
  unfold tailWord_8228264
  simp only [CollatzResearch.WordTrace]
  refine ⟨150054721531206139228301923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200072962041608185637735897 150054721531206139228301923)
  ·
    refine ⟨225082082296809208842452885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150054721531206139228301923 225082082296809208842452885)
    ·
      refine ⟨10550722607662931664489979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 225082082296809208842452885 10550722607662931664489979)
      ·
        refine ⟨15826083911494397496734969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10550722607662931664489979 15826083911494397496734969)
        ·
          refine ⟨11869562933620798122551227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15826083911494397496734969 11869562933620798122551227)
          ·
            refine ⟨17804344400431197183826841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11869562933620798122551227 17804344400431197183826841)
            ·
              refine ⟨13353258300323397887870131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17804344400431197183826841 13353258300323397887870131)
              ·
                refine ⟨20029887450485096831805197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13353258300323397887870131 20029887450485096831805197)
                ·
                  refine ⟨7511207793931911311926949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20029887450485096831805197 7511207793931911311926949)
                  ·
                    refine ⟨1408351461362233370986303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7511207793931911311926949 1408351461362233370986303)
                    ·
                      rfl

theorem cell23_8228264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_8228264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8228264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8228264 prefixEnd_8228264 := by exact prefixLift 8228264
  have htrace : WordTrace (prefixWord ++ tailWord_8228264) baseStart_8228264 baseEnd_8228264 := by
    simpa [prefixWord, tailWord_8228264, baseEnd_8228264] using wordTrace_append hprefix tailTrace_8228264
  have hstable : (prefixWord ++ tailWord_8228264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8228264).length < 2 ^ (prefixWord ++ tailWord_8228264).sum := by decide
  have hdescent : baseEnd_8228264 < baseStart_8228264 := by decide
  rcases family_descends (prefixWord ++ tailWord_8228264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8228277 : List Nat := [1, 3, 3, 2, 2, 2, 3, 1, 6]
def baseStart_8228277 : Nat := 118140960795 + 8228277 * 2 ^ 59
def prefixEnd_8228277 : Nat := 4983230072969 + 3 ^ 40 * 8228277 * 2
def baseEnd_8228277 : Nat := 469451228815023173566261

theorem tailTrace_8228277 : CollatzResearch.WordTrace tailWord_8228277 prefixEnd_8228277 469451228815023173566261 := by
  unfold tailWord_8228277
  simp only [CollatzResearch.WordTrace]
  refine ⟨300109917211365181676827085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200073278140910121117884723 300109917211365181676827085)
  ·
    refine ⟨112541218954261943128810157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 300109917211365181676827085 112541218954261943128810157)
    ·
      refine ⟨42202957107848228673303809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112541218954261943128810157 42202957107848228673303809)
      ·
        refine ⟨31652217830886171504977857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42202957107848228673303809 31652217830886171504977857)
        ·
          refine ⟨23739163373164628628733393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31652217830886171504977857 23739163373164628628733393)
          ·
            refine ⟨17804372529873471471550045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23739163373164628628733393 17804372529873471471550045)
            ·
              refine ⟨6676639698702551801831267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17804372529873471471550045 6676639698702551801831267)
              ·
                refine ⟨10014959548053827702746901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6676639698702551801831267 10014959548053827702746901)
                ·
                  refine ⟨469451228815023173566261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10014959548053827702746901 469451228815023173566261)
                  ·
                    rfl

theorem cell23_8228277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 3, 1, 6].length) (baseStart_8228277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8228277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8228277 prefixEnd_8228277 := by exact prefixLift 8228277
  have htrace : WordTrace (prefixWord ++ tailWord_8228277) baseStart_8228277 baseEnd_8228277 := by
    simpa [prefixWord, tailWord_8228277, baseEnd_8228277] using wordTrace_append hprefix tailTrace_8228277
  have hstable : (prefixWord ++ tailWord_8228277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8228277).length < 2 ^ (prefixWord ++ tailWord_8228277).sum := by decide
  have hdescent : baseEnd_8228277 < baseStart_8228277 := by decide
  rcases family_descends (prefixWord ++ tailWord_8228277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8228280 : List Nat := [2, 1, 2, 1, 2, 2, 3, 2, 1, 5, 2]
def baseStart_8228280 : Nat := 118140960795 + 8228280 * 2 ^ 59
def prefixEnd_8228280 : Nat := 4983230072969 + 3 ^ 40 * 8228280 * 2
def baseEnd_8228280 : Nat := 4225062599777172050358835

theorem tailTrace_8228280 : CollatzResearch.WordTrace tailWord_8228280 prefixEnd_8228280 4225062599777172050358835 := by
  unfold tailWord_8228280
  simp only [CollatzResearch.WordTrace]
  refine ⟨150055013315177156594593147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200073351086902875459457529 150055013315177156594593147)
  ·
    refine ⟨225082519972765734891889721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150055013315177156594593147 225082519972765734891889721)
    ·
      refine ⟨168811889979574301168917291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225082519972765734891889721 168811889979574301168917291)
      ·
        refine ⟨253217834969361451753375937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168811889979574301168917291 253217834969361451753375937)
        ·
          refine ⟨189913376227021088815031953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 253217834969361451753375937 189913376227021088815031953)
          ·
            refine ⟨142435032170265816611273965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189913376227021088815031953 142435032170265816611273965)
            ·
              refine ⟨53413137063849681229227737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142435032170265816611273965 53413137063849681229227737)
              ·
                refine ⟨40059852797887260921920803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53413137063849681229227737 40059852797887260921920803)
                ·
                  refine ⟨60089779196830891382881205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40059852797887260921920803 60089779196830891382881205)
                  ·
                    refine ⟨5633416799702896067145113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60089779196830891382881205 5633416799702896067145113)
                    ·
                      refine ⟨4225062599777172050358835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5633416799702896067145113 4225062599777172050358835)
                      ·
                        rfl

theorem cell23_8228280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 2, 1, 5, 2].length) (baseStart_8228280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8228280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8228280 prefixEnd_8228280 := by exact prefixLift 8228280
  have htrace : WordTrace (prefixWord ++ tailWord_8228280) baseStart_8228280 baseEnd_8228280 := by
    simpa [prefixWord, tailWord_8228280, baseEnd_8228280] using wordTrace_append hprefix tailTrace_8228280
  have hstable : (prefixWord ++ tailWord_8228280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8228280).length < 2 ^ (prefixWord ++ tailWord_8228280).sum := by decide
  have hdescent : baseEnd_8228280 < baseStart_8228280 := by decide
  rcases family_descends (prefixWord ++ tailWord_8228280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8228303 : List Nat := [1, 1, 2, 1, 1, 4, 2, 4, 1, 6]
def baseStart_8228303 : Nat := 118140960795 + 8228303 * 2 ^ 59
def prefixEnd_8228303 : Nat := 4983230072969 + 3 ^ 40 * 8228303 * 2
def baseEnd_8228303 : Nat := 1408358136610741820123743

theorem tailTrace_8228303 : CollatzResearch.WordTrace tailWord_8228303 prefixEnd_8228303 1408358136610741820123743 := by
  unfold tailWord_8228303
  simp only [CollatzResearch.WordTrace]
  refine ⟨300110865509270988117273563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200073910339513992078182375 300110865509270988117273563)
  ·
    refine ⟨450166298263906482175910345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300110865509270988117273563 450166298263906482175910345)
    ·
      refine ⟨337624723697929861631932759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 450166298263906482175910345 337624723697929861631932759)
      ·
        refine ⟨506437085546894792447899139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337624723697929861631932759 506437085546894792447899139)
        ·
          refine ⟨759655628320342188671848709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 506437085546894792447899139 759655628320342188671848709)
          ·
            refine ⟨142435430310064160375971633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 759655628320342188671848709 142435430310064160375971633)
            ·
              refine ⟨106826572732548120281978725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142435430310064160375971633 106826572732548120281978725)
              ·
                refine ⟨20029982387352772552871011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106826572732548120281978725 20029982387352772552871011)
                ·
                  refine ⟨30044973581029158829306517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20029982387352772552871011 30044973581029158829306517)
                  ·
                    refine ⟨1408358136610741820123743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30044973581029158829306517 1408358136610741820123743)
                    ·
                      rfl

theorem cell23_8228303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 4, 1, 6].length) (baseStart_8228303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8228303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8228303 prefixEnd_8228303 := by exact prefixLift 8228303
  have htrace : WordTrace (prefixWord ++ tailWord_8228303) baseStart_8228303 baseEnd_8228303 := by
    simpa [prefixWord, tailWord_8228303, baseEnd_8228303] using wordTrace_append hprefix tailTrace_8228303
  have hstable : (prefixWord ++ tailWord_8228303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8228303).length < 2 ^ (prefixWord ++ tailWord_8228303).sum := by decide
  have hdescent : baseEnd_8228303 < baseStart_8228303 := by decide
  rcases family_descends (prefixWord ++ tailWord_8228303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8228321 : List Nat := [1, 2, 3, 1, 2, 4, 3, 2, 1, 1, 3]
def baseStart_8228321 : Nat := 118140960795 + 8228321 * 2 ^ 59
def prefixEnd_8228321 : Nat := 4983230072969 + 3 ^ 40 * 8228321 * 2
def baseEnd_8228321 : Nat := 4225083652484006389946147

theorem tailTrace_8228321 : CollatzResearch.WordTrace tailWord_8228321 prefixEnd_8228321 4225083652484006389946147 := by
  unfold tailWord_8228321
  simp only [CollatzResearch.WordTrace]
  refine ⟨300111522023205777191428817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200074348015470518127619211 300111522023205777191428817)
  ·
    refine ⟨225083641517404332893571613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300111522023205777191428817 225083641517404332893571613)
    ·
      refine ⟨84406365569026624835089355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225083641517404332893571613 84406365569026624835089355)
      ·
        refine ⟨126609548353539937252634033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84406365569026624835089355 126609548353539937252634033)
        ·
          refine ⟨94957161265154952939475525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126609548353539937252634033 94957161265154952939475525)
          ·
            refine ⟨17804467737216553676151661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94957161265154952939475525 17804467737216553676151661)
            ·
              refine ⟨6676675401456207628556873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17804467737216553676151661 6676675401456207628556873)
              ·
                refine ⟨5007506551092155721417655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6676675401456207628556873 5007506551092155721417655)
                ·
                  refine ⟨7511259826638233582126483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5007506551092155721417655 7511259826638233582126483)
                  ·
                    refine ⟨11266889739957350373189725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7511259826638233582126483 11266889739957350373189725)
                    ·
                      refine ⟨4225083652484006389946147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11266889739957350373189725 4225083652484006389946147)
                      ·
                        rfl

theorem cell23_8228321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 3, 2, 1, 1, 3].length) (baseStart_8228321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8228321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8228321 prefixEnd_8228321 := by exact prefixLift 8228321
  have htrace : WordTrace (prefixWord ++ tailWord_8228321) baseStart_8228321 baseEnd_8228321 := by
    simpa [prefixWord, tailWord_8228321, baseEnd_8228321] using wordTrace_append hprefix tailTrace_8228321
  have hstable : (prefixWord ++ tailWord_8228321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8228321).length < 2 ^ (prefixWord ++ tailWord_8228321).sum := by decide
  have hdescent : baseEnd_8228321 < baseStart_8228321 := by decide
  rcases family_descends (prefixWord ++ tailWord_8228321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8228337 : List Nat := [1, 2, 2, 2, 3, 3, 1, 3, 2, 4]
def baseStart_8228337 : Nat := 118140960795 + 8228337 * 2 ^ 59
def prefixEnd_8228337 : Nat := 4983230072969 + 3 ^ 40 * 8228337 * 2
def baseEnd_8228337 : Nat := 1408363956058159442448691

theorem tailTrace_8228337 : CollatzResearch.WordTrace tailWord_8228337 prefixEnd_8228337 1408363956058159442448691 := by
  unfold tailWord_8228337
  simp only [CollatzResearch.WordTrace]
  refine ⟨300112105591147811924011265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200074737060765207949340843 300112105591147811924011265)
  ·
    refine ⟨225084079193360858943008449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300112105591147811924011265 225084079193360858943008449)
    ·
      refine ⟨168813059395020644207256337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225084079193360858943008449 168813059395020644207256337)
      ·
        refine ⟨126609794546265483155442253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168813059395020644207256337 126609794546265483155442253)
        ·
          refine ⟨47478672954849556183290845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126609794546265483155442253 47478672954849556183290845)
          ·
            refine ⟨17804502358068583568734067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47478672954849556183290845 17804502358068583568734067)
            ·
              refine ⟨26706753537102875353101101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17804502358068583568734067 26706753537102875353101101)
              ·
                refine ⟨10015032576413578257412913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26706753537102875353101101 10015032576413578257412913)
                ·
                  refine ⟨7511274432310183693059685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10015032576413578257412913 7511274432310183693059685)
                  ·
                    refine ⟨1408363956058159442448691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7511274432310183693059685 1408363956058159442448691)
                    ·
                      rfl

theorem cell23_8228337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 3, 2, 4].length) (baseStart_8228337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8228337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8228337 prefixEnd_8228337 := by exact prefixLift 8228337
  have htrace : WordTrace (prefixWord ++ tailWord_8228337) baseStart_8228337 baseEnd_8228337 := by
    simpa [prefixWord, tailWord_8228337, baseEnd_8228337] using wordTrace_append hprefix tailTrace_8228337
  have hstable : (prefixWord ++ tailWord_8228337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8228337).length < 2 ^ (prefixWord ++ tailWord_8228337).sum := by decide
  have hdescent : baseEnd_8228337 < baseStart_8228337 := by decide
  rcases family_descends (prefixWord ++ tailWord_8228337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8228360 : List Nat := [2, 1, 3, 2, 1, 1, 3, 1, 3, 3, 3]
def baseStart_8228360 : Nat := 118140960795 + 8228360 * 2 ^ 59
def prefixEnd_8228360 : Nat := 4983230072969 + 3 ^ 40 * 8228360 * 2
def baseEnd_8228360 : Nat := 4225103678229531737358467

theorem tailTrace_8228360 : CollatzResearch.WordTrace tailWord_8228360 prefixEnd_8228360 4225103678229531737358467 := by
  unfold tailWord_8228360
  simp only [CollatzResearch.WordTrace]
  refine ⟨150056472235032243426049267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200075296313376324568065689 150056472235032243426049267)
  ·
    refine ⟨225084708352548365139073901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150056472235032243426049267 225084708352548365139073901)
    ·
      refine ⟨84406765632205636927152713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225084708352548365139073901 84406765632205636927152713)
      ·
        refine ⟨63305074224154227695364535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84406765632205636927152713 63305074224154227695364535)
        ·
          refine ⟨94957611336231341543046803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63305074224154227695364535 94957611336231341543046803)
          ·
            refine ⟨142436417004347012314570205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94957611336231341543046803 142436417004347012314570205)
            ·
              refine ⟨53413656376630129617963827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142436417004347012314570205 53413656376630129617963827)
              ·
                refine ⟨80120484564945194426945741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53413656376630129617963827 80120484564945194426945741)
                ·
                  refine ⟨30045181711854447910104653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80120484564945194426945741 30045181711854447910104653)
                  ·
                    refine ⟨11266943141945417966289245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30045181711854447910104653 11266943141945417966289245)
                    ·
                      refine ⟨4225103678229531737358467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11266943141945417966289245 4225103678229531737358467)
                      ·
                        rfl

theorem cell23_8228360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 1, 3, 3, 3].length) (baseStart_8228360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8228360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8228360 prefixEnd_8228360 := by exact prefixLift 8228360
  have htrace : WordTrace (prefixWord ++ tailWord_8228360) baseStart_8228360 baseEnd_8228360 := by
    simpa [prefixWord, tailWord_8228360, baseEnd_8228360] using wordTrace_append hprefix tailTrace_8228360
  have hstable : (prefixWord ++ tailWord_8228360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8228360).length < 2 ^ (prefixWord ++ tailWord_8228360).sum := by decide
  have hdescent : baseEnd_8228360 < baseStart_8228360 := by decide
  rcases family_descends (prefixWord ++ tailWord_8228360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8228364 : List Nat := [2, 2, 1, 2, 6, 1, 1, 1, 1, 1, 5]
def baseStart_8228364 : Nat := 118140960795 + 8228364 * 2 ^ 59
def prefixEnd_8228364 : Nat := 4983230072969 + 3 ^ 40 * 8228364 * 2
def baseEnd_8228364 : Nat := 4225105732152149721708449

theorem tailTrace_8228364 : CollatzResearch.WordTrace tailWord_8228364 prefixEnd_8228364 4225105732152149721708449 := by
  unfold tailWord_8228364
  simp only [CollatzResearch.WordTrace]
  refine ⟨150056545181024997767622073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200075393574699997023496097 150056545181024997767622073)
  ·
    refine ⟨112542408885768748325716555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150056545181024997767622073 112542408885768748325716555)
    ·
      refine ⟨168813613328653122488574833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112542408885768748325716555 168813613328653122488574833)
      ·
        refine ⟨126610209996489841866431125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168813613328653122488574833 126610209996489841866431125)
        ·
          refine ⟨5934853593585461337488959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 126610209996489841866431125 5934853593585461337488959)
          ·
            refine ⟨8902280390378192006233439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5934853593585461337488959 8902280390378192006233439)
            ·
              refine ⟨13353420585567288009350159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8902280390378192006233439 13353420585567288009350159)
              ·
                refine ⟨20030130878350932014025239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13353420585567288009350159 20030130878350932014025239)
                ·
                  refine ⟨30045196317526398021037859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20030130878350932014025239 30045196317526398021037859)
                  ·
                    refine ⟨45067794476289597031556789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30045196317526398021037859 45067794476289597031556789)
                    ·
                      refine ⟨4225105732152149721708449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45067794476289597031556789 4225105732152149721708449)
                      ·
                        rfl

theorem cell23_8228364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 1, 1, 1, 1, 5].length) (baseStart_8228364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8228364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8228364 prefixEnd_8228364 := by exact prefixLift 8228364
  have htrace : WordTrace (prefixWord ++ tailWord_8228364) baseStart_8228364 baseEnd_8228364 := by
    simpa [prefixWord, tailWord_8228364, baseEnd_8228364] using wordTrace_append hprefix tailTrace_8228364
  have hstable : (prefixWord ++ tailWord_8228364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8228364).length < 2 ^ (prefixWord ++ tailWord_8228364).sum := by decide
  have hdescent : baseEnd_8228364 < baseStart_8228364 := by decide
  rcases family_descends (prefixWord ++ tailWord_8228364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8228372 : List Nat := [2, 4, 3, 1, 3, 1, 2, 2, 1, 1, 3]
def baseStart_8228372 : Nat := 118140960795 + 8228372 * 2 ^ 59
def prefixEnd_8228372 : Nat := 4983230072969 + 3 ^ 40 * 8228372 * 2
def baseEnd_8228372 : Nat := 4225109839997385690408413

theorem tailTrace_8228372 : CollatzResearch.WordTrace tailWord_8228372 prefixEnd_8228372 4225109839997385690408413 := by
  unfold tailWord_8228372
  simp only [CollatzResearch.WordTrace]
  refine ⟨150056691073010506450767685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200075588097347341934356913 150056691073010506450767685)
  ·
    refine ⟨28135629576189469959518941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150056691073010506450767685 28135629576189469959518941)
    ·
      refine ⟨10550861091071051234819603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28135629576189469959518941 10550861091071051234819603)
      ·
        refine ⟨15826291636606576852229405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10550861091071051234819603 15826291636606576852229405)
        ·
          refine ⟨5934859363727466319586027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15826291636606576852229405 5934859363727466319586027)
          ·
            refine ⟨8902289045591199479379041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5934859363727466319586027 8902289045591199479379041)
            ·
              refine ⟨6676716784193399609534281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8902289045591199479379041 6676716784193399609534281)
              ·
                refine ⟨5007537588145049707150711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6676716784193399609534281 5007537588145049707150711)
                ·
                  refine ⟨7511306382217574560726067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5007537588145049707150711 7511306382217574560726067)
                  ·
                    refine ⟨11266959573326361841089101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7511306382217574560726067 11266959573326361841089101)
                    ·
                      refine ⟨4225109839997385690408413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11266959573326361841089101 4225109839997385690408413)
                      ·
                        rfl

theorem cell23_8228372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 2, 2, 1, 1, 3].length) (baseStart_8228372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8228372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8228372 prefixEnd_8228372 := by exact prefixLift 8228372
  have htrace : WordTrace (prefixWord ++ tailWord_8228372) baseStart_8228372 baseEnd_8228372 := by
    simpa [prefixWord, tailWord_8228372, baseEnd_8228372] using wordTrace_append hprefix tailTrace_8228372
  have hstable : (prefixWord ++ tailWord_8228372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8228372).length < 2 ^ (prefixWord ++ tailWord_8228372).sum := by decide
  have hdescent : baseEnd_8228372 < baseStart_8228372 := by decide
  rcases family_descends (prefixWord ++ tailWord_8228372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8228394 : List Nat := [3, 1, 4, 1, 1, 1, 1, 5, 2, 1, 3]
def baseStart_8228394 : Nat := 118140960795 + 8228394 * 2 ^ 59
def prefixEnd_8228394 : Nat := 4983230072969 + 3 ^ 40 * 8228394 * 2
def baseEnd_8228394 : Nat := 4225121136571784604333311

theorem tailTrace_8228394 : CollatzResearch.WordTrace tailWord_8228394 prefixEnd_8228394 4225121136571784604333311 := by
  unfold tailWord_8228394
  simp only [CollatzResearch.WordTrace]
  refine ⟨75028546137985327664709059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200076123034627540439224157 75028546137985327664709059)
  ·
    refine ⟨112542819206977991497063589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75028546137985327664709059 112542819206977991497063589)
    ·
      refine ⟨21101778601308373405699423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112542819206977991497063589 21101778601308373405699423)
      ·
        refine ⟨31652667901962560108549135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21101778601308373405699423 31652667901962560108549135)
        ·
          refine ⟨47479001852943840162823703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31652667901962560108549135 47479001852943840162823703)
          ·
            refine ⟨71218502779415760244235555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47479001852943840162823703 71218502779415760244235555)
            ·
              refine ⟨106827754169123640366353333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71218502779415760244235555 106827754169123640366353333)
              ·
                refine ⟨10015101953355341284345625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 106827754169123640366353333 10015101953355341284345625)
                ·
                  refine ⟨7511326465016505963259219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10015101953355341284345625 7511326465016505963259219)
                  ·
                    refine ⟨11266989697524758944888829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7511326465016505963259219 11266989697524758944888829)
                    ·
                      refine ⟨4225121136571784604333311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11266989697524758944888829 4225121136571784604333311)
                      ·
                        rfl

theorem cell23_8228394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 5, 2, 1, 3].length) (baseStart_8228394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8228394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8228394 prefixEnd_8228394 := by exact prefixLift 8228394
  have htrace : WordTrace (prefixWord ++ tailWord_8228394) baseStart_8228394 baseEnd_8228394 := by
    simpa [prefixWord, tailWord_8228394, baseEnd_8228394] using wordTrace_append hprefix tailTrace_8228394
  have hstable : (prefixWord ++ tailWord_8228394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8228394).length < 2 ^ (prefixWord ++ tailWord_8228394).sum := by decide
  have hdescent : baseEnd_8228394 < baseStart_8228394 := by decide
  rcases family_descends (prefixWord ++ tailWord_8228394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8228445 : List Nat := [1, 4, 4, 2, 1, 1, 3, 1, 2, 1, 3]
def baseStart_8228445 : Nat := 118140960795 + 8228445 * 2 ^ 59
def prefixEnd_8228445 : Nat := 4983230072969 + 3 ^ 40 * 8228445 * 2
def baseEnd_8228445 : Nat := 4225147324085163904795577

theorem tailTrace_8228445 : CollatzResearch.WordTrace tailWord_8228445 prefixEnd_8228445 4225147324085163904795577 := by
  unfold tailWord_8228445
  simp only [CollatzResearch.WordTrace]
  refine ⟨300116044674756546368942789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200077363116504364245961859 300116044674756546368942789)
  ·
    refine ⟨56271758376516852444176773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 300116044674756546368942789 56271758376516852444176773)
    ·
      refine ⟨10550954695596909833283145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56271758376516852444176773 10550954695596909833283145)
      ·
        refine ⟨7913216021697682374962359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10550954695596909833283145 7913216021697682374962359)
        ·
          refine ⟨11869824032546523562443539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7913216021697682374962359 11869824032546523562443539)
          ·
            refine ⟨17804736048819785343665309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11869824032546523562443539 17804736048819785343665309)
            ·
              refine ⟨6676776018307419503874491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17804736048819785343665309 6676776018307419503874491)
              ·
                refine ⟨10015164027461129255811737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6676776018307419503874491 10015164027461129255811737)
                ·
                  refine ⟨7511373020595846941858803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10015164027461129255811737 7511373020595846941858803)
                  ·
                    refine ⟨11267059530893770412788205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7511373020595846941858803 11267059530893770412788205)
                    ·
                      refine ⟨4225147324085163904795577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11267059530893770412788205 4225147324085163904795577)
                      ·
                        rfl

theorem cell23_8228445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_8228445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8228445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8228445 prefixEnd_8228445 := by exact prefixLift 8228445
  have htrace : WordTrace (prefixWord ++ tailWord_8228445) baseStart_8228445 baseEnd_8228445 := by
    simpa [prefixWord, tailWord_8228445, baseEnd_8228445] using wordTrace_append hprefix tailTrace_8228445
  have hstable : (prefixWord ++ tailWord_8228445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8228445).length < 2 ^ (prefixWord ++ tailWord_8228445).sum := by decide
  have hdescent : baseEnd_8228445 < baseStart_8228445 := by decide
  rcases family_descends (prefixWord ++ tailWord_8228445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8228480 : List Nat := [2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 5]
def baseStart_8228480 : Nat := 118140960795 + 8228480 * 2 ^ 59
def prefixEnd_8228480 : Nat := 4983230072969 + 3 ^ 40 * 8228480 * 2
def baseEnd_8228480 : Nat := 4225165295908071267857915

theorem tailTrace_8228480 : CollatzResearch.WordTrace tailWord_8228480 prefixEnd_8228480 4225165295908071267857915 := by
  unfold tailWord_8228480
  simp only [CollatzResearch.WordTrace]
  refine ⟨150058660614814873673233447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200078214153086498230977929 150058660614814873673233447)
  ·
    refine ⟨225087990922222310509850171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150058660614814873673233447 225087990922222310509850171)
    ·
      refine ⟨337631986383333465764775257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225087990922222310509850171 337631986383333465764775257)
      ·
        refine ⟨253223989787500099323581443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 337631986383333465764775257 253223989787500099323581443)
        ·
          refine ⟨379835984681250148985372165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253223989787500099323581443 379835984681250148985372165)
          ·
            refine ⟨71219247127734402934757281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 379835984681250148985372165 71219247127734402934757281)
            ·
              refine ⟨53414435345800802201067961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71219247127734402934757281 53414435345800802201067961)
              ·
                refine ⟨40060826509350601650800971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53414435345800802201067961 40060826509350601650800971)
                ·
                  refine ⟨60091239764025902476201457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40060826509350601650800971 60091239764025902476201457)
                  ·
                    refine ⟨45068429823019426857151093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60091239764025902476201457 45068429823019426857151093)
                    ·
                      refine ⟨4225165295908071267857915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45068429823019426857151093 4225165295908071267857915)
                      ·
                        rfl

theorem cell23_8228480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 5].length) (baseStart_8228480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8228480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8228480 prefixEnd_8228480 := by exact prefixLift 8228480
  have htrace : WordTrace (prefixWord ++ tailWord_8228480) baseStart_8228480 baseEnd_8228480 := by
    simpa [prefixWord, tailWord_8228480, baseEnd_8228480] using wordTrace_append hprefix tailTrace_8228480
  have hstable : (prefixWord ++ tailWord_8228480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8228480).length < 2 ^ (prefixWord ++ tailWord_8228480).sum := by decide
  have hdescent : baseEnd_8228480 < baseStart_8228480 := by decide
  rcases family_descends (prefixWord ++ tailWord_8228480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8228487 : List Nat := [1, 1, 4, 2, 1, 4, 1, 2, 2, 5]
def baseStart_8228487 : Nat := 118140960795 + 8228487 * 2 ^ 59
def prefixEnd_8228487 : Nat := 4983230072969 + 3 ^ 40 * 8228487 * 2
def baseEnd_8228487 : Nat := 1408389630090884246823461

theorem tailTrace_8228487 : CollatzResearch.WordTrace tailWord_8228487 prefixEnd_8228487 1408389630090884246823461 := by
  unfold tailWord_8228487
  simp only [CollatzResearch.WordTrace]
  refine ⟨300117576540604387541971715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200078384360402925027981143 300117576540604387541971715)
  ·
    refine ⟨450176364810906581312957573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300117576540604387541971715 450176364810906581312957573)
    ·
      refine ⟨84408068402044983996179545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 450176364810906581312957573 84408068402044983996179545)
      ·
        refine ⟨63306051301533737997134659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84408068402044983996179545 63306051301533737997134659)
        ·
          refine ⟨94959076952300606995701989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63306051301533737997134659 94959076952300606995701989)
          ·
            refine ⟨17804826928556363811694123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94959076952300606995701989 17804826928556363811694123)
            ·
              refine ⟨26707240392834545717541185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17804826928556363811694123 26707240392834545717541185)
              ·
                refine ⟨20030430294625909288155889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26707240392834545717541185 20030430294625909288155889)
                ·
                  refine ⟨15022822720969431966116917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20030430294625909288155889 15022822720969431966116917)
                  ·
                    refine ⟨1408389630090884246823461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15022822720969431966116917 1408389630090884246823461)
                    ·
                      rfl

theorem cell23_8228487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 2, 2, 5].length) (baseStart_8228487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8228487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8228487 prefixEnd_8228487 := by exact prefixLift 8228487
  have htrace : WordTrace (prefixWord ++ tailWord_8228487) baseStart_8228487 baseEnd_8228487 := by
    simpa [prefixWord, tailWord_8228487, baseEnd_8228487] using wordTrace_append hprefix tailTrace_8228487
  have hstable : (prefixWord ++ tailWord_8228487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8228487).length < 2 ^ (prefixWord ++ tailWord_8228487).sum := by decide
  have hdescent : baseEnd_8228487 < baseStart_8228487 := by decide
  rcases family_descends (prefixWord ++ tailWord_8228487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8228517 : List Nat := [1, 3, 1, 2, 1, 2, 2, 4, 3, 4]
def baseStart_8228517 : Nat := 118140960795 + 8228517 * 2 ^ 59
def prefixEnd_8228517 : Nat := 4983230072969 + 3 ^ 40 * 8228517 * 2
def baseEnd_8228517 : Nat := 1408394764897429207698415

theorem tailTrace_8228517 : CollatzResearch.WordTrace tailWord_8228517 prefixEnd_8228517 1408394764897429207698415 := by
  unfold tailWord_8228517
  simp only [CollatzResearch.WordTrace]
  refine ⟨300118670730495702665563805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200079113820330468443709203 300118670730495702665563805)
  ·
    refine ⟨112544501523935888499586427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 300118670730495702665563805 112544501523935888499586427)
    ·
      refine ⟨168816752285903832749379641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112544501523935888499586427 168816752285903832749379641)
      ·
        refine ⟨126612564214427874562034731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168816752285903832749379641 126612564214427874562034731)
        ·
          refine ⟨189918846321641811843052097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126612564214427874562034731 189918846321641811843052097)
          ·
            refine ⟨142439134741231358882289073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189918846321641811843052097 142439134741231358882289073)
            ·
              refine ⟨106829351055923519161716805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142439134741231358882289073 106829351055923519161716805)
              ·
                refine ⟨20030503322985659842821901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106829351055923519161716805 20030503322985659842821901)
                ·
                  refine ⟨7511438746119622441058213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20030503322985659842821901 7511438746119622441058213)
                  ·
                    refine ⟨1408394764897429207698415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7511438746119622441058213 1408394764897429207698415)
                    ·
                      rfl

theorem cell23_8228517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 4, 3, 4].length) (baseStart_8228517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8228517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8228517 prefixEnd_8228517 := by exact prefixLift 8228517
  have htrace : WordTrace (prefixWord ++ tailWord_8228517) baseStart_8228517 baseEnd_8228517 := by
    simpa [prefixWord, tailWord_8228517, baseEnd_8228517] using wordTrace_append hprefix tailTrace_8228517
  have hstable : (prefixWord ++ tailWord_8228517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8228517).length < 2 ^ (prefixWord ++ tailWord_8228517).sum := by decide
  have hdescent : baseEnd_8228517 < baseStart_8228517 := by decide
  rcases family_descends (prefixWord ++ tailWord_8228517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8228530 : List Nat := [3, 2, 1, 1, 1, 2, 2, 1, 10]
def baseStart_8228530 : Nat := 118140960795 + 8228530 * 2 ^ 59
def prefixEnd_8228530 : Nat := 4983230072969 + 3 ^ 40 * 8228530 * 2
def baseEnd_8228530 : Nat := 469465663326755119136965

theorem tailTrace_8228530 : CollatzResearch.WordTrace tailWord_8228530 prefixEnd_8228530 469465663326755119136965 := by
  unfold tailWord_8228530
  simp only [CollatzResearch.WordTrace]
  refine ⟨75029786219862151471446761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200079429919632403923858029 75029786219862151471446761)
  ·
    refine ⟨56272339664896613603585071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75029786219862151471446761 56272339664896613603585071)
    ·
      refine ⟨84408509497344920405377607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56272339664896613603585071 84408509497344920405377607)
      ·
        refine ⟨126612764246017380608066411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84408509497344920405377607 126612764246017380608066411)
        ·
          refine ⟨189919146369026070912099617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126612764246017380608066411 189919146369026070912099617)
          ·
            refine ⟨142439359776769553184074713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189919146369026070912099617 142439359776769553184074713)
            ·
              refine ⟨106829519832577164888056035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142439359776769553184074713 106829519832577164888056035)
              ·
                refine ⟨160244279748865747332084053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106829519832577164888056035 160244279748865747332084053)
                ·
                  refine ⟨469465663326755119136965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 160244279748865747332084053 469465663326755119136965)
                  ·
                    rfl

theorem cell23_8228530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 10].length) (baseStart_8228530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8228530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8228530 prefixEnd_8228530 := by exact prefixLift 8228530
  have htrace : WordTrace (prefixWord ++ tailWord_8228530) baseStart_8228530 baseEnd_8228530 := by
    simpa [prefixWord, tailWord_8228530, baseEnd_8228530] using wordTrace_append hprefix tailTrace_8228530
  have hstable : (prefixWord ++ tailWord_8228530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8228530).length < 2 ^ (prefixWord ++ tailWord_8228530).sum := by decide
  have hdescent : baseEnd_8228530 < baseStart_8228530 := by decide
  rcases family_descends (prefixWord ++ tailWord_8228530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8228564 : List Nat := [2, 4, 1, 3, 1, 1, 2, 3, 6]
def baseStart_8228564 : Nat := 118140960795 + 8228564 * 2 ^ 59
def prefixEnd_8228564 : Nat := 4983230072969 + 3 ^ 40 * 8228564 * 2
def baseEnd_8228564 : Nat := 469467603142560993245281

theorem tailTrace_8228564 : CollatzResearch.WordTrace tailWord_8228564 prefixEnd_8228564 469467603142560993245281 := by
  unfold tailWord_8228564
  simp only [CollatzResearch.WordTrace]
  refine ⟨150060192480662714846262373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200080256640883619795016497 150060192480662714846262373)
  ·
    refine ⟨28136286090124259033674195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150060192480662714846262373 28136286090124259033674195)
    ·
      refine ⟨42204429135186388550511293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28136286090124259033674195 42204429135186388550511293)
      ·
        refine ⟨15826660925694895706441735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42204429135186388550511293 15826660925694895706441735)
        ·
          refine ⟨23739991388542343559662603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15826660925694895706441735 23739991388542343559662603)
          ·
            refine ⟨35609987082813515339493905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23739991388542343559662603 35609987082813515339493905)
            ·
              refine ⟨26707490312110136504620429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35609987082813515339493905 26707490312110136504620429)
              ·
                refine ⟨10015308867041301189232661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26707490312110136504620429 10015308867041301189232661)
                ·
                  refine ⟨469467603142560993245281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10015308867041301189232661 469467603142560993245281)
                  ·
                    rfl

theorem cell23_8228564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 3, 6].length) (baseStart_8228564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8228564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8228564 prefixEnd_8228564 := by exact prefixLift 8228564
  have htrace : WordTrace (prefixWord ++ tailWord_8228564) baseStart_8228564 baseEnd_8228564 := by
    simpa [prefixWord, tailWord_8228564, baseEnd_8228564] using wordTrace_append hprefix tailTrace_8228564
  have hstable : (prefixWord ++ tailWord_8228564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8228564).length < 2 ^ (prefixWord ++ tailWord_8228564).sum := by decide
  have hdescent : baseEnd_8228564 < baseStart_8228564 := by decide
  rcases family_descends (prefixWord ++ tailWord_8228564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8228594 : List Nat := [3, 2, 1, 3, 1, 1, 3, 3, 1, 5]
def baseStart_8228594 : Nat := 118140960795 + 8228594 * 2 ^ 59
def prefixEnd_8228594 : Nat := 4983230072969 + 3 ^ 40 * 8228594 * 2
def baseEnd_8228594 : Nat := 1408407944234227940610797

theorem tailTrace_8228594 : CollatzResearch.WordTrace tailWord_8228594 prefixEnd_8228594 1408407944234227940610797 := by
  unfold tailWord_8228594
  simp only [CollatzResearch.WordTrace]
  refine ⟨75030369787804186204029209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200080986100811163210744557 75030369787804186204029209)
  ·
    refine ⟨56272777340853139653021907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75030369787804186204029209 56272777340853139653021907)
    ·
      refine ⟨84409166011279709479532861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56272777340853139653021907 84409166011279709479532861)
      ·
        refine ⟨31653437254229891054824823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84409166011279709479532861 31653437254229891054824823)
        ·
          refine ⟨47480155881344836582237235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31653437254229891054824823 47480155881344836582237235)
          ·
            refine ⟨71220233822017254873355853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47480155881344836582237235 71220233822017254873355853)
            ·
              refine ⟨26707587683256470577508445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71220233822017254873355853 26707587683256470577508445)
              ·
                refine ⟨10015345381221176466565667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26707587683256470577508445 10015345381221176466565667)
                ·
                  refine ⟨15023018071831764699848501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10015345381221176466565667 15023018071831764699848501)
                  ·
                    refine ⟨1408407944234227940610797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15023018071831764699848501 1408407944234227940610797)
                    ·
                      rfl

theorem cell23_8228594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 3, 1, 5].length) (baseStart_8228594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8228594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8228594 prefixEnd_8228594 := by exact prefixLift 8228594
  have htrace : WordTrace (prefixWord ++ tailWord_8228594) baseStart_8228594 baseEnd_8228594 := by
    simpa [prefixWord, tailWord_8228594, baseEnd_8228594] using wordTrace_append hprefix tailTrace_8228594
  have hstable : (prefixWord ++ tailWord_8228594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8228594).length < 2 ^ (prefixWord ++ tailWord_8228594).sum := by decide
  have hdescent : baseEnd_8228594 < baseStart_8228594 := by decide
  rcases family_descends (prefixWord ++ tailWord_8228594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8228627 : List Nat := [1, 1, 1, 2, 1, 3, 2, 5, 1, 2, 4]
def baseStart_8228627 : Nat := 118140960795 + 8228627 * 2 ^ 59
def prefixEnd_8228627 : Nat := 4983230072969 + 3 ^ 40 * 8228627 * 2
def baseEnd_8228627 : Nat := 4225240777564282192719739

theorem tailTrace_8228627 : CollatzResearch.WordTrace tailWord_8228627 prefixEnd_8228627 4225240777564282192719739 := by
  unfold tailWord_8228627
  simp only [CollatzResearch.WordTrace]
  refine ⟨300122682760097191452068135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200081788506731460968045423 300122682760097191452068135)
  ·
    refine ⟨450184024140145787178102203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300122682760097191452068135 450184024140145787178102203)
    ·
      refine ⟨675276036210218680767153305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 450184024140145787178102203 675276036210218680767153305)
      ·
        refine ⟨506457027157664010575364979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 675276036210218680767153305 506457027157664010575364979)
        ·
          refine ⟨759685540736496015863047469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 506457027157664010575364979 759685540736496015863047469)
          ·
            refine ⟨284882077776186005948642801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 759685540736496015863047469 284882077776186005948642801)
            ·
              refine ⟨213661558332139504461482101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 284882077776186005948642801 213661558332139504461482101)
              ·
                refine ⟨20030771093638078543263947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 213661558332139504461482101 20030771093638078543263947)
                ·
                  refine ⟨30046156640457117814895921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20030771093638078543263947 30046156640457117814895921)
                  ·
                    refine ⟨22534617480342838361171941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30046156640457117814895921 22534617480342838361171941)
                    ·
                      refine ⟨4225240777564282192719739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22534617480342838361171941 4225240777564282192719739)
                      ·
                        rfl

theorem cell23_8228627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 5, 1, 2, 4].length) (baseStart_8228627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8228627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8228627 prefixEnd_8228627 := by exact prefixLift 8228627
  have htrace : WordTrace (prefixWord ++ tailWord_8228627) baseStart_8228627 baseEnd_8228627 := by
    simpa [prefixWord, tailWord_8228627, baseEnd_8228627] using wordTrace_append hprefix tailTrace_8228627
  have hstable : (prefixWord ++ tailWord_8228627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8228627).length < 2 ^ (prefixWord ++ tailWord_8228627).sum := by decide
  have hdescent : baseEnd_8228627 < baseStart_8228627 := by decide
  rcases family_descends (prefixWord ++ tailWord_8228627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8228631 : List Nat := [1, 1, 3, 4, 2, 2, 2, 2, 1, 1, 4]
def baseStart_8228631 : Nat := 118140960795 + 8228631 * 2 ^ 59
def prefixEnd_8228631 : Nat := 4983230072969 + 3 ^ 40 * 8228631 * 2
def baseEnd_8228631 : Nat := 4225242831486900177069721

theorem tailTrace_8228631 : CollatzResearch.WordTrace tailWord_8228631 prefixEnd_8228631 4225242831486900177069721 := by
  unfold tailWord_8228631
  simp only [CollatzResearch.WordTrace]
  refine ⟨300122828652082700135213747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200081885768055133423475831 300122828652082700135213747)
  ·
    refine ⟨450184242978124050202820621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300122828652082700135213747 450184242978124050202820621)
    ·
      refine ⟨168819091116796518826057733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 450184242978124050202820621 168819091116796518826057733)
      ·
        refine ⟨31653579584399347279885825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 168819091116796518826057733 31653579584399347279885825)
        ·
          refine ⟨23740184688299510459914369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31653579584399347279885825 23740184688299510459914369)
          ·
            refine ⟨17805138516224632844935777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23740184688299510459914369 17805138516224632844935777)
            ·
              refine ⟨13353853887168474633701833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17805138516224632844935777 13353853887168474633701833)
              ·
                refine ⟨10015390415376355975276375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13353853887168474633701833 10015390415376355975276375)
                ·
                  refine ⟨15023085623064533962914563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10015390415376355975276375 15023085623064533962914563)
                  ·
                    refine ⟨22534628434596800944371845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15023085623064533962914563 22534628434596800944371845)
                    ·
                      refine ⟨4225242831486900177069721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22534628434596800944371845 4225242831486900177069721)
                      ·
                        rfl

theorem cell23_8228631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 2, 2, 1, 1, 4].length) (baseStart_8228631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8228631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8228631 prefixEnd_8228631 := by exact prefixLift 8228631
  have htrace : WordTrace (prefixWord ++ tailWord_8228631) baseStart_8228631 baseEnd_8228631 := by
    simpa [prefixWord, tailWord_8228631, baseEnd_8228631] using wordTrace_append hprefix tailTrace_8228631
  have hstable : (prefixWord ++ tailWord_8228631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8228631).length < 2 ^ (prefixWord ++ tailWord_8228631).sum := by decide
  have hdescent : baseEnd_8228631 < baseStart_8228631 := by decide
  rcases family_descends (prefixWord ++ tailWord_8228631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8228681 : List Nat := [1, 2, 1, 1, 2, 4, 3, 3, 2, 1, 3]
def baseStart_8228681 : Nat := 118140960795 + 8228681 * 2 ^ 59
def prefixEnd_8228681 : Nat := 4983230072969 + 3 ^ 40 * 8228681 * 2
def baseEnd_8228681 : Nat := 4225268505519624981444491

theorem tailTrace_8228681 : CollatzResearch.WordTrace tailWord_8228681 prefixEnd_8228681 4225268505519624981444491 := by
  unfold tailWord_8228681
  simp only [CollatzResearch.WordTrace]
  refine ⟨300124652301901558674533897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200083101534601039116355931 300124652301901558674533897)
  ·
    refine ⟨225093489226426169005900423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300124652301901558674533897 225093489226426169005900423)
    ·
      refine ⟨337640233839639253508850635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225093489226426169005900423 337640233839639253508850635)
      ·
        refine ⟨506460350759458880263275953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337640233839639253508850635 506460350759458880263275953)
        ·
          refine ⟨379845263069594160197456965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 506460350759458880263275953 379845263069594160197456965)
          ·
            refine ⟨71220986825548905037023181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 379845263069594160197456965 71220986825548905037023181)
            ·
              refine ⟨26707870059580839388883693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71220986825548905037023181 26707870059580839388883693)
              ·
                refine ⟨10015451272342814770831385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26707870059580839388883693 10015451272342814770831385)
                ·
                  refine ⟨7511588454257111078123539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10015451272342814770831385 7511588454257111078123539)
                  ·
                    refine ⟨11267382681385666617185309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7511588454257111078123539 11267382681385666617185309)
                    ·
                      refine ⟨4225268505519624981444491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11267382681385666617185309 4225268505519624981444491)
                      ·
                        rfl

theorem cell23_8228681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 3, 2, 1, 3].length) (baseStart_8228681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8228681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8228681 prefixEnd_8228681 := by exact prefixLift 8228681
  have htrace : WordTrace (prefixWord ++ tailWord_8228681) baseStart_8228681 baseEnd_8228681 := by
    simpa [prefixWord, tailWord_8228681, baseEnd_8228681] using wordTrace_append hprefix tailTrace_8228681
  have hstable : (prefixWord ++ tailWord_8228681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8228681).length < 2 ^ (prefixWord ++ tailWord_8228681).sum := by decide
  have hdescent : baseEnd_8228681 < baseStart_8228681 := by decide
  rcases family_descends (prefixWord ++ tailWord_8228681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8228685 : List Nat := [1, 6, 1, 2, 1, 3, 1, 2, 1, 2, 3]
def baseStart_8228685 : Nat := 118140960795 + 8228685 * 2 ^ 59
def prefixEnd_8228685 : Nat := 4983230072969 + 3 ^ 40 * 8228685 * 2
def baseEnd_8228685 : Nat := 4225270559442242965794473

theorem tailTrace_8228685 : CollatzResearch.WordTrace tailWord_8228685 prefixEnd_8228685 4225270559442242965794473 := by
  unfold tailWord_8228685
  simp only [CollatzResearch.WordTrace]
  refine ⟨300124798193887067357679509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200083198795924711571786339 300124798193887067357679509)
  ·
    refine ⟨14068349915338456282391227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 300124798193887067357679509 14068349915338456282391227)
    ·
      refine ⟨21102524873007684423586841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14068349915338456282391227 21102524873007684423586841)
      ·
        refine ⟨15826893654755763317690131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21102524873007684423586841 15826893654755763317690131)
        ·
          refine ⟨23740340482133644976535197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15826893654755763317690131 23740340482133644976535197)
          ·
            refine ⟨8902627680800116866200699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23740340482133644976535197 8902627680800116866200699)
            ·
              refine ⟨13353941521200175299301049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8902627680800116866200699 13353941521200175299301049)
              ·
                refine ⟨10015456140900131474475787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13353941521200175299301049 10015456140900131474475787)
                ·
                  refine ⟨15023184211350197211713681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10015456140900131474475787 15023184211350197211713681)
                  ·
                    refine ⟨11267388158512647908785261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15023184211350197211713681 11267388158512647908785261)
                    ·
                      refine ⟨4225270559442242965794473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11267388158512647908785261 4225270559442242965794473)
                      ·
                        rfl

theorem cell23_8228685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_8228685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8228685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8228685 prefixEnd_8228685 := by exact prefixLift 8228685
  have htrace : WordTrace (prefixWord ++ tailWord_8228685) baseStart_8228685 baseEnd_8228685 := by
    simpa [prefixWord, tailWord_8228685, baseEnd_8228685] using wordTrace_append hprefix tailTrace_8228685
  have hstable : (prefixWord ++ tailWord_8228685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8228685).length < 2 ^ (prefixWord ++ tailWord_8228685).sum := by decide
  have hdescent : baseEnd_8228685 < baseStart_8228685 := by decide
  rcases family_descends (prefixWord ++ tailWord_8228685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8228794 : List Nat := [3, 1, 1, 1, 2, 1, 2, 1, 6, 1, 4]
def baseStart_8228794 : Nat := 118140960795 + 8228794 * 2 ^ 59
def prefixEnd_8228794 : Nat := 4983230072969 + 3 ^ 40 * 8228794 * 2
def baseEnd_8228794 : Nat := 4225326528833583039331471

theorem tailTrace_8228794 : CollatzResearch.WordTrace tailWord_8228794 prefixEnd_8228794 4225326528833583039331471 := by
  unfold tailWord_8228794
  simp only [CollatzResearch.WordTrace]
  refine ⟨75032193437623044743349359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200085849166994785982264957 75032193437623044743349359)
  ·
    refine ⟨112548290156434567115024039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75032193437623044743349359 112548290156434567115024039)
    ·
      refine ⟨168822435234651850672536059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112548290156434567115024039 168822435234651850672536059)
      ·
        refine ⟨253233652851977776008804089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168822435234651850672536059 253233652851977776008804089)
        ·
          refine ⟨189925239638983332006603067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 253233652851977776008804089 189925239638983332006603067)
          ·
            refine ⟨284887859458474998009904601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189925239638983332006603067 284887859458474998009904601)
            ·
              refine ⟨213665894593856248507428451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 284887859458474998009904601 213665894593856248507428451)
              ·
                refine ⟨320498841890784372761142677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 213665894593856248507428451 320498841890784372761142677)
                ·
                  refine ⟨15023383213630517473178563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 320498841890784372761142677 15023383213630517473178563)
                  ·
                    refine ⟨22535074820445776209767845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15023383213630517473178563 22535074820445776209767845)
                    ·
                      refine ⟨4225326528833583039331471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22535074820445776209767845 4225326528833583039331471)
                      ·
                        rfl

theorem cell23_8228794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 6, 1, 4].length) (baseStart_8228794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8228794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8228794 prefixEnd_8228794 := by exact prefixLift 8228794
  have htrace : WordTrace (prefixWord ++ tailWord_8228794) baseStart_8228794 baseEnd_8228794 := by
    simpa [prefixWord, tailWord_8228794, baseEnd_8228794] using wordTrace_append hprefix tailTrace_8228794
  have hstable : (prefixWord ++ tailWord_8228794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8228794).length < 2 ^ (prefixWord ++ tailWord_8228794).sum := by decide
  have hdescent : baseEnd_8228794 < baseStart_8228794 := by decide
  rcases family_descends (prefixWord ++ tailWord_8228794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8228831 : List Nat := [1, 1, 2, 3, 4, 1, 1, 1, 4, 2, 3]
def baseStart_8228831 : Nat := 118140960795 + 8228831 * 2 ^ 59
def prefixEnd_8228831 : Nat := 4983230072969 + 3 ^ 40 * 8228831 * 2
def baseEnd_8228831 : Nat := 4225345527617799394568801

theorem tailTrace_8228831 : CollatzResearch.WordTrace tailWord_8228831 prefixEnd_8228831 4225345527617799394568801 := by
  unfold tailWord_8228831
  simp only [CollatzResearch.WordTrace]
  refine ⟨300130123251358134292494347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200086748834238756194996231 300130123251358134292494347)
  ·
    refine ⟨450195184877037201438741521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300130123251358134292494347 450195184877037201438741521)
    ·
      refine ⟨337646388657777901079056141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 450195184877037201438741521 337646388657777901079056141)
      ·
        refine ⟨126617395746666712904646053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 337646388657777901079056141 126617395746666712904646053)
        ·
          refine ⟨23740761702500008669621135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 126617395746666712904646053 23740761702500008669621135)
          ·
            refine ⟨35611142553750013004431703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23740761702500008669621135 35611142553750013004431703)
            ·
              refine ⟨53416713830625019506647555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35611142553750013004431703 53416713830625019506647555)
              ·
                refine ⟨80125070745937529259971333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53416713830625019506647555 80125070745937529259971333)
                ·
                  refine ⟨15023450764863286736244625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80125070745937529259971333 15023450764863286736244625)
                  ·
                    refine ⟨11267588073647465052183469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15023450764863286736244625 11267588073647465052183469)
                    ·
                      refine ⟨4225345527617799394568801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11267588073647465052183469 4225345527617799394568801)
                      ·
                        rfl

theorem cell23_8228831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 4, 2, 3].length) (baseStart_8228831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8228831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8228831 prefixEnd_8228831 := by exact prefixLift 8228831
  have htrace : WordTrace (prefixWord ++ tailWord_8228831) baseStart_8228831 baseEnd_8228831 := by
    simpa [prefixWord, tailWord_8228831, baseEnd_8228831] using wordTrace_append hprefix tailTrace_8228831
  have hstable : (prefixWord ++ tailWord_8228831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8228831).length < 2 ^ (prefixWord ++ tailWord_8228831).sum := by decide
  have hdescent : baseEnd_8228831 < baseStart_8228831 := by decide
  rcases family_descends (prefixWord ++ tailWord_8228831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8228888 : List Nat := [2, 1, 2, 3, 2, 1, 1, 4, 2, 3, 2]
def baseStart_8228888 : Nat := 118140960795 + 8228888 * 2 ^ 59
def prefixEnd_8228888 : Nat := 4983230072969 + 3 ^ 40 * 8228888 * 2
def baseEnd_8228888 : Nat := 4225374796015105671556039

theorem tailTrace_8228888 : CollatzResearch.WordTrace tailWord_8228888 prefixEnd_8228888 4225374796015105671556039 := by
  unfold tailWord_8228888
  simp only [CollatzResearch.WordTrace]
  refine ⟨150066101106075816513659659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200088134808101088684879545 150066101106075816513659659)
  ·
    refine ⟨225099151659113724770489489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150066101106075816513659659 225099151659113724770489489)
    ·
      refine ⟨168824363744335293577867117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225099151659113724770489489 168824363744335293577867117)
      ·
        refine ⟨63309136404125735091700169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168824363744335293577867117 63309136404125735091700169)
        ·
          refine ⟨47481852303094301318775127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63309136404125735091700169 47481852303094301318775127)
          ·
            refine ⟨71222778454641451978162691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47481852303094301318775127 71222778454641451978162691)
            ·
              refine ⟨106834167681962177967244037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71222778454641451978162691 106834167681962177967244037)
              ·
                refine ⟨20031406440367908368858257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106834167681962177967244037 20031406440367908368858257)
                ·
                  refine ⟨15023554830275931276643693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20031406440367908368858257 15023554830275931276643693)
                  ·
                    refine ⟨5633833061353474228741385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15023554830275931276643693 5633833061353474228741385)
                    ·
                      refine ⟨4225374796015105671556039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5633833061353474228741385 4225374796015105671556039)
                      ·
                        rfl

theorem cell23_8228888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 4, 2, 3, 2].length) (baseStart_8228888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8228888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8228888 prefixEnd_8228888 := by exact prefixLift 8228888
  have htrace : WordTrace (prefixWord ++ tailWord_8228888) baseStart_8228888 baseEnd_8228888 := by
    simpa [prefixWord, tailWord_8228888, baseEnd_8228888] using wordTrace_append hprefix tailTrace_8228888
  have hstable : (prefixWord ++ tailWord_8228888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8228888).length < 2 ^ (prefixWord ++ tailWord_8228888).sum := by decide
  have hdescent : baseEnd_8228888 < baseStart_8228888 := by decide
  rcases family_descends (prefixWord ++ tailWord_8228888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8228895 : List Nat := [1, 1, 2, 4, 1, 2, 3, 4, 1, 1, 3]
def baseStart_8228895 : Nat := 118140960795 + 8228895 * 2 ^ 59
def prefixEnd_8228895 : Nat := 4983230072969 + 3 ^ 40 * 8228895 * 2
def baseEnd_8228895 : Nat := 4225378390379687144168507

theorem tailTrace_8228895 : CollatzResearch.WordTrace tailWord_8228895 prefixEnd_8228895 4225378390379687144168507 := by
  unfold tailWord_8228895
  simp only [CollatzResearch.WordTrace]
  refine ⟨300132457523126273222824139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200088305015417515481882759 300132457523126273222824139)
  ·
    refine ⟨450198686284689409834236209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300132457523126273222824139 450198686284689409834236209)
    ·
      refine ⟨337649014713517057375677157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 450198686284689409834236209 337649014713517057375677157)
      ·
        refine ⟨63309190258784448257939467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 337649014713517057375677157 63309190258784448257939467)
        ·
          refine ⟨94963785388176672386909201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63309190258784448257939467 94963785388176672386909201)
          ·
            refine ⟨71222839041132504290181901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94963785388176672386909201 71222839041132504290181901)
            ·
              refine ⟨26708564640424689108818213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71222839041132504290181901 26708564640424689108818213)
              ·
                refine ⟨5007855870079629207903415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26708564640424689108818213 5007855870079629207903415)
                ·
                  refine ⟨7511783805119443811855123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5007855870079629207903415 7511783805119443811855123)
                  ·
                    refine ⟨11267675707679165717782685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7511783805119443811855123 11267675707679165717782685)
                    ·
                      refine ⟨4225378390379687144168507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11267675707679165717782685 4225378390379687144168507)
                      ·
                        rfl

theorem cell23_8228895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 4, 1, 1, 3].length) (baseStart_8228895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8228895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8228895 prefixEnd_8228895 := by exact prefixLift 8228895
  have htrace : WordTrace (prefixWord ++ tailWord_8228895) baseStart_8228895 baseEnd_8228895 := by
    simpa [prefixWord, tailWord_8228895, baseEnd_8228895] using wordTrace_append hprefix tailTrace_8228895
  have hstable : (prefixWord ++ tailWord_8228895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8228895).length < 2 ^ (prefixWord ++ tailWord_8228895).sum := by decide
  have hdescent : baseEnd_8228895 < baseStart_8228895 := by decide
  rcases family_descends (prefixWord ++ tailWord_8228895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8228901 : List Nat := [1, 3, 1, 2, 2, 3, 1, 2, 3, 1, 4]
def baseStart_8228901 : Nat := 118140960795 + 8228901 * 2 ^ 59
def prefixEnd_8228901 : Nat := 4983230072969 + 3 ^ 40 * 8228901 * 2
def baseEnd_8228901 : Nat := 4225381471263614120693479

theorem tailTrace_8228901 : CollatzResearch.WordTrace tailWord_8228901 prefixEnd_8228901 4225381471263614120693479 := by
  unfold tailWord_8228901
  simp only [CollatzResearch.WordTrace]
  refine ⟨300132676361104536247542557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200088450907403024165028371 300132676361104536247542557)
  ·
    refine ⟨112549753635414201092828459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 300132676361104536247542557 112549753635414201092828459)
    ·
      refine ⟨168824630453121301639242689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112549753635414201092828459 168824630453121301639242689)
      ·
        refine ⟨126618472839840976229432017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168824630453121301639242689 126618472839840976229432017)
        ·
          refine ⟨94963854629880732172074013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126618472839840976229432017 94963854629880732172074013)
          ·
            refine ⟨35611445486205274564527755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94963854629880732172074013 35611445486205274564527755)
            ·
              refine ⟨53417168229307911846791633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35611445486205274564527755 53417168229307911846791633)
              ·
                refine ⟨40062876171980933885093725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53417168229307911846791633 40062876171980933885093725)
                ·
                  refine ⟨15023578564492850206910147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40062876171980933885093725 15023578564492850206910147)
                  ·
                    refine ⟨22535367846739275310365221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15023578564492850206910147 22535367846739275310365221)
                    ·
                      refine ⟨4225381471263614120693479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22535367846739275310365221 4225381471263614120693479)
                      ·
                        rfl

theorem cell23_8228901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 2, 3, 1, 4].length) (baseStart_8228901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8228901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8228901 prefixEnd_8228901 := by exact prefixLift 8228901
  have htrace : WordTrace (prefixWord ++ tailWord_8228901) baseStart_8228901 baseEnd_8228901 := by
    simpa [prefixWord, tailWord_8228901, baseEnd_8228901] using wordTrace_append hprefix tailTrace_8228901
  have hstable : (prefixWord ++ tailWord_8228901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8228901).length < 2 ^ (prefixWord ++ tailWord_8228901).sum := by decide
  have hdescent : baseEnd_8228901 < baseStart_8228901 := by decide
  rcases family_descends (prefixWord ++ tailWord_8228901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8228918 : List Nat := [5, 1, 2, 1, 1, 1, 1, 3, 3, 1, 4]
def baseStart_8228918 : Nat := 118140960795 + 8228918 * 2 ^ 59
def prefixEnd_8228918 : Nat := 4983230072969 + 3 ^ 40 * 8228918 * 2
def baseEnd_8228918 : Nat := 4225390200434740554180901

theorem tailTrace_8228918 : CollatzResearch.WordTrace tailWord_8228918 prefixEnd_8228918 4225390200434740554180901 := by
  unfold tailWord_8228918
  simp only [CollatzResearch.WordTrace]
  refine ⟨18758331025127684259431963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 200088864268028632100607605 18758331025127684259431963)
  ·
    refine ⟨28137496537691526389147945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18758331025127684259431963 28137496537691526389147945)
    ·
      refine ⟨21103122403268644791860959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28137496537691526389147945 21103122403268644791860959)
      ·
        refine ⟨31654683604902967187791439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21103122403268644791860959 31654683604902967187791439)
        ·
          refine ⟨47482025407354450781687159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31654683604902967187791439 47482025407354450781687159)
          ·
            refine ⟨71223038111031676172530739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47482025407354450781687159 71223038111031676172530739)
            ·
              refine ⟨106834557166547514258796109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71223038111031676172530739 106834557166547514258796109)
              ·
                refine ⟨40062958937455317847048541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106834557166547514258796109 40062958937455317847048541)
                ·
                  refine ⟨15023609601545744192643203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40062958937455317847048541 15023609601545744192643203)
                  ·
                    refine ⟨22535414402318616288964805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15023609601545744192643203 22535414402318616288964805)
                    ·
                      refine ⟨4225390200434740554180901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22535414402318616288964805 4225390200434740554180901)
                      ·
                        rfl

theorem cell23_8228918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_8228918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8228918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8228918 prefixEnd_8228918 := by exact prefixLift 8228918
  have htrace : WordTrace (prefixWord ++ tailWord_8228918) baseStart_8228918 baseEnd_8228918 := by
    simpa [prefixWord, tailWord_8228918, baseEnd_8228918] using wordTrace_append hprefix tailTrace_8228918
  have hstable : (prefixWord ++ tailWord_8228918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8228918).length < 2 ^ (prefixWord ++ tailWord_8228918).sum := by decide
  have hdescent : baseEnd_8228918 < baseStart_8228918 := by decide
  rcases family_descends (prefixWord ++ tailWord_8228918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8228941 : List Nat := [1, 6, 1, 1, 1, 1, 12]
def baseStart_8228941 : Nat := 118140960795 + 8228941 * 2 ^ 59
def prefixEnd_8228941 : Nat := 4983230072969 + 3 ^ 40 * 8228941 * 2
def baseEnd_8228941 : Nat := 52165456919627085977695

theorem tailTrace_8228941 : CollatzResearch.WordTrace tailWord_8228941 prefixEnd_8228941 52165456919627085977695 := by
  unfold tailWord_8228941
  simp only [CollatzResearch.WordTrace]
  refine ⟨300134135280959623078998677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200089423520639748719332451 300134135280959623078998677)
  ·
    refine ⟨14068787591294982331828063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 300134135280959623078998677 14068787591294982331828063)
    ·
      refine ⟨21103181386942473497742095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14068787591294982331828063 21103181386942473497742095)
      ·
        refine ⟨31654772080413710246613143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21103181386942473497742095 31654772080413710246613143)
        ·
          refine ⟨47482158120620565369919715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31654772080413710246613143 47482158120620565369919715)
          ·
            refine ⟨71223237180930848054879573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47482158120620565369919715 71223237180930848054879573)
            ·
              refine ⟨52165456919627085977695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 71223237180930848054879573 52165456919627085977695)
              ·
                rfl

theorem cell23_8228941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 12].length) (baseStart_8228941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8228941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8228941 prefixEnd_8228941 := by exact prefixLift 8228941
  have htrace : WordTrace (prefixWord ++ tailWord_8228941) baseStart_8228941 baseEnd_8228941 := by
    simpa [prefixWord, tailWord_8228941, baseEnd_8228941] using wordTrace_append hprefix tailTrace_8228941
  have hstable : (prefixWord ++ tailWord_8228941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8228941).length < 2 ^ (prefixWord ++ tailWord_8228941).sum := by decide
  have hdescent : baseEnd_8228941 < baseStart_8228941 := by decide
  rcases family_descends (prefixWord ++ tailWord_8228941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8228944 : List Nat := [2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 6]
def baseStart_8228944 : Nat := 118140960795 + 8228944 * 2 ^ 59
def prefixEnd_8228944 : Nat := 4983230072969 + 3 ^ 40 * 8228944 * 2
def baseEnd_8228944 : Nat := 4225403550931757452455781

theorem tailTrace_8228944 : CollatzResearch.WordTrace tailWord_8228944 prefixEnd_8228944 4225403550931757452455781 := by
  unfold tailWord_8228944
  simp only [CollatzResearch.WordTrace]
  refine ⟨150067122349974377295678943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200089496466632503060905257 150067122349974377295678943)
  ·
    refine ⟨225100683524961565943518415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150067122349974377295678943 225100683524961565943518415)
    ·
      refine ⟨337651025287442348915277623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225100683524961565943518415 337651025287442348915277623)
      ·
        refine ⟨506476537931163523372916435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337651025287442348915277623 506476537931163523372916435)
        ·
          refine ⟨759714806896745285059374653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 506476537931163523372916435 759714806896745285059374653)
          ·
            refine ⟨284893052586279481897265495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 759714806896745285059374653 284893052586279481897265495)
            ·
              refine ⟨427339578879419222845898243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 284893052586279481897265495 427339578879419222845898243)
              ·
                refine ⟨641009368319128834268847365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 427339578879419222845898243 641009368319128834268847365)
                ·
                  refine ⟨120189256559836656425408881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 641009368319128834268847365 120189256559836656425408881)
                  ·
                    refine ⟨90141942419877492319056661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 120189256559836656425408881 90141942419877492319056661)
                    ·
                      refine ⟨4225403550931757452455781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90141942419877492319056661 4225403550931757452455781)
                      ·
                        rfl

theorem cell23_8228944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 6].length) (baseStart_8228944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8228944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8228944 prefixEnd_8228944 := by exact prefixLift 8228944
  have htrace : WordTrace (prefixWord ++ tailWord_8228944) baseStart_8228944 baseEnd_8228944 := by
    simpa [prefixWord, tailWord_8228944, baseEnd_8228944] using wordTrace_append hprefix tailTrace_8228944
  have hstable : (prefixWord ++ tailWord_8228944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8228944).length < 2 ^ (prefixWord ++ tailWord_8228944).sum := by decide
  have hdescent : baseEnd_8228944 < baseStart_8228944 := by decide
  rcases family_descends (prefixWord ++ tailWord_8228944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8228951 : List Nat := [1, 1, 3, 2, 2, 1, 2, 2, 3, 3, 3]
def baseStart_8228951 : Nat := 118140960795 + 8228951 * 2 ^ 59
def prefixEnd_8228951 : Nat := 4983230072969 + 3 ^ 40 * 8228951 * 2
def baseEnd_8228951 : Nat := 4225407145296338925068249

theorem tailTrace_8228951 : CollatzResearch.WordTrace tailWord_8228951 prefixEnd_8228951 4225407145296338925068249 := by
  unfold tailWord_8228951
  simp only [CollatzResearch.WordTrace]
  refine ⟨300134500010923394786862707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200089666673948929857908471 300134500010923394786862707)
  ·
    refine ⟨450201750016385092180294061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300134500010923394786862707 450201750016385092180294061)
    ·
      refine ⟨168825656256144409567610273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 450201750016385092180294061 168825656256144409567610273)
      ·
        refine ⟨126619242192108307175707705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168825656256144409567610273 126619242192108307175707705)
        ·
          refine ⟨94964431644081230381780779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126619242192108307175707705 94964431644081230381780779)
          ·
            refine ⟨142446647466121845572671169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94964431644081230381780779 142446647466121845572671169)
            ·
              refine ⟨106834985599591384179503377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142446647466121845572671169 106834985599591384179503377)
              ·
                refine ⟨80126239199693538134627533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106834985599591384179503377 80126239199693538134627533)
                ·
                  refine ⟨30047339699885076800485325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80126239199693538134627533 30047339699885076800485325)
                  ·
                    refine ⟨11267752387456903800181997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30047339699885076800485325 11267752387456903800181997)
                    ·
                      refine ⟨4225407145296338925068249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11267752387456903800181997 4225407145296338925068249)
                      ·
                        rfl

theorem cell23_8228951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 2, 3, 3, 3].length) (baseStart_8228951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8228951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8228951 prefixEnd_8228951 := by exact prefixLift 8228951
  have htrace : WordTrace (prefixWord ++ tailWord_8228951) baseStart_8228951 baseEnd_8228951 := by
    simpa [prefixWord, tailWord_8228951, baseEnd_8228951] using wordTrace_append hprefix tailTrace_8228951
  have hstable : (prefixWord ++ tailWord_8228951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8228951).length < 2 ^ (prefixWord ++ tailWord_8228951).sum := by decide
  have hdescent : baseEnd_8228951 < baseStart_8228951 := by decide
  rcases family_descends (prefixWord ++ tailWord_8228951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8228952 : List Nat := [2, 1, 2, 2, 1, 4, 2, 4, 1, 2, 2]
def baseStart_8228952 : Nat := 118140960795 + 8228952 * 2 ^ 59
def prefixEnd_8228952 : Nat := 4983230072969 + 3 ^ 40 * 8228952 * 2
def baseEnd_8228952 : Nat := 4225407658776993421155745

theorem tailTrace_8228952 : CollatzResearch.WordTrace tailWord_8228952 prefixEnd_8228952 4225407658776993421155745 := by
  unfold tailWord_8228952
  simp only [CollatzResearch.WordTrace]
  refine ⟨150067268241959885978824555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200089690989279847971766073 150067268241959885978824555)
  ·
    refine ⟨225100902362939828968236833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150067268241959885978824555 225100902362939828968236833)
    ·
      refine ⟨168825676772204871726177625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225100902362939828968236833 168825676772204871726177625)
      ·
        refine ⟨126619257579153653794633219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168825676772204871726177625 126619257579153653794633219)
        ·
          refine ⟨189928886368730480691949829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126619257579153653794633219 189928886368730480691949829)
          ·
            refine ⟨35611666194136965129740593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 189928886368730480691949829 35611666194136965129740593)
            ·
              refine ⟨26708749645602723847305445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35611666194136965129740593 26708749645602723847305445)
              ·
                refine ⟨5007890558550510721369771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26708749645602723847305445 5007890558550510721369771)
                ·
                  refine ⟨7511835837825766082054657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5007890558550510721369771 7511835837825766082054657)
                  ·
                    refine ⟨5633876878369324561540993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7511835837825766082054657 5633876878369324561540993)
                    ·
                      refine ⟨4225407658776993421155745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5633876878369324561540993 4225407658776993421155745)
                      ·
                        rfl

theorem cell23_8228952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 4, 1, 2, 2].length) (baseStart_8228952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8228952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8228952 prefixEnd_8228952 := by exact prefixLift 8228952
  have htrace : WordTrace (prefixWord ++ tailWord_8228952) baseStart_8228952 baseEnd_8228952 := by
    simpa [prefixWord, tailWord_8228952, baseEnd_8228952] using wordTrace_append hprefix tailTrace_8228952
  have hstable : (prefixWord ++ tailWord_8228952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8228952).length < 2 ^ (prefixWord ++ tailWord_8228952).sum := by decide
  have hdescent : baseEnd_8228952 < baseStart_8228952 := by decide
  rcases family_descends (prefixWord ++ tailWord_8228952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8228962 : List Nat := [3, 3, 2, 2, 3, 1, 1, 1, 1, 6]
def baseStart_8228962 : Nat := 118140960795 + 8228962 * 2 ^ 59
def prefixEnd_8228962 : Nat := 4983230072969 + 3 ^ 40 * 8228962 * 2
def baseEnd_8228962 : Nat := 1408470931194512794010233

theorem tailTrace_8228962 : CollatzResearch.WordTrace tailWord_8228962 prefixEnd_8228962 1408470931194512794010233 := by
  unfold tailWord_8228962
  simp only [CollatzResearch.WordTrace]
  refine ⟨75033725303470885916378285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200089934142589029110342093 75033725303470885916378285)
  ·
    refine ⟨28137646988801582218641857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75033725303470885916378285 28137646988801582218641857)
    ·
      refine ⟨21103235241601186663981393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28137646988801582218641857 21103235241601186663981393)
      ·
        refine ⟨15827426431200889997986045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21103235241601186663981393 15827426431200889997986045)
        ·
          refine ⟨5935284911700333749244767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15827426431200889997986045 5935284911700333749244767)
          ·
            refine ⟨8902927367550500623867151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5935284911700333749244767 8902927367550500623867151)
            ·
              refine ⟨13354391051325750935800727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8902927367550500623867151 13354391051325750935800727)
              ·
                refine ⟨20031586576988626403701091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13354391051325750935800727 20031586576988626403701091)
                ·
                  refine ⟨30047379865482939605551637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20031586576988626403701091 30047379865482939605551637)
                  ·
                    refine ⟨1408470931194512794010233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30047379865482939605551637 1408470931194512794010233)
                    ·
                      rfl

theorem cell23_8228962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 1, 1, 1, 6].length) (baseStart_8228962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8228962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8228962 prefixEnd_8228962 := by exact prefixLift 8228962
  have htrace : WordTrace (prefixWord ++ tailWord_8228962) baseStart_8228962 baseEnd_8228962 := by
    simpa [prefixWord, tailWord_8228962, baseEnd_8228962] using wordTrace_append hprefix tailTrace_8228962
  have hstable : (prefixWord ++ tailWord_8228962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8228962).length < 2 ^ (prefixWord ++ tailWord_8228962).sum := by decide
  have hdescent : baseEnd_8228962 < baseStart_8228962 := by decide
  rcases family_descends (prefixWord ++ tailWord_8228962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8228995 : List Nat := [1, 1, 1, 3, 3, 3, 2, 3, 1, 3, 2]
def baseStart_8228995 : Nat := 118140960795 + 8228995 * 2 ^ 59
def prefixEnd_8228995 : Nat := 4983230072969 + 3 ^ 40 * 8228995 * 2
def baseEnd_8228995 : Nat := 4225429738445136752918047

theorem tailTrace_8228995 : CollatzResearch.WordTrace tailWord_8228995 prefixEnd_8228995 4225429738445136752918047 := by
  unfold tailWord_8228995
  simp only [CollatzResearch.WordTrace]
  refine ⟨300136104822763990301464439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200090736548509326867642959 300136104822763990301464439)
  ·
    refine ⟨450204157234145985452196659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300136104822763990301464439 450204157234145985452196659)
    ·
      refine ⟨675306235851218978178294989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 450204157234145985452196659 675306235851218978178294989)
      ·
        refine ⟨253239838444207116816860621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 675306235851218978178294989 253239838444207116816860621)
        ·
          refine ⟨94964939416577668806322733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 253239838444207116816860621 94964939416577668806322733)
          ·
            refine ⟨35611852281216625802371025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94964939416577668806322733 35611852281216625802371025)
            ·
              refine ⟨26708889210912469351778269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35611852281216625802371025 26708889210912469351778269)
              ·
                refine ⟨10015833454092176006916851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26708889210912469351778269 10015833454092176006916851)
                ·
                  refine ⟨15023750181138264010375277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10015833454092176006916851 15023750181138264010375277)
                  ·
                    refine ⟨5633906317926849003890729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15023750181138264010375277 5633906317926849003890729)
                    ·
                      refine ⟨4225429738445136752918047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5633906317926849003890729 4225429738445136752918047)
                      ·
                        rfl

theorem cell23_8228995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 3, 1, 3, 2].length) (baseStart_8228995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8228995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8228995 prefixEnd_8228995 := by exact prefixLift 8228995
  have htrace : WordTrace (prefixWord ++ tailWord_8228995) baseStart_8228995 baseEnd_8228995 := by
    simpa [prefixWord, tailWord_8228995, baseEnd_8228995] using wordTrace_append hprefix tailTrace_8228995
  have hstable : (prefixWord ++ tailWord_8228995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8228995).length < 2 ^ (prefixWord ++ tailWord_8228995).sum := by decide
  have hdescent : baseEnd_8228995 < baseStart_8228995 := by decide
  rcases family_descends (prefixWord ++ tailWord_8228995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8229011 : List Nat := [1, 1, 1, 2, 1, 2, 3, 3, 2, 4, 3]
def baseStart_8229011 : Nat := 118140960795 + 8229011 * 2 ^ 59
def prefixEnd_8229011 : Nat := 4983230072969 + 3 ^ 40 * 8229011 * 2
def baseEnd_8229011 : Nat := 4225437954135608690317973

theorem tailTrace_8229011 : CollatzResearch.WordTrace tailWord_8229011 prefixEnd_8229011 4225437954135608690317973 := by
  unfold tailWord_8229011
  simp only [CollatzResearch.WordTrace]
  refine ⟨300136688390706025034046887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200091125593804016689364591 300136688390706025034046887)
  ·
    refine ⟨450205032586059037551070331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300136688390706025034046887 450205032586059037551070331)
    ·
      refine ⟨675307548879088556326605497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 450205032586059037551070331 675307548879088556326605497)
      ·
        refine ⟨506480661659316417244954123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 675307548879088556326605497 506480661659316417244954123)
        ·
          refine ⟨759720992488974625867431185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 506480661659316417244954123 759720992488974625867431185)
          ·
            refine ⟨569790744366730969400573389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 759720992488974625867431185 569790744366730969400573389)
            ·
              refine ⟨213671529137524113525215021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 569790744366730969400573389 213671529137524113525215021)
              ·
                refine ⟨80126823426571542571955633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 213671529137524113525215021 80126823426571542571955633)
                ·
                  refine ⟨60095117569928656928966725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80126823426571542571955633 60095117569928656928966725)
                  ·
                    refine ⟨11267834544361623174181261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60095117569928656928966725 11267834544361623174181261)
                    ·
                      refine ⟨4225437954135608690317973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11267834544361623174181261 4225437954135608690317973)
                      ·
                        rfl

theorem cell23_8229011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 3, 2, 4, 3].length) (baseStart_8229011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8229011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8229011 prefixEnd_8229011 := by exact prefixLift 8229011
  have htrace : WordTrace (prefixWord ++ tailWord_8229011) baseStart_8229011 baseEnd_8229011 := by
    simpa [prefixWord, tailWord_8229011, baseEnd_8229011] using wordTrace_append hprefix tailTrace_8229011
  have hstable : (prefixWord ++ tailWord_8229011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8229011).length < 2 ^ (prefixWord ++ tailWord_8229011).sum := by decide
  have hdescent : baseEnd_8229011 < baseStart_8229011 := by decide
  rcases family_descends (prefixWord ++ tailWord_8229011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8229048 : List Nat := [2, 1, 2, 1, 2, 1, 4, 5, 5]
def baseStart_8229048 : Nat := 118140960795 + 8229048 * 2 ^ 59
def prefixEnd_8229048 : Nat := 4983230072969 + 3 ^ 40 * 8229048 * 2
def baseEnd_8229048 : Nat := 469495216991091671728367

theorem tailTrace_8229048 : CollatzResearch.WordTrace tailWord_8229048 prefixEnd_8229048 469495216991091671728367 := by
  unfold tailWord_8229048
  simp only [CollatzResearch.WordTrace]
  refine ⟨150069018945785990176571899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200092025261047986902095865 150069018945785990176571899)
  ·
    refine ⟨225103528418678985264857849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150069018945785990176571899 225103528418678985264857849)
    ·
      refine ⟨168827646314009238948643387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225103528418678985264857849 168827646314009238948643387)
      ·
        refine ⟨253241469471013858422965081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168827646314009238948643387 253241469471013858422965081)
        ·
          refine ⟨189931102103260393817223811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 253241469471013858422965081 189931102103260393817223811)
          ·
            refine ⟨284896653154890590725835717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189931102103260393817223811 284896653154890590725835717)
            ·
              refine ⟨53418122466541985761094197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 284896653154890590725835717 53418122466541985761094197)
              ·
                refine ⟨5007948981238311165102581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53418122466541985761094197 5007948981238311165102581)
                ·
                  refine ⟨469495216991091671728367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5007948981238311165102581 469495216991091671728367)
                  ·
                    rfl

theorem cell23_8229048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 5, 5].length) (baseStart_8229048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8229048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8229048 prefixEnd_8229048 := by exact prefixLift 8229048
  have htrace : WordTrace (prefixWord ++ tailWord_8229048) baseStart_8229048 baseEnd_8229048 := by
    simpa [prefixWord, tailWord_8229048, baseEnd_8229048] using wordTrace_append hprefix tailTrace_8229048
  have hstable : (prefixWord ++ tailWord_8229048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8229048).length < 2 ^ (prefixWord ++ tailWord_8229048).sum := by decide
  have hdescent : baseEnd_8229048 < baseStart_8229048 := by decide
  rcases family_descends (prefixWord ++ tailWord_8229048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8229071 : List Nat := [1, 1, 2, 1, 1, 3, 3, 3, 1, 2, 5]
def baseStart_8229071 : Nat := 118140960795 + 8229071 * 2 ^ 59
def prefixEnd_8229071 : Nat := 4983230072969 + 3 ^ 40 * 8229071 * 2
def baseEnd_8229071 : Nat := 4225468762974878455567697

theorem tailTrace_8229071 : CollatzResearch.WordTrace tailWord_8229071 prefixEnd_8229071 4225468762974878455567697 := by
  unfold tailWord_8229071
  simp only [CollatzResearch.WordTrace]
  refine ⟨300138876770488655281231067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200092584513659103520820711 300138876770488655281231067)
  ·
    refine ⟨450208315155732982921846601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300138876770488655281231067 450208315155732982921846601)
    ·
      refine ⟨337656236366799737191384951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 450208315155732982921846601 337656236366799737191384951)
      ·
        refine ⟨506484354550199605787077427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337656236366799737191384951 506484354550199605787077427)
        ·
          refine ⟨759726531825299408680616141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 506484354550199605787077427 759726531825299408680616141)
          ·
            refine ⟨284897449434487278255231053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 759726531825299408680616141 284897449434487278255231053)
            ·
              refine ⟨106836543537932729345711645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 284897449434487278255231053 106836543537932729345711645)
              ·
                refine ⟨40063703826724773504641867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106836543537932729345711645 40063703826724773504641867)
                ·
                  refine ⟨60095555740087160256962801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40063703826724773504641867 60095555740087160256962801)
                  ·
                    refine ⟨45071666805065370192722101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60095555740087160256962801 45071666805065370192722101)
                    ·
                      refine ⟨4225468762974878455567697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45071666805065370192722101 4225468762974878455567697)
                      ·
                        rfl

theorem cell23_8229071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 3, 1, 2, 5].length) (baseStart_8229071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8229071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8229071 prefixEnd_8229071 := by exact prefixLift 8229071
  have htrace : WordTrace (prefixWord ++ tailWord_8229071) baseStart_8229071 baseEnd_8229071 := by
    simpa [prefixWord, tailWord_8229071, baseEnd_8229071] using wordTrace_append hprefix tailTrace_8229071
  have hstable : (prefixWord ++ tailWord_8229071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8229071).length < 2 ^ (prefixWord ++ tailWord_8229071).sum := by decide
  have hdescent : baseEnd_8229071 < baseStart_8229071 := by decide
  rcases family_descends (prefixWord ++ tailWord_8229071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8229095 : List Nat := [1, 1, 5, 3, 1, 1, 3, 1, 2, 5]
def baseStart_8229095 : Nat := 118140960795 + 8229095 * 2 ^ 59
def prefixEnd_8229095 : Nat := 4983230072969 + 3 ^ 40 * 8229095 * 2
def baseEnd_8229095 : Nat := 1408493695503528787222529

theorem tailTrace_8229095 : CollatzResearch.WordTrace tailWord_8229095 prefixEnd_8229095 1408493695503528787222529 := by
  unfold tailWord_8229095
  simp only [CollatzResearch.WordTrace]
  refine ⟨300139752122401707380104739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200093168081601138253403159 300139752122401707380104739)
  ·
    refine ⟨450209628183602561070157109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300139752122401707380104739 450209628183602561070157109)
    ·
      refine ⟨42207152642212740100327229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 450209628183602561070157109 42207152642212740100327229)
      ·
        refine ⟨15827682240829777537622711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42207152642212740100327229 15827682240829777537622711)
        ·
          refine ⟨23741523361244666306434067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15827682240829777537622711 23741523361244666306434067)
          ·
            refine ⟨35612285041866999459651101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23741523361244666306434067 35612285041866999459651101)
            ·
              refine ⟨13354606890700124797369163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35612285041866999459651101 13354606890700124797369163)
              ·
                refine ⟨20031910336050187196053745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13354606890700124797369163 20031910336050187196053745)
                ·
                  refine ⟨15023932752037640397040309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20031910336050187196053745 15023932752037640397040309)
                  ·
                    refine ⟨1408493695503528787222529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15023932752037640397040309 1408493695503528787222529)
                    ·
                      rfl

theorem cell23_8229095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 3, 1, 2, 5].length) (baseStart_8229095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8229095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8229095 prefixEnd_8229095 := by exact prefixLift 8229095
  have htrace : WordTrace (prefixWord ++ tailWord_8229095) baseStart_8229095 baseEnd_8229095 := by
    simpa [prefixWord, tailWord_8229095, baseEnd_8229095] using wordTrace_append hprefix tailTrace_8229095
  have hstable : (prefixWord ++ tailWord_8229095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8229095).length < 2 ^ (prefixWord ++ tailWord_8229095).sum := by decide
  have hdescent : baseEnd_8229095 < baseStart_8229095 := by decide
  rcases family_descends (prefixWord ++ tailWord_8229095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8229098 : List Nat := [3, 1, 3, 1, 1, 2, 3, 1, 1, 3, 4]
def baseStart_8229098 : Nat := 118140960795 + 8229098 * 2 ^ 59
def prefixEnd_8229098 : Nat := 4983230072969 + 3 ^ 40 * 8229098 * 2
def baseEnd_8229098 : Nat := 4225482626952549849930073

theorem tailTrace_8229098 : CollatzResearch.WordTrace tailWord_8229098 prefixEnd_8229098 4225482626952549849930073 := by
  unfold tailWord_8229098
  simp only [CollatzResearch.WordTrace]
  refine ⟨75034965385347709723115987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200093241027593892594975965 75034965385347709723115987)
  ·
    refine ⟨112552448078021564584673981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75034965385347709723115987 112552448078021564584673981)
    ·
      refine ⟨42207168029258086719252743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112552448078021564584673981 42207168029258086719252743)
      ·
        refine ⟨63310752043887130078879115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42207168029258086719252743 63310752043887130078879115)
        ·
          refine ⟨94966128065830695118318673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63310752043887130078879115 94966128065830695118318673)
          ·
            refine ⟨71224596049373021338739005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94966128065830695118318673 71224596049373021338739005)
            ·
              refine ⟨26709223518514883002027127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71224596049373021338739005 26709223518514883002027127)
              ·
                refine ⟨40063835277772324503040691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26709223518514883002027127 40063835277772324503040691)
                ·
                  refine ⟨60095752916658486754561037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40063835277772324503040691 60095752916658486754561037)
                  ·
                    refine ⟨22535907343746932532960389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60095752916658486754561037 22535907343746932532960389)
                    ·
                      refine ⟨4225482626952549849930073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22535907343746932532960389 4225482626952549849930073)
                      ·
                        rfl

theorem cell23_8229098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 1, 1, 3, 4].length) (baseStart_8229098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8229098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8229098 prefixEnd_8229098 := by exact prefixLift 8229098
  have htrace : WordTrace (prefixWord ++ tailWord_8229098) baseStart_8229098 baseEnd_8229098 := by
    simpa [prefixWord, tailWord_8229098, baseEnd_8229098] using wordTrace_append hprefix tailTrace_8229098
  have hstable : (prefixWord ++ tailWord_8229098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8229098).length < 2 ^ (prefixWord ++ tailWord_8229098).sum := by decide
  have hdescent : baseEnd_8229098 < baseStart_8229098 := by decide
  rcases family_descends (prefixWord ++ tailWord_8229098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8229148 : List Nat := [2, 2, 3, 1, 1, 1, 1, 1, 1, 7, 3]
def baseStart_8229148 : Nat := 118140960795 + 8229148 * 2 ^ 59
def prefixEnd_8229148 : Nat := 4983230072969 + 3 ^ 40 * 8229148 * 2
def baseEnd_8229148 : Nat := 4225508300985274654304843

theorem tailTrace_8229148 : CollatzResearch.WordTrace tailWord_8229148 prefixEnd_8229148 4225508300985274654304843 := by
  unfold tailWord_8229148
  simp only [CollatzResearch.WordTrace]
  refine ⟨150070842595604848715892049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200094456794139798287856065 150070842595604848715892049)
  ·
    refine ⟨112553131946703636536919037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150070842595604848715892049 112553131946703636536919037)
    ·
      refine ⟨42207424480013863701344639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112553131946703636536919037 42207424480013863701344639)
      ·
        refine ⟨63311136720020795552016959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42207424480013863701344639 63311136720020795552016959)
        ·
          refine ⟨94966705080031193328025439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63311136720020795552016959 94966705080031193328025439)
          ·
            refine ⟨142450057620046789992038159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94966705080031193328025439 142450057620046789992038159)
            ·
              refine ⟨213675086430070184988057239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142450057620046789992038159 213675086430070184988057239)
              ·
                refine ⟨320512629645105277482085859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 213675086430070184988057239 320512629645105277482085859)
                ·
                  refine ⟨480768944467657916223128789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 320512629645105277482085859 480768944467657916223128789)
                  ·
                    refine ⟨11268022135960732411479581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 480768944467657916223128789 11268022135960732411479581)
                    ·
                      refine ⟨4225508300985274654304843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11268022135960732411479581 4225508300985274654304843)
                      ·
                        rfl

theorem cell23_8229148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 1, 7, 3].length) (baseStart_8229148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8229148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8229148 prefixEnd_8229148 := by exact prefixLift 8229148
  have htrace : WordTrace (prefixWord ++ tailWord_8229148) baseStart_8229148 baseEnd_8229148 := by
    simpa [prefixWord, tailWord_8229148, baseEnd_8229148] using wordTrace_append hprefix tailTrace_8229148
  have hstable : (prefixWord ++ tailWord_8229148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8229148).length < 2 ^ (prefixWord ++ tailWord_8229148).sum := by decide
  have hdescent : baseEnd_8229148 < baseStart_8229148 := by decide
  rcases family_descends (prefixWord ++ tailWord_8229148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8229228 : List Nat := [2, 2, 1, 1, 6, 11]
def baseStart_8229228 : Nat := 118140960795 + 8229228 * 2 ^ 59
def prefixEnd_8229228 : Nat := 4983230072969 + 3 ^ 40 * 8229228 * 2
def baseEnd_8229228 : Nat := 17389092096451170128825

theorem tailTrace_8229228 : CollatzResearch.WordTrace tailWord_8229228 prefixEnd_8229228 17389092096451170128825 := by
  unfold tailWord_8229228
  simp only [CollatzResearch.WordTrace]
  refine ⟨150072301515459935547348169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200096402020613247396464225 150072301515459935547348169)
  ·
    refine ⟨112554226136594951660511127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150072301515459935547348169 112554226136594951660511127)
    ·
      refine ⟨168831339204892427490766691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112554226136594951660511127 168831339204892427490766691)
      ·
        refine ⟨253247008807338641236150037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168831339204892427490766691 253247008807338641236150037)
        ·
          refine ⟨11870953537843998807944533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 253247008807338641236150037 11870953537843998807944533)
          ·
            refine ⟨17389092096451170128825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 11870953537843998807944533 17389092096451170128825)
            ·
              rfl

theorem cell23_8229228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 11].length) (baseStart_8229228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8229228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8229228 prefixEnd_8229228 := by exact prefixLift 8229228
  have htrace : WordTrace (prefixWord ++ tailWord_8229228) baseStart_8229228 baseEnd_8229228 := by
    simpa [prefixWord, tailWord_8229228, baseEnd_8229228] using wordTrace_append hprefix tailTrace_8229228
  have hstable : (prefixWord ++ tailWord_8229228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8229228).length < 2 ^ (prefixWord ++ tailWord_8229228).sum := by decide
  have hdescent : baseEnd_8229228 < baseStart_8229228 := by decide
  rcases family_descends (prefixWord ++ tailWord_8229228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8229232 : List Nat := [2, 1, 1, 1, 4, 4, 2, 2, 2, 4]
def baseStart_8229232 : Nat := 118140960795 + 8229232 * 2 ^ 59
def prefixEnd_8229232 : Nat := 4983230072969 + 3 ^ 40 * 8229232 * 2
def baseEnd_8229232 : Nat := 1408517144453417441884819

theorem tailTrace_8229232 : CollatzResearch.WordTrace tailWord_8229232 prefixEnd_8229232 1408517144453417441884819 := by
  unfold tailWord_8229232
  simp only [CollatzResearch.WordTrace]
  refine ⟨150072374461452689888920975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200096499281936919851894633 150072374461452689888920975)
  ·
    refine ⟨225108561692179034833381463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150072374461452689888920975 225108561692179034833381463)
    ·
      refine ⟨337662842538268552250072195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225108561692179034833381463 337662842538268552250072195)
      ·
        refine ⟨506494263807402828375108293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337662842538268552250072195 506494263807402828375108293)
        ·
          refine ⟨94967674463888030320332805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 506494263807402828375108293 94967674463888030320332805)
          ·
            refine ⟨17806438961979005685062401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94967674463888030320332805 17806438961979005685062401)
            ·
              refine ⟨13354829221484254263796801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17806438961979005685062401 13354829221484254263796801)
              ·
                refine ⟨10016121916113190697847601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13354829221484254263796801 10016121916113190697847601)
                ·
                  refine ⟨7512091437084893023385701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10016121916113190697847601 7512091437084893023385701)
                  ·
                    refine ⟨1408517144453417441884819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7512091437084893023385701 1408517144453417441884819)
                    ·
                      rfl

theorem cell23_8229232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 2, 2, 2, 4].length) (baseStart_8229232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8229232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8229232 prefixEnd_8229232 := by exact prefixLift 8229232
  have htrace : WordTrace (prefixWord ++ tailWord_8229232) baseStart_8229232 baseEnd_8229232 := by
    simpa [prefixWord, tailWord_8229232, baseEnd_8229232] using wordTrace_append hprefix tailTrace_8229232
  have hstable : (prefixWord ++ tailWord_8229232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8229232).length < 2 ^ (prefixWord ++ tailWord_8229232).sum := by decide
  have hdescent : baseEnd_8229232 < baseStart_8229232 := by decide
  rcases family_descends (prefixWord ++ tailWord_8229232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8229245 : List Nat := [1, 4, 1, 1, 2, 5, 1, 8]
def baseStart_8229245 : Nat := 118140960795 + 8229245 * 2 ^ 59
def prefixEnd_8229245 : Nat := 4983230072969 + 3 ^ 40 * 8229245 * 2
def baseEnd_8229245 : Nat := 156502152170694843510811

theorem tailTrace_8229245 : CollatzResearch.WordTrace tailWord_8229245 prefixEnd_8229245 156502152170694843510811 := by
  unfold tailWord_8229245
  simp only [CollatzResearch.WordTrace]
  refine ⟨300145223071858282998065189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200096815381238855332043459 300145223071858282998065189)
  ·
    refine ⟨56277229325973428062137223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 300145223071858282998065189 56277229325973428062137223)
    ·
      refine ⟨84415843988960142093205835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56277229325973428062137223 84415843988960142093205835)
      ·
        refine ⟨126623765983440213139808753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84415843988960142093205835 126623765983440213139808753)
        ·
          refine ⟨94967824487580159854856565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126623765983440213139808753 94967824487580159854856565)
          ·
            refine ⟨8903233545710639986392803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 94967824487580159854856565 8903233545710639986392803)
            ·
              refine ⟨13354850318565959979589205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8903233545710639986392803 13354850318565959979589205)
              ·
                refine ⟨156502152170694843510811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13354850318565959979589205 156502152170694843510811)
                ·
                  rfl

theorem cell23_8229245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 1, 8].length) (baseStart_8229245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8229245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8229245 prefixEnd_8229245 := by exact prefixLift 8229245
  have htrace : WordTrace (prefixWord ++ tailWord_8229245) baseStart_8229245 baseEnd_8229245 := by
    simpa [prefixWord, tailWord_8229245, baseEnd_8229245] using wordTrace_append hprefix tailTrace_8229245
  have hstable : (prefixWord ++ tailWord_8229245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8229245).length < 2 ^ (prefixWord ++ tailWord_8229245).sum := by decide
  have hdescent : baseEnd_8229245 < baseStart_8229245 := by decide
  rcases family_descends (prefixWord ++ tailWord_8229245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8229262 : List Nat := [4, 1, 1, 4, 1, 2, 3, 7]
def baseStart_8229262 : Nat := 118140960795 + 8229262 * 2 ^ 59
def prefixEnd_8229262 : Nat := 4983230072969 + 3 ^ 40 * 8229262 * 2
def baseEnd_8229262 : Nat := 156502475473329155862197

theorem tailTrace_8229262 : CollatzResearch.WordTrace tailWord_8229262 prefixEnd_8229262 156502475473329155862197 := by
  unfold tailWord_8229262
  simp only [CollatzResearch.WordTrace]
  refine ⟨37518230389099586862679255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200097228741864463267622693 37518230389099586862679255)
  ·
    refine ⟨56277345583649380294018883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37518230389099586862679255 56277345583649380294018883)
    ·
      refine ⟨84416018375474070441028325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56277345583649380294018883 84416018375474070441028325)
      ·
        refine ⟨15828003445401388207692811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84416018375474070441028325 15828003445401388207692811)
        ·
          refine ⟨23742005168102082311539217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15828003445401388207692811 23742005168102082311539217)
          ·
            refine ⟨17806503876076561733654413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23742005168102082311539217 17806503876076561733654413)
            ·
              refine ⟨6677438953528710650120405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17806503876076561733654413 6677438953528710650120405)
              ·
                refine ⟨156502475473329155862197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6677438953528710650120405 156502475473329155862197)
                ·
                  rfl

theorem cell23_8229262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 3, 7].length) (baseStart_8229262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8229262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8229262 prefixEnd_8229262 := by exact prefixLift 8229262
  have htrace : WordTrace (prefixWord ++ tailWord_8229262) baseStart_8229262 baseEnd_8229262 := by
    simpa [prefixWord, tailWord_8229262, baseEnd_8229262] using wordTrace_append hprefix tailTrace_8229262
  have hstable : (prefixWord ++ tailWord_8229262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8229262).length < 2 ^ (prefixWord ++ tailWord_8229262).sum := by decide
  have hdescent : baseEnd_8229262 < baseStart_8229262 := by decide
  rcases family_descends (prefixWord ++ tailWord_8229262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8229270 : List Nat := [5, 3, 1, 2, 1, 2, 2, 1, 1, 5]
def baseStart_8229270 : Nat := 118140960795 + 8229270 * 2 ^ 59
def prefixEnd_8229270 : Nat := 4983230072969 + 3 ^ 40 * 8229270 * 2
def baseEnd_8229270 : Nat := 1408523648541707725659761

theorem tailTrace_8229270 : CollatzResearch.WordTrace tailWord_8229270 prefixEnd_8229270 1408523648541707725659761 := by
  unfold tailWord_8229270
  simp only [CollatzResearch.WordTrace]
  refine ⟨18759133431047982016732829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 200097423264511808178483509 18759133431047982016732829)
  ·
    refine ⟨7034675036642993256274811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18759133431047982016732829 7034675036642993256274811)
    ·
      refine ⟨10552012554964489884412217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7034675036642993256274811 10552012554964489884412217)
      ·
        refine ⟨7914009416223367413309163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10552012554964489884412217 7914009416223367413309163)
        ·
          refine ⟨11871014124335051119963745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7914009416223367413309163 11871014124335051119963745)
          ·
            refine ⟨8903260593251288339972809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11871014124335051119963745 8903260593251288339972809)
            ·
              refine ⟨6677445444938466254979607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8903260593251288339972809 6677445444938466254979607)
              ·
                refine ⟨10016168167407699382469411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6677445444938466254979607 10016168167407699382469411)
                ·
                  refine ⟨15024252251111549073704117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10016168167407699382469411 15024252251111549073704117)
                  ·
                    refine ⟨1408523648541707725659761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15024252251111549073704117 1408523648541707725659761)
                    ·
                      rfl

theorem cell23_8229270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_8229270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8229270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8229270 prefixEnd_8229270 := by exact prefixLift 8229270
  have htrace : WordTrace (prefixWord ++ tailWord_8229270) baseStart_8229270 baseEnd_8229270 := by
    simpa [prefixWord, tailWord_8229270, baseEnd_8229270] using wordTrace_append hprefix tailTrace_8229270
  have hstable : (prefixWord ++ tailWord_8229270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8229270).length < 2 ^ (prefixWord ++ tailWord_8229270).sum := by decide
  have hdescent : baseEnd_8229270 < baseStart_8229270 := by decide
  rcases family_descends (prefixWord ++ tailWord_8229270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8229272 : List Nat := [2, 1, 2, 5, 1, 1, 2, 2, 1, 3, 3]
def baseStart_8229272 : Nat := 118140960795 + 8229272 * 2 ^ 59
def prefixEnd_8229272 : Nat := 4983230072969 + 3 ^ 40 * 8229272 * 2
def baseEnd_8229272 : Nat := 4225571972586432169154273

theorem tailTrace_8229272 : CollatzResearch.WordTrace tailWord_8229272 prefixEnd_8229272 4225571972586432169154273 := by
  unfold tailWord_8229272
  simp only [CollatzResearch.WordTrace]
  refine ⟨150073103921380233304649035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200097471895173644406198713 150073103921380233304649035)
  ·
    refine ⟨225109655882070349956973553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150073103921380233304649035 225109655882070349956973553)
    ·
      refine ⟨168832241911552762467730165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225109655882070349956973553 168832241911552762467730165)
      ·
        refine ⟨15828022679208071481349703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 168832241911552762467730165 15828022679208071481349703)
        ·
          refine ⟨23742034018812107222024555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15828022679208071481349703 23742034018812107222024555)
          ·
            refine ⟨35613051028218160833036833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23742034018812107222024555 35613051028218160833036833)
            ·
              refine ⟨26709788271163620624777625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35613051028218160833036833 26709788271163620624777625)
              ·
                refine ⟨20032341203372715468583219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26709788271163620624777625 20032341203372715468583219)
                ·
                  refine ⟨30048511805059073202874829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20032341203372715468583219 30048511805059073202874829)
                  ·
                    refine ⟨11268191926897152451078061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30048511805059073202874829 11268191926897152451078061)
                    ·
                      refine ⟨4225571972586432169154273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11268191926897152451078061 4225571972586432169154273)
                      ·
                        rfl

theorem cell23_8229272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_8229272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8229272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8229272 prefixEnd_8229272 := by exact prefixLift 8229272
  have htrace : WordTrace (prefixWord ++ tailWord_8229272) baseStart_8229272 baseEnd_8229272 := by
    simpa [prefixWord, tailWord_8229272, baseEnd_8229272] using wordTrace_append hprefix tailTrace_8229272
  have hstable : (prefixWord ++ tailWord_8229272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8229272).length < 2 ^ (prefixWord ++ tailWord_8229272).sum := by decide
  have hdescent : baseEnd_8229272 < baseStart_8229272 := by decide
  rcases family_descends (prefixWord ++ tailWord_8229272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8229290 : List Nat := [3, 1, 6, 1, 1, 1, 2, 1, 3, 2, 2]
def baseStart_8229290 : Nat := 118140960795 + 8229290 * 2 ^ 59
def prefixEnd_8229290 : Nat := 4983230072969 + 3 ^ 40 * 8229290 * 2
def baseEnd_8229290 : Nat := 4225581215238213098729191

theorem tailTrace_8229290 : CollatzResearch.WordTrace tailWord_8229290 prefixEnd_8229290 4225581215238213098729191 := by
  unfold tailWord_8229290
  simp only [CollatzResearch.WordTrace]
  refine ⟨75036716089173813920863331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200097909571130170455635549 75036716089173813920863331)
  ·
    refine ⟨112555074133760720881294997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75036716089173813920863331 112555074133760720881294997)
    ·
      refine ⟨5276019100020033791310703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 112555074133760720881294997 5276019100020033791310703)
      ·
        refine ⟨7914028650030050686966055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5276019100020033791310703 7914028650030050686966055)
        ·
          refine ⟨11871042975045076030449083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7914028650030050686966055 11871042975045076030449083)
          ·
            refine ⟨17806564462567614045673625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11871042975045076030449083 17806564462567614045673625)
            ·
              refine ⟨13354923346925710534255219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17806564462567614045673625 13354923346925710534255219)
              ·
                refine ⟨20032385020388565801382829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13354923346925710534255219 20032385020388565801382829)
                ·
                  refine ⟨7512144382645712175518561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20032385020388565801382829 7512144382645712175518561)
                  ·
                    refine ⟨5634108286984284131638921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7512144382645712175518561 5634108286984284131638921)
                    ·
                      refine ⟨4225581215238213098729191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5634108286984284131638921 4225581215238213098729191)
                      ·
                        rfl

theorem cell23_8229290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_8229290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8229290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8229290 prefixEnd_8229290 := by exact prefixLift 8229290
  have htrace : WordTrace (prefixWord ++ tailWord_8229290) baseStart_8229290 baseEnd_8229290 := by
    simpa [prefixWord, tailWord_8229290, baseEnd_8229290] using wordTrace_append hprefix tailTrace_8229290
  have hstable : (prefixWord ++ tailWord_8229290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8229290).length < 2 ^ (prefixWord ++ tailWord_8229290).sum := by decide
  have hdescent : baseEnd_8229290 < baseStart_8229290 := by decide
  rcases family_descends (prefixWord ++ tailWord_8229290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8229295 : List Nat := [1, 1, 2, 1, 2, 2, 1, 1, 2, 8, 2]
def baseStart_8229295 : Nat := 118140960795 + 8229295 * 2 ^ 59
def prefixEnd_8229295 : Nat := 4983230072969 + 3 ^ 40 * 8229295 * 2
def baseEnd_8229295 : Nat := 4225583782641485579166667

theorem tailTrace_8229295 : CollatzResearch.WordTrace tailWord_8229295 prefixEnd_8229295 4225583782641485579166667 := by
  unfold tailWord_8229295
  simp only [CollatzResearch.WordTrace]
  refine ⟨300147046721677141537385339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200098031147784761024923559 300147046721677141537385339)
  ·
    refine ⟨450220570082515712306078009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300147046721677141537385339 450220570082515712306078009)
    ·
      refine ⟨337665427561886784229558507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 450220570082515712306078009 337665427561886784229558507)
      ·
        refine ⟨506498141342830176344337761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337665427561886784229558507 506498141342830176344337761)
        ·
          refine ⟨379873606007122632258253321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 506498141342830176344337761 379873606007122632258253321)
          ·
            refine ⟨284905204505341974193689991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 379873606007122632258253321 284905204505341974193689991)
            ·
              refine ⟨427357806758012961290534987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 284905204505341974193689991 427357806758012961290534987)
              ·
                refine ⟨641036710137019441935802481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 427357806758012961290534987 641036710137019441935802481)
                ·
                  refine ⟨480777532602764581451851861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 641036710137019441935802481 480777532602764581451851861)
                  ·
                    refine ⟨5634111710188647438888889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 480777532602764581451851861 5634111710188647438888889)
                    ·
                      refine ⟨4225583782641485579166667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5634111710188647438888889 4225583782641485579166667)
                      ·
                        rfl

theorem cell23_8229295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 8, 2].length) (baseStart_8229295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8229295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8229295 prefixEnd_8229295 := by exact prefixLift 8229295
  have htrace : WordTrace (prefixWord ++ tailWord_8229295) baseStart_8229295 baseEnd_8229295 := by
    simpa [prefixWord, tailWord_8229295, baseEnd_8229295] using wordTrace_append hprefix tailTrace_8229295
  have hstable : (prefixWord ++ tailWord_8229295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8229295).length < 2 ^ (prefixWord ++ tailWord_8229295).sum := by decide
  have hdescent : baseEnd_8229295 < baseStart_8229295 := by decide
  rcases family_descends (prefixWord ++ tailWord_8229295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8229305 : List Nat := [1, 2, 1, 4, 3, 1, 2, 1, 2, 6]
def baseStart_8229305 : Nat := 118140960795 + 8229305 * 2 ^ 59
def prefixEnd_8229305 : Nat := 4983230072969 + 3 ^ 40 * 8229305 * 2
def baseEnd_8229305 : Nat := 1408529639149343513347207

theorem tailTrace_8229305 : CollatzResearch.WordTrace tailWord_8229305 prefixEnd_8229305 1408529639149343513347207 := by
  unfold tailWord_8229305
  simp only [CollatzResearch.WordTrace]
  refine ⟨300147411451640913245249369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200098274301093942163499579 300147411451640913245249369)
  ·
    refine ⟨225110558588730684933937027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300147411451640913245249369 225110558588730684933937027)
    ·
      refine ⟨337665837883096027400905541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225110558588730684933937027 337665837883096027400905541)
      ·
        refine ⟨63312344603080505137669789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 337665837883096027400905541 63312344603080505137669789)
        ·
          refine ⟨23742129226155189426626171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63312344603080505137669789 23742129226155189426626171)
          ·
            refine ⟨35613193839232784139939257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23742129226155189426626171 35613193839232784139939257)
            ·
              refine ⟨26709895379424588104954443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35613193839232784139939257 26709895379424588104954443)
              ·
                refine ⟨40064843069136882157431665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26709895379424588104954443 40064843069136882157431665)
                ·
                  refine ⟨30048632301852661618073749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40064843069136882157431665 30048632301852661618073749)
                  ·
                    refine ⟨1408529639149343513347207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30048632301852661618073749 1408529639149343513347207)
                    ·
                      rfl

theorem cell23_8229305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 1, 2, 6].length) (baseStart_8229305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8229305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8229305 prefixEnd_8229305 := by exact prefixLift 8229305
  have htrace : WordTrace (prefixWord ++ tailWord_8229305) baseStart_8229305 baseEnd_8229305 := by
    simpa [prefixWord, tailWord_8229305, baseEnd_8229305] using wordTrace_append hprefix tailTrace_8229305
  have hstable : (prefixWord ++ tailWord_8229305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8229305).length < 2 ^ (prefixWord ++ tailWord_8229305).sum := by decide
  have hdescent : baseEnd_8229305 < baseStart_8229305 := by decide
  rcases family_descends (prefixWord ++ tailWord_8229305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8229313 : List Nat := [1, 2, 7, 1, 2, 1, 2, 7]
def baseStart_8229313 : Nat := 118140960795 + 8229313 * 2 ^ 59
def prefixEnd_8229313 : Nat := 4983230072969 + 3 ^ 40 * 8229313 * 2
def baseEnd_8229313 : Nat := 156503445381232092916355

theorem tailTrace_8229313 : CollatzResearch.WordTrace tailWord_8229313 prefixEnd_8229313 156503445381232092916355 := by
  unfold tailWord_8229313
  simp only [CollatzResearch.WordTrace]
  refine ⟨300147703235611930611540593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200098468823741287074360395 300147703235611930611540593)
  ·
    refine ⟨225110777426708947958655445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300147703235611930611540593 225110777426708947958655445)
    ·
      refine ⟨5276033845938490967780987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 225110777426708947958655445 5276033845938490967780987)
      ·
        refine ⟨7914050768907736451671481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5276033845938490967780987 7914050768907736451671481)
        ·
          refine ⟨5935538076680802338753611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7914050768907736451671481 5935538076680802338753611)
          ·
            refine ⟨8903307115021203508130417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5935538076680802338753611 8903307115021203508130417)
            ·
              refine ⟨6677480336265902631097813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8903307115021203508130417 6677480336265902631097813)
              ·
                refine ⟨156503445381232092916355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6677480336265902631097813 156503445381232092916355)
                ·
                  rfl

theorem cell23_8229313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 2, 7].length) (baseStart_8229313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8229313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8229313 prefixEnd_8229313 := by exact prefixLift 8229313
  have htrace : WordTrace (prefixWord ++ tailWord_8229313) baseStart_8229313 baseEnd_8229313 := by
    simpa [prefixWord, tailWord_8229313, baseEnd_8229313] using wordTrace_append hprefix tailTrace_8229313
  have hstable : (prefixWord ++ tailWord_8229313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8229313).length < 2 ^ (prefixWord ++ tailWord_8229313).sum := by decide
  have hdescent : baseEnd_8229313 < baseStart_8229313 := by decide
  rcases family_descends (prefixWord ++ tailWord_8229313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8229328 : List Nat := [2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 7]
def baseStart_8229328 : Nat := 118140960795 + 8229328 * 2 ^ 59
def prefixEnd_8229328 : Nat := 4983230072969 + 3 ^ 40 * 8229328 * 2
def baseEnd_8229328 : Nat := 4225600727503083950054015

theorem tailTrace_8229328 : CollatzResearch.WordTrace tailWord_8229328 prefixEnd_8229328 4225600727503083950054015 := by
  unfold tailWord_8229328
  simp only [CollatzResearch.WordTrace]
  refine ⟨150074125165278794086668319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200098833553705058782224425 150074125165278794086668319)
  ·
    refine ⟨225111187747918191130002479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150074125165278794086668319 225111187747918191130002479)
    ·
      refine ⟨337666781621877286695003719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225111187747918191130002479 337666781621877286695003719)
      ·
        refine ⟨506500172432815930042505579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337666781621877286695003719 506500172432815930042505579)
        ·
          refine ⟨759750258649223895063758369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 506500172432815930042505579 759750258649223895063758369)
          ·
            refine ⟨569812693986917921297818777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 759750258649223895063758369 569812693986917921297818777)
            ·
              refine ⟨427359520490188440973364083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 569812693986917921297818777 427359520490188440973364083)
              ·
                refine ⟨641039280735282661460046125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 427359520490188440973364083 641039280735282661460046125)
                ·
                  refine ⟨240389730275730998047517297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 641039280735282661460046125 240389730275730998047517297)
                  ·
                    refine ⟨180292297706798248535637973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 240389730275730998047517297 180292297706798248535637973)
                    ·
                      refine ⟨4225600727503083950054015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 180292297706798248535637973 4225600727503083950054015)
                      ·
                        rfl

theorem cell23_8229328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 7].length) (baseStart_8229328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8229328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8229328 prefixEnd_8229328 := by exact prefixLift 8229328
  have htrace : WordTrace (prefixWord ++ tailWord_8229328) baseStart_8229328 baseEnd_8229328 := by
    simpa [prefixWord, tailWord_8229328, baseEnd_8229328] using wordTrace_append hprefix tailTrace_8229328
  have hstable : (prefixWord ++ tailWord_8229328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8229328).length < 2 ^ (prefixWord ++ tailWord_8229328).sum := by decide
  have hdescent : baseEnd_8229328 < baseStart_8229328 := by decide
  rcases family_descends (prefixWord ++ tailWord_8229328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8229332 : List Nat := [2, 4, 1, 2, 2, 2, 1, 1, 2, 1, 5]
def baseStart_8229332 : Nat := 118140960795 + 8229332 * 2 ^ 59
def prefixEnd_8229332 : Nat := 4983230072969 + 3 ^ 40 * 8229332 * 2
def baseEnd_8229332 : Nat := 4225602781425701934403997

theorem tailTrace_8229332 : CollatzResearch.WordTrace tailWord_8229332 prefixEnd_8229332 4225602781425701934403997 := by
  unfold tailWord_8229332
  simp only [CollatzResearch.WordTrace]
  refine ⟨150074198111271548428241125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200098930815028731237654833 150074198111271548428241125)
  ·
    refine ⟨28138912145863415330295211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150074198111271548428241125 28138912145863415330295211)
    ·
      refine ⟨42208368218795122995442817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28138912145863415330295211 42208368218795122995442817)
      ·
        refine ⟨31656276164096342246582113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42208368218795122995442817 31656276164096342246582113)
        ·
          refine ⟨23742207123072256684936585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31656276164096342246582113 23742207123072256684936585)
          ·
            refine ⟨17806655342304192513702439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23742207123072256684936585 17806655342304192513702439)
            ·
              refine ⟨26709983013456288770553659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17806655342304192513702439 26709983013456288770553659)
              ·
                refine ⟨40064974520184433155830489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26709983013456288770553659 40064974520184433155830489)
                ·
                  refine ⟨30048730890138324866872867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40064974520184433155830489 30048730890138324866872867)
                  ·
                    refine ⟨45073096335207487300309301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30048730890138324866872867 45073096335207487300309301)
                    ·
                      refine ⟨4225602781425701934403997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45073096335207487300309301 4225602781425701934403997)
                      ·
                        rfl

theorem cell23_8229332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_8229332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8229332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8229332 prefixEnd_8229332 := by exact prefixLift 8229332
  have htrace : WordTrace (prefixWord ++ tailWord_8229332) baseStart_8229332 baseEnd_8229332 := by
    simpa [prefixWord, tailWord_8229332, baseEnd_8229332] using wordTrace_append hprefix tailTrace_8229332
  have hstable : (prefixWord ++ tailWord_8229332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8229332).length < 2 ^ (prefixWord ++ tailWord_8229332).sum := by decide
  have hdescent : baseEnd_8229332 < baseStart_8229332 := by decide
  rcases family_descends (prefixWord ++ tailWord_8229332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8229352 : List Nat := [2, 1, 4, 1, 1, 5, 1, 1, 7]
def baseStart_8229352 : Nat := 118140960795 + 8229352 * 2 ^ 59
def prefixEnd_8229352 : Nat := 4983230072969 + 3 ^ 40 * 8229352 * 2
def baseEnd_8229352 : Nat := 469512561226532428461545

theorem tailTrace_8229352 : CollatzResearch.WordTrace tailWord_8229352 prefixEnd_8229352 469512561226532428461545 := by
  unfold tailWord_8229352
  simp only [CollatzResearch.WordTrace]
  refine ⟨150074562841235320136105155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200099417121647093514806873 150074562841235320136105155)
  ·
    refine ⟨225111844261852980204157733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150074562841235320136105155 225111844261852980204157733)
    ·
      refine ⟨42208470799097433788279575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 225111844261852980204157733 42208470799097433788279575)
      ·
        refine ⟨63312706198646150682419363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42208470799097433788279575 63312706198646150682419363)
        ·
          refine ⟨94969059297969226023629045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63312706198646150682419363 94969059297969226023629045)
          ·
            refine ⟨8903349309184614939715223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 94969059297969226023629045 8903349309184614939715223)
            ·
              refine ⟨13355023963776922409572835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8903349309184614939715223 13355023963776922409572835)
              ·
                refine ⟨20032535945665383614359253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13355023963776922409572835 20032535945665383614359253)
                ·
                  refine ⟨469512561226532428461545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20032535945665383614359253 469512561226532428461545)
                  ·
                    rfl

theorem cell23_8229352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 1, 1, 7].length) (baseStart_8229352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8229352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8229352 prefixEnd_8229352 := by exact prefixLift 8229352
  have htrace : WordTrace (prefixWord ++ tailWord_8229352) baseStart_8229352 baseEnd_8229352 := by
    simpa [prefixWord, tailWord_8229352, baseEnd_8229352] using wordTrace_append hprefix tailTrace_8229352
  have hstable : (prefixWord ++ tailWord_8229352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8229352).length < 2 ^ (prefixWord ++ tailWord_8229352).sum := by decide
  have hdescent : baseEnd_8229352 < baseStart_8229352 := by decide
  rcases family_descends (prefixWord ++ tailWord_8229352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8229402 : List Nat := [3, 1, 1, 3, 1, 1, 4, 2, 2, 1, 4]
def baseStart_8229402 : Nat := 118140960795 + 8229402 * 2 ^ 59
def prefixEnd_8229402 : Nat := 4983230072969 + 3 ^ 40 * 8229402 * 2
def baseEnd_8229402 : Nat := 4225638725071516660528675

theorem tailTrace_8229402 : CollatzResearch.WordTrace tailWord_8229402 prefixEnd_8229402 4225638725071516660528675 := by
  unfold tailWord_8229402
  simp only [CollatzResearch.WordTrace]
  refine ⟨75037737333072374702882615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200100632888192999207686973 75037737333072374702882615)
  ·
    refine ⟨112556605999608562054323923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75037737333072374702882615 112556605999608562054323923)
    ·
      refine ⟨168834908999412843081485885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112556605999608562054323923 168834908999412843081485885)
      ·
        refine ⟨63313090874779816155557207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168834908999412843081485885 63313090874779816155557207)
        ·
          refine ⟨94969636312169724233335811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63313090874779816155557207 94969636312169724233335811)
          ·
            refine ⟨142454454468254586350003717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94969636312169724233335811 142454454468254586350003717)
            ·
              refine ⟨26710210212797734940625697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 142454454468254586350003717 26710210212797734940625697)
              ·
                refine ⟨20032657659598301205469273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26710210212797734940625697 20032657659598301205469273)
                ·
                  refine ⟨15024493244698725904101955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20032657659598301205469273 15024493244698725904101955)
                  ·
                    refine ⟨22536739867048088856152933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15024493244698725904101955 22536739867048088856152933)
                    ·
                      refine ⟨4225638725071516660528675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22536739867048088856152933 4225638725071516660528675)
                      ·
                        rfl

theorem cell23_8229402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 2, 2, 1, 4].length) (baseStart_8229402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8229402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8229402 prefixEnd_8229402 := by exact prefixLift 8229402
  have htrace : WordTrace (prefixWord ++ tailWord_8229402) baseStart_8229402 baseEnd_8229402 := by
    simpa [prefixWord, tailWord_8229402, baseEnd_8229402] using wordTrace_append hprefix tailTrace_8229402
  have hstable : (prefixWord ++ tailWord_8229402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8229402).length < 2 ^ (prefixWord ++ tailWord_8229402).sum := by decide
  have hdescent : baseEnd_8229402 < baseStart_8229402 := by decide
  rcases family_descends (prefixWord ++ tailWord_8229402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8229486 : List Nat := [4, 1, 2, 2, 2, 1, 2, 2, 3, 1, 3]
def baseStart_8229486 : Nat := 118140960795 + 8229486 * 2 ^ 59
def prefixEnd_8229486 : Nat := 4983230072969 + 3 ^ 40 * 8229486 * 2
def baseEnd_8229486 : Nat := 4225681857446494331878289

theorem tailTrace_8229486 : CollatzResearch.WordTrace tailWord_8229486 prefixEnd_8229486 4225681857446494331878289 := by
  unfold tailWord_8229486
  simp only [CollatzResearch.WordTrace]
  refine ⟨37519251632998147644698539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200102675375990120771725541 37519251632998147644698539)
  ·
    refine ⟨56278877449497221467047809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37519251632998147644698539 56278877449497221467047809)
    ·
      refine ⟨42209158087122916100285857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56278877449497221467047809 42209158087122916100285857)
      ·
        refine ⟨31656868565342187075214393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42209158087122916100285857 31656868565342187075214393)
        ·
          refine ⟨23742651424006640306410795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31656868565342187075214393 23742651424006640306410795)
          ·
            refine ⟨35613977136009960459616193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23742651424006640306410795 35613977136009960459616193)
            ·
              refine ⟨26710482852007470344712145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35613977136009960459616193 26710482852007470344712145)
              ·
                refine ⟨20032862139005602758534109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26710482852007470344712145 20032862139005602758534109)
                ·
                  refine ⟨7512323302127101034450291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20032862139005602758534109 7512323302127101034450291)
                  ·
                    refine ⟨11268484953190651551675437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7512323302127101034450291 11268484953190651551675437)
                    ·
                      refine ⟨4225681857446494331878289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11268484953190651551675437 4225681857446494331878289)
                      ·
                        rfl

theorem cell23_8229486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 2, 3, 1, 3].length) (baseStart_8229486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8229486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8229486 prefixEnd_8229486 := by exact prefixLift 8229486
  have htrace : WordTrace (prefixWord ++ tailWord_8229486) baseStart_8229486 baseEnd_8229486 := by
    simpa [prefixWord, tailWord_8229486, baseEnd_8229486] using wordTrace_append hprefix tailTrace_8229486
  have hstable : (prefixWord ++ tailWord_8229486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8229486).length < 2 ^ (prefixWord ++ tailWord_8229486).sum := by decide
  have hdescent : baseEnd_8229486 < baseStart_8229486 := by decide
  rcases family_descends (prefixWord ++ tailWord_8229486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8229509 : List Nat := [1, 3, 1, 1, 4, 2, 2, 3, 1, 1, 4]
def baseStart_8229509 : Nat := 118140960795 + 8229509 * 2 ^ 59
def prefixEnd_8229509 : Nat := 4983230072969 + 3 ^ 40 * 8229509 * 2
def baseEnd_8229509 : Nat := 4225693667501547741890683

theorem tailTrace_8229509 : CollatzResearch.WordTrace tailWord_8229509 prefixEnd_8229509 4225693667501547741890683 := by
  unfold tailWord_8229509
  simp only [CollatzResearch.WordTrace]
  refine ⟨300154851942901856085675581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200103234628601237390450387 300154851942901856085675581)
  ·
    refine ⟨112558069478588196032128343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 300154851942901856085675581 112558069478588196032128343)
    ·
      refine ⟨168837104217882294048192515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112558069478588196032128343 168837104217882294048192515)
      ·
        refine ⟨253255656326823441072288773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168837104217882294048192515 253255656326823441072288773)
        ·
          refine ⟨47485435561279395201054145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 253255656326823441072288773 47485435561279395201054145)
          ·
            refine ⟨35614076670959546400790609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47485435561279395201054145 35614076670959546400790609)
            ·
              refine ⟨26710557503219659800592957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35614076670959546400790609 26710557503219659800592957)
              ·
                refine ⟨10016459063707372425222359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26710557503219659800592957 10016459063707372425222359)
                ·
                  refine ⟨15024688595561058637833539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10016459063707372425222359 15024688595561058637833539)
                  ·
                    refine ⟨22537032893341587956750309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15024688595561058637833539 22537032893341587956750309)
                    ·
                      refine ⟨4225693667501547741890683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22537032893341587956750309 4225693667501547741890683)
                      ·
                        rfl

theorem cell23_8229509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 3, 1, 1, 4].length) (baseStart_8229509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8229509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8229509 prefixEnd_8229509 := by exact prefixLift 8229509
  have htrace : WordTrace (prefixWord ++ tailWord_8229509) baseStart_8229509 baseEnd_8229509 := by
    simpa [prefixWord, tailWord_8229509, baseEnd_8229509] using wordTrace_append hprefix tailTrace_8229509
  have hstable : (prefixWord ++ tailWord_8229509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8229509).length < 2 ^ (prefixWord ++ tailWord_8229509).sum := by decide
  have hdescent : baseEnd_8229509 < baseStart_8229509 := by decide
  rcases family_descends (prefixWord ++ tailWord_8229509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8229532 : List Nat := [2, 2, 3, 2, 2, 1, 1, 10]
def baseStart_8229532 : Nat := 118140960795 + 8229532 * 2 ^ 59
def prefixEnd_8229532 : Nat := 4983230072969 + 3 ^ 40 * 8229532 * 2
def baseEnd_8229532 : Nat := 156507610279874116737151

theorem tailTrace_8229532 : CollatzResearch.WordTrace tailWord_8229532 prefixEnd_8229532 156507610279874116737151 := by
  unfold tailWord_8229532
  simp only [CollatzResearch.WordTrace]
  refine ⟨150077845410909265506881425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200103793881212354009175233 150077845410909265506881425)
  ·
    refine ⟨112558384058181949130161069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150077845410909265506881425 112558384058181949130161069)
    ·
      refine ⟨42209394021818230923810401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112558384058181949130161069 42209394021818230923810401)
      ·
        refine ⟨31657045516363673192857801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42209394021818230923810401 31657045516363673192857801)
        ·
          refine ⟨23742784137272754894643351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31657045516363673192857801 23742784137272754894643351)
          ·
            refine ⟨35614176205909132341965027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23742784137272754894643351 35614176205909132341965027)
            ·
              refine ⟨53421264308863698512947541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35614176205909132341965027 53421264308863698512947541)
              ·
                refine ⟨156507610279874116737151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 53421264308863698512947541 156507610279874116737151)
                ·
                  rfl

theorem cell23_8229532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 10].length) (baseStart_8229532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8229532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8229532 prefixEnd_8229532 := by exact prefixLift 8229532
  have htrace : WordTrace (prefixWord ++ tailWord_8229532) baseStart_8229532 baseEnd_8229532 := by
    simpa [prefixWord, tailWord_8229532, baseEnd_8229532] using wordTrace_append hprefix tailTrace_8229532
  have hstable : (prefixWord ++ tailWord_8229532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8229532).length < 2 ^ (prefixWord ++ tailWord_8229532).sum := by decide
  have hdescent : baseEnd_8229532 < baseStart_8229532 := by decide
  rcases family_descends (prefixWord ++ tailWord_8229532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8229536 : List Nat := [2, 1, 1, 4, 4, 1, 1, 3, 2, 4]
def baseStart_8229536 : Nat := 118140960795 + 8229536 * 2 ^ 59
def prefixEnd_8229536 : Nat := 4983230072969 + 3 ^ 40 * 8229536 * 2
def baseEnd_8229536 : Nat := 1408569177159739712084353

theorem tailTrace_8229536 : CollatzResearch.WordTrace tailWord_8229536 prefixEnd_8229536 1408569177159739712084353 := by
  unfold tailWord_8229536
  simp only [CollatzResearch.WordTrace]
  refine ⟨150077918356902019848454231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200103891142536026464605641 150077918356902019848454231)
  ·
    refine ⟨225116877535353029772681347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150077918356902019848454231 225116877535353029772681347)
    ·
      refine ⟨337675316303029544659022021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225116877535353029772681347 337675316303029544659022021)
      ·
        refine ⟨63314121806818039623566629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 337675316303029544659022021 63314121806818039623566629)
        ·
          refine ⟨11871397838778382429418743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63314121806818039623566629 11871397838778382429418743)
          ·
            refine ⟨17807096758167573644128115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11871397838778382429418743 17807096758167573644128115)
            ·
              refine ⟨26710645137251360466192173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17807096758167573644128115 26710645137251360466192173)
              ·
                refine ⟨10016491926469260174822065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26710645137251360466192173 10016491926469260174822065)
                ·
                  refine ⟨7512368944851945131116549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10016491926469260174822065 7512368944851945131116549)
                  ·
                    refine ⟨1408569177159739712084353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7512368944851945131116549 1408569177159739712084353)
                    ·
                      rfl

theorem cell23_8229536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 3, 2, 4].length) (baseStart_8229536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8229536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8229536 prefixEnd_8229536 := by exact prefixLift 8229536
  have htrace : WordTrace (prefixWord ++ tailWord_8229536) baseStart_8229536 baseEnd_8229536 := by
    simpa [prefixWord, tailWord_8229536, baseEnd_8229536] using wordTrace_append hprefix tailTrace_8229536
  have hstable : (prefixWord ++ tailWord_8229536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8229536).length < 2 ^ (prefixWord ++ tailWord_8229536).sum := by decide
  have hdescent : baseEnd_8229536 < baseStart_8229536 := by decide
  rcases family_descends (prefixWord ++ tailWord_8229536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8229576 : List Nat := [2, 1, 3, 1, 2, 3, 1, 4, 2, 1, 3]
def baseStart_8229576 : Nat := 118140960795 + 8229576 * 2 ^ 59
def prefixEnd_8229576 : Nat := 4983230072969 + 3 ^ 40 * 8229576 * 2
def baseEnd_8229576 : Nat := 4225728070705398979752875

theorem tailTrace_8229576 : CollatzResearch.WordTrace tailWord_8229576 prefixEnd_8229576 4225728070705398979752875 := by
  unfold tailWord_8229576
  simp only [CollatzResearch.WordTrace]
  refine ⟨150078647816829563264182291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200104863755772751018909721 150078647816829563264182291)
  ·
    refine ⟨225117971725244344896273437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150078647816829563264182291 225117971725244344896273437)
    ·
      refine ⟨84419239396966629336102539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225117971725244344896273437 84419239396966629336102539)
      ·
        refine ⟨126628859095449944004153809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84419239396966629336102539 126628859095449944004153809)
        ·
          refine ⟨94971644321587458003115357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126628859095449944004153809 94971644321587458003115357)
          ·
            refine ⟨35614366620595296751168259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94971644321587458003115357 35614366620595296751168259)
            ·
              refine ⟨53421549930892945126752389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35614366620595296751168259 53421549930892945126752389)
              ·
                refine ⟨10016540612042427211266073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53421549930892945126752389 10016540612042427211266073)
                ·
                  refine ⟨7512405459031820408449555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10016540612042427211266073 7512405459031820408449555)
                  ·
                    refine ⟨11268608188547730612674333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7512405459031820408449555 11268608188547730612674333)
                    ·
                      refine ⟨4225728070705398979752875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11268608188547730612674333 4225728070705398979752875)
                      ·
                        rfl

theorem cell23_8229576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 4, 2, 1, 3].length) (baseStart_8229576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8229576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8229576 prefixEnd_8229576 := by exact prefixLift 8229576
  have htrace : WordTrace (prefixWord ++ tailWord_8229576) baseStart_8229576 baseEnd_8229576 := by
    simpa [prefixWord, tailWord_8229576, baseEnd_8229576] using wordTrace_append hprefix tailTrace_8229576
  have hstable : (prefixWord ++ tailWord_8229576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8229576).length < 2 ^ (prefixWord ++ tailWord_8229576).sum := by decide
  have hdescent : baseEnd_8229576 < baseStart_8229576 := by decide
  rcases family_descends (prefixWord ++ tailWord_8229576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8229592 : List Nat := [2, 1, 2, 2, 3, 2, 1, 1, 1, 8]
def baseStart_8229592 : Nat := 118140960795 + 8229592 * 2 ^ 59
def prefixEnd_8229592 : Nat := 4983230072969 + 3 ^ 40 * 8229592 * 2
def baseEnd_8229592 : Nat := 1408578762131956972384267

theorem tailTrace_8229592 : CollatzResearch.WordTrace tailWord_8229592 prefixEnd_8229592 1408578762131956972384267 := by
  unfold tailWord_8229592
  simp only [CollatzResearch.WordTrace]
  refine ⟨150078939600800580630473515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200105252801067440840631353 150078939600800580630473515)
  ·
    refine ⟨225118409401200870945710273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150078939600800580630473515 225118409401200870945710273)
    ·
      refine ⟨168838807050900653209282705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225118409401200870945710273 168838807050900653209282705)
      ·
        refine ⟨126629105288175489906962029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168838807050900653209282705 126629105288175489906962029)
        ·
          refine ⟨47485914483065808715110761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126629105288175489906962029 47485914483065808715110761)
          ·
            refine ⟨35614435862299356536333071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47485914483065808715110761 35614435862299356536333071)
            ·
              refine ⟨53421653793449034804499607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35614435862299356536333071 53421653793449034804499607)
              ·
                refine ⟨80132480690173552206749411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53421653793449034804499607 80132480690173552206749411)
                ·
                  refine ⟨120198721035260328310124117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80132480690173552206749411 120198721035260328310124117)
                  ·
                    refine ⟨1408578762131956972384267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 120198721035260328310124117 1408578762131956972384267)
                    ·
                      rfl

theorem cell23_8229592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 1, 1, 8].length) (baseStart_8229592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8229592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8229592 prefixEnd_8229592 := by exact prefixLift 8229592
  have htrace : WordTrace (prefixWord ++ tailWord_8229592) baseStart_8229592 baseEnd_8229592 := by
    simpa [prefixWord, tailWord_8229592, baseEnd_8229592] using wordTrace_append hprefix tailTrace_8229592
  have hstable : (prefixWord ++ tailWord_8229592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8229592).length < 2 ^ (prefixWord ++ tailWord_8229592).sum := by decide
  have hdescent : baseEnd_8229592 < baseStart_8229592 := by decide
  rcases family_descends (prefixWord ++ tailWord_8229592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8229612 : List Nat := [2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 4]
def baseStart_8229612 : Nat := 118140960795 + 8229612 * 2 ^ 59
def prefixEnd_8229612 : Nat := 4983230072969 + 3 ^ 40 * 8229612 * 2
def baseEnd_8229612 : Nat := 4225746556008960838902709

theorem tailTrace_8229612 : CollatzResearch.WordTrace tailWord_8229612 prefixEnd_8229612 4225746556008960838902709 := by
  unfold tailWord_8229612
  simp only [CollatzResearch.WordTrace]
  refine ⟨150079304330764352338337545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200105739107685803117783393 150079304330764352338337545)
  ·
    refine ⟨112559478248073264253753159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150079304330764352338337545 112559478248073264253753159)
    ·
      refine ⟨168839217372109896380629739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112559478248073264253753159 168839217372109896380629739)
      ·
        refine ⟨253258826058164844570944609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168839217372109896380629739 253258826058164844570944609)
        ·
          refine ⟨189944119543623633428208457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 253258826058164844570944609 189944119543623633428208457)
          ·
            refine ⟨142458089657717725071156343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189944119543623633428208457 142458089657717725071156343)
            ·
              refine ⟨213687134486576587606734515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142458089657717725071156343 213687134486576587606734515)
              ·
                refine ⟨320530701729864881410101773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 213687134486576587606734515 320530701729864881410101773)
                ·
                  refine ⟨120199013148699330528788165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 320530701729864881410101773 120199013148699330528788165)
                  ·
                    refine ⟨22537314965381124474147781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 120199013148699330528788165 22537314965381124474147781)
                    ·
                      refine ⟨4225746556008960838902709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22537314965381124474147781 4225746556008960838902709)
                      ·
                        rfl

theorem cell23_8229612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 4].length) (baseStart_8229612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8229612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8229612 prefixEnd_8229612 := by exact prefixLift 8229612
  have htrace : WordTrace (prefixWord ++ tailWord_8229612) baseStart_8229612 baseEnd_8229612 := by
    simpa [prefixWord, tailWord_8229612, baseEnd_8229612] using wordTrace_append hprefix tailTrace_8229612
  have hstable : (prefixWord ++ tailWord_8229612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8229612).length < 2 ^ (prefixWord ++ tailWord_8229612).sum := by decide
  have hdescent : baseEnd_8229612 < baseStart_8229612 := by decide
  rcases family_descends (prefixWord ++ tailWord_8229612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8229616 : List Nat := [2, 1, 1, 1, 3, 1, 4, 2, 4, 2, 2]
def baseStart_8229616 : Nat := 118140960795 + 8229616 * 2 ^ 59
def prefixEnd_8229616 : Nat := 4983230072969 + 3 ^ 40 * 8229616 * 2
def baseEnd_8229616 : Nat := 4225748609931578823252691

theorem tailTrace_8229616 : CollatzResearch.WordTrace tailWord_8229616 prefixEnd_8229616 4225748609931578823252691 := by
  unfold tailWord_8229616
  simp only [CollatzResearch.WordTrace]
  refine ⟨150079377276757106679910351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200105836369009475573213801 150079377276757106679910351)
  ·
    refine ⟨225119065915135660019865527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150079377276757106679910351 225119065915135660019865527)
    ·
      refine ⟨337678598872703490029798291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225119065915135660019865527 337678598872703490029798291)
      ·
        refine ⟨506517898309055235044697437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337678598872703490029798291 506517898309055235044697437)
        ·
          refine ⟨189944211865895713141761539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 506517898309055235044697437 189944211865895713141761539)
          ·
            refine ⟨284916317798843569712642309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189944211865895713141761539 284916317798843569712642309)
            ·
              refine ⟨53421809587283169321120433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 284916317798843569712642309 53421809587283169321120433)
              ·
                refine ⟨40066357190462376990840325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53421809587283169321120433 40066357190462376990840325)
                ·
                  refine ⟨7512441973211695685782561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40066357190462376990840325 7512441973211695685782561)
                  ·
                    refine ⟨5634331479908771764336921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7512441973211695685782561 5634331479908771764336921)
                    ·
                      refine ⟨4225748609931578823252691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5634331479908771764336921 4225748609931578823252691)
                      ·
                        rfl

theorem cell23_8229616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 2, 4, 2, 2].length) (baseStart_8229616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8229616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8229616 prefixEnd_8229616 := by exact prefixLift 8229616
  have htrace : WordTrace (prefixWord ++ tailWord_8229616) baseStart_8229616 baseEnd_8229616 := by
    simpa [prefixWord, tailWord_8229616, baseEnd_8229616] using wordTrace_append hprefix tailTrace_8229616
  have hstable : (prefixWord ++ tailWord_8229616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8229616).length < 2 ^ (prefixWord ++ tailWord_8229616).sum := by decide
  have hdescent : baseEnd_8229616 < baseStart_8229616 := by decide
  rcases family_descends (prefixWord ++ tailWord_8229616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8229639 : List Nat := [1, 1, 4, 4, 1, 1, 1, 3, 7]
def baseStart_8229639 : Nat := 118140960795 + 8229639 * 2 ^ 59
def prefixEnd_8229639 : Nat := 4983230072969 + 3 ^ 40 * 8229639 * 2
def baseEnd_8229639 : Nat := 469528935554070248140565

theorem tailTrace_8229639 : CollatzResearch.WordTrace tailWord_8229639 prefixEnd_8229639 469528935554070248140565 := by
  unfold tailWord_8229639
  simp only [CollatzResearch.WordTrace]
  refine ⟨300159593432430888287907971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200106395621620592191938647 300159593432430888287907971)
  ·
    refine ⟨450239390148646332431861957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300159593432430888287907971 450239390148646332431861957)
    ·
      refine ⟨84419885652871187330974117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 450239390148646332431861957 84419885652871187330974117)
      ·
        refine ⟨15828728559913347624557647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84419885652871187330974117 15828728559913347624557647)
        ·
          refine ⟨23743092839870021436836471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15828728559913347624557647 23743092839870021436836471)
          ·
            refine ⟨35614639259805032155254707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23743092839870021436836471 35614639259805032155254707)
            ·
              refine ⟨53421958889707548232882061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35614639259805032155254707 53421958889707548232882061)
              ·
                refine ⟨20033234583640330587330773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53421958889707548232882061 20033234583640330587330773)
                ·
                  refine ⟨469528935554070248140565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20033234583640330587330773 469528935554070248140565)
                  ·
                    rfl

theorem cell23_8229639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 3, 7].length) (baseStart_8229639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8229639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8229639 prefixEnd_8229639 := by exact prefixLift 8229639
  have htrace : WordTrace (prefixWord ++ tailWord_8229639) baseStart_8229639 baseEnd_8229639 := by
    simpa [prefixWord, tailWord_8229639, baseEnd_8229639] using wordTrace_append hprefix tailTrace_8229639
  have hstable : (prefixWord ++ tailWord_8229639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8229639).length < 2 ^ (prefixWord ++ tailWord_8229639).sum := by decide
  have hdescent : baseEnd_8229639 < baseStart_8229639 := by decide
  rcases family_descends (prefixWord ++ tailWord_8229639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8229649 : List Nat := [1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 3]
def baseStart_8229649 : Nat := 118140960795 + 8229649 * 2 ^ 59
def prefixEnd_8229649 : Nat := 4983230072969 + 3 ^ 40 * 8229649 * 2
def baseEnd_8229649 : Nat := 4225765554793177194140039

theorem tailTrace_8229649 : CollatzResearch.WordTrace tailWord_8229649 prefixEnd_8229649 4225765554793177194140039 := by
  unfold tailWord_8229649
  simp only [CollatzResearch.WordTrace]
  refine ⟨300159958162394659995772001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200106638774929773330514667 300159958162394659995772001)
  ·
    refine ⟨225119968621795994996829001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300159958162394659995772001 225119968621795994996829001)
    ·
      refine ⟨168839976466346996247621751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225119968621795994996829001 168839976466346996247621751)
      ·
        refine ⟨253259964699520494371432627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168839976466346996247621751 253259964699520494371432627)
        ·
          refine ⟨379889947049280741557148941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253259964699520494371432627 379889947049280741557148941)
          ·
            refine ⟨142458730143480278083930853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 379889947049280741557148941 142458730143480278083930853)
            ·
              refine ⟨26711011901902552140737035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 142458730143480278083930853 26711011901902552140737035)
              ·
                refine ⟨40066517852853828211105553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26711011901902552140737035 40066517852853828211105553)
                ·
                  refine ⟨30049888389640371158329165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40066517852853828211105553 30049888389640371158329165)
                  ·
                    refine ⟨11268708146115139184373437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30049888389640371158329165 11268708146115139184373437)
                    ·
                      refine ⟨4225765554793177194140039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11268708146115139184373437 4225765554793177194140039)
                      ·
                        rfl

theorem cell23_8229649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 3].length) (baseStart_8229649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8229649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8229649 prefixEnd_8229649 := by exact prefixLift 8229649
  have htrace : WordTrace (prefixWord ++ tailWord_8229649) baseStart_8229649 baseEnd_8229649 := by
    simpa [prefixWord, tailWord_8229649, baseEnd_8229649] using wordTrace_append hprefix tailTrace_8229649
  have hstable : (prefixWord ++ tailWord_8229649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8229649).length < 2 ^ (prefixWord ++ tailWord_8229649).sum := by decide
  have hdescent : baseEnd_8229649 < baseStart_8229649 := by decide
  rcases family_descends (prefixWord ++ tailWord_8229649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8229669 : List Nat := [1, 3, 1, 2, 3, 1, 2, 3, 2, 5]
def baseStart_8229669 : Nat := 118140960795 + 8229669 * 2 ^ 59
def prefixEnd_8229669 : Nat := 4983230072969 + 3 ^ 40 * 8229669 * 2
def baseEnd_8229669 : Nat := 1408591941468755705296649

theorem tailTrace_8229669 : CollatzResearch.WordTrace tailWord_8229669 prefixEnd_8229669 1408591941468755705296649 := by
  unfold tailWord_8229669
  simp only [CollatzResearch.WordTrace]
  refine ⟨300160687622322203411500061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200107125081548135607666707 300160687622322203411500061)
  ·
    refine ⟨112560257858370826279312523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 300160687622322203411500061 112560257858370826279312523)
    ·
      refine ⟨168840386787556239418968785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112560257858370826279312523 168840386787556239418968785)
      ·
        refine ⟨126630290090667179564226589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168840386787556239418968785 126630290090667179564226589)
        ·
          refine ⟨47486358784000192336584971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126630290090667179564226589 47486358784000192336584971)
          ·
            refine ⟨71229538176000288504877457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47486358784000192336584971 71229538176000288504877457)
            ·
              refine ⟨53422153632000216378658093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71229538176000288504877457 53422153632000216378658093)
              ·
                refine ⟨20033307612000081141996785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53422153632000216378658093 20033307612000081141996785)
                ·
                  refine ⟨15024980709000060856497589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20033307612000081141996785 15024980709000060856497589)
                  ·
                    refine ⟨1408591941468755705296649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15024980709000060856497589 1408591941468755705296649)
                    ·
                      rfl

theorem cell23_8229669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 3, 2, 5].length) (baseStart_8229669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8229669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8229669 prefixEnd_8229669 := by exact prefixLift 8229669
  have htrace : WordTrace (prefixWord ++ tailWord_8229669) baseStart_8229669 baseEnd_8229669 := by
    simpa [prefixWord, tailWord_8229669, baseEnd_8229669] using wordTrace_append hprefix tailTrace_8229669
  have hstable : (prefixWord ++ tailWord_8229669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8229669).length < 2 ^ (prefixWord ++ tailWord_8229669).sum := by decide
  have hdescent : baseEnd_8229669 < baseStart_8229669 := by decide
  rcases family_descends (prefixWord ++ tailWord_8229669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8229756 : List Nat := [2, 2, 2, 1, 1, 1, 1, 2, 7, 1, 3]
def baseStart_8229756 : Nat := 118140960795 + 8229756 * 2 ^ 59
def prefixEnd_8229756 : Nat := 4983230072969 + 3 ^ 40 * 8229756 * 2
def baseEnd_8229756 : Nat := 4225820497223208275502047

theorem tailTrace_8229756 : CollatzResearch.WordTrace tailWord_8229756 prefixEnd_8229756 4225820497223208275502047 := by
  unfold tailWord_8229756
  simp only [CollatzResearch.WordTrace]
  refine ⟨150081930386503508634958561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200109240515338011513278081 150081930386503508634958561)
  ·
    refine ⟨112561447789877631476218921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150081930386503508634958561 112561447789877631476218921)
    ·
      refine ⟨84421085842408223607164191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112561447789877631476218921 84421085842408223607164191)
      ·
        refine ⟨126631628763612335410746287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84421085842408223607164191 126631628763612335410746287)
        ·
          refine ⟨189947443145418503116119431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126631628763612335410746287 189947443145418503116119431)
          ·
            refine ⟨284921164718127754674179147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189947443145418503116119431 284921164718127754674179147)
            ·
              refine ⟨427381747077191632011268721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 284921164718127754674179147 427381747077191632011268721)
              ·
                refine ⟨320536310307893724008451541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 427381747077191632011268721 320536310307893724008451541)
                ·
                  refine ⟨7512569772841259156448083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 320536310307893724008451541 7512569772841259156448083)
                  ·
                    refine ⟨11268854659261888734672125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7512569772841259156448083 11268854659261888734672125)
                    ·
                      refine ⟨4225820497223208275502047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11268854659261888734672125 4225820497223208275502047)
                      ·
                        rfl

theorem cell23_8229756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 7, 1, 3].length) (baseStart_8229756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8229756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8229756 prefixEnd_8229756 := by exact prefixLift 8229756
  have htrace : WordTrace (prefixWord ++ tailWord_8229756) baseStart_8229756 baseEnd_8229756 := by
    simpa [prefixWord, tailWord_8229756, baseEnd_8229756] using wordTrace_append hprefix tailTrace_8229756
  have hstable : (prefixWord ++ tailWord_8229756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8229756).length < 2 ^ (prefixWord ++ tailWord_8229756).sum := by decide
  have hdescent : baseEnd_8229756 < baseStart_8229756 := by decide
  rcases family_descends (prefixWord ++ tailWord_8229756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8229759 : List Nat := [1, 1, 2, 2, 1, 1, 5, 2, 3, 5]
def baseStart_8229759 : Nat := 118140960795 + 8229759 * 2 ^ 59
def prefixEnd_8229759 : Nat := 4983230072969 + 3 ^ 40 * 8229759 * 2
def baseEnd_8229759 : Nat := 1408607345888390587921511

theorem tailTrace_8229759 : CollatzResearch.WordTrace tailWord_8229759 prefixEnd_8229759 1408607345888390587921511 := by
  unfold tailWord_8229759
  simp only [CollatzResearch.WordTrace]
  refine ⟨300163970191996148782276331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200109313461330765854850887 300163970191996148782276331)
  ·
    refine ⟨450245955287994223173414497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300163970191996148782276331 450245955287994223173414497)
    ·
      refine ⟨337684466465995667380060873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 450245955287994223173414497 337684466465995667380060873)
      ·
        refine ⟨253263349849496750535045655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 337684466465995667380060873 253263349849496750535045655)
        ·
          refine ⟨379895024774245125802568483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253263349849496750535045655 379895024774245125802568483)
          ·
            refine ⟨569842537161367688703852725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 379895024774245125802568483 569842537161367688703852725)
            ·
              refine ⟨53422737858878220815986193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 569842537161367688703852725 53422737858878220815986193)
              ·
                refine ⟨40067053394158665611989645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53422737858878220815986193 40067053394158665611989645)
                ·
                  refine ⟨15025145022809499604496117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40067053394158665611989645 15025145022809499604496117)
                  ·
                    refine ⟨1408607345888390587921511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15025145022809499604496117 1408607345888390587921511)
                    ·
                      rfl

theorem cell23_8229759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 2, 3, 5].length) (baseStart_8229759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8229759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8229759 prefixEnd_8229759 := by exact prefixLift 8229759
  have htrace : WordTrace (prefixWord ++ tailWord_8229759) baseStart_8229759 baseEnd_8229759 := by
    simpa [prefixWord, tailWord_8229759, baseEnd_8229759] using wordTrace_append hprefix tailTrace_8229759
  have hstable : (prefixWord ++ tailWord_8229759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8229759).length < 2 ^ (prefixWord ++ tailWord_8229759).sum := by decide
  have hdescent : baseEnd_8229759 < baseStart_8229759 := by decide
  rcases family_descends (prefixWord ++ tailWord_8229759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8229793 : List Nat := [1, 2, 3, 4, 1, 2, 1, 3, 1, 5]
def baseStart_8229793 : Nat := 118140960795 + 8229793 * 2 ^ 59
def prefixEnd_8229793 : Nat := 4983230072969 + 3 ^ 40 * 8229793 * 2
def baseEnd_8229793 : Nat := 1408613165335808210246459

theorem tailTrace_8229793 : CollatzResearch.WordTrace tailWord_8229793 prefixEnd_8229793 1408613165335808210246459 := by
  unfold tailWord_8229793
  simp only [CollatzResearch.WordTrace]
  refine ⟨300165210273872972589014033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200110140182581981726009355 300165210273872972589014033)
  ·
    refine ⟨225123907705404729441760525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300165210273872972589014033 225123907705404729441760525)
    ·
      refine ⟨84421465389526773540660197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225123907705404729441760525 84421465389526773540660197)
      ·
        refine ⟨15829024760536270038873787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84421465389526773540660197 15829024760536270038873787)
        ·
          refine ⟨23743537140804405058310681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15829024760536270038873787 23743537140804405058310681)
          ·
            refine ⟨17807652855603303793733011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23743537140804405058310681 17807652855603303793733011)
            ·
              refine ⟨26711479283404955690599517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17807652855603303793733011 26711479283404955690599517)
              ·
                refine ⟨10016804731276858383974819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26711479283404955690599517 10016804731276858383974819)
                ·
                  refine ⟨15025207096915287575962229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10016804731276858383974819 15025207096915287575962229)
                  ·
                    refine ⟨1408613165335808210246459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15025207096915287575962229 1408613165335808210246459)
                    ·
                      rfl

theorem cell23_8229793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 3, 1, 5].length) (baseStart_8229793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8229793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8229793 prefixEnd_8229793 := by exact prefixLift 8229793
  have htrace : WordTrace (prefixWord ++ tailWord_8229793) baseStart_8229793 baseEnd_8229793 := by
    simpa [prefixWord, tailWord_8229793, baseEnd_8229793] using wordTrace_append hprefix tailTrace_8229793
  have hstable : (prefixWord ++ tailWord_8229793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8229793).length < 2 ^ (prefixWord ++ tailWord_8229793).sum := by decide
  have hdescent : baseEnd_8229793 < baseStart_8229793 := by decide
  rcases family_descends (prefixWord ++ tailWord_8229793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8229814 : List Nat := [5, 1, 4, 1, 1, 1, 3, 1, 6]
def baseStart_8229814 : Nat := 118140960795 + 8229814 * 2 ^ 59
def prefixEnd_8229814 : Nat := 4983230072969 + 3 ^ 40 * 8229814 * 2
def baseEnd_8229814 : Nat := 469538919900129894286309

theorem tailTrace_8229814 : CollatzResearch.WordTrace tailWord_8229814 prefixEnd_8229814 469538919900129894286309 := by
  unfold tailWord_8229814
  simp only [CollatzResearch.WordTrace]
  refine ⟨18760373512924805823470531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 200110650804531262117018997 18760373512924805823470531)
  ·
    refine ⟨28140560269387208735205797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18760373512924805823470531 28140560269387208735205797)
    ·
      refine ⟨5276355050510101637851087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28140560269387208735205797 5276355050510101637851087)
      ·
        refine ⟨7914532575765152456776631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5276355050510101637851087 7914532575765152456776631)
        ·
          refine ⟨11871798863647728685164947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7914532575765152456776631 11871798863647728685164947)
          ·
            refine ⟨17807698295471593027747421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11871798863647728685164947 17807698295471593027747421)
            ·
              refine ⟨6677886860801847385405283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17807698295471593027747421 6677886860801847385405283)
              ·
                refine ⟨10016830291202771078107925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6677886860801847385405283 10016830291202771078107925)
                ·
                  refine ⟨469538919900129894286309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10016830291202771078107925 469538919900129894286309)
                  ·
                    rfl

theorem cell23_8229814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 3, 1, 6].length) (baseStart_8229814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8229814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8229814 prefixEnd_8229814 := by exact prefixLift 8229814
  have htrace : WordTrace (prefixWord ++ tailWord_8229814) baseStart_8229814 baseEnd_8229814 := by
    simpa [prefixWord, tailWord_8229814, baseEnd_8229814] using wordTrace_append hprefix tailTrace_8229814
  have hstable : (prefixWord ++ tailWord_8229814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8229814).length < 2 ^ (prefixWord ++ tailWord_8229814).sum := by decide
  have hdescent : baseEnd_8229814 < baseStart_8229814 := by decide
  rcases family_descends (prefixWord ++ tailWord_8229814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8229816 : List Nat := [2, 1, 2, 1, 2, 5, 1, 2, 1, 1, 5]
def baseStart_8229816 : Nat := 118140960795 + 8229816 * 2 ^ 59
def prefixEnd_8229816 : Nat := 4983230072969 + 3 ^ 40 * 8229816 * 2
def baseEnd_8229816 : Nat := 4225851306062478040751771

theorem tailTrace_8229816 : CollatzResearch.WordTrace tailWord_8229816 prefixEnd_8229816 4225851306062478040751771 := by
  unfold tailWord_8229816
  simp only [CollatzResearch.WordTrace]
  refine ⟨150083024576394823758550651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200110699435193098344734201 150083024576394823758550651)
  ·
    refine ⟨225124536864592235637825977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150083024576394823758550651 225124536864592235637825977)
    ·
      refine ⟨168843402648444176728369483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225124536864592235637825977 168843402648444176728369483)
      ·
        refine ⟨253265103972666265092554225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168843402648444176728369483 253265103972666265092554225)
        ·
          refine ⟨189948827979499698819415669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 253265103972666265092554225 189948827979499698819415669)
          ·
            refine ⟨17807702623078096764320219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 189948827979499698819415669 17807702623078096764320219)
            ·
              refine ⟨26711553934617145146480329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17807702623078096764320219 26711553934617145146480329)
              ·
                refine ⟨20033665450962858859860247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26711553934617145146480329 20033665450962858859860247)
                ·
                  refine ⟨30050498176444288289790371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20033665450962858859860247 30050498176444288289790371)
                  ·
                    refine ⟨45075747264666432434685557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30050498176444288289790371 45075747264666432434685557)
                    ·
                      refine ⟨4225851306062478040751771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45075747264666432434685557 4225851306062478040751771)
                      ·
                        rfl

theorem cell23_8229816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 2, 1, 1, 5].length) (baseStart_8229816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8229816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8229816 prefixEnd_8229816 := by exact prefixLift 8229816
  have htrace : WordTrace (prefixWord ++ tailWord_8229816) baseStart_8229816 baseEnd_8229816 := by
    simpa [prefixWord, tailWord_8229816, baseEnd_8229816] using wordTrace_append hprefix tailTrace_8229816
  have hstable : (prefixWord ++ tailWord_8229816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8229816).length < 2 ^ (prefixWord ++ tailWord_8229816).sum := by decide
  have hdescent : baseEnd_8229816 < baseStart_8229816 := by decide
  rcases family_descends (prefixWord ++ tailWord_8229816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8229874 : List Nat := [3, 2, 1, 5, 1, 2, 2, 1, 2, 4]
def baseStart_8229874 : Nat := 118140960795 + 8229874 * 2 ^ 59
def prefixEnd_8229874 : Nat := 4983230072969 + 3 ^ 40 * 8229874 * 2
def baseEnd_8229874 : Nat := 1408627029313479604608835

theorem tailTrace_8229874 : CollatzResearch.WordTrace tailWord_8229874 prefixEnd_8229874 1408627029313479604608835 := by
  unfold tailWord_8229874
  simp only [CollatzResearch.WordTrace]
  refine ⟨75042041146644880855678169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200112109724386348948475117 75042041146644880855678169)
  ·
    refine ⟨56281530859983660641758627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75042041146644880855678169 56281530859983660641758627)
    ·
      refine ⟨84422296289975490962637941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56281530859983660641758627 84422296289975490962637941)
      ·
        refine ⟨7914590277185202277747307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 84422296289975490962637941 7914590277185202277747307)
        ·
          refine ⟨11871885415777803416620961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7914590277185202277747307 11871885415777803416620961)
          ·
            refine ⟨8903914061833352562465721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11871885415777803416620961 8903914061833352562465721)
            ·
              refine ⟨6677935546375014421849291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8903914061833352562465721 6677935546375014421849291)
              ·
                refine ⟨10016903319562521632773937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6677935546375014421849291 10016903319562521632773937)
                ·
                  refine ⟨7512677489671891224580453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10016903319562521632773937 7512677489671891224580453)
                  ·
                    refine ⟨1408627029313479604608835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7512677489671891224580453 1408627029313479604608835)
                    ·
                      rfl

theorem cell23_8229874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 2, 1, 2, 4].length) (baseStart_8229874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8229874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8229874 prefixEnd_8229874 := by exact prefixLift 8229874
  have htrace : WordTrace (prefixWord ++ tailWord_8229874) baseStart_8229874 baseEnd_8229874 := by
    simpa [prefixWord, tailWord_8229874, baseEnd_8229874] using wordTrace_append hprefix tailTrace_8229874
  have hstable : (prefixWord ++ tailWord_8229874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8229874).length < 2 ^ (prefixWord ++ tailWord_8229874).sum := by decide
  have hdescent : baseEnd_8229874 < baseStart_8229874 := by decide
  rcases family_descends (prefixWord ++ tailWord_8229874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8230013 : List Nat := [1, 4, 1, 1, 3, 1, 1, 3, 1, 4, 3]
def baseStart_8230013 : Nat := 118140960795 + 8230013 * 2 ^ 59
def prefixEnd_8230013 : Nat := 4983230072969 + 3 ^ 40 * 8230013 * 2
def baseEnd_8230013 : Nat := 4225952461751413769988365

theorem tailTrace_8230013 : CollatzResearch.WordTrace tailWord_8230013 prefixEnd_8230013 4225952461751413769988365 := by
  unfold tailWord_8230013
  simp only [CollatzResearch.WordTrace]
  refine ⟨300173234333075950162022693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200115489555383966774681795 300173234333075950162022693)
  ·
    refine ⟨56282481437451740655379255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 300173234333075950162022693 56282481437451740655379255)
    ·
      refine ⟨84423722156177610983068883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56282481437451740655379255 84423722156177610983068883)
      ·
        refine ⟨126635583234266416474603325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84423722156177610983068883 126635583234266416474603325)
        ·
          refine ⟨47488343712849906177976247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126635583234266416474603325 47488343712849906177976247)
          ·
            refine ⟨71232515569274859266964371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47488343712849906177976247 71232515569274859266964371)
            ·
              refine ⟨106848773353912288900446557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71232515569274859266964371 106848773353912288900446557)
              ·
                refine ⟨40068290007717108337667459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106848773353912288900446557 40068290007717108337667459)
                ·
                  refine ⟨60102435011575662506501189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40068290007717108337667459 60102435011575662506501189)
                  ·
                    refine ⟨11269206564670436719968973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60102435011575662506501189 11269206564670436719968973)
                    ·
                      refine ⟨4225952461751413769988365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11269206564670436719968973 4225952461751413769988365)
                      ·
                        rfl

theorem cell23_8230013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 3, 1, 4, 3].length) (baseStart_8230013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8230013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8230013 prefixEnd_8230013 := by exact prefixLift 8230013
  have htrace : WordTrace (prefixWord ++ tailWord_8230013) baseStart_8230013 baseEnd_8230013 := by
    simpa [prefixWord, tailWord_8230013, baseEnd_8230013] using wordTrace_append hprefix tailTrace_8230013
  have hstable : (prefixWord ++ tailWord_8230013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8230013).length < 2 ^ (prefixWord ++ tailWord_8230013).sum := by decide
  have hdescent : baseEnd_8230013 < baseStart_8230013 := by decide
  rcases family_descends (prefixWord ++ tailWord_8230013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8230016 : List Nat := [2, 1, 1, 2, 1, 3, 3, 2, 8]
def baseStart_8230016 : Nat := 118140960795 + 8230016 * 2 ^ 59
def prefixEnd_8230016 : Nat := 4983230072969 + 3 ^ 40 * 8230016 * 2
def baseEnd_8230016 : Nat := 469550444688153028694539

theorem tailTrace_8230016 : CollatzResearch.WordTrace tailWord_8230016 prefixEnd_8230016 469550444688153028694539 := by
  unfold tailWord_8230016
  simp only [CollatzResearch.WordTrace]
  refine ⟨150086671876032540837190951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200115562501376721116254601 150086671876032540837190951)
  ·
    refine ⟨225130007814048811255786427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150086671876032540837190951 225130007814048811255786427)
    ·
      refine ⟨337695011721073216883679641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225130007814048811255786427 337695011721073216883679641)
      ·
        refine ⟨253271258790804912662759731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 337695011721073216883679641 253271258790804912662759731)
        ·
          refine ⟨379906888186207368994139597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253271258790804912662759731 379906888186207368994139597)
          ·
            refine ⟨142465083069827763372802349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 379906888186207368994139597 142465083069827763372802349)
            ·
              refine ⟨53424406151185411264800881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142465083069827763372802349 53424406151185411264800881)
              ·
                refine ⟨40068304613389058448600661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53424406151185411264800881 40068304613389058448600661)
                ·
                  refine ⟨469550444688153028694539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40068304613389058448600661 469550444688153028694539)
                  ·
                    rfl

theorem cell23_8230016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 2, 8].length) (baseStart_8230016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8230016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8230016 prefixEnd_8230016 := by exact prefixLift 8230016
  have htrace : WordTrace (prefixWord ++ tailWord_8230016) baseStart_8230016 baseEnd_8230016 := by
    simpa [prefixWord, tailWord_8230016, baseEnd_8230016] using wordTrace_append hprefix tailTrace_8230016
  have hstable : (prefixWord ++ tailWord_8230016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8230016).length < 2 ^ (prefixWord ++ tailWord_8230016).sum := by decide
  have hdescent : baseEnd_8230016 < baseStart_8230016 := by decide
  rcases family_descends (prefixWord ++ tailWord_8230016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8230030 : List Nat := [4, 1, 1, 3, 2, 1, 1, 1, 4, 2, 3]
def baseStart_8230030 : Nat := 118140960795 + 8230030 * 2 ^ 59
def prefixEnd_8230030 : Nat := 4983230072969 + 3 ^ 40 * 8230030 * 2
def baseEnd_8230030 : Nat := 4225961190922540203475787

theorem tailTrace_8230030 : CollatzResearch.WordTrace tailWord_8230030 prefixEnd_8230030 4225961190922540203475787 := by
  unfold tailWord_8230030
  simp only [CollatzResearch.WordTrace]
  refine ⟨37521731796751795258173943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200115902916009574710261029 37521731796751795258173943)
  ·
    refine ⟨56282597695127692887260915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37521731796751795258173943 56282597695127692887260915)
    ·
      refine ⟨84423896542691539330891373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56282597695127692887260915 84423896542691539330891373)
      ·
        refine ⟨31658961203509327249084265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84423896542691539330891373 31658961203509327249084265)
        ·
          refine ⟨23744220902631995436813199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31658961203509327249084265 23744220902631995436813199)
          ·
            refine ⟨35616331353947993155219799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23744220902631995436813199 35616331353947993155219799)
            ·
              refine ⟨53424497030921989732829699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35616331353947993155219799 53424497030921989732829699)
              ·
                refine ⟨80136745546382984599244549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53424497030921989732829699 80136745546382984599244549)
                ·
                  refine ⟨15025639789946809612358353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80136745546382984599244549 15025639789946809612358353)
                  ·
                    refine ⟨11269229842460107209268765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15025639789946809612358353 11269229842460107209268765)
                    ·
                      refine ⟨4225961190922540203475787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11269229842460107209268765 4225961190922540203475787)
                      ·
                        rfl

theorem cell23_8230030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 1, 4, 2, 3].length) (baseStart_8230030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8230030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8230030 prefixEnd_8230030 := by exact prefixLift 8230030
  have htrace : WordTrace (prefixWord ++ tailWord_8230030) baseStart_8230030 baseEnd_8230030 := by
    simpa [prefixWord, tailWord_8230030, baseEnd_8230030] using wordTrace_append hprefix tailTrace_8230030
  have hstable : (prefixWord ++ tailWord_8230030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8230030).length < 2 ^ (prefixWord ++ tailWord_8230030).sum := by decide
  have hdescent : baseEnd_8230030 < baseStart_8230030 := by decide
  rcases family_descends (prefixWord ++ tailWord_8230030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8230103 : List Nat := [1, 1, 3, 2, 1, 2, 2, 4, 1, 1, 5]
def baseStart_8230103 : Nat := 118140960795 + 8230103 * 2 ^ 59
def prefixEnd_8230103 : Nat := 4983230072969 + 3 ^ 40 * 8230103 * 2
def baseEnd_8230103 : Nat := 4225998675010318417862951

theorem tailTrace_8230103 : CollatzResearch.WordTrace tailWord_8230103 prefixEnd_8230103 4225998675010318417862951 := by
  unfold tailWord_8230103
  simp only [CollatzResearch.WordTrace]
  refine ⟨300176516902749895532798963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200117677935166597021865975 300176516902749895532798963)
  ·
    refine ⟨450264775354124843299198445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300176516902749895532798963 450264775354124843299198445)
    ·
      refine ⟨168849290757796816237199417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 450264775354124843299198445 168849290757796816237199417)
      ·
        refine ⟨126636968068347612177899563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168849290757796816237199417 126636968068347612177899563)
        ·
          refine ⟨189955452102521418266849345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126636968068347612177899563 189955452102521418266849345)
          ·
            refine ⟨142466589076891063700137009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189955452102521418266849345 142466589076891063700137009)
            ·
              refine ⟨106849941807668297775102757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142466589076891063700137009 106849941807668297775102757)
              ·
                refine ⟨20034364088937805832831767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106849941807668297775102757 20034364088937805832831767)
                ·
                  refine ⟨30051546133406708749247651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20034364088937805832831767 30051546133406708749247651)
                  ·
                    refine ⟨45077319200110063123871477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30051546133406708749247651 45077319200110063123871477)
                    ·
                      refine ⟨4225998675010318417862951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45077319200110063123871477 4225998675010318417862951)
                      ·
                        rfl

theorem cell23_8230103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 4, 1, 1, 5].length) (baseStart_8230103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8230103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8230103 prefixEnd_8230103 := by exact prefixLift 8230103
  have htrace : WordTrace (prefixWord ++ tailWord_8230103) baseStart_8230103 baseEnd_8230103 := by
    simpa [prefixWord, tailWord_8230103, baseEnd_8230103] using wordTrace_append hprefix tailTrace_8230103
  have hstable : (prefixWord ++ tailWord_8230103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8230103).length < 2 ^ (prefixWord ++ tailWord_8230103).sum := by decide
  have hdescent : baseEnd_8230103 < baseStart_8230103 := by decide
  rcases family_descends (prefixWord ++ tailWord_8230103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8230120 : List Nat := [2, 1, 4, 1, 2, 1, 1, 3, 3, 2, 3]
def baseStart_8230120 : Nat := 118140960795 + 8230120 * 2 ^ 59
def prefixEnd_8230120 : Nat := 4983230072969 + 3 ^ 40 * 8230120 * 2
def baseEnd_8230120 : Nat := 4226007404181444851350373

theorem tailTrace_8230120 : CollatzResearch.WordTrace tailWord_8230120 prefixEnd_8230120 4226007404181444851350373 := by
  unfold tailWord_8230120
  simp only [CollatzResearch.WordTrace]
  refine ⟨150088568471844153718083907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200118091295792204957445209 150088568471844153718083907)
  ·
    refine ⟨225132852707766230577125861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150088568471844153718083907 225132852707766230577125861)
    ·
      refine ⟨42212409882706168233211099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 225132852707766230577125861 42212409882706168233211099)
      ·
        refine ⟨63318614824059252349816649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42212409882706168233211099 63318614824059252349816649)
        ·
          refine ⟨47488961118044439262362487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63318614824059252349816649 47488961118044439262362487)
          ·
            refine ⟨71233441677066658893543731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47488961118044439262362487 71233441677066658893543731)
            ·
              refine ⟨106850162515599988340315597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71233441677066658893543731 106850162515599988340315597)
              ·
                refine ⟨40068810943349995627618349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106850162515599988340315597 40068810943349995627618349)
                ·
                  refine ⟨15025804103756248360356881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40068810943349995627618349 15025804103756248360356881)
                  ·
                    refine ⟨11269353077817186270267661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15025804103756248360356881 11269353077817186270267661)
                    ·
                      refine ⟨4226007404181444851350373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11269353077817186270267661 4226007404181444851350373)
                      ·
                        rfl

theorem cell23_8230120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 3, 3, 2, 3].length) (baseStart_8230120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8230120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8230120 prefixEnd_8230120 := by exact prefixLift 8230120
  have htrace : WordTrace (prefixWord ++ tailWord_8230120) baseStart_8230120 baseEnd_8230120 := by
    simpa [prefixWord, tailWord_8230120, baseEnd_8230120] using wordTrace_append hprefix tailTrace_8230120
  have hstable : (prefixWord ++ tailWord_8230120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8230120).length < 2 ^ (prefixWord ++ tailWord_8230120).sum := by decide
  have hdescent : baseEnd_8230120 < baseStart_8230120 := by decide
  rcases family_descends (prefixWord ++ tailWord_8230120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8230194 : List Nat := [3, 2, 1, 1, 4, 1, 2, 3, 1, 3, 2]
def baseStart_8230194 : Nat := 118140960795 + 8230194 * 2 ^ 59
def prefixEnd_8230194 : Nat := 4983230072969 + 3 ^ 40 * 8230194 * 2
def baseEnd_8230194 : Nat := 4226045401749877561825033

theorem tailTrace_8230194 : CollatzResearch.WordTrace tailWord_8230194 prefixEnd_8230194 4226045401749877561825033 := by
  unfold tailWord_8230194
  simp only [CollatzResearch.WordTrace]
  refine ⟨75044958986355054518590409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200119890630280145382907757 75044958986355054518590409)
  ·
    refine ⟨56283719239766290888942807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75044958986355054518590409 56283719239766290888942807)
    ·
      refine ⟨84425578859649436333414211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56283719239766290888942807 84425578859649436333414211)
      ·
        refine ⟨126638368289474154500121317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84425578859649436333414211 126638368289474154500121317)
        ·
          refine ⟨23744694054276403968772747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 126638368289474154500121317 23744694054276403968772747)
          ·
            refine ⟨35617041081414605953159121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23744694054276403968772747 35617041081414605953159121)
            ·
              refine ⟨26712780811060954464869341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35617041081414605953159121 26712780811060954464869341)
              ·
                refine ⟨10017292804147857924326003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26712780811060954464869341 10017292804147857924326003)
                ·
                  refine ⟨15025939206221786886489005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10017292804147857924326003 15025939206221786886489005)
                  ·
                    refine ⟨5634727202333170082433377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15025939206221786886489005 5634727202333170082433377)
                    ·
                      refine ⟨4226045401749877561825033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5634727202333170082433377 4226045401749877561825033)
                      ·
                        rfl

theorem cell23_8230194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 3, 1, 3, 2].length) (baseStart_8230194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8230194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8230194 prefixEnd_8230194 := by exact prefixLift 8230194
  have htrace : WordTrace (prefixWord ++ tailWord_8230194) baseStart_8230194 baseEnd_8230194 := by
    simpa [prefixWord, tailWord_8230194, baseEnd_8230194] using wordTrace_append hprefix tailTrace_8230194
  have hstable : (prefixWord ++ tailWord_8230194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8230194).length < 2 ^ (prefixWord ++ tailWord_8230194).sum := by decide
  have hdescent : baseEnd_8230194 < baseStart_8230194 := by decide
  rcases family_descends (prefixWord ++ tailWord_8230194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8230224 : List Nat := [2, 1, 1, 1, 1, 5, 3, 3, 2, 2, 2]
def baseStart_8230224 : Nat := 118140960795 + 8230224 * 2 ^ 59
def prefixEnd_8230224 : Nat := 4983230072969 + 3 ^ 40 * 8230224 * 2
def baseEnd_8230224 : Nat := 4226060806169512444449895

theorem tailTrace_8230224 : CollatzResearch.WordTrace tailWord_8230224 prefixEnd_8230224 4226060806169512444449895 := by
  unfold tailWord_8230224
  simp only [CollatzResearch.WordTrace]
  refine ⟨150090465067655766598976863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200120620090207688798635817 150090465067655766598976863)
  ·
    refine ⟨225135697601483649898465295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150090465067655766598976863 225135697601483649898465295)
    ·
      refine ⟨337703546402225474847697943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225135697601483649898465295 337703546402225474847697943)
      ·
        refine ⟨506555319603338212271546915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337703546402225474847697943 506555319603338212271546915)
        ·
          refine ⟨759832979405007318407320373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 506555319603338212271546915 759832979405007318407320373)
          ·
            refine ⟨71234341819219436100686285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 759832979405007318407320373 71234341819219436100686285)
            ·
              refine ⟨26712878182207288537757357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71234341819219436100686285 26712878182207288537757357)
              ·
                refine ⟨10017329318327733201659009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26712878182207288537757357 10017329318327733201659009)
                ·
                  refine ⟨7512996988745799901244257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10017329318327733201659009 7512996988745799901244257)
                  ·
                    refine ⟨5634747741559349925933193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7512996988745799901244257 5634747741559349925933193)
                    ·
                      refine ⟨4226060806169512444449895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5634747741559349925933193 4226060806169512444449895)
                      ·
                        rfl

theorem cell23_8230224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 3, 2, 2, 2].length) (baseStart_8230224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8230224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8230224 prefixEnd_8230224 := by exact prefixLift 8230224
  have htrace : WordTrace (prefixWord ++ tailWord_8230224) baseStart_8230224 baseEnd_8230224 := by
    simpa [prefixWord, tailWord_8230224, baseEnd_8230224] using wordTrace_append hprefix tailTrace_8230224
  have hstable : (prefixWord ++ tailWord_8230224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8230224).length < 2 ^ (prefixWord ++ tailWord_8230224).sum := by decide
  have hdescent : baseEnd_8230224 < baseStart_8230224 := by decide
  rcases family_descends (prefixWord ++ tailWord_8230224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8230274 : List Nat := [3, 4, 2, 1, 1, 1, 1, 1, 1, 5, 3]
def baseStart_8230274 : Nat := 118140960795 + 8230274 * 2 ^ 59
def prefixEnd_8230274 : Nat := 4983230072969 + 3 ^ 40 * 8230274 * 2
def baseEnd_8230274 : Nat := 4226086480202237248824665

theorem tailTrace_8230274 : CollatzResearch.WordTrace tailWord_8230274 prefixEnd_8230274 4226086480202237248824665 := by
  unfold tailWord_8230274
  simp only [CollatzResearch.WordTrace]
  refine ⟨75045688446282597934318469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200121835856753594491515917 75045688446282597934318469)
  ·
    refine ⟨14071066583677987112684713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75045688446282597934318469 14071066583677987112684713)
    ·
      refine ⟨10553299937758490334513535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14071066583677987112684713 10553299937758490334513535)
      ·
        refine ⟨15829949906637735501770303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10553299937758490334513535 15829949906637735501770303)
        ·
          refine ⟨23744924859956603252655455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15829949906637735501770303 23744924859956603252655455)
          ·
            refine ⟨35617387289934904878983183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23744924859956603252655455 35617387289934904878983183)
            ·
              refine ⟨53426080934902357318474775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35617387289934904878983183 53426080934902357318474775)
              ·
                refine ⟨80139121402353535977712163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53426080934902357318474775 80139121402353535977712163)
                ·
                  refine ⟨120208682103530303966568245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80139121402353535977712163 120208682103530303966568245)
                  ·
                    refine ⟨11269563947205965996865773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 120208682103530303966568245 11269563947205965996865773)
                    ·
                      refine ⟨4226086480202237248824665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11269563947205965996865773 4226086480202237248824665)
                      ·
                        rfl

theorem cell23_8230274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_8230274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8230274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8230274 prefixEnd_8230274 := by exact prefixLift 8230274
  have htrace : WordTrace (prefixWord ++ tailWord_8230274) baseStart_8230274 baseEnd_8230274 := by
    simpa [prefixWord, tailWord_8230274, baseEnd_8230274] using wordTrace_append hprefix tailTrace_8230274
  have hstable : (prefixWord ++ tailWord_8230274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8230274).length < 2 ^ (prefixWord ++ tailWord_8230274).sum := by decide
  have hdescent : baseEnd_8230274 < baseStart_8230274 := by decide
  rcases family_descends (prefixWord ++ tailWord_8230274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8230297 : List Nat := [1, 2, 1, 2, 1, 5, 3, 1, 2, 1, 4]
def baseStart_8230297 : Nat := 118140960795 + 8230297 * 2 ^ 59
def prefixEnd_8230297 : Nat := 4983230072969 + 3 ^ 40 * 8230297 * 2
def baseEnd_8230297 : Nat := 4226098290257290658837059

theorem tailTrace_8230297 : CollatzResearch.WordTrace tailWord_8230297 prefixEnd_8230297 4226098290257290658837059 := by
  unfold tailWord_8230297
  simp only [CollatzResearch.WordTrace]
  refine ⟨300183592664047066665361145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200122395109364711110240763 300183592664047066665361145)
  ·
    refine ⟨225137694498035299999020859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300183592664047066665361145 225137694498035299999020859)
    ·
      refine ⟨337706541747052949998531289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225137694498035299999020859 337706541747052949998531289)
      ·
        refine ⟨253279906310289712498898467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 337706541747052949998531289 253279906310289712498898467)
        ·
          refine ⟨379919859465434568748347701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253279906310289712498898467 379919859465434568748347701)
          ·
            refine ⟨35617486824884490820157597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 379919859465434568748347701 35617486824884490820157597)
            ·
              refine ⟨13356557559331684057559099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35617486824884490820157597 13356557559331684057559099)
              ·
                refine ⟨20034836338997526086338649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13356557559331684057559099 20034836338997526086338649)
                ·
                  refine ⟨15026127254248144564753987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20034836338997526086338649 15026127254248144564753987)
                  ·
                    refine ⟨22539190881372216847130981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15026127254248144564753987 22539190881372216847130981)
                    ·
                      refine ⟨4226098290257290658837059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22539190881372216847130981 4226098290257290658837059)
                      ·
                        rfl

theorem cell23_8230297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 3, 1, 2, 1, 4].length) (baseStart_8230297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8230297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8230297 prefixEnd_8230297 := by exact prefixLift 8230297
  have htrace : WordTrace (prefixWord ++ tailWord_8230297) baseStart_8230297 baseEnd_8230297 := by
    simpa [prefixWord, tailWord_8230297, baseEnd_8230297] using wordTrace_append hprefix tailTrace_8230297
  have hstable : (prefixWord ++ tailWord_8230297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8230297).length < 2 ^ (prefixWord ++ tailWord_8230297).sum := by decide
  have hdescent : baseEnd_8230297 < baseStart_8230297 := by decide
  rcases family_descends (prefixWord ++ tailWord_8230297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8230320 : List Nat := [2, 1, 1, 1, 2, 1, 1, 8, 6]
def baseStart_8230320 : Nat := 118140960795 + 8230320 * 2 ^ 59
def prefixEnd_8230320 : Nat := 4983230072969 + 3 ^ 40 * 8230320 * 2
def baseEnd_8230320 : Nat := 469567788923593785427717

theorem tailTrace_8230320 : CollatzResearch.WordTrace tailWord_8230320 prefixEnd_8230320 469567788923593785427717 := by
  unfold tailWord_8230320
  simp only [CollatzResearch.WordTrace]
  refine ⟨150092215771481870796724207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200122954361975827728965609 150092215771481870796724207)
  ·
    refine ⟨225138323657222806195086311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150092215771481870796724207 225138323657222806195086311)
    ·
      refine ⟨337707485485834209292629467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225138323657222806195086311 337707485485834209292629467)
      ·
        refine ⟨506561228228751313938944201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337707485485834209292629467 506561228228751313938944201)
        ·
          refine ⟨379920921171563485454208151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 506561228228751313938944201 379920921171563485454208151)
          ·
            refine ⟨569881381757345228181312227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 379920921171563485454208151 569881381757345228181312227)
            ·
              refine ⟨854822072636017842271968341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 569881381757345228181312227 854822072636017842271968341)
              ·
                refine ⟨10017446163703334089124629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 854822072636017842271968341 10017446163703334089124629)
                ·
                  refine ⟨469567788923593785427717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10017446163703334089124629 469567788923593785427717)
                  ·
                    rfl

theorem cell23_8230320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 8, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 8, 6].length) (baseStart_8230320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8230320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8230320 prefixEnd_8230320 := by exact prefixLift 8230320
  have htrace : WordTrace (prefixWord ++ tailWord_8230320) baseStart_8230320 baseEnd_8230320 := by
    simpa [prefixWord, tailWord_8230320, baseEnd_8230320] using wordTrace_append hprefix tailTrace_8230320
  have hstable : (prefixWord ++ tailWord_8230320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8230320).length < 2 ^ (prefixWord ++ tailWord_8230320).sum := by decide
  have hdescent : baseEnd_8230320 < baseStart_8230320 := by decide
  rcases family_descends (prefixWord ++ tailWord_8230320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8230358 : List Nat := [5, 2, 1, 1, 1, 2, 3, 3, 1, 4]
def baseStart_8230358 : Nat := 118140960795 + 8230358 * 2 ^ 59
def prefixEnd_8230358 : Nat := 4983230072969 + 3 ^ 40 * 8230358 * 2
def baseEnd_8230358 : Nat := 1408709870859071640058093

theorem tailTrace_8230358 : CollatzResearch.WordTrace tailWord_8230358 prefixEnd_8230358 1408709870859071640058093 := by
  unfold tailWord_8230358
  simp only [CollatzResearch.WordTrace]
  refine ⟨18761613594801629630208233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 200123878344550716055554485 18761613594801629630208233)
  ·
    refine ⟨14071210196101222222656175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18761613594801629630208233 14071210196101222222656175)
    ·
      refine ⟨21106815294151833333984263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14071210196101222222656175 21106815294151833333984263)
      ·
        refine ⟨31660222941227750000976395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21106815294151833333984263 31660222941227750000976395)
        ·
          refine ⟨47490334411841625001464593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31660222941227750000976395 47490334411841625001464593)
          ·
            refine ⟨35617750808881218751098445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47490334411841625001464593 35617750808881218751098445)
            ·
              refine ⟨13356656553330457031661917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35617750808881218751098445 13356656553330457031661917)
              ·
                refine ⟨5008746207498921386873219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13356656553330457031661917 5008746207498921386873219)
                ·
                  refine ⟨7513119311248382080309829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5008746207498921386873219 7513119311248382080309829)
                  ·
                    refine ⟨1408709870859071640058093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7513119311248382080309829 1408709870859071640058093)
                    ·
                      rfl

theorem cell23_8230358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 3, 3, 1, 4].length) (baseStart_8230358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8230358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8230358 prefixEnd_8230358 := by exact prefixLift 8230358
  have htrace : WordTrace (prefixWord ++ tailWord_8230358) baseStart_8230358 baseEnd_8230358 := by
    simpa [prefixWord, tailWord_8230358, baseEnd_8230358] using wordTrace_append hprefix tailTrace_8230358
  have hstable : (prefixWord ++ tailWord_8230358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8230358).length < 2 ^ (prefixWord ++ tailWord_8230358).sum := by decide
  have hdescent : baseEnd_8230358 < baseStart_8230358 := by decide
  rcases family_descends (prefixWord ++ tailWord_8230358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8230367 : List Nat := [1, 1, 2, 3, 3, 1, 1, 5, 1, 5]
def baseStart_8230367 : Nat := 118140960795 + 8230367 * 2 ^ 59
def prefixEnd_8230367 : Nat := 4983230072969 + 3 ^ 40 * 8230367 * 2
def baseEnd_8230367 : Nat := 1408711411301035128320579

theorem tailTrace_8230367 : CollatzResearch.WordTrace tailWord_8230367 prefixEnd_8230367 1408711411301035128320579 := by
  unfold tailWord_8230367
  simp only [CollatzResearch.WordTrace]
  refine ⟨300186145773793468620409355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200124097182528979080272903 300186145773793468620409355)
  ·
    refine ⟨450279218660690202930614033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300186145773793468620409355 450279218660690202930614033)
    ·
      refine ⟨337709413995517652197960525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 450279218660690202930614033 337709413995517652197960525)
      ·
        refine ⟨126641030248319119574235197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 337709413995517652197960525 126641030248319119574235197)
        ·
          refine ⟨47490386343119669840338199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126641030248319119574235197 47490386343119669840338199)
          ·
            refine ⟨71235579514679504760507299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47490386343119669840338199 71235579514679504760507299)
            ·
              refine ⟨106853369272019257140760949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71235579514679504760507299 106853369272019257140760949)
              ·
                refine ⟨10017503369251805356946339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 106853369272019257140760949 10017503369251805356946339)
                ·
                  refine ⟨15026255053877708035419509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10017503369251805356946339 15026255053877708035419509)
                  ·
                    refine ⟨1408711411301035128320579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15026255053877708035419509 1408711411301035128320579)
                    ·
                      rfl

theorem cell23_8230367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 5, 1, 5].length) (baseStart_8230367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8230367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8230367 prefixEnd_8230367 := by exact prefixLift 8230367
  have htrace : WordTrace (prefixWord ++ tailWord_8230367) baseStart_8230367 baseEnd_8230367 := by
    simpa [prefixWord, tailWord_8230367, baseEnd_8230367] using wordTrace_append hprefix tailTrace_8230367
  have hstable : (prefixWord ++ tailWord_8230367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8230367).length < 2 ^ (prefixWord ++ tailWord_8230367).sum := by decide
  have hdescent : baseEnd_8230367 < baseStart_8230367 := by decide
  rcases family_descends (prefixWord ++ tailWord_8230367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8230380 : List Nat := [2, 2, 1, 1, 2, 1, 2, 1, 5, 6]
def baseStart_8230380 : Nat := 118140960795 + 8230380 * 2 ^ 59
def prefixEnd_8230380 : Nat := 4983230072969 + 3 ^ 40 * 8230380 * 2
def baseEnd_8230380 : Nat := 1408713636383871278033059

theorem tailTrace_8230380 : CollatzResearch.WordTrace tailWord_8230380 prefixEnd_8230380 1408713636383871278033059 := by
  unfold tailWord_8230380
  simp only [CollatzResearch.WordTrace]
  refine ⟨150093309961373185920316297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200124413281830914560421729 150093309961373185920316297)
  ·
    refine ⟨112569982471029889440237223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150093309961373185920316297 112569982471029889440237223)
    ·
      refine ⟨168854973706544834160355835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112569982471029889440237223 168854973706544834160355835)
      ·
        refine ⟨253282460559817251240533753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168854973706544834160355835 253282460559817251240533753)
        ·
          refine ⟨189961845419862938430400315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 253282460559817251240533753 189961845419862938430400315)
          ·
            refine ⟨284942768129794407645600473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189961845419862938430400315 284942768129794407645600473)
            ·
              refine ⟨213707076097345805734200355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 284942768129794407645600473 213707076097345805734200355)
              ·
                refine ⟨320560614146018708601300533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 213707076097345805734200355 320560614146018708601300533)
                ·
                  refine ⟨30052557576189253931371925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 320560614146018708601300533 30052557576189253931371925)
                  ·
                    refine ⟨1408713636383871278033059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30052557576189253931371925 1408713636383871278033059)
                    ·
                      rfl

theorem cell23_8230380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 6].length) (baseStart_8230380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8230380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8230380 prefixEnd_8230380 := by exact prefixLift 8230380
  have htrace : WordTrace (prefixWord ++ tailWord_8230380) baseStart_8230380 baseEnd_8230380 := by
    simpa [prefixWord, tailWord_8230380, baseEnd_8230380] using wordTrace_append hprefix tailTrace_8230380
  have hstable : (prefixWord ++ tailWord_8230380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8230380).length < 2 ^ (prefixWord ++ tailWord_8230380).sum := by decide
  have hdescent : baseEnd_8230380 < baseStart_8230380 := by decide
  rcases family_descends (prefixWord ++ tailWord_8230380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8230387 : List Nat := [1, 1, 1, 2, 2, 2, 2, 2, 2, 6, 2]
def baseStart_8230387 : Nat := 118140960795 + 8230387 * 2 ^ 59
def prefixEnd_8230387 : Nat := 4983230072969 + 3 ^ 40 * 8230387 * 2
def baseEnd_8230387 : Nat := 4226144503516195306711645

theorem tailTrace_8230387 : CollatzResearch.WordTrace tailWord_8230387 prefixEnd_8230387 4226144503516195306711645 := by
  unfold tailWord_8230387
  simp only [CollatzResearch.WordTrace]
  refine ⟨300186875233721012036137415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200124583489147341357424943 300186875233721012036137415)
  ·
    refine ⟨450280312850581518054206123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300186875233721012036137415 450280312850581518054206123)
    ·
      refine ⟨675420469275872277081309185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 450280312850581518054206123 675420469275872277081309185)
      ·
        refine ⟨506565351956904207810981889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 675420469275872277081309185 506565351956904207810981889)
        ·
          refine ⟨379924013967678155858236417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 506565351956904207810981889 379924013967678155858236417)
          ·
            refine ⟨284943010475758616893677313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 379924013967678155858236417 284943010475758616893677313)
            ·
              refine ⟨213707257856818962670257985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 284943010475758616893677313 213707257856818962670257985)
              ·
                refine ⟨160280443392614222002693489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 213707257856818962670257985 160280443392614222002693489)
                ·
                  refine ⟨120210332544460666502020117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 160280443392614222002693489 120210332544460666502020117)
                  ·
                    refine ⟨5634859338021593742282193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 120210332544460666502020117 5634859338021593742282193)
                    ·
                      refine ⟨4226144503516195306711645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5634859338021593742282193 4226144503516195306711645)
                      ·
                        rfl

theorem cell23_8230387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 6, 2].length) (baseStart_8230387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8230387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8230387 prefixEnd_8230387 := by exact prefixLift 8230387
  have htrace : WordTrace (prefixWord ++ tailWord_8230387) baseStart_8230387 baseEnd_8230387 := by
    simpa [prefixWord, tailWord_8230387, baseEnd_8230387] using wordTrace_append hprefix tailTrace_8230387
  have hstable : (prefixWord ++ tailWord_8230387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8230387).length < 2 ^ (prefixWord ++ tailWord_8230387).sum := by decide
  have hdescent : baseEnd_8230387 < baseStart_8230387 := by decide
  rcases family_descends (prefixWord ++ tailWord_8230387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8230401 : List Nat := [1, 2, 4, 1, 4, 2, 1, 2, 1, 5]
def baseStart_8230401 : Nat := 118140960795 + 8230401 * 2 ^ 59
def prefixEnd_8230401 : Nat := 4983230072969 + 3 ^ 40 * 8230401 * 2
def baseEnd_8230401 : Nat := 1408717230748452750645527

theorem tailTrace_8230401 : CollatzResearch.WordTrace tailWord_8230401 prefixEnd_8230401 1408717230748452750645527 := by
  unfold tailWord_8230401
  simp only [CollatzResearch.WordTrace]
  refine ⟨300187385855670292427147057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200124923903780194951431371 300187385855670292427147057)
  ·
    refine ⟨225140539391752719320360293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300187385855670292427147057 225140539391752719320360293)
    ·
      refine ⟨42213851135953634872567555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 225140539391752719320360293 42213851135953634872567555)
      ·
        refine ⟨63320776703930452308851333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42213851135953634872567555 63320776703930452308851333)
        ·
          refine ⟨11872645631986959807909625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63320776703930452308851333 11872645631986959807909625)
          ·
            refine ⟨8904484223990219855932219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11872645631986959807909625 8904484223990219855932219)
            ·
              refine ⟨13356726335985329783898329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8904484223990219855932219 13356726335985329783898329)
              ·
                refine ⟨10017544751988997337923747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13356726335985329783898329 10017544751988997337923747)
                ·
                  refine ⟨15026317127983496006885621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10017544751988997337923747 15026317127983496006885621)
                  ·
                    refine ⟨1408717230748452750645527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15026317127983496006885621 1408717230748452750645527)
                    ·
                      rfl

theorem cell23_8230401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 1, 2, 1, 5].length) (baseStart_8230401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8230401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8230401 prefixEnd_8230401 := by exact prefixLift 8230401
  have htrace : WordTrace (prefixWord ++ tailWord_8230401) baseStart_8230401 baseEnd_8230401 := by
    simpa [prefixWord, tailWord_8230401, baseEnd_8230401] using wordTrace_append hprefix tailTrace_8230401
  have hstable : (prefixWord ++ tailWord_8230401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8230401).length < 2 ^ (prefixWord ++ tailWord_8230401).sum := by decide
  have hdescent : baseEnd_8230401 < baseStart_8230401 := by decide
  rcases family_descends (prefixWord ++ tailWord_8230401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8230414 : List Nat := [4, 1, 1, 2, 4, 1, 1, 2, 1, 6]
def baseStart_8230414 : Nat := 118140960795 + 8230414 * 2 ^ 59
def prefixEnd_8230414 : Nat := 4983230072969 + 3 ^ 40 * 8230414 * 2
def baseEnd_8230414 : Nat := 1408719455831288900358007

theorem tailTrace_8230414 : CollatzResearch.WordTrace tailWord_8230414 prefixEnd_8230414 1408719455831288900358007 := by
  unfold tailWord_8230414
  simp only [CollatzResearch.WordTrace]
  refine ⟨37523482500577899455921287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200125240003082130431580197 37523482500577899455921287)
  ·
    refine ⟨56285223750866849183881931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37523482500577899455921287 56285223750866849183881931)
    ·
      refine ⟨84427835626300273775822897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56285223750866849183881931 84427835626300273775822897)
      ·
        refine ⟨63320876719725205331867173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84427835626300273775822897 63320876719725205331867173)
        ·
          refine ⟨11872664384948475999725095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63320876719725205331867173 11872664384948475999725095)
          ·
            refine ⟨17808996577422713999587643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11872664384948475999725095 17808996577422713999587643)
            ·
              refine ⟨26713494866134070999381465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17808996577422713999587643 26713494866134070999381465)
              ·
                refine ⟨20035121149600553249536099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26713494866134070999381465 20035121149600553249536099)
                ·
                  refine ⟨30052681724400829874304149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20035121149600553249536099 30052681724400829874304149)
                  ·
                    refine ⟨1408719455831288900358007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30052681724400829874304149 1408719455831288900358007)
                    ·
                      rfl

theorem cell23_8230414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 2, 1, 6].length) (baseStart_8230414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8230414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8230414 prefixEnd_8230414 := by exact prefixLift 8230414
  have htrace : WordTrace (prefixWord ++ tailWord_8230414) baseStart_8230414 baseEnd_8230414 := by
    simpa [prefixWord, tailWord_8230414, baseEnd_8230414] using wordTrace_append hprefix tailTrace_8230414
  have hstable : (prefixWord ++ tailWord_8230414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8230414).length < 2 ^ (prefixWord ++ tailWord_8230414).sum := by decide
  have hdescent : baseEnd_8230414 < baseStart_8230414 := by decide
  rcases family_descends (prefixWord ++ tailWord_8230414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8230417 : List Nat := [1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 4]
def baseStart_8230417 : Nat := 118140960795 + 8230417 * 2 ^ 59
def prefixEnd_8230417 : Nat := 4983230072969 + 3 ^ 40 * 8230417 * 2
def baseEnd_8230417 : Nat := 4226159907935830189336507

theorem tailTrace_8230417 : CollatzResearch.WordTrace tailWord_8230417 prefixEnd_8230417 4226159907935830189336507 := by
  unfold tailWord_8230417
  simp only [CollatzResearch.WordTrace]
  refine ⟨300187969423612327159729505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200125312949074884773153003 300187969423612327159729505)
  ·
    refine ⟨225140977067709245369797129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300187969423612327159729505 225140977067709245369797129)
    ·
      refine ⟨168855732800781934027347847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225140977067709245369797129 168855732800781934027347847)
      ·
        refine ⟨253283599201172901041021771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168855732800781934027347847 253283599201172901041021771)
        ·
          refine ⟨379925398801759351561532657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253283599201172901041021771 379925398801759351561532657)
          ·
            refine ⟨284944049101319513671149493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 379925398801759351561532657 284944049101319513671149493)
            ·
              refine ⟨26713504603248704406670265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 284944049101319513671149493 26713504603248704406670265)
              ·
                refine ⟨20035128452436528305002699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26713504603248704406670265 20035128452436528305002699)
                ·
                  refine ⟨30052692678654792457504049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20035128452436528305002699 30052692678654792457504049)
                  ·
                    refine ⟨22539519508991094343128037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30052692678654792457504049 22539519508991094343128037)
                    ·
                      refine ⟨4226159907935830189336507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22539519508991094343128037 4226159907935830189336507)
                      ·
                        rfl

theorem cell23_8230417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 4].length) (baseStart_8230417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8230417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8230417 prefixEnd_8230417 := by exact prefixLift 8230417
  have htrace : WordTrace (prefixWord ++ tailWord_8230417) baseStart_8230417 baseEnd_8230417 := by
    simpa [prefixWord, tailWord_8230417, baseEnd_8230417] using wordTrace_append hprefix tailTrace_8230417
  have hstable : (prefixWord ++ tailWord_8230417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8230417).length < 2 ^ (prefixWord ++ tailWord_8230417).sum := by decide
  have hdescent : baseEnd_8230417 < baseStart_8230417 := by decide
  rcases family_descends (prefixWord ++ tailWord_8230417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8230421 : List Nat := [1, 3, 2, 1, 3, 3, 3, 1, 1, 1, 4]
def baseStart_8230421 : Nat := 118140960795 + 8230421 * 2 ^ 59
def prefixEnd_8230421 : Nat := 4983230072969 + 3 ^ 40 * 8230421 * 2
def baseEnd_8230421 : Nat := 4226161961858448173686489

theorem tailTrace_8230421 : CollatzResearch.WordTrace tailWord_8230421 prefixEnd_8230421 4226161961858448173686489 := by
  unfold tailWord_8230421
  simp only [CollatzResearch.WordTrace]
  refine ⟨300188115315597835842875117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200125410210398557228583411 300188115315597835842875117)
  ·
    refine ⟨112570543243349188441078169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 300188115315597835842875117 112570543243349188441078169)
    ·
      refine ⟨84427907432511891330808627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112570543243349188441078169 84427907432511891330808627)
      ·
        refine ⟨126641861148767836996212941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84427907432511891330808627 126641861148767836996212941)
        ·
          refine ⟨47490697930787938873579853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126641861148767836996212941 47490697930787938873579853)
          ·
            refine ⟨17809011724045477077592445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47490697930787938873579853 17809011724045477077592445)
            ·
              refine ⟨6678379396517053904097167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17809011724045477077592445 6678379396517053904097167)
              ·
                refine ⟨10017569094775580856145751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6678379396517053904097167 10017569094775580856145751)
                ·
                  refine ⟨15026353642163371284218627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10017569094775580856145751 15026353642163371284218627)
                  ·
                    refine ⟨22539530463245056926327941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15026353642163371284218627 22539530463245056926327941)
                    ·
                      refine ⟨4226161961858448173686489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22539530463245056926327941 4226161961858448173686489)
                      ·
                        rfl

theorem cell23_8230421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 3, 1, 1, 1, 4].length) (baseStart_8230421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8230421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8230421 prefixEnd_8230421 := by exact prefixLift 8230421
  have htrace : WordTrace (prefixWord ++ tailWord_8230421) baseStart_8230421 baseEnd_8230421 := by
    simpa [prefixWord, tailWord_8230421, baseEnd_8230421] using wordTrace_append hprefix tailTrace_8230421
  have hstable : (prefixWord ++ tailWord_8230421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8230421).length < 2 ^ (prefixWord ++ tailWord_8230421).sum := by decide
  have hdescent : baseEnd_8230421 < baseStart_8230421 := by decide
  rcases family_descends (prefixWord ++ tailWord_8230421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8230437 : List Nat := [1, 3, 1, 2, 2, 1, 1, 1, 5, 3, 3]
def baseStart_8230437 : Nat := 118140960795 + 8230437 * 2 ^ 59
def prefixEnd_8230437 : Nat := 4983230072969 + 3 ^ 40 * 8230437 * 2
def baseEnd_8230437 : Nat := 4226170177548920111086415

theorem tailTrace_8230437 : CollatzResearch.WordTrace tailWord_8230437 prefixEnd_8230437 4226170177548920111086415 := by
  unfold tailWord_8230437
  simp only [CollatzResearch.WordTrace]
  refine ⟨300188698883539870575457565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200125799255693247050305043 300188698883539870575457565)
  ·
    refine ⟨112570762081327451465796587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 300188698883539870575457565 112570762081327451465796587)
    ·
      refine ⟨168856143121991177198694881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112570762081327451465796587 168856143121991177198694881)
      ·
        refine ⟨126642107341493382899021161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168856143121991177198694881 126642107341493382899021161)
        ·
          refine ⟨94981580506120037174265871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126642107341493382899021161 94981580506120037174265871)
          ·
            refine ⟨142472370759180055761398807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94981580506120037174265871 142472370759180055761398807)
            ·
              refine ⟨213708556138770083642098211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142472370759180055761398807 213708556138770083642098211)
              ·
                refine ⟨320562834208155125463147317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 213708556138770083642098211 320562834208155125463147317)
                ·
                  refine ⟨30052765707014543012170061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 320562834208155125463147317 30052765707014543012170061)
                  ·
                    refine ⟨11269787140130453629563773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30052765707014543012170061 11269787140130453629563773)
                    ·
                      refine ⟨4226170177548920111086415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11269787140130453629563773 4226170177548920111086415)
                      ·
                        rfl

theorem cell23_8230437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 5, 3, 3].length) (baseStart_8230437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8230437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8230437 prefixEnd_8230437 := by exact prefixLift 8230437
  have htrace : WordTrace (prefixWord ++ tailWord_8230437) baseStart_8230437 baseEnd_8230437 := by
    simpa [prefixWord, tailWord_8230437, baseEnd_8230437] using wordTrace_append hprefix tailTrace_8230437
  have hstable : (prefixWord ++ tailWord_8230437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8230437).length < 2 ^ (prefixWord ++ tailWord_8230437).sum := by decide
  have hdescent : baseEnd_8230437 < baseStart_8230437 := by decide
  rcases family_descends (prefixWord ++ tailWord_8230437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8230481 : List Nat := [1, 2, 2, 1, 3, 2, 3, 3, 1, 3, 2]
def baseStart_8230481 : Nat := 118140960795 + 8230481 * 2 ^ 59
def prefixEnd_8230481 : Nat := 4983230072969 + 3 ^ 40 * 8230481 * 2
def baseEnd_8230481 : Nat := 4226192770697717938936213

theorem tailTrace_8230481 : CollatzResearch.WordTrace tailWord_8230481 prefixEnd_8230481 4226192770697717938936213 := by
  unfold tailWord_8230481
  simp only [CollatzResearch.WordTrace]
  refine ⟨300190303695380466090059297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200126869130253644060039531 300190303695380466090059297)
  ·
    refine ⟨225142727771535349567544473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300190303695380466090059297 225142727771535349567544473)
    ·
      refine ⟨168857045828651512175658355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225142727771535349567544473 168857045828651512175658355)
      ·
        refine ⟨253285568742977268263487533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168857045828651512175658355 253285568742977268263487533)
        ·
          refine ⟨94982088278616475598807825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 253285568742977268263487533 94982088278616475598807825)
          ·
            refine ⟨71236566208962356699105869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94982088278616475598807825 71236566208962356699105869)
            ·
              refine ⟨26713712328360883762164701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71236566208962356699105869 26713712328360883762164701)
              ·
                refine ⟨10017642123135331410811763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26713712328360883762164701 10017642123135331410811763)
                ·
                  refine ⟨15026463184702997116217645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10017642123135331410811763 15026463184702997116217645)
                  ·
                    refine ⟨5634923694263623918581617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15026463184702997116217645 5634923694263623918581617)
                    ·
                      refine ⟨4226192770697717938936213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5634923694263623918581617 4226192770697717938936213)
                      ·
                        rfl

theorem cell23_8230481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 3, 1, 3, 2].length) (baseStart_8230481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8230481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8230481 prefixEnd_8230481 := by exact prefixLift 8230481
  have htrace : WordTrace (prefixWord ++ tailWord_8230481) baseStart_8230481 baseEnd_8230481 := by
    simpa [prefixWord, tailWord_8230481, baseEnd_8230481] using wordTrace_append hprefix tailTrace_8230481
  have hstable : (prefixWord ++ tailWord_8230481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8230481).length < 2 ^ (prefixWord ++ tailWord_8230481).sum := by decide
  have hdescent : baseEnd_8230481 < baseStart_8230481 := by decide
  rcases family_descends (prefixWord ++ tailWord_8230481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8230487 : List Nat := [1, 1, 3, 2, 2, 3, 1, 2, 2, 6]
def baseStart_8230487 : Nat := 118140960795 + 8230487 * 2 ^ 59
def prefixEnd_8230487 : Nat := 4983230072969 + 3 ^ 40 * 8230487 * 2
def baseEnd_8230487 : Nat := 1408731950527214971820395

theorem tailTrace_8230487 : CollatzResearch.WordTrace tailWord_8230487 prefixEnd_8230487 1408731950527214971820395 := by
  unfold tailWord_8230487
  simp only [CollatzResearch.WordTrace]
  refine ⟨300190522533358729114777715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200127015022239152743185143 300190522533358729114777715)
  ·
    refine ⟨450285783800038093672166573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300190522533358729114777715 450285783800038093672166573)
    ·
      refine ⟨168857168925014285127062465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 450285783800038093672166573 168857168925014285127062465)
      ·
        refine ⟨126642876693760713845296849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168857168925014285127062465 126642876693760713845296849)
        ·
          refine ⟨94982157520320535383972637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126642876693760713845296849 94982157520320535383972637)
          ·
            refine ⟨35618309070120200768989739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94982157520320535383972637 35618309070120200768989739)
            ·
              refine ⟨53427463605180301153484609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35618309070120200768989739 53427463605180301153484609)
              ·
                refine ⟨40070597703885225865113457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53427463605180301153484609 40070597703885225865113457)
                ·
                  refine ⟨30052948277913919398835093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40070597703885225865113457 30052948277913919398835093)
                  ·
                    refine ⟨1408731950527214971820395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30052948277913919398835093 1408731950527214971820395)
                    ·
                      rfl

theorem cell23_8230487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 2, 2, 6].length) (baseStart_8230487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8230487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8230487 prefixEnd_8230487 := by exact prefixLift 8230487
  have htrace : WordTrace (prefixWord ++ tailWord_8230487) baseStart_8230487 baseEnd_8230487 := by
    simpa [prefixWord, tailWord_8230487, baseEnd_8230487] using wordTrace_append hprefix tailTrace_8230487
  have hstable : (prefixWord ++ tailWord_8230487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8230487).length < 2 ^ (prefixWord ++ tailWord_8230487).sum := by decide
  have hdescent : baseEnd_8230487 < baseStart_8230487 := by decide
  rcases family_descends (prefixWord ++ tailWord_8230487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8230504 : List Nat := [2, 1, 4, 3, 1, 1, 2, 1, 2, 6]
def baseStart_8230504 : Nat := 118140960795 + 8230504 * 2 ^ 59
def prefixEnd_8230504 : Nat := 4983230072969 + 3 ^ 40 * 8230504 * 2
def baseEnd_8230504 : Nat := 1408734860250923782982869

theorem tailTrace_8230504 : CollatzResearch.WordTrace tailWord_8230504 prefixEnd_8230504 1408734860250923782982869 := by
  unfold tailWord_8230504
  simp only [CollatzResearch.WordTrace]
  refine ⟨150095571287148570509073283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200127428382864760678764377 150095571287148570509073283)
  ·
    refine ⟨225143356930722855763609925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150095571287148570509073283 225143356930722855763609925)
    ·
      refine ⟨42214379424510535455676861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 225143356930722855763609925 42214379424510535455676861)
      ·
        refine ⟨15830392284191450795878823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42214379424510535455676861 15830392284191450795878823)
        ·
          refine ⟨23745588426287176193818235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15830392284191450795878823 23745588426287176193818235)
          ·
            refine ⟨35618382639430764290727353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23745588426287176193818235 35618382639430764290727353)
            ·
              refine ⟨26713786979573073218045515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35618382639430764290727353 26713786979573073218045515)
              ·
                refine ⟨40070680469359609827068273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26713786979573073218045515 40070680469359609827068273)
                ·
                  refine ⟨30053010352019707370301205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40070680469359609827068273 30053010352019707370301205)
                  ·
                    refine ⟨1408734860250923782982869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30053010352019707370301205 1408734860250923782982869)
                    ·
                      rfl

theorem cell23_8230504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 1, 2, 6].length) (baseStart_8230504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8230504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8230504 prefixEnd_8230504 := by exact prefixLift 8230504
  have htrace : WordTrace (prefixWord ++ tailWord_8230504) baseStart_8230504 baseEnd_8230504 := by
    simpa [prefixWord, tailWord_8230504, baseEnd_8230504] using wordTrace_append hprefix tailTrace_8230504
  have hstable : (prefixWord ++ tailWord_8230504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8230504).length < 2 ^ (prefixWord ++ tailWord_8230504).sum := by decide
  have hdescent : baseEnd_8230504 < baseStart_8230504 := by decide
  rcases family_descends (prefixWord ++ tailWord_8230504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8230562 : List Nat := [3, 3, 1, 4, 1, 1, 1, 3, 2, 2, 2]
def baseStart_8230562 : Nat := 118140960795 + 8230562 * 2 ^ 59
def prefixEnd_8230562 : Nat := 4983230072969 + 3 ^ 40 * 8230562 * 2
def baseEnd_8230562 : Nat := 4226234362630732122023341

theorem tailTrace_8230562 : CollatzResearch.WordTrace tailWord_8230562 prefixEnd_8230562 4226234362630732122023341 := by
  unfold tailWord_8230562
  simp only [CollatzResearch.WordTrace]
  refine ⟨75048314502021754230939485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200128838672058011282505293 75048314502021754230939485)
  ·
    refine ⟨28143117938258157836602307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75048314502021754230939485 28143117938258157836602307)
    ·
      refine ⟨42214676907387236754903461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28143117938258157836602307 42214676907387236754903461)
      ·
        refine ⟨7915251920135106891544399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42214676907387236754903461 7915251920135106891544399)
        ·
          refine ⟨11872877880202660337316599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7915251920135106891544399 11872877880202660337316599)
          ·
            refine ⟨17809316820303990505974899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11872877880202660337316599 17809316820303990505974899)
            ·
              refine ⟨26713975230455985758962349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17809316820303990505974899 26713975230455985758962349)
              ·
                refine ⟨10017740711420994659610881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26713975230455985758962349 10017740711420994659610881)
                ·
                  refine ⟨7513305533565745994708161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10017740711420994659610881 7513305533565745994708161)
                  ·
                    refine ⟨5634979150174309496031121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7513305533565745994708161 5634979150174309496031121)
                    ·
                      refine ⟨4226234362630732122023341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5634979150174309496031121 4226234362630732122023341)
                      ·
                        rfl

theorem cell23_8230562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_8230562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8230562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8230562 prefixEnd_8230562 := by exact prefixLift 8230562
  have htrace : WordTrace (prefixWord ++ tailWord_8230562) baseStart_8230562 baseEnd_8230562 := by
    simpa [prefixWord, tailWord_8230562, baseEnd_8230562] using wordTrace_append hprefix tailTrace_8230562
  have hstable : (prefixWord ++ tailWord_8230562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8230562).length < 2 ^ (prefixWord ++ tailWord_8230562).sum := by decide
  have hdescent : baseEnd_8230562 < baseStart_8230562 := by decide
  rcases family_descends (prefixWord ++ tailWord_8230562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8230597 : List Nat := [1, 3, 1, 1, 1, 1, 2, 3, 1, 3, 6]
def baseStart_8230597 : Nat := 118140960795 + 8230597 * 2 ^ 59
def prefixEnd_8230597 : Nat := 4983230072969 + 3 ^ 40 * 8230597 * 2
def baseEnd_8230597 : Nat := 4226252334453639485085679

theorem tailTrace_8230597 : CollatzResearch.WordTrace tailWord_8230597 prefixEnd_8230597 4226252334453639485085679 := by
  unfold tailWord_8230597
  simp only [CollatzResearch.WordTrace]
  refine ⟨300194534562960217901282045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200129689708640145267521363 300194534562960217901282045)
  ·
    refine ⟨112572950461110081712980767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 300194534562960217901282045 112572950461110081712980767)
    ·
      refine ⟨168859425691665122569471151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112572950461110081712980767 168859425691665122569471151)
      ·
        refine ⟨253289138537497683854206727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168859425691665122569471151 253289138537497683854206727)
        ·
          refine ⟨379933707806246525781310091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253289138537497683854206727 379933707806246525781310091)
          ·
            refine ⟨569900561709369788671965137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 379933707806246525781310091 569900561709369788671965137)
            ·
              refine ⟨427425421282027341503973853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 569900561709369788671965137 427425421282027341503973853)
              ·
                refine ⟨160284532980760253063990195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 427425421282027341503973853 160284532980760253063990195)
                ·
                  refine ⟨240426799471140379595985293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 160284532980760253063990195 240426799471140379595985293)
                  ·
                    refine ⟨90160049801677642348494485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 240426799471140379595985293 90160049801677642348494485)
                    ·
                      refine ⟨4226252334453639485085679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90160049801677642348494485 4226252334453639485085679)
                      ·
                        rfl

theorem cell23_8230597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 3, 6].length) (baseStart_8230597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8230597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8230597 prefixEnd_8230597 := by exact prefixLift 8230597
  have htrace : WordTrace (prefixWord ++ tailWord_8230597) baseStart_8230597 baseEnd_8230597 := by
    simpa [prefixWord, tailWord_8230597, baseEnd_8230597] using wordTrace_append hprefix tailTrace_8230597
  have hstable : (prefixWord ++ tailWord_8230597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8230597).length < 2 ^ (prefixWord ++ tailWord_8230597).sum := by decide
  have hdescent : baseEnd_8230597 < baseStart_8230597 := by decide
  rcases family_descends (prefixWord ++ tailWord_8230597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8230607 : List Nat := [1, 1, 2, 1, 1, 3, 1, 5, 8]
def baseStart_8230607 : Nat := 118140960795 + 8230607 * 2 ^ 59
def prefixEnd_8230607 : Nat := 4983230072969 + 3 ^ 40 * 8230607 * 2
def baseEnd_8230607 : Nat := 469584163251131605106737

theorem tailTrace_8230607 : CollatzResearch.WordTrace tailWord_8230607 prefixEnd_8230607 469584163251131605106737 := by
  unfold tailWord_8230607
  simp only [CollatzResearch.WordTrace]
  refine ⟨300194899292923989609146075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200129932861949326406097383 300194899292923989609146075)
  ·
    refine ⟨450292348939385984413719113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300194899292923989609146075 450292348939385984413719113)
    ·
      refine ⟨337719261704539488310289335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 450292348939385984413719113 337719261704539488310289335)
      ·
        refine ⟨506578892556809232465434003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337719261704539488310289335 506578892556809232465434003)
        ·
          refine ⟨759868338835213848698151005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 506578892556809232465434003 759868338835213848698151005)
          ·
            refine ⟨284950627063205193261806627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 759868338835213848698151005 284950627063205193261806627)
            ·
              refine ⟨427425940594807789892709941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 284950627063205193261806627 427425940594807789892709941)
              ·
                refine ⟨40071181930763230302441557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 427425940594807789892709941 40071181930763230302441557)
                ·
                  refine ⟨469584163251131605106737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40071181930763230302441557 469584163251131605106737)
                  ·
                    rfl

theorem cell23_8230607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 5, 8].length) (baseStart_8230607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8230607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8230607 prefixEnd_8230607 := by exact prefixLift 8230607
  have htrace : WordTrace (prefixWord ++ tailWord_8230607) baseStart_8230607 baseEnd_8230607 := by
    simpa [prefixWord, tailWord_8230607, baseEnd_8230607] using wordTrace_append hprefix tailTrace_8230607
  have hstable : (prefixWord ++ tailWord_8230607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8230607).length < 2 ^ (prefixWord ++ tailWord_8230607).sum := by decide
  have hdescent : baseEnd_8230607 < baseStart_8230607 := by decide
  rcases family_descends (prefixWord ++ tailWord_8230607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8230624 : List Nat := [2, 1, 1, 3, 1, 2, 4, 3, 6]
def baseStart_8230624 : Nat := 118140960795 + 8230624 * 2 ^ 59
def prefixEnd_8230624 : Nat := 4983230072969 + 3 ^ 40 * 8230624 * 2
def baseEnd_8230624 : Nat := 469585133159034542160895

theorem tailTrace_8230624 : CollatzResearch.WordTrace tailWord_8230624 prefixEnd_8230624 469585133159034542160895 := by
  unfold tailWord_8230624
  simp only [CollatzResearch.WordTrace]
  refine ⟨150097759666931200756257463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200130346222574934341676617 150097759666931200756257463)
  ·
    refine ⟨225146639500396801134386195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150097759666931200756257463 225146639500396801134386195)
    ·
      refine ⟨337719959250595201701579293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225146639500396801134386195 337719959250595201701579293)
      ·
        refine ⟨126644984718973200638092235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 337719959250595201701579293 126644984718973200638092235)
        ·
          refine ⟨189967477078459800957138353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126644984718973200638092235 189967477078459800957138353)
          ·
            refine ⟨142475607808844850717853765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189967477078459800957138353 142475607808844850717853765)
            ·
              refine ⟨26714176464158409509597581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 142475607808844850717853765 26714176464158409509597581)
              ·
                refine ⟨10017816174059403566099093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26714176464158409509597581 10017816174059403566099093)
                ·
                  refine ⟨469585133159034542160895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10017816174059403566099093 469585133159034542160895)
                  ·
                    rfl

theorem cell23_8230624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 3, 6].length) (baseStart_8230624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8230624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8230624 prefixEnd_8230624 := by exact prefixLift 8230624
  have htrace : WordTrace (prefixWord ++ tailWord_8230624) baseStart_8230624 baseEnd_8230624 := by
    simpa [prefixWord, tailWord_8230624, baseEnd_8230624] using wordTrace_append hprefix tailTrace_8230624
  have hstable : (prefixWord ++ tailWord_8230624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8230624).length < 2 ^ (prefixWord ++ tailWord_8230624).sum := by decide
  have hdescent : baseEnd_8230624 < baseStart_8230624 := by decide
  rcases family_descends (prefixWord ++ tailWord_8230624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8230691 : List Nat := [1, 1, 1, 4, 2, 1, 3, 4, 1, 1, 4]
def baseStart_8230691 : Nat := 118140960795 + 8230691 * 2 ^ 59
def prefixEnd_8230691 : Nat := 4983230072969 + 3 ^ 40 * 8230691 * 2
def baseEnd_8230691 : Nat := 4226300601635162117310247

theorem tailTrace_8230691 : CollatzResearch.WordTrace tailWord_8230691 prefixEnd_8230691 4226300601635162117310247 := by
  unfold tailWord_8230691
  simp only [CollatzResearch.WordTrace]
  refine ⟨300197963024619671955203927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200131975349746447970135951 300197963024619671955203927)
  ·
    refine ⟨450296944536929507932805891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300197963024619671955203927 450296944536929507932805891)
    ·
      refine ⟨675445416805394261899208837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 450296944536929507932805891 675445416805394261899208837)
      ·
        refine ⟨126646015651011424106101657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 675445416805394261899208837 126646015651011424106101657)
        ·
          refine ⟨94984511738258568079576243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126646015651011424106101657 94984511738258568079576243)
          ·
            refine ⟨142476767607387852119364365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94984511738258568079576243 142476767607387852119364365)
            ·
              refine ⟨53428787852770444544761637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142476767607387852119364365 53428787852770444544761637)
              ·
                refine ⟨10017897722394458352142807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53428787852770444544761637 10017897722394458352142807)
                ·
                  refine ⟨15026846583591687528214211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10017897722394458352142807 15026846583591687528214211)
                  ·
                    refine ⟨22540269875387531292321317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15026846583591687528214211 22540269875387531292321317)
                    ·
                      refine ⟨4226300601635162117310247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22540269875387531292321317 4226300601635162117310247)
                      ·
                        rfl

theorem cell23_8230691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 4, 1, 1, 4].length) (baseStart_8230691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8230691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8230691 prefixEnd_8230691 := by exact prefixLift 8230691
  have htrace : WordTrace (prefixWord ++ tailWord_8230691) baseStart_8230691 baseEnd_8230691 := by
    simpa [prefixWord, tailWord_8230691, baseEnd_8230691] using wordTrace_append hprefix tailTrace_8230691
  have hstable : (prefixWord ++ tailWord_8230691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8230691).length < 2 ^ (prefixWord ++ tailWord_8230691).sum := by decide
  have hdescent : baseEnd_8230691 < baseStart_8230691 := by decide
  rcases family_descends (prefixWord ++ tailWord_8230691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8230714 : List Nat := [3, 1, 1, 1, 5, 1, 11]
def baseStart_8230714 : Nat := 118140960795 + 8230714 * 2 ^ 59
def prefixEnd_8230714 : Nat := 4983230072969 + 3 ^ 40 * 8230714 * 2
def baseEnd_8230714 : Nat := 52176696440619944781761

theorem tailTrace_8230714 : CollatzResearch.WordTrace tailWord_8230714 prefixEnd_8230714 52176696440619944781761 := by
  unfold tailWord_8230714
  simp only [CollatzResearch.WordTrace]
  refine ⟨75049700475884086720822799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200132534602357564588860797 75049700475884086720822799)
  ·
    refine ⟨112574550713826130081234199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75049700475884086720822799 112574550713826130081234199)
    ·
      refine ⟨168861826070739195121851299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112574550713826130081234199 168861826070739195121851299)
      ·
        refine ⟨253292739106108792682776949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168861826070739195121851299 253292739106108792682776949)
        ·
          refine ⟨23746194291197699314010339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 253292739106108792682776949 23746194291197699314010339)
          ·
            refine ⟨35619291436796548971015509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23746194291197699314010339 35619291436796548971015509)
            ·
              refine ⟨52176696440619944781761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 35619291436796548971015509 52176696440619944781761)
              ·
                rfl

theorem cell23_8230714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 11].length) (baseStart_8230714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8230714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8230714 prefixEnd_8230714 := by exact prefixLift 8230714
  have htrace : WordTrace (prefixWord ++ tailWord_8230714) baseStart_8230714 baseEnd_8230714 := by
    simpa [prefixWord, tailWord_8230714, baseEnd_8230714] using wordTrace_append hprefix tailTrace_8230714
  have hstable : (prefixWord ++ tailWord_8230714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8230714).length < 2 ^ (prefixWord ++ tailWord_8230714).sum := by decide
  have hdescent : baseEnd_8230714 < baseStart_8230714 := by decide
  rcases family_descends (prefixWord ++ tailWord_8230714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8230718 : List Nat := [4, 2, 1, 2, 2, 1, 2, 1, 4, 4]
def baseStart_8230718 : Nat := 118140960795 + 8230718 * 2 ^ 59
def prefixEnd_8230718 : Nat := 4983230072969 + 3 ^ 40 * 8230718 * 2
def baseEnd_8230718 : Nat := 1408771488537611170557541

theorem tailTrace_8230718 : CollatzResearch.WordTrace tailWord_8230718 prefixEnd_8230718 1408771488537611170557541 := by
  unfold tailWord_8230718
  simp only [CollatzResearch.WordTrace]
  refine ⟨37524868474440231945804601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200132631863681237044291205 37524868474440231945804601)
  ·
    refine ⟨28143651355830173959353451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37524868474440231945804601 28143651355830173959353451)
    ·
      refine ⟨42215477033745260939030177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28143651355830173959353451 42215477033745260939030177)
      ·
        refine ⟨31661607775308945704272633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42215477033745260939030177 31661607775308945704272633)
        ·
          refine ⟨23746205831481709278204475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31661607775308945704272633 23746205831481709278204475)
          ·
            refine ⟨35619308747222563917306713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23746205831481709278204475 35619308747222563917306713)
            ·
              refine ⟨26714481560416922937980035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35619308747222563917306713 26714481560416922937980035)
              ·
                refine ⟨40071722340625384406970053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26714481560416922937980035 40071722340625384406970053)
                ·
                  refine ⟨7513447938867259576306885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40071722340625384406970053 7513447938867259576306885)
                  ·
                    refine ⟨1408771488537611170557541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7513447938867259576306885 1408771488537611170557541)
                    ·
                      rfl

theorem cell23_8230718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 1, 4, 4].length) (baseStart_8230718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8230718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8230718 prefixEnd_8230718 := by exact prefixLift 8230718
  have htrace : WordTrace (prefixWord ++ tailWord_8230718) baseStart_8230718 baseEnd_8230718 := by
    simpa [prefixWord, tailWord_8230718, baseEnd_8230718] using wordTrace_append hprefix tailTrace_8230718
  have hstable : (prefixWord ++ tailWord_8230718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8230718).length < 2 ^ (prefixWord ++ tailWord_8230718).sum := by decide
  have hdescent : baseEnd_8230718 < baseStart_8230718 := by decide
  rcases family_descends (prefixWord ++ tailWord_8230718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8230762 : List Nat := [3, 1, 3, 4, 2, 1, 1, 1, 1, 1, 5]
def baseStart_8230762 : Nat := 118140960795 + 8230762 * 2 ^ 59
def prefixEnd_8230762 : Nat := 4983230072969 + 3 ^ 40 * 8230762 * 2
def baseEnd_8230762 : Nat := 4226337058761631339522421

theorem tailTrace_8230762 : CollatzResearch.WordTrace tailWord_8230762 prefixEnd_8230762 4226337058761631339522421 := by
  unfold tailWord_8230762
  simp only [CollatzResearch.WordTrace]
  refine ⟨75050138151840612770259635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200133701738241634054025693 75050138151840612770259635)
  ·
    refine ⟨112575207227760919155389453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75050138151840612770259635 112575207227760919155389453)
    ·
      refine ⟨42215702710410344683271045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112575207227760919155389453 42215702710410344683271045)
      ·
        refine ⟨7915444258201939628113321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42215702710410344683271045 7915444258201939628113321)
        ·
          refine ⟨5936583193651454721084991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7915444258201939628113321 5936583193651454721084991)
          ·
            refine ⟨8904874790477182081627487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5936583193651454721084991 8904874790477182081627487)
            ·
              refine ⟨13357312185715773122441231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8904874790477182081627487 13357312185715773122441231)
              ·
                refine ⟨20035968278573659683661847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13357312185715773122441231 20035968278573659683661847)
                ·
                  refine ⟨30053952417860489525492771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20035968278573659683661847 30053952417860489525492771)
                  ·
                    refine ⟨45080928626790734288239157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30053952417860489525492771 45080928626790734288239157)
                    ·
                      refine ⟨4226337058761631339522421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45080928626790734288239157 4226337058761631339522421)
                      ·
                        rfl

theorem cell23_8230762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_8230762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8230762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8230762 prefixEnd_8230762 := by exact prefixLift 8230762
  have htrace : WordTrace (prefixWord ++ tailWord_8230762) baseStart_8230762 baseEnd_8230762 := by
    simpa [prefixWord, tailWord_8230762, baseEnd_8230762] using wordTrace_append hprefix tailTrace_8230762
  have hstable : (prefixWord ++ tailWord_8230762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8230762).length < 2 ^ (prefixWord ++ tailWord_8230762).sum := by decide
  have hdescent : baseEnd_8230762 < baseStart_8230762 := by decide
  rcases family_descends (prefixWord ++ tailWord_8230762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8230831 : List Nat := [1, 1, 2, 1, 2, 2, 3, 1, 4, 3, 3]
def baseStart_8230831 : Nat := 118140960795 + 8230831 * 2 ^ 59
def prefixEnd_8230831 : Nat := 4983230072969 + 3 ^ 40 * 8230831 * 2
def baseEnd_8230831 : Nat := 4226372488926791569559603

theorem tailTrace_8230831 : CollatzResearch.WordTrace tailWord_8230831 prefixEnd_8230831 4226372488926791569559603 := by
  unfold tailWord_8230831
  simp only [CollatzResearch.WordTrace]
  refine ⟨300203069244112475865300347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200135379496074983910200231 300203069244112475865300347)
  ·
    refine ⟨450304603866168713797950521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300203069244112475865300347 450304603866168713797950521)
    ·
      refine ⟨337728452899626535348462891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 450304603866168713797950521 337728452899626535348462891)
      ·
        refine ⟨506592679349439803022694337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337728452899626535348462891 506592679349439803022694337)
        ·
          refine ⟨379944509512079852267020753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 506592679349439803022694337 379944509512079852267020753)
          ·
            refine ⟨284958382134059889200265565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 379944509512079852267020753 284958382134059889200265565)
            ·
              refine ⟨106859393300272458450099587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 284958382134059889200265565 106859393300272458450099587)
              ·
                refine ⟨160289089950408687675149381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106859393300272458450099587 160289089950408687675149381)
                ·
                  refine ⟨30054204365701628939090509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 160289089950408687675149381 30054204365701628939090509)
                  ·
                    refine ⟨11270326637138110852158941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30054204365701628939090509 11270326637138110852158941)
                    ·
                      refine ⟨4226372488926791569559603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11270326637138110852158941 4226372488926791569559603)
                      ·
                        rfl

theorem cell23_8230831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 4, 3, 3].length) (baseStart_8230831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8230831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8230831 prefixEnd_8230831 := by exact prefixLift 8230831
  have htrace : WordTrace (prefixWord ++ tailWord_8230831) baseStart_8230831 baseEnd_8230831 := by
    simpa [prefixWord, tailWord_8230831, baseEnd_8230831] using wordTrace_append hprefix tailTrace_8230831
  have hstable : (prefixWord ++ tailWord_8230831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8230831).length < 2 ^ (prefixWord ++ tailWord_8230831).sum := by decide
  have hdescent : baseEnd_8230831 < baseStart_8230831 := by decide
  rcases family_descends (prefixWord ++ tailWord_8230831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8230858 : List Nat := [3, 1, 2, 1, 2, 1, 2, 2, 2, 5, 2]
def baseStart_8230858 : Nat := 118140960795 + 8230858 * 2 ^ 59
def prefixEnd_8230858 : Nat := 4983230072969 + 3 ^ 40 * 8230858 * 2
def baseEnd_8230858 : Nat := 4226386352904462963921979

theorem tailTrace_8230858 : CollatzResearch.WordTrace tailWord_8230858 prefixEnd_8230858 4226386352904462963921979 := by
  unfold tailWord_8230858
  simp only [CollatzResearch.WordTrace]
  refine ⟨75051013503753664869133307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200136036010009772984355485 75051013503753664869133307)
  ·
    refine ⟨112576520255630497303699961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75051013503753664869133307 112576520255630497303699961)
    ·
      refine ⟨84432390191722872977774971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112576520255630497303699961 84432390191722872977774971)
      ·
        refine ⟨126648585287584309466662457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84432390191722872977774971 126648585287584309466662457)
        ·
          refine ⟨94986438965688232099996843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126648585287584309466662457 94986438965688232099996843)
          ·
            refine ⟨142479658448532348149995265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94986438965688232099996843 142479658448532348149995265)
            ·
              refine ⟨106859743836399261112496449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142479658448532348149995265 106859743836399261112496449)
              ·
                refine ⟨80144807877299445834372337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106859743836399261112496449 80144807877299445834372337)
                ·
                  refine ⟨60108605907974584375779253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80144807877299445834372337 60108605907974584375779253)
                  ·
                    refine ⟨5635181803872617285229305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60108605907974584375779253 5635181803872617285229305)
                    ·
                      refine ⟨4226386352904462963921979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5635181803872617285229305 4226386352904462963921979)
                      ·
                        rfl

theorem cell23_8230858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 2, 2, 5, 2].length) (baseStart_8230858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8230858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8230858 prefixEnd_8230858 := by exact prefixLift 8230858
  have htrace : WordTrace (prefixWord ++ tailWord_8230858) baseStart_8230858 baseEnd_8230858 := by
    simpa [prefixWord, tailWord_8230858, baseEnd_8230858] using wordTrace_append hprefix tailTrace_8230858
  have hstable : (prefixWord ++ tailWord_8230858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8230858).length < 2 ^ (prefixWord ++ tailWord_8230858).sum := by decide
  have hdescent : baseEnd_8230858 < baseStart_8230858 := by decide
  rcases family_descends (prefixWord ++ tailWord_8230858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8230868 : List Nat := [2, 4, 1, 2, 1, 1, 2, 3, 2, 5]
def baseStart_8230868 : Nat := 118140960795 + 8230868 * 2 ^ 59
def prefixEnd_8230868 : Nat := 4983230072969 + 3 ^ 40 * 8230868 * 2
def baseEnd_8230868 : Nat := 1408797162570335974932311

theorem tailTrace_8230868 : CollatzResearch.WordTrace tailWord_8230868 prefixEnd_8230868 1408797162570335974932311 := by
  unfold tailWord_8230868
  simp only [CollatzResearch.WordTrace]
  refine ⟨150102209372489215592198629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200136279163318954122931505 150102209372489215592198629)
  ·
    refine ⟨28144164257341727923537243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150102209372489215592198629 28144164257341727923537243)
    ·
      refine ⟨42216246386012591885305865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28144164257341727923537243 42216246386012591885305865)
      ·
        refine ⟨31662184789509443913979399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42216246386012591885305865 31662184789509443913979399)
        ·
          refine ⟨47493277184264165870969099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31662184789509443913979399 47493277184264165870969099)
          ·
            refine ⟨71239915776396248806453649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47493277184264165870969099 71239915776396248806453649)
            ·
              refine ⟨53429936832297186604840237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71239915776396248806453649 53429936832297186604840237)
              ·
                refine ⟨20036226312111444976815089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53429936832297186604840237 20036226312111444976815089)
                ·
                  refine ⟨15027169734083583732611317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20036226312111444976815089 15027169734083583732611317)
                  ·
                    refine ⟨1408797162570335974932311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15027169734083583732611317 1408797162570335974932311)
                    ·
                      rfl

theorem cell23_8230868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 3, 2, 5].length) (baseStart_8230868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8230868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8230868 prefixEnd_8230868 := by exact prefixLift 8230868
  have htrace : WordTrace (prefixWord ++ tailWord_8230868) baseStart_8230868 baseEnd_8230868 := by
    simpa [prefixWord, tailWord_8230868, baseEnd_8230868] using wordTrace_append hprefix tailTrace_8230868
  have hstable : (prefixWord ++ tailWord_8230868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8230868).length < 2 ^ (prefixWord ++ tailWord_8230868).sum := by decide
  have hdescent : baseEnd_8230868 < baseStart_8230868 := by decide
  rcases family_descends (prefixWord ++ tailWord_8230868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8230871 : List Nat := [1, 1, 3, 2, 1, 1, 3, 3, 1, 3, 4]
def baseStart_8230871 : Nat := 118140960795 + 8230871 * 2 ^ 59
def prefixEnd_8230871 : Nat := 4983230072969 + 3 ^ 40 * 8230871 * 2
def baseEnd_8230871 : Nat := 4226393028152971413059419

theorem tailTrace_8230871 : CollatzResearch.WordTrace tailWord_8230871 prefixEnd_8230871 4226393028152971413059419 := by
  unfold tailWord_8230871
  simp only [CollatzResearch.WordTrace]
  refine ⟨300204528163967562696756467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200136352109311708464504311 300204528163967562696756467)
  ·
    refine ⟨450306792245951344045134701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300204528163967562696756467 450306792245951344045134701)
    ·
      refine ⟨168865047092231754016925513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 450306792245951344045134701 168865047092231754016925513)
      ·
        refine ⟨126648785319173815512694135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168865047092231754016925513 126648785319173815512694135)
        ·
          refine ⟨189973177978760723269041203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126648785319173815512694135 189973177978760723269041203)
          ·
            refine ⟨284959766968141084903561805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189973177978760723269041203 284959766968141084903561805)
            ·
              refine ⟨106859912613052906838835677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 284959766968141084903561805 106859912613052906838835677)
              ·
                refine ⟨40072467229894840064563379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106859912613052906838835677 40072467229894840064563379)
                ·
                  refine ⟨60108700844842260096845069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40072467229894840064563379 60108700844842260096845069)
                  ·
                    refine ⟨22540762816815847536316901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60108700844842260096845069 22540762816815847536316901)
                    ·
                      refine ⟨4226393028152971413059419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22540762816815847536316901 4226393028152971413059419)
                      ·
                        rfl

theorem cell23_8230871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 3, 1, 3, 4].length) (baseStart_8230871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8230871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8230871 prefixEnd_8230871 := by exact prefixLift 8230871
  have htrace : WordTrace (prefixWord ++ tailWord_8230871) baseStart_8230871 baseEnd_8230871 := by
    simpa [prefixWord, tailWord_8230871, baseEnd_8230871] using wordTrace_append hprefix tailTrace_8230871
  have hstable : (prefixWord ++ tailWord_8230871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8230871).length < 2 ^ (prefixWord ++ tailWord_8230871).sum := by decide
  have hdescent : baseEnd_8230871 < baseStart_8230871 := by decide
  rcases family_descends (prefixWord ++ tailWord_8230871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8230908 : List Nat := [2, 2, 2, 1, 2, 2, 1, 2, 4, 2, 3]
def baseStart_8230908 : Nat := 118140960795 + 8230908 * 2 ^ 59
def prefixEnd_8230908 : Nat := 4983230072969 + 3 ^ 40 * 8230908 * 2
def baseEnd_8230908 : Nat := 4226412026937187768296749

theorem tailTrace_8230908 : CollatzResearch.WordTrace tailWord_8230908 prefixEnd_8230908 4226412026937187768296749 := by
  unfold tailWord_8230908
  simp only [CollatzResearch.WordTrace]
  refine ⟨150102938832416759007926689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200137251776555678677235585 150102938832416759007926689)
  ·
    refine ⟨112577204124312569255945017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150102938832416759007926689 112577204124312569255945017)
    ·
      refine ⟨84432903093234426941958763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112577204124312569255945017 84432903093234426941958763)
      ·
        refine ⟨126649354639851640412938145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84432903093234426941958763 126649354639851640412938145)
        ·
          refine ⟨94987015979888730309703609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126649354639851640412938145 94987015979888730309703609)
          ·
            refine ⟨71240261984916547732277707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94987015979888730309703609 71240261984916547732277707)
            ·
              refine ⟨106860392977374821598416561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71240261984916547732277707 106860392977374821598416561)
              ·
                refine ⟨80145294733031116198812421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106860392977374821598416561 80145294733031116198812421)
                ·
                  refine ⟨15027242762443334287277329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80145294733031116198812421 15027242762443334287277329)
                  ·
                    refine ⟨11270432071832500715457997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15027242762443334287277329 11270432071832500715457997)
                    ·
                      refine ⟨4226412026937187768296749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11270432071832500715457997 4226412026937187768296749)
                      ·
                        rfl

theorem cell23_8230908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 2, 4, 2, 3].length) (baseStart_8230908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8230908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8230908 prefixEnd_8230908 := by exact prefixLift 8230908
  have htrace : WordTrace (prefixWord ++ tailWord_8230908) baseStart_8230908 baseEnd_8230908 := by
    simpa [prefixWord, tailWord_8230908, baseEnd_8230908] using wordTrace_append hprefix tailTrace_8230908
  have hstable : (prefixWord ++ tailWord_8230908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8230908).length < 2 ^ (prefixWord ++ tailWord_8230908).sum := by decide
  have hdescent : baseEnd_8230908 < baseStart_8230908 := by decide
  rcases family_descends (prefixWord ++ tailWord_8230908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8230945 : List Nat := [1, 2, 3, 2, 4, 1, 2, 2, 6]
def baseStart_8230945 : Nat := 118140960795 + 8230945 * 2 ^ 59
def prefixEnd_8230945 : Nat := 4983230072969 + 3 ^ 40 * 8230945 * 2
def baseEnd_8230945 : Nat := 469603447302378235948231

theorem tailTrace_8230945 : CollatzResearch.WordTrace tailWord_8230945 prefixEnd_8230945 469603447302378235948231 := by
  unfold tailWord_8230945
  simp only [CollatzResearch.WordTrace]
  refine ⟨300207227165699473334950289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200138151443799648889966859 300207227165699473334950289)
  ·
    refine ⟨225155420374274605001212717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300207227165699473334950289 225155420374274605001212717)
    ·
      refine ⟨84433282640352976875454769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225155420374274605001212717 84433282640352976875454769)
      ·
        refine ⟨63324961980264732656591077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84433282640352976875454769 63324961980264732656591077)
        ·
          refine ⟨11873430371299637373110827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63324961980264732656591077 11873430371299637373110827)
          ·
            refine ⟨17810145556949456059666241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11873430371299637373110827 17810145556949456059666241)
            ·
              refine ⟨13357609167712092044749681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17810145556949456059666241 13357609167712092044749681)
              ·
                refine ⟨10018206875784069033562261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13357609167712092044749681 10018206875784069033562261)
                ·
                  refine ⟨469603447302378235948231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10018206875784069033562261 469603447302378235948231)
                  ·
                    rfl

theorem cell23_8230945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 2, 2, 6].length) (baseStart_8230945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8230945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8230945 prefixEnd_8230945 := by exact prefixLift 8230945
  have htrace : WordTrace (prefixWord ++ tailWord_8230945) baseStart_8230945 baseEnd_8230945 := by
    simpa [prefixWord, tailWord_8230945, baseEnd_8230945] using wordTrace_append hprefix tailTrace_8230945
  have hstable : (prefixWord ++ tailWord_8230945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8230945).length < 2 ^ (prefixWord ++ tailWord_8230945).sum := by decide
  have hdescent : baseEnd_8230945 < baseStart_8230945 := by decide
  rcases family_descends (prefixWord ++ tailWord_8230945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8230949 : List Nat := [1, 3, 1, 2, 2, 5, 2, 2, 1, 4]
def baseStart_8230949 : Nat := 118140960795 + 8230949 * 2 ^ 59
def prefixEnd_8230949 : Nat := 4983230072969 + 3 ^ 40 * 8230949 * 2
def baseEnd_8230949 : Nat := 1408811026548007369294687

theorem tailTrace_8230949 : CollatzResearch.WordTrace tailWord_8230949 prefixEnd_8230949 1408811026548007369294687 := by
  unfold tailWord_8230949
  simp only [CollatzResearch.WordTrace]
  refine ⟨300207373057684982018095901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200138248705123321345397267 300207373057684982018095901)
  ·
    refine ⟨112577764896631868256785963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 300207373057684982018095901 112577764896631868256785963)
    ·
      refine ⟨168866647344947802385178945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112577764896631868256785963 168866647344947802385178945)
      ·
        refine ⟨126649985508710851788884209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168866647344947802385178945 126649985508710851788884209)
        ·
          refine ⟨94987489131533138841663157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126649985508710851788884209 94987489131533138841663157)
          ·
            refine ⟨8905077106081231766405921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 94987489131533138841663157 8905077106081231766405921)
            ·
              refine ⟨6678807829560923824804441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8905077106081231766405921 6678807829560923824804441)
              ·
                refine ⟨5009105872170692868603331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6678807829560923824804441 5009105872170692868603331)
                ·
                  refine ⟨7513658808256039302904997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5009105872170692868603331 7513658808256039302904997)
                  ·
                    refine ⟨1408811026548007369294687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7513658808256039302904997 1408811026548007369294687)
                    ·
                      rfl

theorem cell23_8230949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 2, 2, 1, 4].length) (baseStart_8230949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8230949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8230949 prefixEnd_8230949 := by exact prefixLift 8230949
  have htrace : WordTrace (prefixWord ++ tailWord_8230949) baseStart_8230949 baseEnd_8230949 := by
    simpa [prefixWord, tailWord_8230949, baseEnd_8230949] using wordTrace_append hprefix tailTrace_8230949
  have hstable : (prefixWord ++ tailWord_8230949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8230949).length < 2 ^ (prefixWord ++ tailWord_8230949).sum := by decide
  have hdescent : baseEnd_8230949 < baseStart_8230949 := by decide
  rcases family_descends (prefixWord ++ tailWord_8230949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8230965 : List Nat := [1, 3, 3, 1, 1, 1, 2, 2, 4, 3, 2]
def baseStart_8230965 : Nat := 118140960795 + 8230965 * 2 ^ 59
def prefixEnd_8230965 : Nat := 4983230072969 + 3 ^ 40 * 8230965 * 2
def baseEnd_8230965 : Nat := 4226441295334494045283987

theorem tailTrace_8230965 : CollatzResearch.WordTrace tailWord_8230965 prefixEnd_8230965 4226441295334494045283987 := by
  unfold tailWord_8230965
  simp only [CollatzResearch.WordTrace]
  refine ⟨300207956625627016750678349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200138637750418011167118899 300207956625627016750678349)
  ·
    refine ⟨112577983734610131281504381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 300207956625627016750678349 112577983734610131281504381)
    ·
      refine ⟨42216743900478799230564143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112577983734610131281504381 42216743900478799230564143)
      ·
        refine ⟨63325115850718198845846215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42216743900478799230564143 63325115850718198845846215)
        ·
          refine ⟨94987673776077298268769323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63325115850718198845846215 94987673776077298268769323)
          ·
            refine ⟨142481510664115947403153985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94987673776077298268769323 142481510664115947403153985)
            ·
              refine ⟨106861132998086960552365489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142481510664115947403153985 106861132998086960552365489)
              ·
                refine ⟨80145849748565220414274117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106861132998086960552365489 80145849748565220414274117)
                ·
                  refine ⟨15027346827855978827676397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80145849748565220414274117 15027346827855978827676397)
                  ·
                    refine ⟨5635255060445992060378649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15027346827855978827676397 5635255060445992060378649)
                    ·
                      refine ⟨4226441295334494045283987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5635255060445992060378649 4226441295334494045283987)
                      ·
                        rfl

theorem cell23_8230965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 4, 3, 2].length) (baseStart_8230965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8230965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8230965 prefixEnd_8230965 := by exact prefixLift 8230965
  have htrace : WordTrace (prefixWord ++ tailWord_8230965) baseStart_8230965 baseEnd_8230965 := by
    simpa [prefixWord, tailWord_8230965, baseEnd_8230965] using wordTrace_append hprefix tailTrace_8230965
  have hstable : (prefixWord ++ tailWord_8230965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8230965).length < 2 ^ (prefixWord ++ tailWord_8230965).sum := by decide
  have hdescent : baseEnd_8230965 < baseStart_8230965 := by decide
  rcases family_descends (prefixWord ++ tailWord_8230965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8230971 : List Nat := [1, 1, 1, 1, 1, 2, 1, 4, 5, 6]
def baseStart_8230971 : Nat := 118140960795 + 8230971 * 2 ^ 59
def prefixEnd_8230971 : Nat := 4983230072969 + 3 ^ 40 * 8230971 * 2
def baseEnd_8230971 : Nat := 1408814792072807007269653

theorem tailTrace_8230971 : CollatzResearch.WordTrace tailWord_8230971 prefixEnd_8230971 1408814792072807007269653 := by
  unfold tailWord_8230971
  simp only [CollatzResearch.WordTrace]
  refine ⟨300208175463605279775396767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200138783642403519850264511 300208175463605279775396767)
  ·
    refine ⟨450312263195407919663095151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300208175463605279775396767 450312263195407919663095151)
    ·
      refine ⟨675468394793111879494642727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 450312263195407919663095151 675468394793111879494642727)
      ·
        refine ⟨1013202592189667819241964091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 675468394793111879494642727 1013202592189667819241964091)
        ·
          refine ⟨1519803888284501728862946137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1013202592189667819241964091 1519803888284501728862946137)
          ·
            refine ⟨1139852916213376296647209603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1519803888284501728862946137 1139852916213376296647209603)
            ·
              refine ⟨1709779374320064444970814405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1139852916213376296647209603 1709779374320064444970814405)
              ·
                refine ⟨320583632685012083432027701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1709779374320064444970814405 320583632685012083432027701)
                ·
                  refine ⟨30054715564219882821752597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 320583632685012083432027701 30054715564219882821752597)
                  ·
                    refine ⟨1408814792072807007269653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30054715564219882821752597 1408814792072807007269653)
                    ·
                      rfl

theorem cell23_8230971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 5, 6].length) (baseStart_8230971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8230971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8230971 prefixEnd_8230971 := by exact prefixLift 8230971
  have htrace : WordTrace (prefixWord ++ tailWord_8230971) baseStart_8230971 baseEnd_8230971 := by
    simpa [prefixWord, tailWord_8230971, baseEnd_8230971] using wordTrace_append hprefix tailTrace_8230971
  have hstable : (prefixWord ++ tailWord_8230971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8230971).length < 2 ^ (prefixWord ++ tailWord_8230971).sum := by decide
  have hdescent : baseEnd_8230971 < baseStart_8230971 := by decide
  rcases family_descends (prefixWord ++ tailWord_8230971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8230988 : List Nat := [2, 2, 1, 3, 1, 1, 4, 2, 1, 6]
def baseStart_8230988 : Nat := 118140960795 + 8230988 * 2 ^ 59
def prefixEnd_8230988 : Nat := 4983230072969 + 3 ^ 40 * 8230988 * 2
def baseEnd_8230988 : Nat := 1408817701796515818432127

theorem tailTrace_8230988 : CollatzResearch.WordTrace tailWord_8230988 prefixEnd_8230988 1408817701796515818432127 := by
  unfold tailWord_8230988
  simp only [CollatzResearch.WordTrace]
  refine ⟨150104397752271845839382809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200139197003029127785843745 150104397752271845839382809)
  ·
    refine ⟨112578298314203884379537107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150104397752271845839382809 112578298314203884379537107)
    ·
      refine ⟨168867447471305826569305661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112578298314203884379537107 168867447471305826569305661)
      ·
        refine ⟨63325292801739684963489623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168867447471305826569305661 63325292801739684963489623)
        ·
          refine ⟨94987939202609527445234435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63325292801739684963489623 94987939202609527445234435)
          ·
            refine ⟨142481908803914291167851653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94987939202609527445234435 142481908803914291167851653)
            ·
              refine ⟨26715357900733929593972185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 142481908803914291167851653 26715357900733929593972185)
              ·
                refine ⟨20036518425550447195479139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26715357900733929593972185 20036518425550447195479139)
                ·
                  refine ⟨30054777638325670793218709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20036518425550447195479139 30054777638325670793218709)
                  ·
                    refine ⟨1408817701796515818432127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30054777638325670793218709 1408817701796515818432127)
                    ·
                      rfl

theorem cell23_8230988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 2, 1, 6].length) (baseStart_8230988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8230988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8230988 prefixEnd_8230988 := by exact prefixLift 8230988
  have htrace : WordTrace (prefixWord ++ tailWord_8230988) baseStart_8230988 baseEnd_8230988 := by
    simpa [prefixWord, tailWord_8230988, baseEnd_8230988] using wordTrace_append hprefix tailTrace_8230988
  have hstable : (prefixWord ++ tailWord_8230988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8230988).length < 2 ^ (prefixWord ++ tailWord_8230988).sum := by decide
  have hdescent : baseEnd_8230988 < baseStart_8230988 := by decide
  rcases family_descends (prefixWord ++ tailWord_8230988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8231001 : List Nat := [1, 2, 1, 2, 2, 1, 14]
def baseStart_8231001 : Nat := 118140960795 + 8231001 * 2 ^ 59
def prefixEnd_8231001 : Nat := 4983230072969 + 3 ^ 40 * 8231001 * 2
def baseEnd_8231001 : Nat := 52178515810346369190541

theorem tailTrace_8231001 : CollatzResearch.WordTrace tailWord_8231001 prefixEnd_8231001 52178515810346369190541 := by
  unfold tailWord_8231001
  simp only [CollatzResearch.WordTrace]
  refine ⟨300209269653496594898988857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200139513102331063265992571 300209269653496594898988857)
  ·
    refine ⟨225156952240122446174241643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300209269653496594898988857 225156952240122446174241643)
    ·
      refine ⟨337735428360183669261362465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225156952240122446174241643 337735428360183669261362465)
      ·
        refine ⟨253301571270137751946021849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 337735428360183669261362465 253301571270137751946021849)
        ·
          refine ⟨189976178452603313959516387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 253301571270137751946021849 189976178452603313959516387)
          ·
            refine ⟨284964267678904970939274581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189976178452603313959516387 284964267678904970939274581)
            ·
              refine ⟨52178515810346369190541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 14 284964267678904970939274581 52178515810346369190541)
              ·
                rfl

theorem cell23_8231001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 14].length) (baseStart_8231001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8231001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8231001 prefixEnd_8231001 := by exact prefixLift 8231001
  have htrace : WordTrace (prefixWord ++ tailWord_8231001) baseStart_8231001 baseEnd_8231001 := by
    simpa [prefixWord, tailWord_8231001, baseEnd_8231001] using wordTrace_append hprefix tailTrace_8231001
  have hstable : (prefixWord ++ tailWord_8231001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8231001).length < 2 ^ (prefixWord ++ tailWord_8231001).sum := by decide
  have hdescent : baseEnd_8231001 < baseStart_8231001 := by decide
  rcases family_descends (prefixWord ++ tailWord_8231001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8231012 : List Nat := [2, 3, 1, 1, 2, 1, 3, 3, 3, 2, 2]
def baseStart_8231012 : Nat := 118140960795 + 8231012 * 2 ^ 59
def prefixEnd_8231012 : Nat := 4983230072969 + 3 ^ 40 * 8231012 * 2
def baseEnd_8231012 : Nat := 4226465428925255361396271

theorem tailTrace_8231012 : CollatzResearch.WordTrace tailWord_8231012 prefixEnd_8231012 4226465428925255361396271 := by
  unfold tailWord_8231012
  simp only [CollatzResearch.WordTrace]
  refine ⟨150104835428228371888819645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200139780570971162518426193 150104835428228371888819645)
  ·
    refine ⟨56289313285585639458307367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150104835428228371888819645 56289313285585639458307367)
    ·
      refine ⟨84433969928378459187461051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56289313285585639458307367 84433969928378459187461051)
      ·
        refine ⟨126650954892567688781191577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84433969928378459187461051 126650954892567688781191577)
        ·
          refine ⟨94988216169425766585893683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126650954892567688781191577 94988216169425766585893683)
          ·
            refine ⟨142482324254138649878840525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94988216169425766585893683 142482324254138649878840525)
            ·
              refine ⟨53430871595301993704565197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142482324254138649878840525 53430871595301993704565197)
              ·
                refine ⟨20036576848238247639211949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53430871595301993704565197 20036576848238247639211949)
                ·
                  refine ⟨7513716318089342864704481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20036576848238247639211949 7513716318089342864704481)
                  ·
                    refine ⟨5635287238567007148528361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7513716318089342864704481 5635287238567007148528361)
                    ·
                      refine ⟨4226465428925255361396271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5635287238567007148528361 4226465428925255361396271)
                      ·
                        rfl

theorem cell23_8231012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 3, 3, 2, 2].length) (baseStart_8231012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8231012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8231012 prefixEnd_8231012 := by exact prefixLift 8231012
  have htrace : WordTrace (prefixWord ++ tailWord_8231012) baseStart_8231012 baseEnd_8231012 := by
    simpa [prefixWord, tailWord_8231012, baseEnd_8231012] using wordTrace_append hprefix tailTrace_8231012
  have hstable : (prefixWord ++ tailWord_8231012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8231012).length < 2 ^ (prefixWord ++ tailWord_8231012).sum := by decide
  have hdescent : baseEnd_8231012 < baseStart_8231012 := by decide
  rcases family_descends (prefixWord ++ tailWord_8231012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8231063 : List Nat := [1, 1, 3, 3, 4, 1, 3, 2, 1, 2, 2]
def baseStart_8231063 : Nat := 118140960795 + 8231063 * 2 ^ 59
def prefixEnd_8231063 : Nat := 4983230072969 + 3 ^ 40 * 8231063 * 2
def baseEnd_8231063 : Nat := 4226491616438634661858537

theorem tailTrace_8231063 : CollatzResearch.WordTrace tailWord_8231063 prefixEnd_8231063 4226491616438634661858537 := by
  unfold tailWord_8231063
  simp only [CollatzResearch.WordTrace]
  refine ⟨300211530979271979487745843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200141020652847986325163895 300211530979271979487745843)
  ·
    refine ⟨450317296468907969231618765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300211530979271979487745843 450317296468907969231618765)
    ·
      refine ⟨168868986175840488461857037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 450317296468907969231618765 168868986175840488461857037)
      ·
        refine ⟨63325869815940183173196389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168868986175840488461857037 63325869815940183173196389)
        ·
          refine ⟨11873600590488784344974323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63325869815940183173196389 11873600590488784344974323)
          ·
            refine ⟨17810400885733176517461485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11873600590488784344974323 17810400885733176517461485)
            ·
              refine ⟨6678900332149941194048057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17810400885733176517461485 6678900332149941194048057)
              ·
                refine ⟨5009175249112455895536043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6678900332149941194048057 5009175249112455895536043)
                ·
                  refine ⟨7513762873668683843304065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5009175249112455895536043 7513762873668683843304065)
                  ·
                    refine ⟨5635322155251512882478049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7513762873668683843304065 5635322155251512882478049)
                    ·
                      refine ⟨4226491616438634661858537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5635322155251512882478049 4226491616438634661858537)
                      ·
                        rfl

theorem cell23_8231063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 3, 2, 1, 2, 2].length) (baseStart_8231063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8231063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8231063 prefixEnd_8231063 := by exact prefixLift 8231063
  have htrace : WordTrace (prefixWord ++ tailWord_8231063) baseStart_8231063 baseEnd_8231063 := by
    simpa [prefixWord, tailWord_8231063, baseEnd_8231063] using wordTrace_append hprefix tailTrace_8231063
  have hstable : (prefixWord ++ tailWord_8231063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8231063).length < 2 ^ (prefixWord ++ tailWord_8231063).sum := by decide
  have hdescent : baseEnd_8231063 < baseStart_8231063 := by decide
  rcases family_descends (prefixWord ++ tailWord_8231063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8231089 : List Nat := [1, 2, 2, 5, 2, 1, 1, 1, 3, 3, 2]
def baseStart_8231089 : Nat := 118140960795 + 8231089 * 2 ^ 59
def prefixEnd_8231089 : Nat := 4983230072969 + 3 ^ 40 * 8231089 * 2
def baseEnd_8231089 : Nat := 4226504966935651560133417

theorem tailTrace_8231089 : CollatzResearch.WordTrace tailWord_8231089 prefixEnd_8231089 4226504966935651560133417 := by
  unfold tailWord_8231089
  simp only [CollatzResearch.WordTrace]
  refine ⟨300212479277177785928192321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200141652851451857285461547 300212479277177785928192321)
  ·
    refine ⟨225159359457883339446144241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300212479277177785928192321 225159359457883339446144241)
    ·
      refine ⟨168869519593412504584608181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225159359457883339446144241 168869519593412504584608181)
      ·
        refine ⟨15831517461882422304807017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 168869519593412504584608181 15831517461882422304807017)
        ·
          refine ⟨11873638096411816728605263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15831517461882422304807017 11873638096411816728605263)
          ·
            refine ⟨17810457144617725092907895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11873638096411816728605263 17810457144617725092907895)
            ·
              refine ⟨26715685716926587639361843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17810457144617725092907895 26715685716926587639361843)
              ·
                refine ⟨40073528575389881459042765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26715685716926587639361843 40073528575389881459042765)
                ·
                  refine ⟨15027573215771205547141037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40073528575389881459042765 15027573215771205547141037)
                  ·
                    refine ⟨5635339955914202080177889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15027573215771205547141037 5635339955914202080177889)
                    ·
                      refine ⟨4226504966935651560133417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5635339955914202080177889 4226504966935651560133417)
                      ·
                        rfl

theorem cell23_8231089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 1, 3, 3, 2].length) (baseStart_8231089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8231089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8231089 prefixEnd_8231089 := by exact prefixLift 8231089
  have htrace : WordTrace (prefixWord ++ tailWord_8231089) baseStart_8231089 baseEnd_8231089 := by
    simpa [prefixWord, tailWord_8231089, baseEnd_8231089] using wordTrace_append hprefix tailTrace_8231089
  have hstable : (prefixWord ++ tailWord_8231089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8231089).length < 2 ^ (prefixWord ++ tailWord_8231089).sum := by decide
  have hdescent : baseEnd_8231089 < baseStart_8231089 := by decide
  rcases family_descends (prefixWord ++ tailWord_8231089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8231119 : List Nat := [1, 1, 2, 1, 1, 3, 6, 2, 2, 2, 2]
def baseStart_8231119 : Nat := 118140960795 + 8231119 * 2 ^ 59
def prefixEnd_8231119 : Nat := 4983230072969 + 3 ^ 40 * 8231119 * 2
def baseEnd_8231119 : Nat := 4226520371355286442758279

theorem tailTrace_8231119 : CollatzResearch.WordTrace tailWord_8231119 prefixEnd_8231119 4226520371355286442758279 := by
  unfold tailWord_8231119
  simp only [CollatzResearch.WordTrace]
  refine ⟨300213573467069101051784411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200142382311379400701189607 300213573467069101051784411)
  ·
    refine ⟨450320360200603651577676617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300213573467069101051784411 450320360200603651577676617)
    ·
      refine ⟨337740270150452738683257463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 450320360200603651577676617 337740270150452738683257463)
      ·
        refine ⟨506610405225679108024886195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337740270150452738683257463 506610405225679108024886195)
        ·
          refine ⟨759915607838518662037329293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 506610405225679108024886195 759915607838518662037329293)
          ·
            refine ⟨284968352939444498263998485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 759915607838518662037329293 284968352939444498263998485)
            ·
              refine ⟨13357891544036460856124929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 284968352939444498263998485 13357891544036460856124929)
              ·
                refine ⟨10018418658027345642093697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13357891544036460856124929 10018418658027345642093697)
                ·
                  refine ⟨7513813993520509231570273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10018418658027345642093697 7513813993520509231570273)
                  ·
                    refine ⟨5635360495140381923677705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7513813993520509231570273 5635360495140381923677705)
                    ·
                      refine ⟨4226520371355286442758279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5635360495140381923677705 4226520371355286442758279)
                      ·
                        rfl

theorem cell23_8231119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 6, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 6, 2, 2, 2, 2].length) (baseStart_8231119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8231119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8231119 prefixEnd_8231119 := by exact prefixLift 8231119
  have htrace : WordTrace (prefixWord ++ tailWord_8231119) baseStart_8231119 baseEnd_8231119 := by
    simpa [prefixWord, tailWord_8231119, baseEnd_8231119] using wordTrace_append hprefix tailTrace_8231119
  have hstable : (prefixWord ++ tailWord_8231119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8231119).length < 2 ^ (prefixWord ++ tailWord_8231119).sum := by decide
  have hdescent : baseEnd_8231119 < baseStart_8231119 := by decide
  rcases family_descends (prefixWord ++ tailWord_8231119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8231192 : List Nat := [2, 1, 2, 3, 1, 2, 1, 3, 2, 4, 2]
def baseStart_8231192 : Nat := 118140960795 + 8231192 * 2 ^ 59
def prefixEnd_8231192 : Nat := 4983230072969 + 3 ^ 40 * 8231192 * 2
def baseEnd_8231192 : Nat := 4226557855443064657145443

theorem tailTrace_8231192 : CollatzResearch.WordTrace tailWord_8231192 prefixEnd_8231192 4226557855443064657145443 := by
  unfold tailWord_8231192
  simp only [CollatzResearch.WordTrace]
  refine ⟨150108117997902317259595915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200144157330536423012794553 150108117997902317259595915)
  ·
    refine ⟨225162176996853475889393873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150108117997902317259595915 225162176996853475889393873)
    ·
      refine ⟨168871632747640106917045405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225162176996853475889393873 168871632747640106917045405)
      ·
        refine ⟨63326862280365040093892027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168871632747640106917045405 63326862280365040093892027)
        ·
          refine ⟨94990293420547560140838041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63326862280365040093892027 94990293420547560140838041)
          ·
            refine ⟨71242720065410670105628531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94990293420547560140838041 71242720065410670105628531)
            ·
              refine ⟨106864080098116005158442797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71242720065410670105628531 106864080098116005158442797)
              ·
                refine ⟨40074030036793501934416049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106864080098116005158442797 40074030036793501934416049)
                ·
                  refine ⟨30055522527595126450812037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40074030036793501934416049 30055522527595126450812037)
                  ·
                    refine ⟨5635410473924086209527257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30055522527595126450812037 5635410473924086209527257)
                    ·
                      refine ⟨4226557855443064657145443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5635410473924086209527257 4226557855443064657145443)
                      ·
                        rfl

theorem cell23_8231192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 3, 2, 4, 2].length) (baseStart_8231192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8231192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8231192 prefixEnd_8231192 := by exact prefixLift 8231192
  have htrace : WordTrace (prefixWord ++ tailWord_8231192) baseStart_8231192 baseEnd_8231192 := by
    simpa [prefixWord, tailWord_8231192, baseEnd_8231192] using wordTrace_append hprefix tailTrace_8231192
  have hstable : (prefixWord ++ tailWord_8231192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8231192).length < 2 ^ (prefixWord ++ tailWord_8231192).sum := by decide
  have hdescent : baseEnd_8231192 < baseStart_8231192 := by decide
  rcases family_descends (prefixWord ++ tailWord_8231192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8231195 : List Nat := [1, 1, 1, 1, 1, 1, 7, 2, 1, 4, 3]
def baseStart_8231195 : Nat := 118140960795 + 8231195 * 2 ^ 59
def prefixEnd_8231195 : Nat := 4983230072969 + 3 ^ 40 * 8231195 * 2
def baseEnd_8231195 : Nat := 4226559395885028145407929

theorem tailTrace_8231195 : CollatzResearch.WordTrace tailWord_8231195 prefixEnd_8231195 4226559395885028145407929 := by
  unfold tailWord_8231195
  simp only [CollatzResearch.WordTrace]
  refine ⟨300216345414793766031551039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200144230276529177354367359 300216345414793766031551039)
  ·
    refine ⟨450324518122190649047326559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300216345414793766031551039 450324518122190649047326559)
    ·
      refine ⟨675486777183285973570989839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 450324518122190649047326559 675486777183285973570989839)
      ·
        refine ⟨1013230165774928960356484759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 675486777183285973570989839 1013230165774928960356484759)
        ·
          refine ⟨1519845248662393440534727139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1013230165774928960356484759 1519845248662393440534727139)
          ·
            refine ⟨2279767872993590160802090709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1519845248662393440534727139 2279767872993590160802090709)
            ·
              refine ⟨53432059523287269393799001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2279767872993590160802090709 53432059523287269393799001)
              ·
                refine ⟨40074044642465452045349251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53432059523287269393799001 40074044642465452045349251)
                ·
                  refine ⟨60111066963698178068023877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40074044642465452045349251 60111066963698178068023877)
                  ·
                    refine ⟨11270825055693408387754477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60111066963698178068023877 11270825055693408387754477)
                    ·
                      refine ⟨4226559395885028145407929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11270825055693408387754477 4226559395885028145407929)
                      ·
                        rfl

theorem cell23_8231195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 2, 1, 4, 3].length) (baseStart_8231195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8231195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8231195 prefixEnd_8231195 := by exact prefixLift 8231195
  have htrace : WordTrace (prefixWord ++ tailWord_8231195) baseStart_8231195 baseEnd_8231195 := by
    simpa [prefixWord, tailWord_8231195, baseEnd_8231195] using wordTrace_append hprefix tailTrace_8231195
  have hstable : (prefixWord ++ tailWord_8231195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8231195).length < 2 ^ (prefixWord ++ tailWord_8231195).sum := by decide
  have hdescent : baseEnd_8231195 < baseStart_8231195 := by decide
  rcases family_descends (prefixWord ++ tailWord_8231195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8231249 : List Nat := [1, 2, 2, 1, 4, 4, 2, 1, 6]
def baseStart_8231249 : Nat := 118140960795 + 8231249 * 2 ^ 59
def prefixEnd_8231249 : Nat := 4983230072969 + 3 ^ 40 * 8231249 * 2
def baseEnd_8231249 : Nat := 469620791537818992681409

theorem tailTrace_8231249 : CollatzResearch.WordTrace tailWord_8231249 prefixEnd_8231249 469620791537818992681409 := by
  unfold tailWord_8231249
  simp only [CollatzResearch.WordTrace]
  refine ⟨300218314956598133254016801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200145543304398755502677867 300218314956598133254016801)
  ·
    refine ⟨225163736217448599940512601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300218314956598133254016801 225163736217448599940512601)
    ·
      refine ⟨168872802163086449955384451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225163736217448599940512601 168872802163086449955384451)
      ·
        refine ⟨253309203244629674933076677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168872802163086449955384451 253309203244629674933076677)
        ·
          refine ⟨47495475608368064049951877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 253309203244629674933076677 47495475608368064049951877)
          ·
            refine ⟨8905401676569012009365977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47495475608368064049951877 8905401676569012009365977)
            ·
              refine ⟨6679051257426759007024483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8905401676569012009365977 6679051257426759007024483)
              ·
                refine ⟨10018576886140138510536725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6679051257426759007024483 10018576886140138510536725)
                ·
                  refine ⟨469620791537818992681409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10018576886140138510536725 469620791537818992681409)
                  ·
                    rfl

theorem cell23_8231249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 2, 1, 6].length) (baseStart_8231249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8231249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8231249 prefixEnd_8231249 := by exact prefixLift 8231249
  have htrace : WordTrace (prefixWord ++ tailWord_8231249) baseStart_8231249 baseEnd_8231249 := by
    simpa [prefixWord, tailWord_8231249, baseEnd_8231249] using wordTrace_append hprefix tailTrace_8231249
  have hstable : (prefixWord ++ tailWord_8231249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8231249).length < 2 ^ (prefixWord ++ tailWord_8231249).sum := by decide
  have hdescent : baseEnd_8231249 < baseStart_8231249 := by decide
  rcases family_descends (prefixWord ++ tailWord_8231249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8231269 : List Nat := [1, 3, 1, 3, 1, 3, 1, 3, 2, 3, 2]
def baseStart_8231269 : Nat := 118140960795 + 8231269 * 2 ^ 59
def prefixEnd_8231269 : Nat := 4983230072969 + 3 ^ 40 * 8231269 * 2
def baseEnd_8231269 : Nat := 4226597393453460855882589

theorem tailTrace_8231269 : CollatzResearch.WordTrace tailWord_8231269 prefixEnd_8231269 4226597393453460855882589 := by
  unfold tailWord_8231269
  simp only [CollatzResearch.WordTrace]
  refine ⟨300219044416525676669744861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200146029611017117779829907 300219044416525676669744861)
  ·
    refine ⟨112582141656197128751154323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 300219044416525676669744861 112582141656197128751154323)
    ·
      refine ⟨168873212484295693126731485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112582141656197128751154323 168873212484295693126731485)
      ·
        refine ⟨63327454681610884922524307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168873212484295693126731485 63327454681610884922524307)
        ·
          refine ⟨94991182022416327383786461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63327454681610884922524307 94991182022416327383786461)
          ·
            refine ⟨35621693258406122768919923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94991182022416327383786461 35621693258406122768919923)
            ·
              refine ⟨53432539887609184153379885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35621693258406122768919923 53432539887609184153379885)
              ·
                refine ⟨20037202457853444057517457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53432539887609184153379885 20037202457853444057517457)
                ·
                  refine ⟨15027901843390083043138093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20037202457853444057517457 15027901843390083043138093)
                  ·
                    refine ⟨5635463191271281141176785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15027901843390083043138093 5635463191271281141176785)
                    ·
                      refine ⟨4226597393453460855882589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5635463191271281141176785 4226597393453460855882589)
                      ·
                        rfl

theorem cell23_8231269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 3, 2, 3, 2].length) (baseStart_8231269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8231269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8231269 prefixEnd_8231269 := by exact prefixLift 8231269
  have htrace : WordTrace (prefixWord ++ tailWord_8231269) baseStart_8231269 baseEnd_8231269 := by
    simpa [prefixWord, tailWord_8231269, baseEnd_8231269] using wordTrace_append hprefix tailTrace_8231269
  have hstable : (prefixWord ++ tailWord_8231269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8231269).length < 2 ^ (prefixWord ++ tailWord_8231269).sum := by decide
  have hdescent : baseEnd_8231269 < baseStart_8231269 := by decide
  rcases family_descends (prefixWord ++ tailWord_8231269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8231275 : List Nat := [1, 1, 1, 1, 2, 2, 2, 6, 1, 6]
def baseStart_8231275 : Nat := 118140960795 + 8231275 * 2 ^ 59
def prefixEnd_8231275 : Nat := 4983230072969 + 3 ^ 40 * 8231275 * 2
def baseEnd_8231275 : Nat := 1408866824779129277469187

theorem tailTrace_8231275 : CollatzResearch.WordTrace tailWord_8231275 prefixEnd_8231275 1408866824779129277469187 := by
  unfold tailWord_8231275
  simp only [CollatzResearch.WordTrace]
  refine ⟨300219263254503939694463279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200146175503002626462975519 300219263254503939694463279)
  ·
    refine ⟨450328894881755909541694919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300219263254503939694463279 450328894881755909541694919)
    ·
      refine ⟨675493342322633864312542379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 450328894881755909541694919 675493342322633864312542379)
      ·
        refine ⟨1013240013483950796468813569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 675493342322633864312542379 1013240013483950796468813569)
        ·
          refine ⟨759930010112963097351610177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1013240013483950796468813569 759930010112963097351610177)
          ·
            refine ⟨569947507584722323013707633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 759930010112963097351610177 569947507584722323013707633)
            ·
              refine ⟨427460630688541742260280725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 569947507584722323013707633 427460630688541742260280725)
              ·
                refine ⟨20037217063525394168450659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 427460630688541742260280725 20037217063525394168450659)
                ·
                  refine ⟨30055825595288091252675989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20037217063525394168450659 30055825595288091252675989)
                  ·
                    refine ⟨1408866824779129277469187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30055825595288091252675989 1408866824779129277469187)
                    ·
                      rfl

theorem cell23_8231275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 6, 1, 6].length) (baseStart_8231275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8231275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8231275 prefixEnd_8231275 := by exact prefixLift 8231275
  have htrace : WordTrace (prefixWord ++ tailWord_8231275) baseStart_8231275 baseEnd_8231275 := by
    simpa [prefixWord, tailWord_8231275, baseEnd_8231275] using wordTrace_append hprefix tailTrace_8231275
  have hstable : (prefixWord ++ tailWord_8231275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8231275).length < 2 ^ (prefixWord ++ tailWord_8231275).sum := by decide
  have hdescent : baseEnd_8231275 < baseStart_8231275 := by decide
  rcases family_descends (prefixWord ++ tailWord_8231275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8231293 : List Nat := [1, 4, 1, 1, 2, 3, 4, 2, 1, 1, 3]
def baseStart_8231293 : Nat := 118140960795 + 8231293 * 2 ^ 59
def prefixEnd_8231293 : Nat := 4983230072969 + 3 ^ 40 * 8231293 * 2
def baseEnd_8231293 : Nat := 4226609716989168761982479

theorem tailTrace_8231293 : CollatzResearch.WordTrace tailWord_8231293 prefixEnd_8231293 4226609716989168761982479 := by
  unfold tailWord_8231293
  simp only [CollatzResearch.WordTrace]
  refine ⟨300219919768438728768618533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200146613178959152512412355 300219919768438728768618533)
  ·
    refine ⟨56291234956582261644115975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 300219919768438728768618533 56291234956582261644115975)
    ·
      refine ⟨84436852434873392466173963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56291234956582261644115975 84436852434873392466173963)
      ·
        refine ⟨126655278652310088699260945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84436852434873392466173963 126655278652310088699260945)
        ·
          refine ⟨94991458989232566524445709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126655278652310088699260945 94991458989232566524445709)
          ·
            refine ⟨35621797120962212446667141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94991458989232566524445709 35621797120962212446667141)
            ·
              refine ⟨6679086960180414833750089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35621797120962212446667141 6679086960180414833750089)
              ·
                refine ⟨5009315220135311125312567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6679086960180414833750089 5009315220135311125312567)
                ·
                  refine ⟨7513972830202966687968851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5009315220135311125312567 7513972830202966687968851)
                  ·
                    refine ⟨11270959245304450031953277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7513972830202966687968851 11270959245304450031953277)
                    ·
                      refine ⟨4226609716989168761982479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11270959245304450031953277 4226609716989168761982479)
                      ·
                        rfl

theorem cell23_8231293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 4, 2, 1, 1, 3].length) (baseStart_8231293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8231293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8231293 prefixEnd_8231293 := by exact prefixLift 8231293
  have htrace : WordTrace (prefixWord ++ tailWord_8231293) baseStart_8231293 baseEnd_8231293 := by
    simpa [prefixWord, tailWord_8231293, baseEnd_8231293] using wordTrace_append hprefix tailTrace_8231293
  have hstable : (prefixWord ++ tailWord_8231293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8231293).length < 2 ^ (prefixWord ++ tailWord_8231293).sum := by decide
  have hdescent : baseEnd_8231293 < baseStart_8231293 := by decide
  rcases family_descends (prefixWord ++ tailWord_8231293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8231333 : List Nat := [1, 3, 1, 2, 1, 1, 6, 3, 1, 2, 2]
def baseStart_8231333 : Nat := 118140960795 + 8231333 * 2 ^ 59
def prefixEnd_8231333 : Nat := 4983230072969 + 3 ^ 40 * 8231333 * 2
def baseEnd_8231333 : Nat := 4226630256215348605482295

theorem tailTrace_8231333 : CollatzResearch.WordTrace tailWord_8231333 prefixEnd_8231333 4226630256215348605482295 := by
  unfold tailWord_8231333
  simp only [CollatzResearch.WordTrace]
  refine ⟨300221378688293815600074653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200147585792195877066716435 300221378688293815600074653)
  ·
    refine ⟨112583017008110180850027995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 300221378688293815600074653 112583017008110180850027995)
    ·
      refine ⟨168874525512165271275041993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112583017008110180850027995 168874525512165271275041993)
      ·
        refine ⟨126655894134123953456281495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168874525512165271275041993 126655894134123953456281495)
        ·
          refine ⟨189983841201185930184422243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126655894134123953456281495 189983841201185930184422243)
          ·
            refine ⟨284975761801778895276633365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189983841201185930184422243 284975761801778895276633365)
            ·
              refine ⟨13358238834458385716092189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 284975761801778895276633365 13358238834458385716092189)
              ·
                refine ⟨5009339562921894643534571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13358238834458385716092189 5009339562921894643534571)
                ·
                  refine ⟨7514009344382841965301857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5009339562921894643534571 7514009344382841965301857)
                  ·
                    refine ⟨5635507008287131473976393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7514009344382841965301857 5635507008287131473976393)
                    ·
                      refine ⟨4226630256215348605482295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5635507008287131473976393 4226630256215348605482295)
                      ·
                        rfl

theorem cell23_8231333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 6, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 6, 3, 1, 2, 2].length) (baseStart_8231333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8231333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8231333 prefixEnd_8231333 := by exact prefixLift 8231333
  have htrace : WordTrace (prefixWord ++ tailWord_8231333) baseStart_8231333 baseEnd_8231333 := by
    simpa [prefixWord, tailWord_8231333, baseEnd_8231333] using wordTrace_append hprefix tailTrace_8231333
  have hstable : (prefixWord ++ tailWord_8231333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8231333).length < 2 ^ (prefixWord ++ tailWord_8231333).sum := by decide
  have hdescent : baseEnd_8231333 < baseStart_8231333 := by decide
  rcases family_descends (prefixWord ++ tailWord_8231333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8231392 : List Nat := [2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 5]
def baseStart_8231392 : Nat := 118140960795 + 8231392 * 2 ^ 59
def prefixEnd_8231392 : Nat := 4983230072969 + 3 ^ 40 * 8231392 * 2
def baseEnd_8231392 : Nat := 4226660551573963874644523

theorem tailTrace_8231392 : CollatzResearch.WordTrace tailWord_8231392 prefixEnd_8231392 4226660551573963874644523 := by
  unfold tailWord_8231392
  simp only [CollatzResearch.WordTrace]
  refine ⟨150111765297540034338236215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200149020396720045784314953 150111765297540034338236215)
  ·
    refine ⟨225167647946310051507354323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150111765297540034338236215 225167647946310051507354323)
    ·
      refine ⟨337751471919465077261031485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225167647946310051507354323 337751471919465077261031485)
      ·
        refine ⟨126656801969799403972886807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 337751471919465077261031485 126656801969799403972886807)
        ·
          refine ⟨189985202954699105959330211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126656801969799403972886807 189985202954699105959330211)
          ·
            refine ⟨284977804432048658938995317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189985202954699105959330211 284977804432048658938995317)
            ·
              refine ⟨26716669165504561775530811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 284977804432048658938995317 26716669165504561775530811)
              ·
                refine ⟨40075003748256842663296217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26716669165504561775530811 40075003748256842663296217)
                ·
                  refine ⟨30056252811192631997472163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40075003748256842663296217 30056252811192631997472163)
                  ·
                    refine ⟨45084379216788947996208245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30056252811192631997472163 45084379216788947996208245)
                    ·
                      refine ⟨4226660551573963874644523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45084379216788947996208245 4226660551573963874644523)
                      ·
                        rfl

theorem cell23_8231392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 5].length) (baseStart_8231392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8231392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8231392 prefixEnd_8231392 := by exact prefixLift 8231392
  have htrace : WordTrace (prefixWord ++ tailWord_8231392) baseStart_8231392 baseEnd_8231392 := by
    simpa [prefixWord, tailWord_8231392, baseEnd_8231392] using wordTrace_append hprefix tailTrace_8231392
  have hstable : (prefixWord ++ tailWord_8231392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8231392).length < 2 ^ (prefixWord ++ tailWord_8231392).sum := by decide
  have hdescent : baseEnd_8231392 < baseStart_8231392 := by decide
  rcases family_descends (prefixWord ++ tailWord_8231392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8231459 : List Nat := [1, 1, 1, 4, 4, 1, 2, 2, 2, 5]
def baseStart_8231459 : Nat := 118140960795 + 8231459 * 2 ^ 59
def prefixEnd_8231459 : Nat := 4983230072969 + 3 ^ 40 * 8231459 * 2
def baseEnd_8231459 : Nat := 1408898318259271704168905

theorem tailTrace_8231459 : CollatzResearch.WordTrace tailWord_8231459 prefixEnd_8231459 1408898318259271704168905 := by
  unfold tailWord_8231459
  simp only [CollatzResearch.WordTrace]
  refine ⟨300225974285837339119161431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200150649523891559412774287 300225974285837339119161431)
  ·
    refine ⟨450338961428756008678742147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300225974285837339119161431 450338961428756008678742147)
    ·
      refine ⟨675508442143134013018113221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 450338961428756008678742147 675508442143134013018113221)
      ·
        refine ⟨126657832901837627440896229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 675508442143134013018113221 126657832901837627440896229)
        ·
          refine ⟨23748343669094555145168043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 126657832901837627440896229 23748343669094555145168043)
          ·
            refine ⟨35622515503641832717752065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23748343669094555145168043 35622515503641832717752065)
            ·
              refine ⟨26716886627731374538314049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35622515503641832717752065 26716886627731374538314049)
              ·
                refine ⟨20037664970798530903735537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26716886627731374538314049 20037664970798530903735537)
                ·
                  refine ⟨15028248728098898177801653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20037664970798530903735537 15028248728098898177801653)
                  ·
                    refine ⟨1408898318259271704168905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15028248728098898177801653 1408898318259271704168905)
                    ·
                      rfl

theorem cell23_8231459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 2, 2, 5].length) (baseStart_8231459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8231459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8231459 prefixEnd_8231459 := by exact prefixLift 8231459
  have htrace : WordTrace (prefixWord ++ tailWord_8231459) baseStart_8231459 baseEnd_8231459 := by
    simpa [prefixWord, tailWord_8231459, baseEnd_8231459] using wordTrace_append hprefix tailTrace_8231459
  have hstable : (prefixWord ++ tailWord_8231459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8231459).length < 2 ^ (prefixWord ++ tailWord_8231459).sum := by decide
  have hdescent : baseEnd_8231459 < baseStart_8231459 := by decide
  rcases family_descends (prefixWord ++ tailWord_8231459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8231466 : List Nat := [3, 1, 4, 1, 1, 2, 1, 1, 2, 5, 2]
def baseStart_8231466 : Nat := 118140960795 + 8231466 * 2 ^ 59
def prefixEnd_8231466 : Nat := 4983230072969 + 3 ^ 40 * 8231466 * 2
def baseEnd_8231466 : Nat := 4226698549142396585119183

theorem tailTrace_8231466 : CollatzResearch.WordTrace tailWord_8231466 prefixEnd_8231466 4226698549142396585119183 := by
  unfold tailWord_8231466
  simp only [CollatzResearch.WordTrace]
  refine ⟨75056557399202994828666563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200150819731207986209777501 75056557399202994828666563)
  ·
    refine ⟨112584836098804492242999845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75056557399202994828666563 112584836098804492242999845)
    ·
      refine ⟨21109656768525842295562471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112584836098804492242999845 21109656768525842295562471)
      ·
        refine ⟨31664485152788763443343707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21109656768525842295562471 31664485152788763443343707)
        ·
          refine ⟨47496727729183145165015561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31664485152788763443343707 47496727729183145165015561)
          ·
            refine ⟨35622545796887358873761671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47496727729183145165015561 35622545796887358873761671)
            ·
              refine ⟨53433818695331038310642507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35622545796887358873761671 53433818695331038310642507)
              ·
                refine ⟨80150728042996557465963761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53433818695331038310642507 80150728042996557465963761)
                ·
                  refine ⟨60113046032247418099472821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80150728042996557465963761 60113046032247418099472821)
                  ·
                    refine ⟨5635598065523195446825577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60113046032247418099472821 5635598065523195446825577)
                    ·
                      refine ⟨4226698549142396585119183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5635598065523195446825577 4226698549142396585119183)
                      ·
                        rfl

theorem cell23_8231466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 1, 2, 5, 2].length) (baseStart_8231466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8231466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8231466 prefixEnd_8231466 := by exact prefixLift 8231466
  have htrace : WordTrace (prefixWord ++ tailWord_8231466) baseStart_8231466 baseEnd_8231466 := by
    simpa [prefixWord, tailWord_8231466, baseEnd_8231466] using wordTrace_append hprefix tailTrace_8231466
  have hstable : (prefixWord ++ tailWord_8231466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8231466).length < 2 ^ (prefixWord ++ tailWord_8231466).sum := by decide
  have hdescent : baseEnd_8231466 < baseStart_8231466 := by decide
  rcases family_descends (prefixWord ++ tailWord_8231466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8231563 : List Nat := [1, 1, 1, 1, 4, 1, 2, 7, 1, 1, 3]
def baseStart_8231563 : Nat := 118140960795 + 8231563 * 2 ^ 59
def prefixEnd_8231563 : Nat := 4983230072969 + 3 ^ 40 * 8231563 * 2
def baseEnd_8231563 : Nat := 4226748356765882705606237

theorem tailTrace_8231563 : CollatzResearch.WordTrace tailWord_8231563 prefixEnd_8231563 4226748356765882705606237 := by
  unfold tailWord_8231563
  simp only [CollatzResearch.WordTrace]
  refine ⟨300229767477460564880947343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200153178318307043253964895 300229767477460564880947343)
  ·
    refine ⟨450344651216190847321421015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300229767477460564880947343 450344651216190847321421015)
    ·
      refine ⟨675516976824286270982131523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 450344651216190847321421015 675516976824286270982131523)
      ·
        refine ⟨1013275465236429406473197285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 675516976824286270982131523 1013275465236429406473197285)
        ·
          refine ⟨189989149731830513713724491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1013275465236429406473197285 189989149731830513713724491)
          ·
            refine ⟨284983724597745770570586737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189989149731830513713724491 284983724597745770570586737)
            ·
              refine ⟨213737793448309327927940053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 284983724597745770570586737 213737793448309327927940053)
              ·
                refine ⟨5009479533944749873311095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 213737793448309327927940053 5009479533944749873311095)
                ·
                  refine ⟨7514219300917124809966643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5009479533944749873311095 7514219300917124809966643)
                  ·
                    refine ⟨11271328951375687214949965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7514219300917124809966643 11271328951375687214949965)
                    ·
                      refine ⟨4226748356765882705606237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11271328951375687214949965 4226748356765882705606237)
                      ·
                        rfl

theorem cell23_8231563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 7, 1, 1, 3].length) (baseStart_8231563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8231563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8231563 prefixEnd_8231563 := by exact prefixLift 8231563
  have htrace : WordTrace (prefixWord ++ tailWord_8231563) baseStart_8231563 baseEnd_8231563 := by
    simpa [prefixWord, tailWord_8231563, baseEnd_8231563] using wordTrace_append hprefix tailTrace_8231563
  have hstable : (prefixWord ++ tailWord_8231563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8231563).length < 2 ^ (prefixWord ++ tailWord_8231563).sum := by decide
  have hdescent : baseEnd_8231563 < baseStart_8231563 := by decide
  rcases family_descends (prefixWord ++ tailWord_8231563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8231566 : List Nat := [4, 1, 1, 3, 1, 1, 1, 5, 1, 5]
def baseStart_8231566 : Nat := 118140960795 + 8231566 * 2 ^ 59
def prefixEnd_8231566 : Nat := 4983230072969 + 3 ^ 40 * 8231566 * 2
def baseEnd_8231566 : Nat := 1408916632402615397956241

theorem tailTrace_8231566 : CollatzResearch.WordTrace tailWord_8231566 prefixEnd_8231566 1408916632402615397956241 := by
  unfold tailWord_8231566
  simp only [CollatzResearch.WordTrace]
  refine ⟨37528734612056212049163319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200153251264299797595537701 37528734612056212049163319)
  ·
    refine ⟨56293101918084318073744979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37528734612056212049163319 56293101918084318073744979)
    ·
      refine ⟨84439652877126477110617469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56293101918084318073744979 84439652877126477110617469)
      ·
        refine ⟨31664869828922428916481551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84439652877126477110617469 31664869828922428916481551)
        ·
          refine ⟨47497304743383643374722327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31664869828922428916481551 47497304743383643374722327)
          ·
            refine ⟨71245957115075465062083491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47497304743383643374722327 71245957115075465062083491)
            ·
              refine ⟨106868935672613197593125237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71245957115075465062083491 106868935672613197593125237)
              ·
                refine ⟨10018962719307487274355491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 106868935672613197593125237 10018962719307487274355491)
                ·
                  refine ⟨15028444078961230911533237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10018962719307487274355491 15028444078961230911533237)
                  ·
                    refine ⟨1408916632402615397956241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15028444078961230911533237 1408916632402615397956241)
                    ·
                      rfl

theorem cell23_8231566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 5, 1, 5].length) (baseStart_8231566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8231566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8231566 prefixEnd_8231566 := by exact prefixLift 8231566
  have htrace : WordTrace (prefixWord ++ tailWord_8231566) baseStart_8231566 baseEnd_8231566 := by
    simpa [prefixWord, tailWord_8231566, baseEnd_8231566] using wordTrace_append hprefix tailTrace_8231566
  have hstable : (prefixWord ++ tailWord_8231566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8231566).length < 2 ^ (prefixWord ++ tailWord_8231566).sum := by decide
  have hdescent : baseEnd_8231566 < baseStart_8231566 := by decide
  rcases family_descends (prefixWord ++ tailWord_8231566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8231580 : List Nat := [2, 2, 3, 2, 2, 3, 1, 1, 3, 1, 3]
def baseStart_8231580 : Nat := 118140960795 + 8231580 * 2 ^ 59
def prefixEnd_8231580 : Nat := 4983230072969 + 3 ^ 40 * 8231580 * 2
def baseEnd_8231580 : Nat := 4226757085937009139093659

theorem tailTrace_8231580 : CollatzResearch.WordTrace tailWord_8231580 prefixEnd_8231580 4226757085937009139093659 := by
  unfold tailWord_8231580
  simp only [CollatzResearch.WordTrace]
  refine ⟨150115193759199488392158097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200153591678932651189544129 150115193759199488392158097)
  ·
    refine ⟨112586395319399616294118573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150115193759199488392158097 112586395319399616294118573)
    ·
      refine ⟨42219898244774856110294465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112586395319399616294118573 42219898244774856110294465)
      ·
        refine ⟨31664923683581142082720849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42219898244774856110294465 31664923683581142082720849)
        ·
          refine ⟨23748692762685856562040637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31664923683581142082720849 23748692762685856562040637)
          ·
            refine ⟨8905759786007196210765239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23748692762685856562040637 8905759786007196210765239)
            ·
              refine ⟨13358639679010794316147859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8905759786007196210765239 13358639679010794316147859)
              ·
                refine ⟨20037959518516191474221789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13358639679010794316147859 20037959518516191474221789)
                ·
                  refine ⟨7514234819443571802833171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20037959518516191474221789 7514234819443571802833171)
                  ·
                    refine ⟨11271352229165357704249757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7514234819443571802833171 11271352229165357704249757)
                    ·
                      refine ⟨4226757085937009139093659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11271352229165357704249757 4226757085937009139093659)
                      ·
                        rfl

theorem cell23_8231580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 1, 1, 3, 1, 3].length) (baseStart_8231580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8231580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8231580 prefixEnd_8231580 := by exact prefixLift 8231580
  have htrace : WordTrace (prefixWord ++ tailWord_8231580) baseStart_8231580 baseEnd_8231580 := by
    simpa [prefixWord, tailWord_8231580, baseEnd_8231580] using wordTrace_append hprefix tailTrace_8231580
  have hstable : (prefixWord ++ tailWord_8231580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8231580).length < 2 ^ (prefixWord ++ tailWord_8231580).sum := by decide
  have hdescent : baseEnd_8231580 < baseStart_8231580 := by decide
  rcases family_descends (prefixWord ++ tailWord_8231580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8231589 : List Nat := [1, 3, 1, 2, 1, 2, 1, 1, 2, 6, 3]
def baseStart_8231589 : Nat := 118140960795 + 8231589 * 2 ^ 59
def prefixEnd_8231589 : Nat := 4983230072969 + 3 ^ 40 * 8231589 * 2
def baseEnd_8231589 : Nat := 4226761707262899603881117

theorem tailTrace_8231589 : CollatzResearch.WordTrace tailWord_8231589 prefixEnd_8231589 4226761707262899603881117 := by
  unfold tailWord_8231589
  simp only [CollatzResearch.WordTrace]
  refine ⟨300230715775366371321393821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200153810516910914214262547 300230715775366371321393821)
  ·
    refine ⟨112586518415762389245522683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 300230715775366371321393821 112586518415762389245522683)
    ·
      refine ⟨168879777623643583868284025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112586518415762389245522683 168879777623643583868284025)
      ·
        refine ⟨126659833217732687901213019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168879777623643583868284025 126659833217732687901213019)
        ·
          refine ⟨189989749826599031851819529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126659833217732687901213019 189989749826599031851819529)
          ·
            refine ⟨142492312369949273888864647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189989749826599031851819529 142492312369949273888864647)
            ·
              refine ⟨213738468554923910833296971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142492312369949273888864647 213738468554923910833296971)
              ·
                refine ⟨320607702832385866249945457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 213738468554923910833296971 320607702832385866249945457)
                ·
                  refine ⟨240455777124289399687459093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 320607702832385866249945457 240455777124289399687459093)
                  ·
                    refine ⟨11271364552701065610349645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 240455777124289399687459093 11271364552701065610349645)
                    ·
                      refine ⟨4226761707262899603881117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11271364552701065610349645 4226761707262899603881117)
                      ·
                        rfl

theorem cell23_8231589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 6, 3].length) (baseStart_8231589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8231589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8231589 prefixEnd_8231589 := by exact prefixLift 8231589
  have htrace : WordTrace (prefixWord ++ tailWord_8231589) baseStart_8231589 baseEnd_8231589 := by
    simpa [prefixWord, tailWord_8231589, baseEnd_8231589] using wordTrace_append hprefix tailTrace_8231589
  have hstable : (prefixWord ++ tailWord_8231589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8231589).length < 2 ^ (prefixWord ++ tailWord_8231589).sum := by decide
  have hdescent : baseEnd_8231589 < baseStart_8231589 := by decide
  rcases family_descends (prefixWord ++ tailWord_8231589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8231599 : List Nat := [1, 1, 2, 1, 2, 5, 2, 1, 1, 1, 6]
def baseStart_8231599 : Nat := 118140960795 + 8231599 * 2 ^ 59
def prefixEnd_8231599 : Nat := 4983230072969 + 3 ^ 40 * 8231599 * 2
def baseEnd_8231599 : Nat := 4226766842069444564756071

theorem tailTrace_8231599 : CollatzResearch.WordTrace tailWord_8231599 prefixEnd_8231599 4226766842069444564756071 := by
  unfold tailWord_8231599
  simp only [CollatzResearch.WordTrace]
  refine ⟨300231080505330143029257851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200154053670220095352838567 300231080505330143029257851)
  ·
    refine ⟨450346620757995214543886777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300231080505330143029257851 450346620757995214543886777)
    ·
      refine ⟨337759965568496410907915083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 450346620757995214543886777 337759965568496410907915083)
      ·
        refine ⟨506639948352744616361872625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337759965568496410907915083 506639948352744616361872625)
        ·
          refine ⟨379979961264558462271404469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 506639948352744616361872625 379979961264558462271404469)
          ·
            refine ⟨35623121368552355837944169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 379979961264558462271404469 35623121368552355837944169)
            ·
              refine ⟨26717341026414266878458127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35623121368552355837944169 26717341026414266878458127)
              ·
                refine ⟨40076011539621400317687191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26717341026414266878458127 40076011539621400317687191)
                ·
                  refine ⟨60114017309432100476530787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40076011539621400317687191 60114017309432100476530787)
                  ·
                    refine ⟨90171025964148150714796181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60114017309432100476530787 90171025964148150714796181)
                    ·
                      refine ⟨4226766842069444564756071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90171025964148150714796181 4226766842069444564756071)
                      ·
                        rfl

theorem cell23_8231599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 1, 1, 1, 6].length) (baseStart_8231599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8231599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8231599 prefixEnd_8231599 := by exact prefixLift 8231599
  have htrace : WordTrace (prefixWord ++ tailWord_8231599) baseStart_8231599 baseEnd_8231599 := by
    simpa [prefixWord, tailWord_8231599, baseEnd_8231599] using wordTrace_append hprefix tailTrace_8231599
  have hstable : (prefixWord ++ tailWord_8231599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8231599).length < 2 ^ (prefixWord ++ tailWord_8231599).sum := by decide
  have hdescent : baseEnd_8231599 < baseStart_8231599 := by decide
  rcases family_descends (prefixWord ++ tailWord_8231599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8231603 : List Nat := [1, 1, 1, 2, 3, 6, 1, 2, 1, 1, 4]
def baseStart_8231603 : Nat := 118140960795 + 8231603 * 2 ^ 59
def prefixEnd_8231603 : Nat := 4983230072969 + 3 ^ 40 * 8231603 * 2
def baseEnd_8231603 : Nat := 4226768895992062549106053

theorem tailTrace_8231603 : CollatzResearch.WordTrace tailWord_8231603 prefixEnd_8231603 4226768895992062549106053 := by
  unfold tailWord_8231603
  simp only [CollatzResearch.WordTrace]
  refine ⟨300231226397315651712403463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200154150931543767808268975 300231226397315651712403463)
  ·
    refine ⟨450346839595973477568605195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300231226397315651712403463 450346839595973477568605195)
    ·
      refine ⟨675520259393960216352907793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 450346839595973477568605195 675520259393960216352907793)
      ·
        refine ⟨506640194545470162264680845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 675520259393960216352907793 506640194545470162264680845)
        ·
          refine ⟨189990072954551310849255317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 506640194545470162264680845 189990072954551310849255317)
          ·
            refine ⟨8905784669744592696058843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 189990072954551310849255317 8905784669744592696058843)
            ·
              refine ⟨13358677004616889044088265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8905784669744592696058843 13358677004616889044088265)
              ·
                refine ⟨10019007753462666783066199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13358677004616889044088265 10019007753462666783066199)
                ·
                  refine ⟨15028511630194000174599299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10019007753462666783066199 15028511630194000174599299)
                  ·
                    refine ⟨22542767445291000261898949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15028511630194000174599299 22542767445291000261898949)
                    ·
                      refine ⟨4226768895992062549106053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22542767445291000261898949 4226768895992062549106053)
                      ·
                        rfl

theorem cell23_8231603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 1, 2, 1, 1, 4].length) (baseStart_8231603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8231603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8231603 prefixEnd_8231603 := by exact prefixLift 8231603
  have htrace : WordTrace (prefixWord ++ tailWord_8231603) baseStart_8231603 baseEnd_8231603 := by
    simpa [prefixWord, tailWord_8231603, baseEnd_8231603] using wordTrace_append hprefix tailTrace_8231603
  have hstable : (prefixWord ++ tailWord_8231603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8231603).length < 2 ^ (prefixWord ++ tailWord_8231603).sum := by decide
  have hdescent : baseEnd_8231603 < baseStart_8231603 := by decide
  rcases family_descends (prefixWord ++ tailWord_8231603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8231616 : List Nat := [2, 1, 1, 2, 4, 3, 1, 2, 1, 2, 4]
def baseStart_8231616 : Nat := 118140960795 + 8231616 * 2 ^ 59
def prefixEnd_8231616 : Nat := 4983230072969 + 3 ^ 40 * 8231616 * 2
def baseEnd_8231616 : Nat := 4226775571240570998243493

theorem tailTrace_8231616 : CollatzResearch.WordTrace tailWord_8231616 prefixEnd_8231616 4226775571240570998243493 := by
  unfold tailWord_8231616
  simp only [CollatzResearch.WordTrace]
  refine ⟨150115850273134277466313351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200154467030845703288417801 150115850273134277466313351)
  ·
    refine ⟨225173775409701416199470027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150115850273134277466313351 225173775409701416199470027)
    ·
      refine ⟨337760663114552124299205041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225173775409701416199470027 337760663114552124299205041)
      ·
        refine ⟨253320497335914093224403781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 337760663114552124299205041 253320497335914093224403781)
        ·
          refine ⟨47497593250483892479575709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 253320497335914093224403781 47497593250483892479575709)
          ·
            refine ⟨17811597468931459679840891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47497593250483892479575709 17811597468931459679840891)
            ·
              refine ⟨26717396203397189519761337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17811597468931459679840891 26717396203397189519761337)
              ·
                refine ⟨20038047152547892139821003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26717396203397189519761337 20038047152547892139821003)
                ·
                  refine ⟨30057070728821838209731505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20038047152547892139821003 30057070728821838209731505)
                  ·
                    refine ⟨22542803046616378657298629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30057070728821838209731505 22542803046616378657298629)
                    ·
                      refine ⟨4226775571240570998243493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22542803046616378657298629 4226775571240570998243493)
                      ·
                        rfl

theorem cell23_8231616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 2, 1, 2, 4].length) (baseStart_8231616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8231616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8231616 prefixEnd_8231616 := by exact prefixLift 8231616
  have htrace : WordTrace (prefixWord ++ tailWord_8231616) baseStart_8231616 baseEnd_8231616 := by
    simpa [prefixWord, tailWord_8231616, baseEnd_8231616] using wordTrace_append hprefix tailTrace_8231616
  have hstable : (prefixWord ++ tailWord_8231616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8231616).length < 2 ^ (prefixWord ++ tailWord_8231616).sum := by decide
  have hdescent : baseEnd_8231616 < baseStart_8231616 := by decide
  rcases family_descends (prefixWord ++ tailWord_8231616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8231617 : List Nat := [1, 2, 6, 2, 1, 1, 3, 1, 1, 5]
def baseStart_8231617 : Nat := 118140960795 + 8231617 * 2 ^ 59
def prefixEnd_8231617 : Nat := 4983230072969 + 3 ^ 40 * 8231617 * 2
def baseEnd_8231617 : Nat := 1408925361573741831443663

theorem tailTrace_8231617 : CollatzResearch.WordTrace tailWord_8231617 prefixEnd_8231617 1408925361573741831443663 := by
  unfold tailWord_8231617
  simp only [CollatzResearch.WordTrace]
  refine ⟨300231737019264932103413105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200154491346176621402275403 300231737019264932103413105)
  ·
    refine ⟨225173802764448699077559829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300231737019264932103413105 225173802764448699077559829)
    ·
      refine ⟨10555022004583532769260617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 225173802764448699077559829 10555022004583532769260617)
      ·
        refine ⟨7916266503437649576945463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10555022004583532769260617 7916266503437649576945463)
        ·
          refine ⟨11874399755156474365418195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7916266503437649576945463 11874399755156474365418195)
          ·
            refine ⟨17811599632734711548127293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11874399755156474365418195 17811599632734711548127293)
            ·
              refine ⟨6679349862275516830547735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17811599632734711548127293 6679349862275516830547735)
              ·
                refine ⟨10019024793413275245821603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6679349862275516830547735 10019024793413275245821603)
                ·
                  refine ⟨15028537190119912868732405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10019024793413275245821603 15028537190119912868732405)
                  ·
                    refine ⟨1408925361573741831443663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15028537190119912868732405 1408925361573741831443663)
                    ·
                      rfl

theorem cell23_8231617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_8231617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8231617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8231617 prefixEnd_8231617 := by exact prefixLift 8231617
  have htrace : WordTrace (prefixWord ++ tailWord_8231617) baseStart_8231617 baseEnd_8231617 := by
    simpa [prefixWord, tailWord_8231617, baseEnd_8231617] using wordTrace_append hprefix tailTrace_8231617
  have hstable : (prefixWord ++ tailWord_8231617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8231617).length < 2 ^ (prefixWord ++ tailWord_8231617).sum := by decide
  have hdescent : baseEnd_8231617 < baseStart_8231617 := by decide
  rcases family_descends (prefixWord ++ tailWord_8231617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8231620 : List Nat := [2, 3, 3, 1, 1, 3, 3, 1, 1, 1, 4]
def baseStart_8231620 : Nat := 118140960795 + 8231620 * 2 ^ 59
def prefixEnd_8231620 : Nat := 4983230072969 + 3 ^ 40 * 8231620 * 2
def baseEnd_8231620 : Nat := 4226777625163188982593475

theorem tailTrace_8231620 : CollatzResearch.WordTrace tailWord_8231620 prefixEnd_8231620 4226777625163188982593475 := by
  unfold tailWord_8231620
  simp only [CollatzResearch.WordTrace]
  refine ⟨150115923219127031807886157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200154564292169375743848209 150115923219127031807886157)
  ·
    refine ⟨56293471207172636927957309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150115923219127031807886157 56293471207172636927957309)
    ·
      refine ⟨21110051702689738847983991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56293471207172636927957309 21110051702689738847983991)
      ·
        refine ⟨31665077554034608271975987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21110051702689738847983991 31665077554034608271975987)
        ·
          refine ⟨47497616331051912407963981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31665077554034608271975987 47497616331051912407963981)
          ·
            refine ⟨17811606124144467152986493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47497616331051912407963981 17811606124144467152986493)
            ·
              refine ⟨6679352296554175182369935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17811606124144467152986493 6679352296554175182369935)
              ·
                refine ⟨10019028444831262773554903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6679352296554175182369935 10019028444831262773554903)
                ·
                  refine ⟨15028542667246894160332355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10019028444831262773554903 15028542667246894160332355)
                  ·
                    refine ⟨22542814000870341240498533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15028542667246894160332355 22542814000870341240498533)
                    ·
                      refine ⟨4226777625163188982593475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22542814000870341240498533 4226777625163188982593475)
                      ·
                        rfl

theorem cell23_8231620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 3, 1, 1, 1, 4].length) (baseStart_8231620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8231620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8231620 prefixEnd_8231620 := by exact prefixLift 8231620
  have htrace : WordTrace (prefixWord ++ tailWord_8231620) baseStart_8231620 baseEnd_8231620 := by
    simpa [prefixWord, tailWord_8231620, baseEnd_8231620] using wordTrace_append hprefix tailTrace_8231620
  have hstable : (prefixWord ++ tailWord_8231620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8231620).length < 2 ^ (prefixWord ++ tailWord_8231620).sum := by decide
  have hdescent : baseEnd_8231620 < baseStart_8231620 := by decide
  rcases family_descends (prefixWord ++ tailWord_8231620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8231639 : List Nat := [1, 1, 3, 2, 1, 4, 1, 1, 2, 7]
def baseStart_8231639 : Nat := 118140960795 + 8231639 * 2 ^ 59
def prefixEnd_8231639 : Nat := 4983230072969 + 3 ^ 40 * 8231639 * 2
def baseEnd_8231639 : Nat := 1408929127098541469418629

theorem tailTrace_8231639 : CollatzResearch.WordTrace tailWord_8231639 prefixEnd_8231639 1408929127098541469418629 := by
  unfold tailWord_8231639
  simp only [CollatzResearch.WordTrace]
  refine ⟨300232539425185229860713971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200155026283456819907142647 300232539425185229860713971)
  ·
    refine ⟨450348809137777844791070957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300232539425185229860713971 450348809137777844791070957)
    ·
      refine ⟨168880803426666691796651609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 450348809137777844791070957 168880803426666691796651609)
      ·
        refine ⟨126660602570000018847488707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168880803426666691796651609 126660602570000018847488707)
        ·
          refine ⟨189990903855000028271233061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126660602570000018847488707 189990903855000028271233061)
          ·
            refine ⟨35623294472812505300856199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 189990903855000028271233061 35623294472812505300856199)
            ·
              refine ⟨53434941709218757951284299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35623294472812505300856199 53434941709218757951284299)
              ·
                refine ⟨80152412563828136926926449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53434941709218757951284299 80152412563828136926926449)
                ·
                  refine ⟨60114309422871102695194837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80152412563828136926926449 60114309422871102695194837)
                  ·
                    refine ⟨1408929127098541469418629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60114309422871102695194837 1408929127098541469418629)
                    ·
                      rfl

theorem cell23_8231639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 1, 2, 7].length) (baseStart_8231639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8231639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8231639 prefixEnd_8231639 := by exact prefixLift 8231639
  have htrace : WordTrace (prefixWord ++ tailWord_8231639) baseStart_8231639 baseEnd_8231639 := by
    simpa [prefixWord, tailWord_8231639, baseEnd_8231639] using wordTrace_append hprefix tailTrace_8231639
  have hstable : (prefixWord ++ tailWord_8231639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8231639).length < 2 ^ (prefixWord ++ tailWord_8231639).sum := by decide
  have hdescent : baseEnd_8231639 < baseStart_8231639 := by decide
  rcases family_descends (prefixWord ++ tailWord_8231639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8231653 : List Nat := [1, 3, 1, 4, 1, 3, 2, 1, 1, 3, 3]
def baseStart_8231653 : Nat := 118140960795 + 8231653 * 2 ^ 59
def prefixEnd_8231653 : Nat := 4983230072969 + 3 ^ 40 * 8231653 * 2
def baseEnd_8231653 : Nat := 4226794570024787353480823

theorem tailTrace_8231653 : CollatzResearch.WordTrace tailWord_8231653 prefixEnd_8231653 4226794570024787353480823 := by
  unfold tailWord_8231653
  simp only [CollatzResearch.WordTrace]
  refine ⟨300233050047134510251723613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200155366698089673501149075 300233050047134510251723613)
  ·
    refine ⟨112587393767675441344396355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 300233050047134510251723613 112587393767675441344396355)
    ·
      refine ⟨168881090651513162016594533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112587393767675441344396355 168881090651513162016594533)
      ·
        refine ⟨31665204497158717878111475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 168881090651513162016594533 31665204497158717878111475)
        ·
          refine ⟨47497806745738076817167213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31665204497158717878111475 47497806745738076817167213)
          ·
            refine ⟨17811677529651778806437705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47497806745738076817167213 17811677529651778806437705)
            ·
              refine ⟨13358758147238834104828279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17811677529651778806437705 13358758147238834104828279)
              ·
                refine ⟨20038137220858251157242419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13358758147238834104828279 20038137220858251157242419)
                ·
                  refine ⟨30057205831287376735863629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20038137220858251157242419 30057205831287376735863629)
                  ·
                    refine ⟨11271452186732766275948861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30057205831287376735863629 11271452186732766275948861)
                    ·
                      refine ⟨4226794570024787353480823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11271452186732766275948861 4226794570024787353480823)
                      ·
                        rfl

theorem cell23_8231653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 2, 1, 1, 3, 3].length) (baseStart_8231653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8231653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8231653 prefixEnd_8231653 := by exact prefixLift 8231653
  have htrace : WordTrace (prefixWord ++ tailWord_8231653) baseStart_8231653 baseEnd_8231653 := by
    simpa [prefixWord, tailWord_8231653, baseEnd_8231653] using wordTrace_append hprefix tailTrace_8231653
  have hstable : (prefixWord ++ tailWord_8231653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8231653).length < 2 ^ (prefixWord ++ tailWord_8231653).sum := by decide
  have hdescent : baseEnd_8231653 < baseStart_8231653 := by decide
  rcases family_descends (prefixWord ++ tailWord_8231653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8231659 : List Nat := [1, 1, 1, 1, 2, 4, 1, 1, 4, 3, 4]
def baseStart_8231659 : Nat := 118140960795 + 8231659 * 2 ^ 59
def prefixEnd_8231659 : Nat := 4983230072969 + 3 ^ 40 * 8231659 * 2
def baseEnd_8231659 : Nat := 4226797650908714330005795

theorem tailTrace_8231659 : CollatzResearch.WordTrace tailWord_8231659 prefixEnd_8231659 4226797650908714330005795 := by
  unfold tailWord_8231659
  simp only [CollatzResearch.WordTrace]
  refine ⟨300233268885112773276442031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200155512590075182184294687 300233268885112773276442031)
  ·
    refine ⟨450349903327669159914663047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300233268885112773276442031 450349903327669159914663047)
    ·
      refine ⟨675524854991503739871994571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 450349903327669159914663047 675524854991503739871994571)
      ·
        refine ⟨1013287282487255609807991857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 675524854991503739871994571 1013287282487255609807991857)
        ·
          refine ⟨759965461865441707355993893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1013287282487255609807991857 759965461865441707355993893)
          ·
            refine ⟨142493524099770320129248855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 759965461865441707355993893 142493524099770320129248855)
            ·
              refine ⟨213740286149655480193873283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142493524099770320129248855 213740286149655480193873283)
              ·
                refine ⟨320610429224483220290809925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 213740286149655480193873283 320610429224483220290809925)
                ·
                  refine ⟨60114455479590603804526861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 320610429224483220290809925 60114455479590603804526861)
                  ·
                    refine ⟨22542920804846476426697573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60114455479590603804526861 22542920804846476426697573)
                    ·
                      refine ⟨4226797650908714330005795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22542920804846476426697573 4226797650908714330005795)
                      ·
                        rfl

theorem cell23_8231659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 4, 3, 4].length) (baseStart_8231659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8231659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8231659 prefixEnd_8231659 := by exact prefixLift 8231659
  have htrace : WordTrace (prefixWord ++ tailWord_8231659) baseStart_8231659 baseEnd_8231659 := by
    simpa [prefixWord, tailWord_8231659, baseEnd_8231659] using wordTrace_append hprefix tailTrace_8231659
  have hstable : (prefixWord ++ tailWord_8231659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8231659).length < 2 ^ (prefixWord ++ tailWord_8231659).sum := by decide
  have hdescent : baseEnd_8231659 < baseStart_8231659 := by decide
  rcases family_descends (prefixWord ++ tailWord_8231659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8231663 : List Nat := [1, 1, 2, 1, 5, 2, 2, 1, 3, 3, 2]
def baseStart_8231663 : Nat := 118140960795 + 8231663 * 2 ^ 59
def prefixEnd_8231663 : Nat := 4983230072969 + 3 ^ 40 * 8231663 * 2
def baseEnd_8231663 : Nat := 4226799704831332314355777

theorem tailTrace_8231663 : CollatzResearch.WordTrace tailWord_8231663 prefixEnd_8231663 4226799704831332314355777 := by
  unfold tailWord_8231663
  simp only [CollatzResearch.WordTrace]
  refine ⟨300233414777098281959587643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200155609851398854639725095 300233414777098281959587643)
  ·
    refine ⟨450350122165647422939381465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300233414777098281959587643 450350122165647422939381465)
    ·
      refine ⟨337762591624235567204536099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 450350122165647422939381465 337762591624235567204536099)
      ·
        refine ⟨506643887436353350806804149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337762591624235567204536099 506643887436353350806804149)
        ·
          refine ⟨47497864447158126638137889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 506643887436353350806804149 47497864447158126638137889)
          ·
            refine ⟨35623398335368594978603417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47497864447158126638137889 35623398335368594978603417)
            ·
              refine ⟨26717548751526446233952563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35623398335368594978603417 26717548751526446233952563)
              ·
                refine ⟨40076323127289669350928845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26717548751526446233952563 40076323127289669350928845)
                ·
                  refine ⟨15028621172733626006598317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40076323127289669350928845 15028621172733626006598317)
                  ·
                    refine ⟨5635732939775109752474369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15028621172733626006598317 5635732939775109752474369)
                    ·
                      refine ⟨4226799704831332314355777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5635732939775109752474369 4226799704831332314355777)
                      ·
                        rfl

theorem cell23_8231663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 1, 3, 3, 2].length) (baseStart_8231663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8231663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8231663 prefixEnd_8231663 := by exact prefixLift 8231663
  have htrace : WordTrace (prefixWord ++ tailWord_8231663) baseStart_8231663 baseEnd_8231663 := by
    simpa [prefixWord, tailWord_8231663, baseEnd_8231663] using wordTrace_append hprefix tailTrace_8231663
  have hstable : (prefixWord ++ tailWord_8231663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8231663).length < 2 ^ (prefixWord ++ tailWord_8231663).sum := by decide
  have hdescent : baseEnd_8231663 < baseStart_8231663 := by decide
  rcases family_descends (prefixWord ++ tailWord_8231663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8231679 : List Nat := [1, 1, 2, 2, 1, 3, 1, 3, 1, 3, 5]
def baseStart_8231679 : Nat := 118140960795 + 8231679 * 2 ^ 59
def prefixEnd_8231679 : Nat := 4983230072969 + 3 ^ 40 * 8231679 * 2
def baseEnd_8231679 : Nat := 4226807920521804251755703

theorem tailTrace_8231679 : CollatzResearch.WordTrace tailWord_8231679 prefixEnd_8231679 4226807920521804251755703 := by
  unfold tailWord_8231679
  simp only [CollatzResearch.WordTrace]
  refine ⟨300233998345040316692170091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200155998896693544461446727 300233998345040316692170091)
  ·
    refine ⟨450350997517560475038255137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300233998345040316692170091 450350997517560475038255137)
    ·
      refine ⟨337763248138170356278691353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 450350997517560475038255137 337763248138170356278691353)
      ·
        refine ⟨253322436103627767209018515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 337763248138170356278691353 253322436103627767209018515)
        ·
          refine ⟨379983654155441650813527773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253322436103627767209018515 379983654155441650813527773)
          ·
            refine ⟨142493870308290619055072915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 379983654155441650813527773 142493870308290619055072915)
            ·
              refine ⟨213740805462435928582609373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142493870308290619055072915 213740805462435928582609373)
              ·
                refine ⟨80152802048413473218478515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 213740805462435928582609373 80152802048413473218478515)
                ·
                  refine ⟨120229203072620209827717773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80152802048413473218478515 120229203072620209827717773)
                  ·
                    refine ⟨45085951152232578685394165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 120229203072620209827717773 45085951152232578685394165)
                    ·
                      refine ⟨4226807920521804251755703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45085951152232578685394165 4226807920521804251755703)
                      ·
                        rfl

theorem cell23_8231679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 3, 1, 3, 5].length) (baseStart_8231679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8231679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8231679 prefixEnd_8231679 := by exact prefixLift 8231679
  have htrace : WordTrace (prefixWord ++ tailWord_8231679) baseStart_8231679 baseEnd_8231679 := by
    simpa [prefixWord, tailWord_8231679, baseEnd_8231679] using wordTrace_append hprefix tailTrace_8231679
  have hstable : (prefixWord ++ tailWord_8231679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8231679).length < 2 ^ (prefixWord ++ tailWord_8231679).sum := by decide
  have hdescent : baseEnd_8231679 < baseStart_8231679 := by decide
  rcases family_descends (prefixWord ++ tailWord_8231679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8231687 : List Nat := [1, 1, 4, 4, 1, 3, 1, 2, 2, 1, 3]
def baseStart_8231687 : Nat := 118140960795 + 8231687 * 2 ^ 59
def prefixEnd_8231687 : Nat := 4983230072969 + 3 ^ 40 * 8231687 * 2
def baseEnd_8231687 : Nat := 4226812028367040220455667

theorem tailTrace_8231687 : CollatzResearch.WordTrace tailWord_8231687 prefixEnd_8231687 4226812028367040220455667 := by
  unfold tailWord_8231687
  simp only [CollatzResearch.WordTrace]
  refine ⟨300234290129011334058461315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200156193419340889372307543 300234290129011334058461315)
  ·
    refine ⟨450351435193517001087691973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300234290129011334058461315 450351435193517001087691973)
    ·
      refine ⟨84440894098784437703942245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 450351435193517001087691973 84440894098784437703942245)
      ·
        refine ⟨15832667643522082069489171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84440894098784437703942245 15832667643522082069489171)
        ·
          refine ⟨23749001465283123104233757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15832667643522082069489171 23749001465283123104233757)
          ·
            refine ⟨8905875549481171164087659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23749001465283123104233757 8905875549481171164087659)
            ·
              refine ⟨13358813324221756746131489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8905875549481171164087659 13358813324221756746131489)
              ·
                refine ⟨10019109993166317559598617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13358813324221756746131489 10019109993166317559598617)
                ·
                  refine ⟨7514332494874738169698963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10019109993166317559598617 7514332494874738169698963)
                  ·
                    refine ⟨11271498742312107254548445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7514332494874738169698963 11271498742312107254548445)
                    ·
                      refine ⟨4226812028367040220455667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11271498742312107254548445 4226812028367040220455667)
                      ·
                        rfl

theorem cell23_8231687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_8231687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8231687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8231687 prefixEnd_8231687 := by exact prefixLift 8231687
  have htrace : WordTrace (prefixWord ++ tailWord_8231687) baseStart_8231687 baseEnd_8231687 := by
    simpa [prefixWord, tailWord_8231687, baseEnd_8231687] using wordTrace_append hprefix tailTrace_8231687
  have hstable : (prefixWord ++ tailWord_8231687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8231687).length < 2 ^ (prefixWord ++ tailWord_8231687).sum := by decide
  have hdescent : baseEnd_8231687 < baseStart_8231687 := by decide
  rcases family_descends (prefixWord ++ tailWord_8231687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8231706 : List Nat := [3, 1, 1, 3, 2, 1, 1, 3, 2, 2, 4]
def baseStart_8231706 : Nat := 118140960795 + 8231706 * 2 ^ 59
def prefixEnd_8231706 : Nat := 4983230072969 + 3 ^ 40 * 8231706 * 2
def baseEnd_8231706 : Nat := 4226821784499475646118079

theorem tailTrace_8231706 : CollatzResearch.WordTrace tailWord_8231706 prefixEnd_8231706 4226821784499475646118079 := by
  unfold tailWord_8231706
  simp only [CollatzResearch.WordTrace]
  refine ⟨75058745778985625075850743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200156655410628333535601981 75058745778985625075850743)
  ·
    refine ⟨112588118668478437613776115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75058745778985625075850743 112588118668478437613776115)
    ·
      refine ⟨168882178002717656420664173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112588118668478437613776115 168882178002717656420664173)
      ·
        refine ⟨63330816751019121157749065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168882178002717656420664173 63330816751019121157749065)
        ·
          refine ⟨47498112563264340868311799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63330816751019121157749065 47498112563264340868311799)
          ·
            refine ⟨71247168844896511302467699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47498112563264340868311799 71247168844896511302467699)
            ·
              refine ⟨106870753267344766953701549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71247168844896511302467699 106870753267344766953701549)
              ·
                refine ⟨40076532475254287607638081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106870753267344766953701549 40076532475254287607638081)
                ·
                  refine ⟨30057399356440715705728561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40076532475254287607638081 30057399356440715705728561)
                  ·
                    refine ⟨22543049517330536779296421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30057399356440715705728561 22543049517330536779296421)
                    ·
                      refine ⟨4226821784499475646118079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22543049517330536779296421 4226821784499475646118079)
                      ·
                        rfl

theorem cell23_8231706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 3, 2, 2, 4].length) (baseStart_8231706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8231706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8231706 prefixEnd_8231706 := by exact prefixLift 8231706
  have htrace : WordTrace (prefixWord ++ tailWord_8231706) baseStart_8231706 baseEnd_8231706 := by
    simpa [prefixWord, tailWord_8231706, baseEnd_8231706] using wordTrace_append hprefix tailTrace_8231706
  have hstable : (prefixWord ++ tailWord_8231706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8231706).length < 2 ^ (prefixWord ++ tailWord_8231706).sum := by decide
  have hdescent : baseEnd_8231706 < baseStart_8231706 := by decide
  rcases family_descends (prefixWord ++ tailWord_8231706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8231756 : List Nat := [2, 2, 1, 3, 3, 1, 1, 1, 1, 1, 7]
def baseStart_8231756 : Nat := 118140960795 + 8231756 * 2 ^ 59
def prefixEnd_8231756 : Nat := 4983230072969 + 3 ^ 40 * 8231756 * 2
def baseEnd_8231756 : Nat := 4226847458532200450492849

theorem tailTrace_8231756 : CollatzResearch.WordTrace tailWord_8231756 prefixEnd_8231756 4226847458532200450492849 := by
  unfold tailWord_8231756
  simp only [CollatzResearch.WordTrace]
  refine ⟨150118403382880679421361561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200157871177174239228482081 150118403382880679421361561)
  ·
    refine ⟨112588802537160509566021171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150118403382880679421361561 112588802537160509566021171)
    ·
      refine ⟨168883203805740764349031757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112588802537160509566021171 168883203805740764349031757)
      ·
        refine ⟨63331201427152786630886909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168883203805740764349031757 63331201427152786630886909)
        ·
          refine ⟨23749200535182294986582591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63331201427152786630886909 23749200535182294986582591)
          ·
            refine ⟨35623800802773442479873887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23749200535182294986582591 35623800802773442479873887)
            ·
              refine ⟨53435701204160163719810831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35623800802773442479873887 53435701204160163719810831)
              ·
                refine ⟨80153551806240245579716247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53435701204160163719810831 80153551806240245579716247)
                ·
                  refine ⟨120230327709360368369574371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80153551806240245579716247 120230327709360368369574371)
                  ·
                    refine ⟨180345491564040552554361557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 120230327709360368369574371 180345491564040552554361557)
                    ·
                      refine ⟨4226847458532200450492849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 180345491564040552554361557 4226847458532200450492849)
                      ·
                        rfl

theorem cell23_8231756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 1, 1, 1, 7].length) (baseStart_8231756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8231756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8231756 prefixEnd_8231756 := by exact prefixLift 8231756
  have htrace : WordTrace (prefixWord ++ tailWord_8231756) baseStart_8231756 baseEnd_8231756 := by
    simpa [prefixWord, tailWord_8231756, baseEnd_8231756] using wordTrace_append hprefix tailTrace_8231756
  have hstable : (prefixWord ++ tailWord_8231756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8231756).length < 2 ^ (prefixWord ++ tailWord_8231756).sum := by decide
  have hdescent : baseEnd_8231756 < baseStart_8231756 := by decide
  rcases family_descends (prefixWord ++ tailWord_8231756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8231761 : List Nat := [1, 2, 2, 1, 7, 1, 2, 1, 2, 2, 2]
def baseStart_8231761 : Nat := 118140960795 + 8231761 * 2 ^ 59
def prefixEnd_8231761 : Nat := 4983230072969 + 3 ^ 40 * 8231761 * 2
def baseEnd_8231761 : Nat := 4226850025935472930930327

theorem tailTrace_8231761 : CollatzResearch.WordTrace tailWord_8231761 prefixEnd_8231761 4226850025935472930930327 := by
  unfold tailWord_8231761
  simp only [CollatzResearch.WordTrace]
  refine ⟨300236989130743244696655137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200157992753828829797770091 300236989130743244696655137)
  ·
    refine ⟨225177741848057433522491353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300236989130743244696655137 225177741848057433522491353)
    ·
      refine ⟨168883306386043075141868515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225177741848057433522491353 168883306386043075141868515)
      ·
        refine ⟨253324959579064612712802773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168883306386043075141868515 253324959579064612712802773)
        ·
          refine ⟨5937303740134326860456315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 253324959579064612712802773 5937303740134326860456315)
          ·
            refine ⟨8905955610201490290684473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5937303740134326860456315 8905955610201490290684473)
            ·
              refine ⟨6679466707651117718013355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8905955610201490290684473 6679466707651117718013355)
              ·
                refine ⟨10019200061476676577020033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6679466707651117718013355 10019200061476676577020033)
                ·
                  refine ⟨7514400046107507432765025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10019200061476676577020033 7514400046107507432765025)
                  ·
                    refine ⟨5635800034580630574573769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7514400046107507432765025 5635800034580630574573769)
                    ·
                      refine ⟨4226850025935472930930327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5635800034580630574573769 4226850025935472930930327)
                      ·
                        rfl

theorem cell23_8231761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 2, 1, 2, 2, 2].length) (baseStart_8231761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8231761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8231761 prefixEnd_8231761 := by exact prefixLift 8231761
  have htrace : WordTrace (prefixWord ++ tailWord_8231761) baseStart_8231761 baseEnd_8231761 := by
    simpa [prefixWord, tailWord_8231761, baseEnd_8231761] using wordTrace_append hprefix tailTrace_8231761
  have hstable : (prefixWord ++ tailWord_8231761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8231761).length < 2 ^ (prefixWord ++ tailWord_8231761).sum := by decide
  have hdescent : baseEnd_8231761 < baseStart_8231761 := by decide
  rcases family_descends (prefixWord ++ tailWord_8231761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8231783 : List Nat := [1, 1, 5, 1, 2, 2, 1, 3, 2, 1, 4]
def baseStart_8231783 : Nat := 118140960795 + 8231783 * 2 ^ 59
def prefixEnd_8231783 : Nat := 4983230072969 + 3 ^ 40 * 8231783 * 2
def baseEnd_8231783 : Nat := 4226861322509871844855225

theorem tailTrace_8231783 : CollatzResearch.WordTrace tailWord_8231783 prefixEnd_8231783 4226861322509871844855225 := by
  unfold tailWord_8231783
  simp only [CollatzResearch.WordTrace]
  refine ⟨300237791536663542453956003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200158527691109028302637335 300237791536663542453956003)
  ·
    refine ⟨450356687304995313680934005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300237791536663542453956003 450356687304995313680934005)
    ·
      refine ⟨42220939434843310657587563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 450356687304995313680934005 42220939434843310657587563)
      ·
        refine ⟨63331409152264965986381345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42220939434843310657587563 63331409152264965986381345)
        ·
          refine ⟨47498556864198724489786009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63331409152264965986381345 47498556864198724489786009)
          ·
            refine ⟨35623917648149043367339507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47498556864198724489786009 35623917648149043367339507)
            ·
              refine ⟨53435876472223565051009261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35623917648149043367339507 53435876472223565051009261)
              ·
                refine ⟨20038453677083836894128473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53435876472223565051009261 20038453677083836894128473)
                ·
                  refine ⟨15028840257812877670596355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20038453677083836894128473 15028840257812877670596355)
                  ·
                    refine ⟨22543260386719316505894533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15028840257812877670596355 22543260386719316505894533)
                    ·
                      refine ⟨4226861322509871844855225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22543260386719316505894533 4226861322509871844855225)
                      ·
                        rfl

theorem cell23_8231783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 3, 2, 1, 4].length) (baseStart_8231783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8231783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8231783 prefixEnd_8231783 := by exact prefixLift 8231783
  have htrace : WordTrace (prefixWord ++ tailWord_8231783) baseStart_8231783 baseEnd_8231783 := by
    simpa [prefixWord, tailWord_8231783, baseEnd_8231783] using wordTrace_append hprefix tailTrace_8231783
  have hstable : (prefixWord ++ tailWord_8231783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8231783).length < 2 ^ (prefixWord ++ tailWord_8231783).sum := by decide
  have hdescent : baseEnd_8231783 < baseStart_8231783 := by decide
  rcases family_descends (prefixWord ++ tailWord_8231783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8231803 : List Nat := [1, 1, 1, 1, 1, 5, 4, 2, 2, 2, 3]
def baseStart_8231803 : Nat := 118140960795 + 8231803 * 2 ^ 59
def prefixEnd_8231803 : Nat := 4983230072969 + 3 ^ 40 * 8231803 * 2
def baseEnd_8231803 : Nat := 4226871592122961766605133

theorem tailTrace_8231803 : CollatzResearch.WordTrace tailWord_8231803 prefixEnd_8231803 4226871592122961766605133 := by
  unfold tailWord_8231803
  simp only [CollatzResearch.WordTrace]
  refine ⟨300238520996591085869684063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200159013997727390579789375 300238520996591085869684063)
  ·
    refine ⟨450357781494886628804526095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300238520996591085869684063 450357781494886628804526095)
    ·
      refine ⟨675536672242329943206789143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 450357781494886628804526095 675536672242329943206789143)
      ·
        refine ⟨1013305008363494914810183715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 675536672242329943206789143 1013305008363494914810183715)
        ·
          refine ⟨1519957512545242372215275573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1013305008363494914810183715 1519957512545242372215275573)
          ·
            refine ⟨142496016801116472395182085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1519957512545242372215275573 142496016801116472395182085)
            ·
              refine ⟨26718003150209338574096641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 142496016801116472395182085 26718003150209338574096641)
              ·
                refine ⟨20038502362657003930572481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26718003150209338574096641 20038502362657003930572481)
                ·
                  refine ⟨15028876771992752947929361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20038502362657003930572481 15028876771992752947929361)
                  ·
                    refine ⟨11271657578994564710947021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15028876771992752947929361 11271657578994564710947021)
                    ·
                      refine ⟨4226871592122961766605133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11271657578994564710947021 4226871592122961766605133)
                      ·
                        rfl

theorem cell23_8231803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 2, 2, 2, 3].length) (baseStart_8231803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8231803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8231803 prefixEnd_8231803 := by exact prefixLift 8231803
  have htrace : WordTrace (prefixWord ++ tailWord_8231803) baseStart_8231803 baseEnd_8231803 := by
    simpa [prefixWord, tailWord_8231803, baseEnd_8231803] using wordTrace_append hprefix tailTrace_8231803
  have hstable : (prefixWord ++ tailWord_8231803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8231803).length < 2 ^ (prefixWord ++ tailWord_8231803).sum := by decide
  have hdescent : baseEnd_8231803 < baseStart_8231803 := by decide
  rcases family_descends (prefixWord ++ tailWord_8231803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8231857 : List Nat := [1, 2, 2, 4, 4, 1, 1, 2, 6]
def baseStart_8231857 : Nat := 118140960795 + 8231857 * 2 ^ 59
def prefixEnd_8231857 : Nat := 4983230072969 + 3 ^ 40 * 8231857 * 2
def baseEnd_8231857 : Nat := 469655480008700506147765

theorem tailTrace_8231857 : CollatzResearch.WordTrace tailWord_8231857 prefixEnd_8231857 469655480008700506147765 := by
  unfold tailWord_8231857
  simp only [CollatzResearch.WordTrace]
  refine ⟨300240490538395453092149825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200160327025596968728099883 300240490538395453092149825)
  ·
    refine ⟨225180367903796589819112369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300240490538395453092149825 225180367903796589819112369)
    ·
      refine ⟨168885275927847442364334277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225180367903796589819112369 168885275927847442364334277)
      ·
        refine ⟨31665989236471395443312677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 168885275927847442364334277 31665989236471395443312677)
        ·
          refine ⟨5937372981838386645621127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31665989236471395443312677 5937372981838386645621127)
          ·
            refine ⟨8906059472757579968431691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5937372981838386645621127 8906059472757579968431691)
            ·
              refine ⟨13359089209136369952647537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8906059472757579968431691 13359089209136369952647537)
              ·
                refine ⟨10019316906852277464485653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13359089209136369952647537 10019316906852277464485653)
                ·
                  refine ⟨469655480008700506147765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10019316906852277464485653 469655480008700506147765)
                  ·
                    rfl

theorem cell23_8231857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 1, 2, 6].length) (baseStart_8231857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8231857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8231857 prefixEnd_8231857 := by exact prefixLift 8231857
  have htrace : WordTrace (prefixWord ++ tailWord_8231857) baseStart_8231857 baseEnd_8231857 := by
    simpa [prefixWord, tailWord_8231857, baseEnd_8231857] using wordTrace_append hprefix tailTrace_8231857
  have hstable : (prefixWord ++ tailWord_8231857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8231857).length < 2 ^ (prefixWord ++ tailWord_8231857).sum := by decide
  have hdescent : baseEnd_8231857 < baseStart_8231857 := by decide
  rcases family_descends (prefixWord ++ tailWord_8231857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8231860 : List Nat := [2, 5, 2, 1, 1, 1, 1, 1, 1, 2, 6]
def baseStart_8231860 : Nat := 118140960795 + 8231860 * 2 ^ 59
def prefixEnd_8231860 : Nat := 4983230072969 + 3 ^ 40 * 8231860 * 2
def baseEnd_8231860 : Nat := 4226900860520268043592371

theorem tailTrace_8231860 : CollatzResearch.WordTrace tailWord_8231860 prefixEnd_8231860 4226900860520268043592371 := by
  unfold tailWord_8231860
  simp only [CollatzResearch.WordTrace]
  refine ⟨150120299978692292302254517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200160399971589723069672689 150120299978692292302254517)
  ·
    refine ⟨14073778123002402403336361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 150120299978692292302254517 14073778123002402403336361)
    ·
      refine ⟨10555333592251801802502271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14073778123002402403336361 10555333592251801802502271)
      ·
        refine ⟨15833000388377702703753407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10555333592251801802502271 15833000388377702703753407)
        ·
          refine ⟨23749500582566554055630111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15833000388377702703753407 23749500582566554055630111)
          ·
            refine ⟨35624250873849831083445167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23749500582566554055630111 35624250873849831083445167)
            ·
              refine ⟨53436376310774746625167751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35624250873849831083445167 53436376310774746625167751)
              ·
                refine ⟨80154564466162119937751627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53436376310774746625167751 80154564466162119937751627)
                ·
                  refine ⟨120231846699243179906627441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80154564466162119937751627 120231846699243179906627441)
                  ·
                    refine ⟨90173885024432384929970581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 120231846699243179906627441 90173885024432384929970581)
                    ·
                      refine ⟨4226900860520268043592371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90173885024432384929970581 4226900860520268043592371)
                      ·
                        rfl

theorem cell23_8231860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_8231860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8231860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8231860 prefixEnd_8231860 := by exact prefixLift 8231860
  have htrace : WordTrace (prefixWord ++ tailWord_8231860) baseStart_8231860 baseEnd_8231860 := by
    simpa [prefixWord, tailWord_8231860, baseEnd_8231860] using wordTrace_append hprefix tailTrace_8231860
  have hstable : (prefixWord ++ tailWord_8231860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8231860).length < 2 ^ (prefixWord ++ tailWord_8231860).sum := by decide
  have hdescent : baseEnd_8231860 < baseStart_8231860 := by decide
  rcases family_descends (prefixWord ++ tailWord_8231860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8231883 : List Nat := [1, 1, 1, 1, 3, 5, 3, 1, 1, 6]
def baseStart_8231883 : Nat := 118140960795 + 8231883 * 2 ^ 59
def prefixEnd_8231883 : Nat := 4983230072969 + 3 ^ 40 * 8231883 * 2
def baseEnd_8231883 : Nat := 1408970890191773817868255

theorem tailTrace_8231883 : CollatzResearch.WordTrace tailWord_8231883 prefixEnd_8231883 1408970890191773817868255 := by
  unfold tailWord_8231883
  simp only [CollatzResearch.WordTrace]
  refine ⟨300241438836301259532596303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200160959224200839688397535 300241438836301259532596303)
  ·
    refine ⟨450362158254451889298894455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300241438836301259532596303 450362158254451889298894455)
    ·
      refine ⟨675543237381677833948341683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 450362158254451889298894455 675543237381677833948341683)
      ·
        refine ⟨1013314856072516750922512525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 675543237381677833948341683 1013314856072516750922512525)
        ·
          refine ⟨379993071027193781595942197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1013314856072516750922512525 379993071027193781595942197)
          ·
            refine ⟨35624350408799417024619581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 379993071027193781595942197 35624350408799417024619581)
            ·
              refine ⟨13359131403299781384232343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35624350408799417024619581 13359131403299781384232343)
              ·
                refine ⟨20038697104949672076348515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13359131403299781384232343 20038697104949672076348515)
                ·
                  refine ⟨30058045657424508114522773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20038697104949672076348515 30058045657424508114522773)
                  ·
                    refine ⟨1408970890191773817868255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30058045657424508114522773 1408970890191773817868255)
                    ·
                      rfl

theorem cell23_8231883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 3, 1, 1, 6].length) (baseStart_8231883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8231883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8231883 prefixEnd_8231883 := by exact prefixLift 8231883
  have htrace : WordTrace (prefixWord ++ tailWord_8231883) baseStart_8231883 baseEnd_8231883 := by
    simpa [prefixWord, tailWord_8231883, baseEnd_8231883] using wordTrace_append hprefix tailTrace_8231883
  have hstable : (prefixWord ++ tailWord_8231883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8231883).length < 2 ^ (prefixWord ++ tailWord_8231883).sum := by decide
  have hdescent : baseEnd_8231883 < baseStart_8231883 := by decide
  rcases family_descends (prefixWord ++ tailWord_8231883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8231901 : List Nat := [1, 4, 3, 1, 2, 3, 1, 3, 1, 1, 3]
def baseStart_8231901 : Nat := 118140960795 + 8231901 * 2 ^ 59
def prefixEnd_8231901 : Nat := 4983230072969 + 3 ^ 40 * 8231901 * 2
def baseEnd_8231901 : Nat := 4226921913227102383179683

theorem tailTrace_8231901 : CollatzResearch.WordTrace tailWord_8231901 prefixEnd_8231901 4226921913227102383179683 := by
  unfold tailWord_8231901
  simp only [CollatzResearch.WordTrace]
  refine ⟨300242095350236048606751557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200161396900157365737834371 300242095350236048606751557)
  ·
    refine ⟨56295392878169259113765917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 300242095350236048606751557 56295392878169259113765917)
    ·
      refine ⟨21110772329313472167662219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56295392878169259113765917 21110772329313472167662219)
      ·
        refine ⟨31666158493970208251493329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21110772329313472167662219 31666158493970208251493329)
        ·
          refine ⟨23749618870477656188619997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31666158493970208251493329 23749618870477656188619997)
          ·
            refine ⟨8906107076429121070732499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23749618870477656188619997 8906107076429121070732499)
            ·
              refine ⟨13359160614643681606098749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8906107076429121070732499 13359160614643681606098749)
              ·
                refine ⟨5009685230491380602287031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13359160614643681606098749 5009685230491380602287031)
                ·
                  refine ⟨7514527845737070903430547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5009685230491380602287031 7514527845737070903430547)
                  ·
                    refine ⟨11271791768605606355145821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7514527845737070903430547 11271791768605606355145821)
                    ·
                      refine ⟨4226921913227102383179683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11271791768605606355145821 4226921913227102383179683)
                      ·
                        rfl

theorem cell23_8231901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 1, 3, 1, 1, 3].length) (baseStart_8231901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8231901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8231901 prefixEnd_8231901 := by exact prefixLift 8231901
  have htrace : WordTrace (prefixWord ++ tailWord_8231901) baseStart_8231901 baseEnd_8231901 := by
    simpa [prefixWord, tailWord_8231901, baseEnd_8231901] using wordTrace_append hprefix tailTrace_8231901
  have hstable : (prefixWord ++ tailWord_8231901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8231901).length < 2 ^ (prefixWord ++ tailWord_8231901).sum := by decide
  have hdescent : baseEnd_8231901 < baseStart_8231901 := by decide
  rcases family_descends (prefixWord ++ tailWord_8231901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8231934 : List Nat := [4, 2, 2, 2, 2, 1, 1, 3, 2, 4]
def baseStart_8231934 : Nat := 118140960795 + 8231934 * 2 ^ 59
def prefixEnd_8231934 : Nat := 4983230072969 + 3 ^ 40 * 8231934 * 2
def baseEnd_8231934 : Nat := 1408979619362900251355677

theorem tailTrace_8231934 : CollatzResearch.WordTrace tailWord_8231934 prefixEnd_8231934 1408979619362900251355677 := by
  unfold tailWord_8231934
  simp only [CollatzResearch.WordTrace]
  refine ⟨37530412369889561905337857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200162199306077663495135237 37530412369889561905337857)
  ·
    refine ⟨28147809277417171429003393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37530412369889561905337857 28147809277417171429003393)
    ·
      refine ⟨21110856958062878571752545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28147809277417171429003393 21110856958062878571752545)
      ·
        refine ⟨15833142718547158928814409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21110856958062878571752545 15833142718547158928814409)
        ·
          refine ⟨11874857038910369196610807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15833142718547158928814409 11874857038910369196610807)
          ·
            refine ⟨17812285558365553794916211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11874857038910369196610807 17812285558365553794916211)
            ·
              refine ⟨26718428337548330692374317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17812285558365553794916211 26718428337548330692374317)
              ·
                refine ⟨10019410626580624009640369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26718428337548330692374317 10019410626580624009640369)
                ·
                  refine ⟨7514557969935468007230277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10019410626580624009640369 7514557969935468007230277)
                  ·
                    refine ⟨1408979619362900251355677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7514557969935468007230277 1408979619362900251355677)
                    ·
                      rfl

theorem cell23_8231934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 3, 2, 4].length) (baseStart_8231934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8231934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8231934 prefixEnd_8231934 := by exact prefixLift 8231934
  have htrace : WordTrace (prefixWord ++ tailWord_8231934) baseStart_8231934 baseEnd_8231934 := by
    simpa [prefixWord, tailWord_8231934, baseEnd_8231934] using wordTrace_append hprefix tailTrace_8231934
  have hstable : (prefixWord ++ tailWord_8231934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8231934).length < 2 ^ (prefixWord ++ tailWord_8231934).sum := by decide
  have hdescent : baseEnd_8231934 < baseStart_8231934 := by decide
  rcases family_descends (prefixWord ++ tailWord_8231934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8231973 : List Nat := [1, 3, 1, 2, 2, 2, 2, 2, 2, 6]
def baseStart_8231973 : Nat := 118140960795 + 8231973 * 2 ^ 59
def prefixEnd_8231973 : Nat := 4983230072969 + 3 ^ 40 * 8231973 * 2
def baseEnd_8231973 : Nat := 1408986294611408700493117

theorem tailTrace_8231973 : CollatzResearch.WordTrace tailWord_8231973 prefixEnd_8231973 1408986294611408700493117 := by
  unfold tailWord_8231973
  simp only [CollatzResearch.WordTrace]
  refine ⟨300244721405975204903372573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200163147603983469935581715 300244721405975204903372573)
  ·
    refine ⟨112591770527240701838764715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 300244721405975204903372573 112591770527240701838764715)
    ·
      refine ⟨168887655790861052758147073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112591770527240701838764715 168887655790861052758147073)
      ·
        refine ⟨126665741843145789568610305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168887655790861052758147073 126665741843145789568610305)
        ·
          refine ⟨94999306382359342176457729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126665741843145789568610305 94999306382359342176457729)
          ·
            refine ⟨71249479786769506632343297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94999306382359342176457729 71249479786769506632343297)
            ·
              refine ⟨53437109840077129974257473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71249479786769506632343297 53437109840077129974257473)
              ·
                refine ⟨40077832380057847480693105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53437109840077129974257473 40077832380057847480693105)
                ·
                  refine ⟨30058374285043385610519829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40077832380057847480693105 30058374285043385610519829)
                  ·
                    refine ⟨1408986294611408700493117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30058374285043385610519829 1408986294611408700493117)
                    ·
                      rfl

theorem cell23_8231973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 2, 2, 6].length) (baseStart_8231973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8231973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8231973 prefixEnd_8231973 := by exact prefixLift 8231973
  have htrace : WordTrace (prefixWord ++ tailWord_8231973) baseStart_8231973 baseEnd_8231973 := by
    simpa [prefixWord, tailWord_8231973, baseEnd_8231973] using wordTrace_append hprefix tailTrace_8231973
  have hstable : (prefixWord ++ tailWord_8231973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8231973).length < 2 ^ (prefixWord ++ tailWord_8231973).sum := by decide
  have hdescent : baseEnd_8231973 < baseStart_8231973 := by decide
  rcases family_descends (prefixWord ++ tailWord_8231973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8231975 : List Nat := [1, 1, 7, 1, 1, 3, 2, 2, 1, 2, 2]
def baseStart_8231975 : Nat := 118140960795 + 8231975 * 2 ^ 59
def prefixEnd_8231975 : Nat := 4983230072969 + 3 ^ 40 * 8231975 * 2
def baseEnd_8231975 : Nat := 4226959910795535093654343

theorem tailTrace_8231975 : CollatzResearch.WordTrace tailWord_8231975 prefixEnd_8231975 4226959910795535093654343 := by
  unfold tailWord_8231975
  simp only [CollatzResearch.WordTrace]
  refine ⟨300244794351967959244945379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200163196234645306163296919 300244794351967959244945379)
  ·
    refine ⟨450367191527951938867418069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300244794351967959244945379 450367191527951938867418069)
    ·
      refine ⟨10555481051436373567205111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 450367191527951938867418069 10555481051436373567205111)
      ·
        refine ⟨15833221577154560350807667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10555481051436373567205111 15833221577154560350807667)
        ·
          refine ⟨23749832365731840526211501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15833221577154560350807667 23749832365731840526211501)
          ·
            refine ⟨8906187137149440197329313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23749832365731840526211501 8906187137149440197329313)
            ·
              refine ⟨6679640352862080147996985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8906187137149440197329313 6679640352862080147996985)
              ·
                refine ⟨5009730264646560110997739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6679640352862080147996985 5009730264646560110997739)
                ·
                  refine ⟨7514595396969840166496609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5009730264646560110997739 7514595396969840166496609)
                  ·
                    refine ⟨5635946547727380124872457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7514595396969840166496609 5635946547727380124872457)
                    ·
                      refine ⟨4226959910795535093654343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5635946547727380124872457 4226959910795535093654343)
                      ·
                        rfl

theorem cell23_8231975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 2, 2, 1, 2, 2].length) (baseStart_8231975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8231975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8231975 prefixEnd_8231975 := by exact prefixLift 8231975
  have htrace : WordTrace (prefixWord ++ tailWord_8231975) baseStart_8231975 baseEnd_8231975 := by
    simpa [prefixWord, tailWord_8231975, baseEnd_8231975] using wordTrace_append hprefix tailTrace_8231975
  have hstable : (prefixWord ++ tailWord_8231975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8231975).length < 2 ^ (prefixWord ++ tailWord_8231975).sum := by decide
  have hdescent : baseEnd_8231975 < baseStart_8231975 := by decide
  rcases family_descends (prefixWord ++ tailWord_8231975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8231980 : List Nat := [2, 2, 1, 1, 1, 2, 3, 2, 3, 4, 2]
def baseStart_8231980 : Nat := 118140960795 + 8231980 * 2 ^ 59
def prefixEnd_8231980 : Nat := 4983230072969 + 3 ^ 40 * 8231980 * 2
def baseEnd_8231980 : Nat := 4226962478198807574091819

theorem tailTrace_8231980 : CollatzResearch.WordTrace tailWord_8231980 prefixEnd_8231980 4226962478198807574091819 := by
  unfold tailWord_8231980
  simp only [CollatzResearch.WordTrace]
  refine ⟨150122488358474922549438697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200163317811299896732584929 150122488358474922549438697)
  ·
    refine ⟨112591866268856191912079023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150122488358474922549438697 112591866268856191912079023)
    ·
      refine ⟨168887799403284287868118535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112591866268856191912079023 168887799403284287868118535)
      ·
        refine ⟨253331699104926431802177803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168887799403284287868118535 253331699104926431802177803)
        ·
          refine ⟨379997548657389647703266705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253331699104926431802177803 379997548657389647703266705)
          ·
            refine ⟨284998161493042235777450029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 379997548657389647703266705 284998161493042235777450029)
            ·
              refine ⟨106874310559890838416543761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 284998161493042235777450029 106874310559890838416543761)
              ·
                refine ⟨80155732919918128812407821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106874310559890838416543761 80155732919918128812407821)
                ·
                  refine ⟨30058399844969298304652933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80155732919918128812407821 30058399844969298304652933)
                  ·
                    refine ⟨5635949970931743432122425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30058399844969298304652933 5635949970931743432122425)
                    ·
                      refine ⟨4226962478198807574091819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5635949970931743432122425 4226962478198807574091819)
                      ·
                        rfl

theorem cell23_8231980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 4, 2].length) (baseStart_8231980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8231980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8231980 prefixEnd_8231980 := by exact prefixLift 8231980
  have htrace : WordTrace (prefixWord ++ tailWord_8231980) baseStart_8231980 baseEnd_8231980 := by
    simpa [prefixWord, tailWord_8231980, baseEnd_8231980] using wordTrace_append hprefix tailTrace_8231980
  have hstable : (prefixWord ++ tailWord_8231980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8231980).length < 2 ^ (prefixWord ++ tailWord_8231980).sum := by decide
  have hdescent : baseEnd_8231980 < baseStart_8231980 := by decide
  rcases family_descends (prefixWord ++ tailWord_8231980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8231990 : List Nat := [5, 1, 2, 1, 1, 2, 1, 1, 1, 8]
def baseStart_8231990 : Nat := 118140960795 + 8231990 * 2 ^ 59
def prefixEnd_8231990 : Nat := 4983230072969 + 3 ^ 40 * 8231990 * 2
def baseEnd_8231990 : Nat := 1408989204335117511655591

theorem tailTrace_8231990 : CollatzResearch.WordTrace tailWord_8231990 prefixEnd_8231990 1408989204335117511655591 := by
  unfold tailWord_8231990
  simp only [CollatzResearch.WordTrace]
  refine ⟨18765333840432101050421339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 200163560964609077871160949 18765333840432101050421339)
  ·
    refine ⟨28148000760648151575632009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18765333840432101050421339 28148000760648151575632009)
    ·
      refine ⟨21111000570486113681724007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28148000760648151575632009 21111000570486113681724007)
      ·
        refine ⟨31666500855729170522586011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21111000570486113681724007 31666500855729170522586011)
        ·
          refine ⟨47499751283593755783879017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31666500855729170522586011 47499751283593755783879017)
          ·
            refine ⟨35624813462695316837909263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47499751283593755783879017 35624813462695316837909263)
            ·
              refine ⟨53437220194042975256863895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35624813462695316837909263 53437220194042975256863895)
              ·
                refine ⟨80155830291064462885295843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53437220194042975256863895 80155830291064462885295843)
                ·
                  refine ⟨120233745436596694327943765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80155830291064462885295843 120233745436596694327943765)
                  ·
                    refine ⟨1408989204335117511655591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 120233745436596694327943765 1408989204335117511655591)
                    ·
                      rfl

theorem cell23_8231990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 1, 1, 8].length) (baseStart_8231990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8231990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8231990 prefixEnd_8231990 := by exact prefixLift 8231990
  have htrace : WordTrace (prefixWord ++ tailWord_8231990) baseStart_8231990 baseEnd_8231990 := by
    simpa [prefixWord, tailWord_8231990, baseEnd_8231990] using wordTrace_append hprefix tailTrace_8231990
  have hstable : (prefixWord ++ tailWord_8231990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8231990).length < 2 ^ (prefixWord ++ tailWord_8231990).sum := by decide
  have hdescent : baseEnd_8231990 < baseStart_8231990 := by decide
  rcases family_descends (prefixWord ++ tailWord_8231990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8231997 : List Nat := [1, 4, 1, 3, 1, 2, 1, 3, 1, 4, 2]
def baseStart_8231997 : Nat := 118140960795 + 8231997 * 2 ^ 59
def prefixEnd_8231997 : Nat := 4983230072969 + 3 ^ 40 * 8231997 * 2
def baseEnd_8231997 : Nat := 4226971207369934007579241

theorem tailTrace_8231997 : CollatzResearch.WordTrace tailWord_8231997 prefixEnd_8231997 4226971207369934007579241 := by
  unfold tailWord_8231997
  simp only [CollatzResearch.WordTrace]
  refine ⟨300245596757888257002246245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200163731171925504668164163 300245596757888257002246245)
  ·
    refine ⟨56296049392104048187921171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 300245596757888257002246245 56296049392104048187921171)
    ·
      refine ⟨84444074088156072281881757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56296049392104048187921171 84444074088156072281881757)
      ·
        refine ⟨31666527783058527105705659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84444074088156072281881757 31666527783058527105705659)
        ·
          refine ⟨47499791674587790658558489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31666527783058527105705659 47499791674587790658558489)
          ·
            refine ⟨35624843755940842993918867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47499791674587790658558489 35624843755940842993918867)
            ·
              refine ⟨53437265633911264490878301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35624843755940842993918867 53437265633911264490878301)
              ·
                refine ⟨20038974612716724184079363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53437265633911264490878301 20038974612716724184079363)
                ·
                  refine ⟨30058461919075086276119045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20038974612716724184079363 30058461919075086276119045)
                  ·
                    refine ⟨5635961609826578676772321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30058461919075086276119045 5635961609826578676772321)
                    ·
                      refine ⟨4226971207369934007579241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5635961609826578676772321 4226971207369934007579241)
                      ·
                        rfl

theorem cell23_8231997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 3, 1, 4, 2].length) (baseStart_8231997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8231997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8231997 prefixEnd_8231997 := by exact prefixLift 8231997
  have htrace : WordTrace (prefixWord ++ tailWord_8231997) baseStart_8231997 baseEnd_8231997 := by
    simpa [prefixWord, tailWord_8231997, baseEnd_8231997] using wordTrace_append hprefix tailTrace_8231997
  have hstable : (prefixWord ++ tailWord_8231997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8231997).length < 2 ^ (prefixWord ++ tailWord_8231997).sum := by decide
  have hdescent : baseEnd_8231997 < baseStart_8231997 := by decide
  rcases family_descends (prefixWord ++ tailWord_8231997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8232003 : List Nat := [1, 1, 1, 3, 1, 2, 5, 2, 7]
def baseStart_8232003 : Nat := 118140960795 + 8232003 * 2 ^ 59
def prefixEnd_8232003 : Nat := 4983230072969 + 3 ^ 40 * 8232003 * 2
def baseEnd_8232003 : Nat := 469663809805984553789357

theorem tailTrace_8232003 : CollatzResearch.WordTrace tailWord_8232003 prefixEnd_8232003 469663809805984553789357 := by
  unfold tailWord_8232003
  simp only [CollatzResearch.WordTrace]
  refine ⟨300245815595866520026964663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200163877063911013351309775 300245815595866520026964663)
  ·
    refine ⟨450368723393799780040446995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300245815595866520026964663 450368723393799780040446995)
    ·
      refine ⟨675553085090699670060670493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 450368723393799780040446995 675553085090699670060670493)
      ·
        refine ⟨253332406909012376272751435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 675553085090699670060670493 253332406909012376272751435)
        ·
          refine ⟨379998610363518564409127153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253332406909012376272751435 379998610363518564409127153)
          ·
            refine ⟨284998957772638923306845365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 379998610363518564409127153 284998957772638923306845365)
            ·
              refine ⟨26718652291184899060016753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 284998957772638923306845365 26718652291184899060016753)
              ·
                refine ⟨20038989218388674295012565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26718652291184899060016753 20038989218388674295012565)
                ·
                  refine ⟨469663809805984553789357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20038989218388674295012565 469663809805984553789357)
                  ·
                    rfl

theorem cell23_8232003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 2, 7].length) (baseStart_8232003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8232003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8232003 prefixEnd_8232003 := by exact prefixLift 8232003
  have htrace : WordTrace (prefixWord ++ tailWord_8232003) baseStart_8232003 baseEnd_8232003 := by
    simpa [prefixWord, tailWord_8232003, baseEnd_8232003] using wordTrace_append hprefix tailTrace_8232003
  have hstable : (prefixWord ++ tailWord_8232003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8232003).length < 2 ^ (prefixWord ++ tailWord_8232003).sum := by decide
  have hdescent : baseEnd_8232003 < baseStart_8232003 := by decide
  rcases family_descends (prefixWord ++ tailWord_8232003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8232083 : List Nat := [1, 1, 1, 2, 1, 2, 4, 1, 1, 3, 6]
def baseStart_8232083 : Nat := 118140960795 + 8232083 * 2 ^ 59
def prefixEnd_8232083 : Nat := 4983230072969 + 3 ^ 40 * 8232083 * 2
def baseEnd_8232083 : Nat := 4227015366706220671103845

theorem tailTrace_8232083 : CollatzResearch.WordTrace tailWord_8232083 prefixEnd_8232083 4227015366706220671103845 := by
  unfold tailWord_8232083
  simp only [CollatzResearch.WordTrace]
  refine ⟨300248733435576693689876903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200165822290384462459917935 300248733435576693689876903)
  ·
    refine ⟨450373100153365040534815355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300248733435576693689876903 450373100153365040534815355)
    ·
      refine ⟨675559650230047560802223033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 450373100153365040534815355 675559650230047560802223033)
      ·
        refine ⟨506669737672535670601667275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 675559650230047560802223033 506669737672535670601667275)
        ·
          refine ⟨760004606508803505902500913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 506669737672535670601667275 760004606508803505902500913)
          ·
            refine ⟨570003454881602629426875685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 760004606508803505902500913 570003454881602629426875685)
            ·
              refine ⟨106875647790300493017539191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 570003454881602629426875685 106875647790300493017539191)
              ·
                refine ⟨160313471685450739526308787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106875647790300493017539191 160313471685450739526308787)
                ·
                  refine ⟨240470207528176109289463181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 160313471685450739526308787 240470207528176109289463181)
                  ·
                    refine ⟨90176327823066040983548693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 240470207528176109289463181 90176327823066040983548693)
                    ·
                      refine ⟨4227015366706220671103845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90176327823066040983548693 4227015366706220671103845)
                      ·
                        rfl

theorem cell23_8232083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 3, 6].length) (baseStart_8232083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8232083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8232083 prefixEnd_8232083 := by exact prefixLift 8232083
  have htrace : WordTrace (prefixWord ++ tailWord_8232083) baseStart_8232083 baseEnd_8232083 := by
    simpa [prefixWord, tailWord_8232083, baseEnd_8232083] using wordTrace_append hprefix tailTrace_8232083
  have hstable : (prefixWord ++ tailWord_8232083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8232083).length < 2 ^ (prefixWord ++ tailWord_8232083).sum := by decide
  have hdescent : baseEnd_8232083 < baseStart_8232083 := by decide
  rcases family_descends (prefixWord ++ tailWord_8232083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8232087 : List Nat := [1, 1, 3, 3, 3, 2, 1, 2, 2, 1, 4]
def baseStart_8232087 : Nat := 118140960795 + 8232087 * 2 ^ 59
def prefixEnd_8232087 : Nat := 4983230072969 + 3 ^ 40 * 8232087 * 2
def baseEnd_8232087 : Nat := 4227017420628838655453827

theorem tailTrace_8232087 : CollatzResearch.WordTrace tailWord_8232087 prefixEnd_8232087 4227017420628838655453827 := by
  unfold tailWord_8232087
  simp only [CollatzResearch.WordTrace]
  refine ⟨300248879327562202373022515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200165919551708134915348343 300248879327562202373022515)
  ·
    refine ⟨450373318991343303559533773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300248879327562202373022515 450373318991343303559533773)
    ·
      refine ⟨168889994621753738834825165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 450373318991343303559533773 168889994621753738834825165)
      ·
        refine ⟨63333747983157652063059437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168889994621753738834825165 63333747983157652063059437)
        ·
          refine ⟨23750155493684119523647289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63333747983157652063059437 23750155493684119523647289)
          ·
            refine ⟨17812616620263089642735467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23750155493684119523647289 17812616620263089642735467)
            ·
              refine ⟨26718924930394634464103201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17812616620263089642735467 26718924930394634464103201)
              ·
                refine ⟨20039193697795975848077401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26718924930394634464103201 20039193697795975848077401)
                ·
                  refine ⟨15029395273346981886058051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20039193697795975848077401 15029395273346981886058051)
                  ·
                    refine ⟨22544092910020472829087077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15029395273346981886058051 22544092910020472829087077)
                    ·
                      refine ⟨4227017420628838655453827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22544092910020472829087077 4227017420628838655453827)
                      ·
                        rfl

theorem cell23_8232087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 2, 2, 1, 4].length) (baseStart_8232087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8232087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8232087 prefixEnd_8232087 := by exact prefixLift 8232087
  have htrace : WordTrace (prefixWord ++ tailWord_8232087) baseStart_8232087 baseEnd_8232087 := by
    simpa [prefixWord, tailWord_8232087, baseEnd_8232087] using wordTrace_append hprefix tailTrace_8232087
  have hstable : (prefixWord ++ tailWord_8232087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8232087).length < 2 ^ (prefixWord ++ tailWord_8232087).sum := by decide
  have hdescent : baseEnd_8232087 < baseStart_8232087 := by decide
  rcases family_descends (prefixWord ++ tailWord_8232087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8232124 : List Nat := [2, 2, 2, 3, 2, 2, 2, 1, 2, 2, 3]
def baseStart_8232124 : Nat := 118140960795 + 8232124 * 2 ^ 59
def prefixEnd_8232124 : Nat := 4983230072969 + 3 ^ 40 * 8232124 * 2
def baseEnd_8232124 : Nat := 4227036419413055010691157

theorem tailTrace_8232124 : CollatzResearch.WordTrace tailWord_8232124 prefixEnd_8232124 4227036419413055010691157 := by
  unfold tailWord_8232124
  simp only [CollatzResearch.WordTrace]
  refine ⟨150125114414214078846059713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200166819218952105128079617 150125114414214078846059713)
  ·
    refine ⟨112593835810660559134544785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150125114414214078846059713 112593835810660559134544785)
    ·
      refine ⟨84445376857995419350908589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112593835810660559134544785 84445376857995419350908589)
      ·
        refine ⟨31667016321748282256590721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84445376857995419350908589 31667016321748282256590721)
        ·
          refine ⟨23750262241311211692443041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31667016321748282256590721 23750262241311211692443041)
          ·
            refine ⟨17812696680983408769332281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23750262241311211692443041 17812696680983408769332281)
            ·
              refine ⟨13359522510737556576999211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17812696680983408769332281 13359522510737556576999211)
              ·
                refine ⟨20039283766106334865498817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13359522510737556576999211 20039283766106334865498817)
                ·
                  refine ⟨15029462824579751149124113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20039283766106334865498817 15029462824579751149124113)
                  ·
                    refine ⟨11272097118434813361843085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15029462824579751149124113 11272097118434813361843085)
                    ·
                      refine ⟨4227036419413055010691157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11272097118434813361843085 4227036419413055010691157)
                      ·
                        rfl

theorem cell23_8232124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 2, 1, 2, 2, 3].length) (baseStart_8232124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8232124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8232124 prefixEnd_8232124 := by exact prefixLift 8232124
  have htrace : WordTrace (prefixWord ++ tailWord_8232124) baseStart_8232124 baseEnd_8232124 := by
    simpa [prefixWord, tailWord_8232124, baseEnd_8232124] using wordTrace_append hprefix tailTrace_8232124
  have hstable : (prefixWord ++ tailWord_8232124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8232124).length < 2 ^ (prefixWord ++ tailWord_8232124).sum := by decide
  have hdescent : baseEnd_8232124 < baseStart_8232124 := by decide
  rcases family_descends (prefixWord ++ tailWord_8232124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8232148 : List Nat := [2, 4, 1, 4, 1, 1, 1, 4, 1, 4]
def baseStart_8232148 : Nat := 118140960795 + 8232148 * 2 ^ 59
def prefixEnd_8232148 : Nat := 4983230072969 + 3 ^ 40 * 8232148 * 2
def baseEnd_8232148 : Nat := 1409016247649587638930349

theorem tailTrace_8232148 : CollatzResearch.WordTrace tailWord_8232148 prefixEnd_8232148 1409016247649587638930349 := by
  unfold tailWord_8232148
  simp only [CollatzResearch.WordTrace]
  refine ⟨150125552090170604895496549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200167402786894139860662065 150125552090170604895496549)
  ·
    refine ⟨28148541016906988417905603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150125552090170604895496549 28148541016906988417905603)
    ·
      refine ⟨42222811525360482626858405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28148541016906988417905603 42222811525360482626858405)
      ·
        refine ⟨7916777161005090492535951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42222811525360482626858405 7916777161005090492535951)
        ·
          refine ⟨11875165741507635738803927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7916777161005090492535951 11875165741507635738803927)
          ·
            refine ⟨17812748612261453608205891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11875165741507635738803927 17812748612261453608205891)
            ·
              refine ⟨26719122918392180412308837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17812748612261453608205891 26719122918392180412308837)
              ·
                refine ⟨5009835547198533827307907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26719122918392180412308837 5009835547198533827307907)
                ·
                  refine ⟨7514753320797800740961861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5009835547198533827307907 7514753320797800740961861)
                  ·
                    refine ⟨1409016247649587638930349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7514753320797800740961861 1409016247649587638930349)
                    ·
                      rfl

theorem cell23_8232148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 4, 1, 4].length) (baseStart_8232148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8232148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8232148 prefixEnd_8232148 := by exact prefixLift 8232148
  have htrace : WordTrace (prefixWord ++ tailWord_8232148) baseStart_8232148 baseEnd_8232148 := by
    simpa [prefixWord, tailWord_8232148, baseEnd_8232148] using wordTrace_append hprefix tailTrace_8232148
  have hstable : (prefixWord ++ tailWord_8232148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8232148).length < 2 ^ (prefixWord ++ tailWord_8232148).sum := by decide
  have hdescent : baseEnd_8232148 < baseStart_8232148 := by decide
  rcases family_descends (prefixWord ++ tailWord_8232148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8232177 : List Nat := [1, 2, 2, 2, 2, 1, 1, 6, 1, 1, 4]
def baseStart_8232177 : Nat := 118140960795 + 8232177 * 2 ^ 59
def prefixEnd_8232177 : Nat := 4983230072969 + 3 ^ 40 * 8232177 * 2
def baseEnd_8232177 : Nat := 4227063633887743303328413

theorem tailTrace_8232177 : CollatzResearch.WordTrace tailWord_8232177 prefixEnd_8232177 4227063633887743303328413 := by
  unfold tailWord_8232177
  simp only [CollatzResearch.WordTrace]
  refine ⟨300252161897236147743798785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200168107931490765162532523 300252161897236147743798785)
  ·
    refine ⟨225189121422927110807849089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300252161897236147743798785 225189121422927110807849089)
    ·
      refine ⟨168891841067195333105886817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225189121422927110807849089 168891841067195333105886817)
      ·
        refine ⟨126668880800396499829415113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168891841067195333105886817 126668880800396499829415113)
        ·
          refine ⟨95001660600297374872061335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126668880800396499829415113 95001660600297374872061335)
          ·
            refine ⟨142502490900446062308092003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95001660600297374872061335 142502490900446062308092003)
            ·
              refine ⟨213753736350669093462138005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142502490900446062308092003 213753736350669093462138005)
              ·
                refine ⟨10019706391437613756037719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 213753736350669093462138005 10019706391437613756037719)
                ·
                  refine ⟨15029559587156420634056579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10019706391437613756037719 15029559587156420634056579)
                  ·
                    refine ⟨22544339380734630951084869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15029559587156420634056579 22544339380734630951084869)
                    ·
                      refine ⟨4227063633887743303328413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22544339380734630951084869 4227063633887743303328413)
                      ·
                        rfl

theorem cell23_8232177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 6, 1, 1, 4].length) (baseStart_8232177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8232177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8232177 prefixEnd_8232177 := by exact prefixLift 8232177
  have htrace : WordTrace (prefixWord ++ tailWord_8232177) baseStart_8232177 baseEnd_8232177 := by
    simpa [prefixWord, tailWord_8232177, baseEnd_8232177] using wordTrace_append hprefix tailTrace_8232177
  have hstable : (prefixWord ++ tailWord_8232177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8232177).length < 2 ^ (prefixWord ++ tailWord_8232177).sum := by decide
  have hdescent : baseEnd_8232177 < baseStart_8232177 := by decide
  rcases family_descends (prefixWord ++ tailWord_8232177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8232188 : List Nat := [2, 2, 2, 1, 5, 1, 2, 3, 1, 1, 3]
def baseStart_8232188 : Nat := 118140960795 + 8232188 * 2 ^ 59
def prefixEnd_8232188 : Nat := 4983230072969 + 3 ^ 40 * 8232188 * 2
def baseEnd_8232188 : Nat := 4227069282174942760290863

theorem tailTrace_8232188 : CollatzResearch.WordTrace tailWord_8232188 prefixEnd_8232188 4227069282174942760290863 := by
  unfold tailWord_8232188
  simp only [CollatzResearch.WordTrace]
  refine ⟨150126281550098148311224609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200168375400130864414966145 150126281550098148311224609)
  ·
    refine ⟨112594711162573611233418457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150126281550098148311224609 112594711162573611233418457)
    ·
      refine ⟨84446033371930208425063843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112594711162573611233418457 84446033371930208425063843)
      ·
        refine ⟨126669050057895312637595765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84446033371930208425063843 126669050057895312637595765)
        ·
          refine ⟨11875223442927685559774603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 126669050057895312637595765 11875223442927685559774603)
          ·
            refine ⟨17812835164391528339661905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11875223442927685559774603 17812835164391528339661905)
            ·
              refine ⟨13359626373293646254746429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17812835164391528339661905 13359626373293646254746429)
              ·
                refine ⟨5009859889985117345529911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13359626373293646254746429 5009859889985117345529911)
                ·
                  refine ⟨7514789834977676018294867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5009859889985117345529911 7514789834977676018294867)
                  ·
                    refine ⟨11272184752466514027442301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7514789834977676018294867 11272184752466514027442301)
                    ·
                      refine ⟨4227069282174942760290863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11272184752466514027442301 4227069282174942760290863)
                      ·
                        rfl

theorem cell23_8232188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 2, 3, 1, 1, 3].length) (baseStart_8232188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8232188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8232188 prefixEnd_8232188 := by exact prefixLift 8232188
  have htrace : WordTrace (prefixWord ++ tailWord_8232188) baseStart_8232188 baseEnd_8232188 := by
    simpa [prefixWord, tailWord_8232188, baseEnd_8232188] using wordTrace_append hprefix tailTrace_8232188
  have hstable : (prefixWord ++ tailWord_8232188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8232188).length < 2 ^ (prefixWord ++ tailWord_8232188).sum := by decide
  have hdescent : baseEnd_8232188 < baseStart_8232188 := by decide
  rcases family_descends (prefixWord ++ tailWord_8232188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8232204 : List Nat := [2, 2, 1, 2, 2, 3, 3, 2, 2, 4]
def baseStart_8232204 : Nat := 118140960795 + 8232204 * 2 ^ 59
def prefixEnd_8232204 : Nat := 4983230072969 + 3 ^ 40 * 8232204 * 2
def baseEnd_8232204 : Nat := 1409025832621804899230263

theorem tailTrace_8232204 : CollatzResearch.WordTrace tailWord_8232204 prefixEnd_8232204 1409025832621804899230263 := by
  unfold tailWord_8232204
  simp only [CollatzResearch.WordTrace]
  refine ⟨150126573334069165677515833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200168764445425554236687777 150126573334069165677515833)
  ·
    refine ⟨112594930000551874258136875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150126573334069165677515833 112594930000551874258136875)
    ·
      refine ⟨168892395000827811387205313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112594930000551874258136875 168892395000827811387205313)
      ·
        refine ⟨126669296250620858540403985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168892395000827811387205313 126669296250620858540403985)
        ·
          refine ⟨95001972187965643905302989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126669296250620858540403985 95001972187965643905302989)
          ·
            refine ⟨35625739570487116464488621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95001972187965643905302989 35625739570487116464488621)
            ·
              refine ⟨13359652338932668674183233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35625739570487116464488621 13359652338932668674183233)
              ·
                refine ⟨10019739254199501505637425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13359652338932668674183233 10019739254199501505637425)
                ·
                  refine ⟨7514804440649626129228069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10019739254199501505637425 7514804440649626129228069)
                  ·
                    refine ⟨1409025832621804899230263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7514804440649626129228069 1409025832621804899230263)
                    ·
                      rfl

theorem cell23_8232204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 3, 2, 2, 4].length) (baseStart_8232204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8232204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8232204 prefixEnd_8232204 := by exact prefixLift 8232204
  have htrace : WordTrace (prefixWord ++ tailWord_8232204) baseStart_8232204 baseEnd_8232204 := by
    simpa [prefixWord, tailWord_8232204, baseEnd_8232204] using wordTrace_append hprefix tailTrace_8232204
  have hstable : (prefixWord ++ tailWord_8232204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8232204).length < 2 ^ (prefixWord ++ tailWord_8232204).sum := by decide
  have hdescent : baseEnd_8232204 < baseStart_8232204 := by decide
  rcases family_descends (prefixWord ++ tailWord_8232204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8232234 : List Nat := [3, 1, 4, 2, 1, 1, 4, 7]
def baseStart_8232234 : Nat := 118140960795 + 8232234 * 2 ^ 59
def prefixEnd_8232234 : Nat := 4983230072969 + 3 ^ 40 * 8232234 * 2
def baseEnd_8232234 : Nat := 156558996380927762233913

theorem tailTrace_8232234 : CollatzResearch.WordTrace tailWord_8232234 prefixEnd_8232234 156558996380927762233913 := by
  unfold tailWord_8232234
  simp only [CollatzResearch.WordTrace]
  refine ⟨75063560214507411619655939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200169493905353097652415837 75063560214507411619655939)
  ·
    refine ⟨112595340321761117429483909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75063560214507411619655939 112595340321761117429483909)
    ·
      refine ⟨21111626310330209518028233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112595340321761117429483909 21111626310330209518028233)
      ·
        refine ⟨15833719732747657138521175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21111626310330209518028233 15833719732747657138521175)
        ·
          refine ⟨23750579599121485707781763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15833719732747657138521175 23750579599121485707781763)
          ·
            refine ⟨35625869398682228561672645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23750579599121485707781763 35625869398682228561672645)
            ·
              refine ⟨6679850512252917855313621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35625869398682228561672645 6679850512252917855313621)
              ·
                refine ⟨156558996380927762233913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6679850512252917855313621 156558996380927762233913)
                ·
                  rfl

theorem cell23_8232234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 4, 7].length) (baseStart_8232234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8232234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8232234 prefixEnd_8232234 := by exact prefixLift 8232234
  have htrace : WordTrace (prefixWord ++ tailWord_8232234) baseStart_8232234 baseEnd_8232234 := by
    simpa [prefixWord, tailWord_8232234, baseEnd_8232234] using wordTrace_append hprefix tailTrace_8232234
  have hstable : (prefixWord ++ tailWord_8232234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8232234).length < 2 ^ (prefixWord ++ tailWord_8232234).sum := by decide
  have hdescent : baseEnd_8232234 < baseStart_8232234 := by decide
  rcases family_descends (prefixWord ++ tailWord_8232234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8232240 : List Nat := [2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 5]
def baseStart_8232240 : Nat := 118140960795 + 8232240 * 2 ^ 59
def prefixEnd_8232240 : Nat := 4983230072969 + 3 ^ 40 * 8232240 * 2
def baseEnd_8232240 : Nat := 4227095983168976556840623

theorem tailTrace_8232240 : CollatzResearch.WordTrace tailWord_8232240 prefixEnd_8232240 4227095983168976556840623 := by
  unfold tailWord_8232240
  simp only [CollatzResearch.WordTrace]
  refine ⟨150127229848003954751671087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200169639797338606335561449 150127229848003954751671087)
  ·
    refine ⟨225190844772005932127506631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150127229848003954751671087 225190844772005932127506631)
    ·
      refine ⟨337786267158008898191259947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225190844772005932127506631 337786267158008898191259947)
      ·
        refine ⟨506679400737013347286889921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337786267158008898191259947 506679400737013347286889921)
        ·
          refine ⟨380009550552760010465167441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 506679400737013347286889921 380009550552760010465167441)
          ·
            refine ⟨285007162914570007848875581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 380009550552760010465167441 285007162914570007848875581)
            ·
              refine ⟨106877686092963752943328343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 285007162914570007848875581 106877686092963752943328343)
              ·
                refine ⟨160316529139445629414992515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106877686092963752943328343 160316529139445629414992515)
                ·
                  refine ⟨240474793709168444122488773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 160316529139445629414992515 240474793709168444122488773)
                  ·
                    refine ⟨45089023820469083272966645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 240474793709168444122488773 45089023820469083272966645)
                    ·
                      refine ⟨4227095983168976556840623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45089023820469083272966645 4227095983168976556840623)
                      ·
                        rfl

theorem cell23_8232240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 5].length) (baseStart_8232240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8232240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8232240 prefixEnd_8232240 := by exact prefixLift 8232240
  have htrace : WordTrace (prefixWord ++ tailWord_8232240) baseStart_8232240 baseEnd_8232240 := by
    simpa [prefixWord, tailWord_8232240, baseEnd_8232240] using wordTrace_append hprefix tailTrace_8232240
  have hstable : (prefixWord ++ tailWord_8232240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8232240).length < 2 ^ (prefixWord ++ tailWord_8232240).sum := by decide
  have hdescent : baseEnd_8232240 < baseStart_8232240 := by decide
  rcases family_descends (prefixWord ++ tailWord_8232240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8232244 : List Nat := [2, 5, 1, 1, 1, 1, 2, 1, 3, 3, 3]
def baseStart_8232244 : Nat := 118140960795 + 8232244 * 2 ^ 59
def prefixEnd_8232244 : Nat := 4983230072969 + 3 ^ 40 * 8232244 * 2
def baseEnd_8232244 : Nat := 4227098037091594541190605

theorem tailTrace_8232244 : CollatzResearch.WordTrace tailWord_8232244 prefixEnd_8232244 4227098037091594541190605 := by
  unfold tailWord_8232244
  simp only [CollatzResearch.WordTrace]
  refine ⟨150127302793996709093243893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200169737058662278790991857 150127302793996709093243893)
  ·
    refine ⟨14074434636937191477491615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 150127302793996709093243893 14074434636937191477491615)
    ·
      refine ⟨21111651955405787216237423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14074434636937191477491615 21111651955405787216237423)
      ·
        refine ⟨31667477933108680824356135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21111651955405787216237423 31667477933108680824356135)
        ·
          refine ⟨47501216899663021236534203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31667477933108680824356135 47501216899663021236534203)
          ·
            refine ⟨71251825349494531854801305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47501216899663021236534203 71251825349494531854801305)
            ·
              refine ⟨53438869012120898891100979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71251825349494531854801305 53438869012120898891100979)
              ·
                refine ⟨80158303518181348336651469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53438869012120898891100979 80158303518181348336651469)
                ·
                  refine ⟨30059363819318005626244301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80158303518181348336651469 30059363819318005626244301)
                  ·
                    refine ⟨11272261432244252109841613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30059363819318005626244301 11272261432244252109841613)
                    ·
                      refine ⟨4227098037091594541190605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11272261432244252109841613 4227098037091594541190605)
                      ·
                        rfl

theorem cell23_8232244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 1, 3, 3, 3].length) (baseStart_8232244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8232244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8232244 prefixEnd_8232244 := by exact prefixLift 8232244
  have htrace : WordTrace (prefixWord ++ tailWord_8232244) baseStart_8232244 baseEnd_8232244 := by
    simpa [prefixWord, tailWord_8232244, baseEnd_8232244] using wordTrace_append hprefix tailTrace_8232244
  have hstable : (prefixWord ++ tailWord_8232244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8232244).length < 2 ^ (prefixWord ++ tailWord_8232244).sum := by decide
  have hdescent : baseEnd_8232244 < baseStart_8232244 := by decide
  rcases family_descends (prefixWord ++ tailWord_8232244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8232245 : List Nat := [1, 3, 3, 1, 2, 4, 1, 3, 1, 2, 2]
def baseStart_8232245 : Nat := 118140960795 + 8232245 * 2 ^ 59
def prefixEnd_8232245 : Nat := 4983230072969 + 3 ^ 40 * 8232245 * 2
def baseEnd_8232245 : Nat := 4227098550572249037278101

theorem tailTrace_8232245 : CollatzResearch.WordTrace tailWord_8232245 prefixEnd_8232245 4227098550572249037278101 := by
  unfold tailWord_8232245
  simp only [CollatzResearch.WordTrace]
  refine ⟨300254642060989795357274189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200169761373993196904849459 300254642060989795357274189)
  ·
    refine ⟨112595490772871173258977821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 300254642060989795357274189 112595490772871173258977821)
    ·
      refine ⟨42223309039826689972116683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112595490772871173258977821 42223309039826689972116683)
      ·
        refine ⟨63334963559740034958175025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42223309039826689972116683 63334963559740034958175025)
        ·
          refine ⟨47501222669805026218631269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63334963559740034958175025 47501222669805026218631269)
          ·
            refine ⟨8906479250588442415993363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47501222669805026218631269 8906479250588442415993363)
            ·
              refine ⟨13359718875882663623990045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8906479250588442415993363 13359718875882663623990045)
              ·
                refine ⟨5009894578455998858996267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13359718875882663623990045 5009894578455998858996267)
                ·
                  refine ⟨7514841867683998288494401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5009894578455998858996267 7514841867683998288494401)
                  ·
                    refine ⟨5636131400762998716370801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7514841867683998288494401 5636131400762998716370801)
                    ·
                      refine ⟨4227098550572249037278101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5636131400762998716370801 4227098550572249037278101)
                      ·
                        rfl

theorem cell23_8232245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 1, 3, 1, 2, 2].length) (baseStart_8232245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8232245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8232245 prefixEnd_8232245 := by exact prefixLift 8232245
  have htrace : WordTrace (prefixWord ++ tailWord_8232245) baseStart_8232245 baseEnd_8232245 := by
    simpa [prefixWord, tailWord_8232245, baseEnd_8232245] using wordTrace_append hprefix tailTrace_8232245
  have hstable : (prefixWord ++ tailWord_8232245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8232245).length < 2 ^ (prefixWord ++ tailWord_8232245).sum := by decide
  have hdescent : baseEnd_8232245 < baseStart_8232245 := by decide
  rcases family_descends (prefixWord ++ tailWord_8232245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8232288 : List Nat := [2, 1, 1, 3, 4, 3, 1, 2, 1, 3, 2]
def baseStart_8232288 : Nat := 118140960795 + 8232288 * 2 ^ 59
def prefixEnd_8232288 : Nat := 4983230072969 + 3 ^ 40 * 8232288 * 2
def baseEnd_8232288 : Nat := 4227120630240392369040403

theorem tailTrace_8232288 : CollatzResearch.WordTrace tailWord_8232288 prefixEnd_8232288 4227120630240392369040403 := by
  unfold tailWord_8232288
  simp only [CollatzResearch.WordTrace]
  refine ⟨150128105199917006850544759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200170806933222675800726345 150128105199917006850544759)
  ·
    refine ⟨225192157799875510275817139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150128105199917006850544759 225192157799875510275817139)
    ·
      refine ⟨337788236699813265413725709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225192157799875510275817139 337788236699813265413725709)
      ·
        refine ⟨126670588762429974530147141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 337788236699813265413725709 126670588762429974530147141)
        ·
          refine ⟨23750735392955620224402589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 126670588762429974530147141 23750735392955620224402589)
          ·
            refine ⟨8906525772358357584150971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23750735392955620224402589 8906525772358357584150971)
            ·
              refine ⟨13359788658537536376226457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8906525772358357584150971 13359788658537536376226457)
              ·
                refine ⟨10019841493903152282169843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13359788658537536376226457 10019841493903152282169843)
                ·
                  refine ⟨15029762240854728423254765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10019841493903152282169843 15029762240854728423254765)
                  ·
                    refine ⟨5636160840320523158720537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15029762240854728423254765 5636160840320523158720537)
                    ·
                      refine ⟨4227120630240392369040403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5636160840320523158720537 4227120630240392369040403)
                      ·
                        rfl

theorem cell23_8232288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 1, 2, 1, 3, 2].length) (baseStart_8232288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8232288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8232288 prefixEnd_8232288 := by exact prefixLift 8232288
  have htrace : WordTrace (prefixWord ++ tailWord_8232288) baseStart_8232288 baseEnd_8232288 := by
    simpa [prefixWord, tailWord_8232288, baseEnd_8232288] using wordTrace_append hprefix tailTrace_8232288
  have hstable : (prefixWord ++ tailWord_8232288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8232288).length < 2 ^ (prefixWord ++ tailWord_8232288).sum := by decide
  have hdescent : baseEnd_8232288 < baseStart_8232288 := by decide
  rcases family_descends (prefixWord ++ tailWord_8232288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8232301 : List Nat := [1, 5, 1, 1, 1, 4, 1, 2, 1, 4, 2]
def baseStart_8232301 : Nat := 118140960795 + 8232301 * 2 ^ 59
def prefixEnd_8232301 : Nat := 4983230072969 + 3 ^ 40 * 8232301 * 2
def baseEnd_8232301 : Nat := 4227127305488900818177843

theorem tailTrace_8232301 : CollatzResearch.WordTrace tailWord_8232301 prefixEnd_8232301 4227127305488900818177843 := by
  unfold tailWord_8232301
  simp only [CollatzResearch.WordTrace]
  refine ⟨300256684548786916921312757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200171123032524611280875171 300256684548786916921312757)
  ·
    refine ⟨28149064176448773461373071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 300256684548786916921312757 28149064176448773461373071)
    ·
      refine ⟨42223596264673160192059607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28149064176448773461373071 42223596264673160192059607)
      ·
        refine ⟨63335394397009740288089411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42223596264673160192059607 63335394397009740288089411)
        ·
          refine ⟨95003091595514610432134117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63335394397009740288089411 95003091595514610432134117)
          ·
            refine ⟨17813079674158989456025147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95003091595514610432134117 17813079674158989456025147)
            ·
              refine ⟨26719619511238484184037721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17813079674158989456025147 26719619511238484184037721)
              ·
                refine ⟨20039714633428863138028291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26719619511238484184037721 20039714633428863138028291)
                ·
                  refine ⟨30059571950143294707042437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20039714633428863138028291 30059571950143294707042437)
                  ·
                    refine ⟨5636169740651867757570457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30059571950143294707042437 5636169740651867757570457)
                    ·
                      refine ⟨4227127305488900818177843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5636169740651867757570457 4227127305488900818177843)
                      ·
                        rfl

theorem cell23_8232301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 2, 1, 4, 2].length) (baseStart_8232301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8232301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8232301 prefixEnd_8232301 := by exact prefixLift 8232301
  have htrace : WordTrace (prefixWord ++ tailWord_8232301) baseStart_8232301 baseEnd_8232301 := by
    simpa [prefixWord, tailWord_8232301, baseEnd_8232301] using wordTrace_append hprefix tailTrace_8232301
  have hstable : (prefixWord ++ tailWord_8232301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8232301).length < 2 ^ (prefixWord ++ tailWord_8232301).sum := by decide
  have hdescent : baseEnd_8232301 < baseStart_8232301 := by decide
  rcases family_descends (prefixWord ++ tailWord_8232301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8232354 : List Nat := [3, 3, 1, 2, 1, 3, 1, 1, 1, 7]
def baseStart_8232354 : Nat := 118140960795 + 8232354 * 2 ^ 59
def prefixEnd_8232354 : Nat := 4983230072969 + 3 ^ 40 * 8232354 * 2
def baseEnd_8232354 : Nat := 1409051506654529703605033

theorem tailTrace_8232354 : CollatzResearch.WordTrace tailWord_8232354 prefixEnd_8232354 1409051506654529703605033 := by
  unfold tailWord_8232354
  simp only [CollatzResearch.WordTrace]
  refine ⟨75064654404398726743248029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200172411745063271315328077 75064654404398726743248029)
  ·
    refine ⟨28149245401649522528718011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75064654404398726743248029 28149245401649522528718011)
    ·
      refine ⟨42223868102474283793077017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28149245401649522528718011 42223868102474283793077017)
      ·
        refine ⟨31667901076855712844807763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42223868102474283793077017 31667901076855712844807763)
        ·
          refine ⟨47501851615283569267211645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31667901076855712844807763 47501851615283569267211645)
          ·
            refine ⟨17813194355731338475204367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47501851615283569267211645 17813194355731338475204367)
            ·
              refine ⟨26719791533597007712806551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17813194355731338475204367 26719791533597007712806551)
              ·
                refine ⟨40079687300395511569209827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26719791533597007712806551 40079687300395511569209827)
                ·
                  refine ⟨60119530950593267353814741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40079687300395511569209827 60119530950593267353814741)
                  ·
                    refine ⟨1409051506654529703605033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60119530950593267353814741 1409051506654529703605033)
                    ·
                      rfl

theorem cell23_8232354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 1, 1, 7].length) (baseStart_8232354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8232354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8232354 prefixEnd_8232354 := by exact prefixLift 8232354
  have htrace : WordTrace (prefixWord ++ tailWord_8232354) baseStart_8232354 baseEnd_8232354 := by
    simpa [prefixWord, tailWord_8232354, baseEnd_8232354] using wordTrace_append hprefix tailTrace_8232354
  have hstable : (prefixWord ++ tailWord_8232354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8232354).length < 2 ^ (prefixWord ++ tailWord_8232354).sum := by decide
  have hdescent : baseEnd_8232354 < baseStart_8232354 := by decide
  rcases family_descends (prefixWord ++ tailWord_8232354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8232384 : List Nat := [2, 1, 1, 2, 3, 1, 3, 3, 3, 4]
def baseStart_8232384 : Nat := 118140960795 + 8232384 * 2 ^ 59
def prefixEnd_8232384 : Nat := 4983230072969 + 3 ^ 40 * 8232384 * 2
def baseEnd_8232384 : Nat := 1409056641461074664479987

theorem tailTrace_8232384 : CollatzResearch.WordTrace tailWord_8232384 prefixEnd_8232384 1409056641461074664479987 := by
  unfold tailWord_8232384
  simp only [CollatzResearch.WordTrace]
  refine ⟨150129855903743111048292103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200173141204990814731056137 150129855903743111048292103)
  ·
    refine ⟨225194783855614666572438155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150129855903743111048292103 225194783855614666572438155)
    ·
      refine ⟨337792175783421999858657233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225194783855614666572438155 337792175783421999858657233)
      ·
        refine ⟨253344131837566499893992925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 337792175783421999858657233 253344131837566499893992925)
        ·
          refine ⟨95004049439087437460247347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 253344131837566499893992925 95004049439087437460247347)
          ·
            refine ⟨142506074158631156190371021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95004049439087437460247347 142506074158631156190371021)
            ·
              refine ⟨53439777809486683571389133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142506074158631156190371021 53439777809486683571389133)
              ·
                refine ⟨20039916678557506339270925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53439777809486683571389133 20039916678557506339270925)
                ·
                  refine ⟨7514968754459064877226597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20039916678557506339270925 7514968754459064877226597)
                  ·
                    refine ⟨1409056641461074664479987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7514968754459064877226597 1409056641461074664479987)
                    ·
                      rfl

theorem cell23_8232384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 3, 3, 4].length) (baseStart_8232384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8232384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8232384 prefixEnd_8232384 := by exact prefixLift 8232384
  have htrace : WordTrace (prefixWord ++ tailWord_8232384) baseStart_8232384 baseEnd_8232384 := by
    simpa [prefixWord, tailWord_8232384, baseEnd_8232384] using wordTrace_append hprefix tailTrace_8232384
  have hstable : (prefixWord ++ tailWord_8232384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8232384).length < 2 ^ (prefixWord ++ tailWord_8232384).sum := by decide
  have hdescent : baseEnd_8232384 < baseStart_8232384 := by decide
  rcases family_descends (prefixWord ++ tailWord_8232384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8232386 : List Nat := [3, 5, 2, 1, 2, 1, 1, 1, 1, 4, 2]
def baseStart_8232386 : Nat := 118140960795 + 8232386 * 2 ^ 59
def prefixEnd_8232386 : Nat := 4983230072969 + 3 ^ 40 * 8232386 * 2
def baseEnd_8232386 : Nat := 4227170951344532985614953

theorem tailTrace_8232386 : CollatzResearch.WordTrace tailWord_8232386 prefixEnd_8232386 4227170951344532985614953 := by
  unfold tailWord_8232386
  simp only [CollatzResearch.WordTrace]
  refine ⟨75064946188369744109539253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200173189835652650958771341 75064946188369744109539253)
  ·
    refine ⟨7037338705159663510269305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 75064946188369744109539253 7037338705159663510269305)
    ·
      refine ⟨5278004028869747632701979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7037338705159663510269305 5278004028869747632701979)
      ·
        refine ⟨7917006043304621449052969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5278004028869747632701979 7917006043304621449052969)
        ·
          refine ⟨5937754532478466086789727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7917006043304621449052969 5937754532478466086789727)
          ·
            refine ⟨8906631798717699130184591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5937754532478466086789727 8906631798717699130184591)
            ·
              refine ⟨13359947698076548695276887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8906631798717699130184591 13359947698076548695276887)
              ·
                refine ⟨20039921547114823042915331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13359947698076548695276887 20039921547114823042915331)
                ·
                  refine ⟨30059882320672234564372997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20039921547114823042915331 30059882320672234564372997)
                  ·
                    refine ⟨5636227935126043980819937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30059882320672234564372997 5636227935126043980819937)
                    ·
                      refine ⟨4227170951344532985614953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5636227935126043980819937 4227170951344532985614953)
                      ·
                        rfl

theorem cell23_8232386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_8232386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8232386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8232386 prefixEnd_8232386 := by exact prefixLift 8232386
  have htrace : WordTrace (prefixWord ++ tailWord_8232386) baseStart_8232386 baseEnd_8232386 := by
    simpa [prefixWord, tailWord_8232386, baseEnd_8232386] using wordTrace_append hprefix tailTrace_8232386
  have hstable : (prefixWord ++ tailWord_8232386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8232386).length < 2 ^ (prefixWord ++ tailWord_8232386).sum := by decide
  have hdescent : baseEnd_8232386 < baseStart_8232386 := by decide
  rcases family_descends (prefixWord ++ tailWord_8232386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8232394 : List Nat := [3, 1, 2, 1, 2, 3, 1, 2, 1, 4, 3]
def baseStart_8232394 : Nat := 118140960795 + 8232394 * 2 ^ 59
def prefixEnd_8232394 : Nat := 4983230072969 + 3 ^ 40 * 8232394 * 2
def baseEnd_8232394 : Nat := 4227175059189768954314915

theorem tailTrace_8232394 : CollatzResearch.WordTrace tailWord_8232394 prefixEnd_8232394 4227175059189768954314915 := by
  unfold tailWord_8232394
  simp only [CollatzResearch.WordTrace]
  refine ⟨75065019134362498451112059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200173384358299995869632157 75065019134362498451112059)
  ·
    refine ⟨112597528701543747676668089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75065019134362498451112059 112597528701543747676668089)
    ·
      refine ⟨84448146526157810757501067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112597528701543747676668089 84448146526157810757501067)
      ·
        refine ⟨126672219789236716136251601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84448146526157810757501067 126672219789236716136251601)
        ·
          refine ⟨95004164841927537102188701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126672219789236716136251601 95004164841927537102188701)
          ·
            refine ⟨35626561815722826413320763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95004164841927537102188701 35626561815722826413320763)
            ·
              refine ⟨53439842723584239619981145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35626561815722826413320763 53439842723584239619981145)
              ·
                refine ⟨40079882042688179714985859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53439842723584239619981145 40079882042688179714985859)
                ·
                  refine ⟨60119823064032269572478789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40079882042688179714985859 60119823064032269572478789)
                  ·
                    refine ⟨11272466824506050544839773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60119823064032269572478789 11272466824506050544839773)
                    ·
                      refine ⟨4227175059189768954314915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11272466824506050544839773 4227175059189768954314915)
                      ·
                        rfl

theorem cell23_8232394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 2, 1, 4, 3].length) (baseStart_8232394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8232394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8232394 prefixEnd_8232394 := by exact prefixLift 8232394
  have htrace : WordTrace (prefixWord ++ tailWord_8232394) baseStart_8232394 baseEnd_8232394 := by
    simpa [prefixWord, tailWord_8232394, baseEnd_8232394] using wordTrace_append hprefix tailTrace_8232394
  have hstable : (prefixWord ++ tailWord_8232394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8232394).length < 2 ^ (prefixWord ++ tailWord_8232394).sum := by decide
  have hdescent : baseEnd_8232394 < baseStart_8232394 := by decide
  rcases family_descends (prefixWord ++ tailWord_8232394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8232498 : List Nat := [3, 2, 1, 1, 2, 1, 1, 5, 3, 2, 2]
def baseStart_8232498 : Nat := 118140960795 + 8232498 * 2 ^ 59
def prefixEnd_8232498 : Nat := 4983230072969 + 3 ^ 40 * 8232498 * 2
def baseEnd_8232498 : Nat := 4227228461177836547414437

theorem tailTrace_8232498 : CollatzResearch.WordTrace tailWord_8232498 prefixEnd_8232498 4227228461177836547414437 := by
  unfold tailWord_8232498
  simp only [CollatzResearch.WordTrace]
  refine ⟨75065967432268304891558537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200175913152715479710822765 75065967432268304891558537)
  ·
    refine ⟨56299475574201228668668903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75065967432268304891558537 56299475574201228668668903)
    ·
      refine ⟨84449213361301843003003355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56299475574201228668668903 84449213361301843003003355)
      ·
        refine ⟨126673820041952764504505033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84449213361301843003003355 126673820041952764504505033)
        ·
          refine ⟨95005365031464573378378775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126673820041952764504505033 95005365031464573378378775)
          ·
            refine ⟨142508047547196860067568163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95005365031464573378378775 142508047547196860067568163)
            ·
              refine ⟨213762071320795290101352245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142508047547196860067568163 213762071320795290101352245)
              ·
                refine ⟨20040194186324558447001773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 213762071320795290101352245 20040194186324558447001773)
                ·
                  refine ⟨7515072819871709417625665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20040194186324558447001773 7515072819871709417625665)
                  ·
                    refine ⟨5636304614903782063219249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7515072819871709417625665 5636304614903782063219249)
                    ·
                      refine ⟨4227228461177836547414437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5636304614903782063219249 4227228461177836547414437)
                      ·
                        rfl

theorem cell23_8232498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 5, 3, 2, 2].length) (baseStart_8232498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8232498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8232498 prefixEnd_8232498 := by exact prefixLift 8232498
  have htrace : WordTrace (prefixWord ++ tailWord_8232498) baseStart_8232498 baseEnd_8232498 := by
    simpa [prefixWord, tailWord_8232498, baseEnd_8232498] using wordTrace_append hprefix tailTrace_8232498
  have hstable : (prefixWord ++ tailWord_8232498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8232498).length < 2 ^ (prefixWord ++ tailWord_8232498).sum := by decide
  have hdescent : baseEnd_8232498 < baseStart_8232498 := by decide
  rcases family_descends (prefixWord ++ tailWord_8232498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8232501 : List Nat := [1, 3, 3, 1, 1, 3, 1, 2, 3, 2, 3]
def baseStart_8232501 : Nat := 118140960795 + 8232501 * 2 ^ 59
def prefixEnd_8232501 : Nat := 4983230072969 + 3 ^ 40 * 8232501 * 2
def baseEnd_8232501 : Nat := 4227230001619800035676923

theorem tailTrace_8232501 : CollatzResearch.WordTrace tailWord_8232501 prefixEnd_8232501 4227230001619800035676923 := by
  unfold tailWord_8232501
  simp only [CollatzResearch.WordTrace]
  refine ⟨300263979148062351078593357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200175986098708234052395571 300263979148062351078593357)
  ·
    refine ⟨112598992180523381654472509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 300263979148062351078593357 112598992180523381654472509)
    ·
      refine ⟨42224622067696268120427191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112598992180523381654472509 42224622067696268120427191)
      ·
        refine ⟨63336933101544402180640787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42224622067696268120427191 63336933101544402180640787)
        ·
          refine ⟨95005399652316603270961181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63336933101544402180640787 95005399652316603270961181)
          ·
            refine ⟨35627024869618726226610443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95005399652316603270961181 35627024869618726226610443)
            ·
              refine ⟨53440537304428089339915665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35627024869618726226610443 53440537304428089339915665)
              ·
                refine ⟨40080402978321067004936749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53440537304428089339915665 40080402978321067004936749)
                ·
                  refine ⟨15030151116870400126851281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40080402978321067004936749 15030151116870400126851281)
                  ·
                    refine ⟨11272613337652800095138461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15030151116870400126851281 11272613337652800095138461)
                    ·
                      refine ⟨4227230001619800035676923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11272613337652800095138461 4227230001619800035676923)
                      ·
                        rfl

theorem cell23_8232501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 2, 3, 2, 3].length) (baseStart_8232501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8232501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8232501 prefixEnd_8232501 := by exact prefixLift 8232501
  have htrace : WordTrace (prefixWord ++ tailWord_8232501) baseStart_8232501 baseEnd_8232501 := by
    simpa [prefixWord, tailWord_8232501, baseEnd_8232501] using wordTrace_append hprefix tailTrace_8232501
  have hstable : (prefixWord ++ tailWord_8232501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8232501).length < 2 ^ (prefixWord ++ tailWord_8232501).sum := by decide
  have hdescent : baseEnd_8232501 < baseStart_8232501 := by decide
  rcases family_descends (prefixWord ++ tailWord_8232501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8232504 : List Nat := [2, 1, 2, 1, 4, 2, 3, 8]
def baseStart_8232504 : Nat := 118140960795 + 8232504 * 2 ^ 59
def prefixEnd_8232504 : Nat := 4983230072969 + 3 ^ 40 * 8232504 * 2
def baseEnd_8232504 : Nat := 156564131187472723108867

theorem tailTrace_8232504 : CollatzResearch.WordTrace tailWord_8232504 prefixEnd_8232504 156564131187472723108867 := by
  unfold tailWord_8232504
  simp only [CollatzResearch.WordTrace]
  refine ⟨150132044283525741295476283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200176059044700988393968377 150132044283525741295476283)
  ·
    refine ⟨225198066425288611943214425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150132044283525741295476283 225198066425288611943214425)
    ·
      refine ⟨168898549818966458957410819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225198066425288611943214425 168898549818966458957410819)
      ·
        refine ⟨253347824728449688436116229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168898549818966458957410819 253347824728449688436116229)
        ·
          refine ⟨47502717136584316581771793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 253347824728449688436116229 47502717136584316581771793)
          ·
            refine ⟨35627037852438237436328845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47502717136584316581771793 35627037852438237436328845)
            ·
              refine ⟨13360139194664339038623317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35627037852438237436328845 13360139194664339038623317)
              ·
                refine ⟨156564131187472723108867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13360139194664339038623317 156564131187472723108867)
                ·
                  rfl

theorem cell23_8232504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 3, 8].length) (baseStart_8232504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8232504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8232504 prefixEnd_8232504 := by exact prefixLift 8232504
  have htrace : WordTrace (prefixWord ++ tailWord_8232504) baseStart_8232504 baseEnd_8232504 := by
    simpa [prefixWord, tailWord_8232504, baseEnd_8232504] using wordTrace_append hprefix tailTrace_8232504
  have hstable : (prefixWord ++ tailWord_8232504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8232504).length < 2 ^ (prefixWord ++ tailWord_8232504).sum := by decide
  have hdescent : baseEnd_8232504 < baseStart_8232504 := by decide
  rcases family_descends (prefixWord ++ tailWord_8232504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8232511 : List Nat := [1, 1, 2, 2, 3, 4, 2, 1, 1, 2, 4]
def baseStart_8232511 : Nat := 118140960795 + 8232511 * 2 ^ 59
def prefixEnd_8232511 : Nat := 4983230072969 + 3 ^ 40 * 8232511 * 2
def baseEnd_8232511 : Nat := 4227235136426344996551877

theorem tailTrace_8232511 : CollatzResearch.WordTrace tailWord_8232511 prefixEnd_8232511 4227235136426344996551877 := by
  unfold tailWord_8232511
  simp only [CollatzResearch.WordTrace]
  refine ⟨300264343878026122786457387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200176229252017415190971591 300264343878026122786457387)
  ·
    refine ⟨450396515817039184179686081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300264343878026122786457387 450396515817039184179686081)
    ·
      refine ⟨337797386862779388134764561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 450396515817039184179686081 337797386862779388134764561)
      ·
        refine ⟨253348040147084541101073421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 337797386862779388134764561 253348040147084541101073421)
        ·
          refine ⟨95005515055156702912902533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 253348040147084541101073421 95005515055156702912902533)
          ·
            refine ⟨17813534072841881796169225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95005515055156702912902533 17813534072841881796169225)
            ·
              refine ⟨13360150554631411347126919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17813534072841881796169225 13360150554631411347126919)
              ·
                refine ⟨20040225831947117020690379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13360150554631411347126919 20040225831947117020690379)
                ·
                  refine ⟨30060338747920675531035569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20040225831947117020690379 30060338747920675531035569)
                  ·
                    refine ⟨22545254060940506648276677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30060338747920675531035569 22545254060940506648276677)
                    ·
                      refine ⟨4227235136426344996551877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22545254060940506648276677 4227235136426344996551877)
                      ·
                        rfl

theorem cell23_8232511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 2, 1, 1, 2, 4].length) (baseStart_8232511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8232511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8232511 prefixEnd_8232511 := by exact prefixLift 8232511
  have htrace : WordTrace (prefixWord ++ tailWord_8232511) baseStart_8232511 baseEnd_8232511 := by
    simpa [prefixWord, tailWord_8232511, baseEnd_8232511] using wordTrace_append hprefix tailTrace_8232511
  have hstable : (prefixWord ++ tailWord_8232511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8232511).length < 2 ^ (prefixWord ++ tailWord_8232511).sum := by decide
  have hdescent : baseEnd_8232511 < baseStart_8232511 := by decide
  rcases family_descends (prefixWord ++ tailWord_8232511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8232532 : List Nat := [2, 4, 1, 1, 1, 2, 4, 3, 1, 2, 2]
def baseStart_8232532 : Nat := 118140960795 + 8232532 * 2 ^ 59
def prefixEnd_8232532 : Nat := 4983230072969 + 3 ^ 40 * 8232532 * 2
def baseEnd_8232532 : Nat := 4227245919520089414389281

theorem tailTrace_8232532 : CollatzResearch.WordTrace tailWord_8232532 prefixEnd_8232532 4227245919520089414389281 := by
  unfold tailWord_8232532
  simp only [CollatzResearch.WordTrace]
  refine ⟨150132554905475021686485925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200176739873966695581981233 150132554905475021686485925)
  ·
    refine ⟨28149854044776566566216111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150132554905475021686485925 28149854044776566566216111)
    ·
      refine ⟨42224781067164849849324167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28149854044776566566216111 42224781067164849849324167)
      ·
        refine ⟨63337171600747274773986251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42224781067164849849324167 63337171600747274773986251)
        ·
          refine ⟨95005757401120912160979377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63337171600747274773986251 95005757401120912160979377)
          ·
            refine ⟨71254318050840684120734533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95005757401120912160979377 71254318050840684120734533)
            ·
              refine ⟨13360184634532628272637725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71254318050840684120734533 13360184634532628272637725)
              ·
                refine ⟨5010069237949735602239147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13360184634532628272637725 5010069237949735602239147)
                ·
                  refine ⟨7515103856924603403358721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5010069237949735602239147 7515103856924603403358721)
                  ·
                    refine ⟨5636327892693452552519041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7515103856924603403358721 5636327892693452552519041)
                    ·
                      refine ⟨4227245919520089414389281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5636327892693452552519041 4227245919520089414389281)
                      ·
                        rfl

theorem cell23_8232532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 4, 3, 1, 2, 2].length) (baseStart_8232532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8232532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8232532 prefixEnd_8232532 := by exact prefixLift 8232532
  have htrace : WordTrace (prefixWord ++ tailWord_8232532) baseStart_8232532 baseEnd_8232532 := by
    simpa [prefixWord, tailWord_8232532, baseEnd_8232532] using wordTrace_append hprefix tailTrace_8232532
  have hstable : (prefixWord ++ tailWord_8232532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8232532).length < 2 ^ (prefixWord ++ tailWord_8232532).sum := by decide
  have hdescent : baseEnd_8232532 < baseStart_8232532 := by decide
  rcases family_descends (prefixWord ++ tailWord_8232532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8232535 : List Nat := [1, 1, 3, 2, 2, 5, 2, 1, 1, 2, 3]
def baseStart_8232535 : Nat := 118140960795 + 8232535 * 2 ^ 59
def prefixEnd_8232535 : Nat := 4983230072969 + 3 ^ 40 * 8232535 * 2
def baseEnd_8232535 : Nat := 4227247459962052902651767

theorem tailTrace_8232535 : CollatzResearch.WordTrace tailWord_8232535 prefixEnd_8232535 4227247459962052902651767 := by
  unfold tailWord_8232535
  simp only [CollatzResearch.WordTrace]
  refine ⟨300265219229939174885331059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200176812819959449923554039 300265219229939174885331059)
  ·
    refine ⟨450397828844908762327996589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300265219229939174885331059 450397828844908762327996589)
    ·
      refine ⟨168899185816840785872998721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 450397828844908762327996589 168899185816840785872998721)
      ·
        refine ⟨126674389362630589404749041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168899185816840785872998721 126674389362630589404749041)
        ·
          refine ⟨95005792021972942053561781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126674389362630589404749041 95005792021972942053561781)
          ·
            refine ⟨8906793002059963317521417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 95005792021972942053561781 8906793002059963317521417)
            ·
              refine ⟨6680094751544972488141063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8906793002059963317521417 6680094751544972488141063)
              ·
                refine ⟨10020142127317458732211595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6680094751544972488141063 10020142127317458732211595)
                ·
                  refine ⟨15030213190976188098317393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10020142127317458732211595 15030213190976188098317393)
                  ·
                    refine ⟨11272659893232141073738045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15030213190976188098317393 11272659893232141073738045)
                    ·
                      refine ⟨4227247459962052902651767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11272659893232141073738045 4227247459962052902651767)
                      ·
                        rfl

theorem cell23_8232535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 2, 1, 1, 2, 3].length) (baseStart_8232535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8232535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8232535 prefixEnd_8232535 := by exact prefixLift 8232535
  have htrace : WordTrace (prefixWord ++ tailWord_8232535) baseStart_8232535 baseEnd_8232535 := by
    simpa [prefixWord, tailWord_8232535, baseEnd_8232535] using wordTrace_append hprefix tailTrace_8232535
  have hstable : (prefixWord ++ tailWord_8232535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8232535).length < 2 ^ (prefixWord ++ tailWord_8232535).sum := by decide
  have hdescent : baseEnd_8232535 < baseStart_8232535 := by decide
  rcases family_descends (prefixWord ++ tailWord_8232535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8232548 : List Nat := [2, 3, 1, 1, 2, 4, 1, 1, 4, 1, 3]
def baseStart_8232548 : Nat := 118140960795 + 8232548 * 2 ^ 59
def prefixEnd_8232548 : Nat := 4983230072969 + 3 ^ 40 * 8232548 * 2
def baseEnd_8232548 : Nat := 4227254135210561351789207

theorem tailTrace_8232548 : CollatzResearch.WordTrace tailWord_8232548 prefixEnd_8232548 4227254135210561351789207 := by
  unfold tailWord_8232548
  simp only [CollatzResearch.WordTrace]
  refine ⟨150132846689446039052777149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200177128919261385403702865 150132846689446039052777149)
  ·
    refine ⟨56299817508542264644791431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150132846689446039052777149 56299817508542264644791431)
    ·
      refine ⟨84449726262813396967187147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56299817508542264644791431 84449726262813396967187147)
      ·
        refine ⟨126674589394220095450780721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84449726262813396967187147 126674589394220095450780721)
        ·
          refine ⟨95005942045665071588085541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126674589394220095450780721 95005942045665071588085541)
          ·
            refine ⟨17813614133562200922766039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95005942045665071588085541 17813614133562200922766039)
            ·
              refine ⟨26720421200343301384149059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17813614133562200922766039 26720421200343301384149059)
              ·
                refine ⟨40080631800514952076223589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26720421200343301384149059 40080631800514952076223589)
                ·
                  refine ⟨7515118462596553514291923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40080631800514952076223589 7515118462596553514291923)
                  ·
                    refine ⟨11272677693894830271437885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7515118462596553514291923 11272677693894830271437885)
                    ·
                      refine ⟨4227254135210561351789207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11272677693894830271437885 4227254135210561351789207)
                      ·
                        rfl

theorem cell23_8232548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 1, 4, 1, 3].length) (baseStart_8232548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8232548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8232548 prefixEnd_8232548 := by exact prefixLift 8232548
  have htrace : WordTrace (prefixWord ++ tailWord_8232548) baseStart_8232548 baseEnd_8232548 := by
    simpa [prefixWord, tailWord_8232548, baseEnd_8232548] using wordTrace_append hprefix tailTrace_8232548
  have hstable : (prefixWord ++ tailWord_8232548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8232548).length < 2 ^ (prefixWord ++ tailWord_8232548).sum := by decide
  have hdescent : baseEnd_8232548 < baseStart_8232548 := by decide
  rcases family_descends (prefixWord ++ tailWord_8232548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8232565 : List Nat := [1, 3, 4, 2, 1, 3, 1, 1, 1, 3, 3]
def baseStart_8232565 : Nat := 118140960795 + 8232565 * 2 ^ 59
def prefixEnd_8232565 : Nat := 4983230072969 + 3 ^ 40 * 8232565 * 2
def baseEnd_8232565 : Nat := 4227262864381687785276629

theorem tailTrace_8232565 : CollatzResearch.WordTrace tailWord_8232565 prefixEnd_8232565 4227262864381687785276629 := by
  unfold tailWord_8232565
  simp only [CollatzResearch.WordTrace]
  refine ⟨300266313419830490008923149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200177542279886993339282099 300266313419830490008923149)
  ·
    refine ⟨112599867532436433753346181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 300266313419830490008923149 112599867532436433753346181)
    ·
      refine ⟨21112475162331831328752409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112599867532436433753346181 21112475162331831328752409)
      ·
        refine ⟨15834356371748873496564307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21112475162331831328752409 15834356371748873496564307)
        ·
          refine ⟨23751534557623310244846461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15834356371748873496564307 23751534557623310244846461)
          ·
            refine ⟨8906825459108741341817423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23751534557623310244846461 8906825459108741341817423)
            ·
              refine ⟨13360238188663112012726135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8906825459108741341817423 13360238188663112012726135)
              ·
                refine ⟨20040357282994668019089203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13360238188663112012726135 20040357282994668019089203)
                ·
                  refine ⟨30060535924492002028633805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20040357282994668019089203 30060535924492002028633805)
                  ·
                    refine ⟨11272700971684500760737677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30060535924492002028633805 11272700971684500760737677)
                    ·
                      refine ⟨4227262864381687785276629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11272700971684500760737677 4227262864381687785276629)
                      ·
                        rfl

theorem cell23_8232565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_8232565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8232565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8232565 prefixEnd_8232565 := by exact prefixLift 8232565
  have htrace : WordTrace (prefixWord ++ tailWord_8232565) baseStart_8232565 baseEnd_8232565 := by
    simpa [prefixWord, tailWord_8232565, baseEnd_8232565] using wordTrace_append hprefix tailTrace_8232565
  have hstable : (prefixWord ++ tailWord_8232565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8232565).length < 2 ^ (prefixWord ++ tailWord_8232565).sum := by decide
  have hdescent : baseEnd_8232565 < baseStart_8232565 := by decide
  rcases family_descends (prefixWord ++ tailWord_8232565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8232588 : List Nat := [2, 2, 1, 2, 1, 1, 3, 1, 6, 2, 2]
def baseStart_8232588 : Nat := 118140960795 + 8232588 * 2 ^ 59
def prefixEnd_8232588 : Nat := 4983230072969 + 3 ^ 40 * 8232588 * 2
def baseEnd_8232588 : Nat := 4227274674436741195289023

theorem tailTrace_8232588 : CollatzResearch.WordTrace tailWord_8232588 prefixEnd_8232588 4227274674436741195289023 := by
  unfold tailWord_8232588
  simp only [CollatzResearch.WordTrace]
  refine ⟨150133576149373582468505209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200178101532498109958006945 150133576149373582468505209)
  ·
    refine ⟨112600182112030186851378907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150133576149373582468505209 112600182112030186851378907)
    ·
      refine ⟨168900273168045280277068361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112600182112030186851378907 168900273168045280277068361)
      ·
        refine ⟨126675204876033960207801271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168900273168045280277068361 126675204876033960207801271)
        ·
          refine ⟨190012807314050940311701907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126675204876033960207801271 190012807314050940311701907)
          ·
            refine ⟨285019210971076410467552861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190012807314050940311701907 285019210971076410467552861)
            ·
              refine ⟨106882204114153653925332323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 285019210971076410467552861 106882204114153653925332323)
              ·
                refine ⟨160323306171230480887998485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106882204114153653925332323 160323306171230480887998485)
                ·
                  refine ⟨7515154976776428791624929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 160323306171230480887998485 7515154976776428791624929)
                  ·
                    refine ⟨5636366232582321593718697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7515154976776428791624929 5636366232582321593718697)
                    ·
                      refine ⟨4227274674436741195289023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5636366232582321593718697 4227274674436741195289023)
                      ·
                        rfl

theorem cell23_8232588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 6, 2, 2].length) (baseStart_8232588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8232588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8232588 prefixEnd_8232588 := by exact prefixLift 8232588
  have htrace : WordTrace (prefixWord ++ tailWord_8232588) baseStart_8232588 baseEnd_8232588 := by
    simpa [prefixWord, tailWord_8232588, baseEnd_8232588] using wordTrace_append hprefix tailTrace_8232588
  have hstable : (prefixWord ++ tailWord_8232588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8232588).length < 2 ^ (prefixWord ++ tailWord_8232588).sum := by decide
  have hdescent : baseEnd_8232588 < baseStart_8232588 := by decide
  rcases family_descends (prefixWord ++ tailWord_8232588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8232605 : List Nat := [1, 4, 2, 1, 1, 1, 1, 6, 2, 2, 2]
def baseStart_8232605 : Nat := 118140960795 + 8232605 * 2 ^ 59
def prefixEnd_8232605 : Nat := 4983230072969 + 3 ^ 40 * 8232605 * 2
def baseEnd_8232605 : Nat := 4227283403607867628776445

theorem tailTrace_8232605 : CollatzResearch.WordTrace tailWord_8232605 prefixEnd_8232605 4227283403607867628776445 := by
  unfold tailWord_8232605
  simp only [CollatzResearch.WordTrace]
  refine ⟨300267772339685576840379269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200178514893123717893586179 300267772339685576840379269)
  ·
    refine ⟨56300207313691045657571113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 300267772339685576840379269 56300207313691045657571113)
    ·
      refine ⟨42225155485268284243178335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56300207313691045657571113 42225155485268284243178335)
      ·
        refine ⟨63337733227902426364767503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42225155485268284243178335 63337733227902426364767503)
        ·
          refine ⟨95006599841853639547151255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63337733227902426364767503 95006599841853639547151255)
          ·
            refine ⟨142509899762780459320726883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95006599841853639547151255 142509899762780459320726883)
            ·
              refine ⟨213764849644170688981090325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142509899762780459320726883 213764849644170688981090325)
              ·
                refine ⟨10020227327070501045988609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 213764849644170688981090325 10020227327070501045988609)
                ·
                  refine ⟨7515170495302875784491457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10020227327070501045988609 7515170495302875784491457)
                  ·
                    refine ⟨5636377871477156838368593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7515170495302875784491457 5636377871477156838368593)
                    ·
                      refine ⟨4227283403607867628776445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5636377871477156838368593 4227283403607867628776445)
                      ·
                        rfl

theorem cell23_8232605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 6, 2, 2, 2].length) (baseStart_8232605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8232605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8232605 prefixEnd_8232605 := by exact prefixLift 8232605
  have htrace : WordTrace (prefixWord ++ tailWord_8232605) baseStart_8232605 baseEnd_8232605 := by
    simpa [prefixWord, tailWord_8232605, baseEnd_8232605] using wordTrace_append hprefix tailTrace_8232605
  have hstable : (prefixWord ++ tailWord_8232605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8232605).length < 2 ^ (prefixWord ++ tailWord_8232605).sum := by decide
  have hdescent : baseEnd_8232605 < baseStart_8232605 := by decide
  rcases family_descends (prefixWord ++ tailWord_8232605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8232624 : List Nat := [2, 1, 1, 1, 2, 1, 4, 1, 3, 7]
def baseStart_8232624 : Nat := 118140960795 + 8232624 * 2 ^ 59
def prefixEnd_8232624 : Nat := 4983230072969 + 3 ^ 40 * 8232624 * 2
def baseEnd_8232624 : Nat := 1409097719913434351479619

theorem tailTrace_8232624 : CollatzResearch.WordTrace tailWord_8232624 prefixEnd_8232624 1409097719913434351479619 := by
  unfold tailWord_8232624
  simp only [CollatzResearch.WordTrace]
  refine ⟨150134232663308371542660463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200178976884411162056880617 150134232663308371542660463)
  ·
    refine ⟨225201348994962557313990695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150134232663308371542660463 225201348994962557313990695)
    ·
      refine ⟨337802023492443835970986043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225201348994962557313990695 337802023492443835970986043)
      ·
        refine ⟨506703035238665753956479065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337802023492443835970986043 506703035238665753956479065)
        ·
          refine ⟨380027276428999315467359299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 506703035238665753956479065 380027276428999315467359299)
          ·
            refine ⟨570040914643498973201038949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 380027276428999315467359299 570040914643498973201038949)
            ·
              refine ⟨106882671495656057475194803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 570040914643498973201038949 106882671495656057475194803)
              ·
                refine ⟨160324007243484086212792205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106882671495656057475194803 160324007243484086212792205)
                ·
                  refine ⟨60121502716306532329797077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 160324007243484086212792205 60121502716306532329797077)
                  ·
                    refine ⟨1409097719913434351479619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60121502716306532329797077 1409097719913434351479619)
                    ·
                      rfl

theorem cell23_8232624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 3, 7].length) (baseStart_8232624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8232624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8232624 prefixEnd_8232624 := by exact prefixLift 8232624
  have htrace : WordTrace (prefixWord ++ tailWord_8232624) baseStart_8232624 baseEnd_8232624 := by
    simpa [prefixWord, tailWord_8232624, baseEnd_8232624] using wordTrace_append hprefix tailTrace_8232624
  have hstable : (prefixWord ++ tailWord_8232624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8232624).length < 2 ^ (prefixWord ++ tailWord_8232624).sum := by decide
  have hdescent : baseEnd_8232624 < baseStart_8232624 := by decide
  rcases family_descends (prefixWord ++ tailWord_8232624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8232658 : List Nat := [3, 2, 2, 2, 2, 1, 2, 2, 2, 5]
def baseStart_8232658 : Nat := 118140960795 + 8232658 * 2 ^ 59
def prefixEnd_8232658 : Nat := 4983230072969 + 3 ^ 40 * 8232658 * 2
def baseEnd_8232658 : Nat := 1409103539360851973804567

theorem tailTrace_8232658 : CollatzResearch.WordTrace tailWord_8232658 prefixEnd_8232658 1409103539360851973804567 := by
  unfold tailWord_8232658
  simp only [CollatzResearch.WordTrace]
  refine ⟨75067426352123391723014657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200179803605662377928039085 75067426352123391723014657)
  ·
    refine ⟨56300569764092543792260993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75067426352123391723014657 56300569764092543792260993)
    ·
      refine ⟨42225427323069407844195745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56300569764092543792260993 42225427323069407844195745)
      ·
        refine ⟨31669070492302055883146809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42225427323069407844195745 31669070492302055883146809)
        ·
          refine ⟨23751802869226541912360107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31669070492302055883146809 23751802869226541912360107)
          ·
            refine ⟨35627704303839812868540161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23751802869226541912360107 35627704303839812868540161)
            ·
              refine ⟨26720778227879859651405121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35627704303839812868540161 26720778227879859651405121)
              ·
                refine ⟨20040583670909894738553841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26720778227879859651405121 20040583670909894738553841)
                ·
                  refine ⟨15030437753182421053915381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20040583670909894738553841 15030437753182421053915381)
                  ·
                    refine ⟨1409103539360851973804567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15030437753182421053915381 1409103539360851973804567)
                    ·
                      rfl

theorem cell23_8232658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 2, 2, 5].length) (baseStart_8232658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8232658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8232658 prefixEnd_8232658 := by exact prefixLift 8232658
  have htrace : WordTrace (prefixWord ++ tailWord_8232658) baseStart_8232658 baseEnd_8232658 := by
    simpa [prefixWord, tailWord_8232658, baseEnd_8232658] using wordTrace_append hprefix tailTrace_8232658
  have hstable : (prefixWord ++ tailWord_8232658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8232658).length < 2 ^ (prefixWord ++ tailWord_8232658).sum := by decide
  have hdescent : baseEnd_8232658 < baseStart_8232658 := by decide
  rcases family_descends (prefixWord ++ tailWord_8232658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8232681 : List Nat := [1, 2, 1, 1, 1, 2, 3, 4, 1, 4, 3]
def baseStart_8232681 : Nat := 118140960795 + 8232681 * 2 ^ 59
def prefixEnd_8232681 : Nat := 4983230072969 + 3 ^ 40 * 8232681 * 2
def baseEnd_8232681 : Nat := 4227322428137609331426095

theorem tailTrace_8232681 : CollatzResearch.WordTrace tailWord_8232681 prefixEnd_8232681 4227322428137609331426095 := by
  unfold tailWord_8232681
  simp only [CollatzResearch.WordTrace]
  refine ⟨300270544287410241820145897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200180362858273494546763931 300270544287410241820145897)
  ·
    refine ⟨225202908215557681365109423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300270544287410241820145897 225202908215557681365109423)
    ·
      refine ⟨337804362323336522047664135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225202908215557681365109423 337804362323336522047664135)
      ·
        refine ⟨506706543485004783071496203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337804362323336522047664135 506706543485004783071496203)
        ·
          refine ⟨760059815227507174607244305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 506706543485004783071496203 760059815227507174607244305)
          ·
            refine ⟨570044861420630380955433229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 760059815227507174607244305 570044861420630380955433229)
            ·
              refine ⟨213766823032736392858287461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 570044861420630380955433229 213766823032736392858287461)
              ·
                refine ⟨40081279318638073660928899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 213766823032736392858287461 40081279318638073660928899)
                ·
                  refine ⟨60121918977957110491393349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40081279318638073660928899 60121918977957110491393349)
                  ·
                    refine ⟨11272859808366958217136253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60121918977957110491393349 11272859808366958217136253)
                    ·
                      refine ⟨4227322428137609331426095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11272859808366958217136253 4227322428137609331426095)
                      ·
                        rfl

theorem cell23_8232681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 4, 1, 4, 3].length) (baseStart_8232681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8232681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8232681 prefixEnd_8232681 := by exact prefixLift 8232681
  have htrace : WordTrace (prefixWord ++ tailWord_8232681) baseStart_8232681 baseEnd_8232681 := by
    simpa [prefixWord, tailWord_8232681, baseEnd_8232681] using wordTrace_append hprefix tailTrace_8232681
  have hstable : (prefixWord ++ tailWord_8232681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8232681).length < 2 ^ (prefixWord ++ tailWord_8232681).sum := by decide
  have hdescent : baseEnd_8232681 < baseStart_8232681 := by decide
  rcases family_descends (prefixWord ++ tailWord_8232681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8232692 : List Nat := [2, 6, 1, 1, 1, 1, 3, 1, 2, 5]
def baseStart_8232692 : Nat := 118140960795 + 8232692 * 2 ^ 59
def prefixEnd_8232692 : Nat := 4983230072969 + 3 ^ 40 * 8232692 * 2
def baseEnd_8232692 : Nat := 1409109358808269596129515

theorem tailTrace_8232692 : CollatzResearch.WordTrace tailWord_8232692 prefixEnd_8232692 1409109358808269596129515 := by
  unfold tailWord_8232692
  simp only [CollatzResearch.WordTrace]
  refine ⟨150135472745185195349398165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200180630326913593799197553 150135472745185195349398165)
  ·
    refine ⟨7037600284930556032003039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 150135472745185195349398165 7037600284930556032003039)
    ·
      refine ⟨10556400427395834048004559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7037600284930556032003039 10556400427395834048004559)
      ·
        refine ⟨15834600641093751072006839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10556400427395834048004559 15834600641093751072006839)
        ·
          refine ⟨23751900961640626608010259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15834600641093751072006839 23751900961640626608010259)
          ·
            refine ⟨35627851442460939912015389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23751900961640626608010259 35627851442460939912015389)
            ·
              refine ⟨13360444290922852467005771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35627851442460939912015389 13360444290922852467005771)
              ·
                refine ⟨20040666436384278700508657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13360444290922852467005771 20040666436384278700508657)
                ·
                  refine ⟨15030499827288209025381493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20040666436384278700508657 15030499827288209025381493)
                  ·
                    refine ⟨1409109358808269596129515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15030499827288209025381493 1409109358808269596129515)
                    ·
                      rfl

theorem cell23_8232692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_8232692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8232692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8232692 prefixEnd_8232692 := by exact prefixLift 8232692
  have htrace : WordTrace (prefixWord ++ tailWord_8232692) baseStart_8232692 baseEnd_8232692 := by
    simpa [prefixWord, tailWord_8232692, baseEnd_8232692] using wordTrace_append hprefix tailTrace_8232692
  have hstable : (prefixWord ++ tailWord_8232692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8232692).length < 2 ^ (prefixWord ++ tailWord_8232692).sum := by decide
  have hdescent : baseEnd_8232692 < baseStart_8232692 := by decide
  rcases family_descends (prefixWord ++ tailWord_8232692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8232705 : List Nat := [1, 2, 4, 1, 1, 1, 3, 5, 1, 4]
def baseStart_8232705 : Nat := 118140960795 + 8232705 * 2 ^ 59
def prefixEnd_8232705 : Nat := 4983230072969 + 3 ^ 40 * 8232705 * 2
def baseEnd_8232705 : Nat := 1409111583891105745841995

theorem tailTrace_8232705 : CollatzResearch.WordTrace tailWord_8232705 prefixEnd_8232705 1409111583891105745841995 := by
  unfold tailWord_8232705
  simp only [CollatzResearch.WordTrace]
  refine ⟨300271419639323293919019569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200180946426215529279346379 300271419639323293919019569)
  ·
    refine ⟨225203564729492470439264677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300271419639323293919019569 225203564729492470439264677)
    ·
      refine ⟨42225668386779838207362127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 225203564729492470439264677 42225668386779838207362127)
      ·
        refine ⟨63338502580169757311043191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42225668386779838207362127 63338502580169757311043191)
        ·
          refine ⟨95007753870254635966564787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63338502580169757311043191 95007753870254635966564787)
          ·
            refine ⟨142511630805381953949847181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95007753870254635966564787 142511630805381953949847181)
            ·
              refine ⟨53441861552018232731192693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142511630805381953949847181 53441861552018232731192693)
              ·
                refine ⟨5010174520501709318549315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53441861552018232731192693 5010174520501709318549315)
                ·
                  refine ⟨7515261780752563977823973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5010174520501709318549315 7515261780752563977823973)
                  ·
                    refine ⟨1409111583891105745841995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7515261780752563977823973 1409111583891105745841995)
                    ·
                      rfl

theorem cell23_8232705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 5, 1, 4].length) (baseStart_8232705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8232705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8232705 prefixEnd_8232705 := by exact prefixLift 8232705
  have htrace : WordTrace (prefixWord ++ tailWord_8232705) baseStart_8232705 baseEnd_8232705 := by
    simpa [prefixWord, tailWord_8232705, baseEnd_8232705] using wordTrace_append hprefix tailTrace_8232705
  have hstable : (prefixWord ++ tailWord_8232705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8232705).length < 2 ^ (prefixWord ++ tailWord_8232705).sum := by decide
  have hdescent : baseEnd_8232705 < baseStart_8232705 := by decide
  rcases family_descends (prefixWord ++ tailWord_8232705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8232718 : List Nat := [4, 1, 1, 2, 1, 1, 5, 2, 6]
def baseStart_8232718 : Nat := 118140960795 + 8232718 * 2 ^ 59
def prefixEnd_8232718 : Nat := 4983230072969 + 3 ^ 40 * 8232718 * 2
def baseEnd_8232718 : Nat := 469704602991313965184825

theorem tailTrace_8232718 : CollatzResearch.WordTrace tailWord_8232718 prefixEnd_8232718 469704602991313965184825 := by
  unfold tailWord_8232718
  simp only [CollatzResearch.WordTrace]
  refine ⟨37533986723534524642405351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200181262525517464759495205 37533986723534524642405351)
  ·
    refine ⟨56300980085301786963608027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37533986723534524642405351 56300980085301786963608027)
    ·
      refine ⟨84451470127952680445412041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56300980085301786963608027 84451470127952680445412041)
      ·
        refine ⟨63338602595964510334059031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84451470127952680445412041 63338602595964510334059031)
        ·
          refine ⟨95007903893946765501088547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63338602595964510334059031 95007903893946765501088547)
          ·
            refine ⟨142511855840920148251632821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95007903893946765501088547 142511855840920148251632821)
            ·
              refine ⟨13360486485086263898590577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 142511855840920148251632821 13360486485086263898590577)
              ·
                refine ⟨10020364863814697923942933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13360486485086263898590577 10020364863814697923942933)
                ·
                  refine ⟨469704602991313965184825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10020364863814697923942933 469704602991313965184825)
                  ·
                    rfl

theorem cell23_8232718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 5, 2, 6].length) (baseStart_8232718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8232718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8232718 prefixEnd_8232718 := by exact prefixLift 8232718
  have htrace : WordTrace (prefixWord ++ tailWord_8232718) baseStart_8232718 baseEnd_8232718 := by
    simpa [prefixWord, tailWord_8232718, baseEnd_8232718] using wordTrace_append hprefix tailTrace_8232718
  have hstable : (prefixWord ++ tailWord_8232718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8232718).length < 2 ^ (prefixWord ++ tailWord_8232718).sum := by decide
  have hdescent : baseEnd_8232718 < baseStart_8232718 := by decide
  rcases family_descends (prefixWord ++ tailWord_8232718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8232722 : List Nat := [3, 2, 4, 1, 1, 2, 2, 1, 3, 4]
def baseStart_8232722 : Nat := 118140960795 + 8232722 * 2 ^ 59
def prefixEnd_8232722 : Nat := 4983230072969 + 3 ^ 40 * 8232722 * 2
def baseEnd_8232722 : Nat := 1409114493614814557004469

theorem tailTrace_8232722 : CollatzResearch.WordTrace tailWord_8232722 prefixEnd_8232722 1409114493614814557004469 := by
  unfold tailWord_8232722
  simp only [CollatzResearch.WordTrace]
  refine ⟨75068009920065426455597105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200181359786841137214925613 75068009920065426455597105)
  ·
    refine ⟨56301007440049069841697829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75068009920065426455597105 56301007440049069841697829)
    ·
      refine ⟨10556438895009200595318343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56301007440049069841697829 10556438895009200595318343)
      ·
        refine ⟨15834658342513800892977515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10556438895009200595318343 15834658342513800892977515)
        ·
          refine ⟨23751987513770701339466273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15834658342513800892977515 23751987513770701339466273)
          ·
            refine ⟨17813990635328026004599705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23751987513770701339466273 17813990635328026004599705)
            ·
              refine ⟨13360492976496019503449779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17813990635328026004599705 13360492976496019503449779)
              ·
                refine ⟨20040739464744029255174669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13360492976496019503449779 20040739464744029255174669)
                ·
                  refine ⟨7515277299279010970690501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20040739464744029255174669 7515277299279010970690501)
                  ·
                    refine ⟨1409114493614814557004469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7515277299279010970690501 1409114493614814557004469)
                    ·
                      rfl

theorem cell23_8232722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_8232722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8232722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8232722 prefixEnd_8232722 := by exact prefixLift 8232722
  have htrace : WordTrace (prefixWord ++ tailWord_8232722) baseStart_8232722 baseEnd_8232722 := by
    simpa [prefixWord, tailWord_8232722, baseEnd_8232722] using wordTrace_append hprefix tailTrace_8232722
  have hstable : (prefixWord ++ tailWord_8232722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8232722).length < 2 ^ (prefixWord ++ tailWord_8232722).sum := by decide
  have hdescent : baseEnd_8232722 < baseStart_8232722 := by decide
  rcases family_descends (prefixWord ++ tailWord_8232722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8232748 : List Nat := [2, 2, 1, 1, 1, 5, 1, 4, 1, 5]
def baseStart_8232748 : Nat := 118140960795 + 8232748 * 2 ^ 59
def prefixEnd_8232748 : Nat := 4983230072969 + 3 ^ 40 * 8232748 * 2
def baseEnd_8232748 : Nat := 1409118943780486856429429

theorem tailTrace_8232748 : CollatzResearch.WordTrace tailWord_8232748 prefixEnd_8232748 1409118943780486856429429 := by
  unfold tailWord_8232748
  simp only [CollatzResearch.WordTrace]
  refine ⟨150136493989083756131417449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 200181991985445008175223265 150136493989083756131417449)
  ·
    refine ⟨112602370491812817098563087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150136493989083756131417449 112602370491812817098563087)
    ·
      refine ⟨168903555737719225647844631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112602370491812817098563087 168903555737719225647844631)
      ·
        refine ⟨253355333606578838471766947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168903555737719225647844631 253355333606578838471766947)
        ·
          refine ⟨380033000409868257707650421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253355333606578838471766947 380033000409868257707650421)
          ·
            refine ⟨35628093788425149160092227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 380033000409868257707650421 35628093788425149160092227)
            ·
              refine ⟨53442140682637723740138341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35628093788425149160092227 53442140682637723740138341)
              ·
                refine ⟨10020401377994573201275939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53442140682637723740138341 10020401377994573201275939)
                ·
                  refine ⟨15030602066991859801913909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10020401377994573201275939 15030602066991859801913909)
                  ·
                    refine ⟨1409118943780486856429429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15030602066991859801913909 1409118943780486856429429)
                    ·
                      rfl

theorem cell23_8232748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 5].length) (baseStart_8232748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8232748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8232748 prefixEnd_8232748 := by exact prefixLift 8232748
  have htrace : WordTrace (prefixWord ++ tailWord_8232748) baseStart_8232748 baseEnd_8232748 := by
    simpa [prefixWord, tailWord_8232748, baseEnd_8232748] using wordTrace_append hprefix tailTrace_8232748
  have hstable : (prefixWord ++ tailWord_8232748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8232748).length < 2 ^ (prefixWord ++ tailWord_8232748).sum := by decide
  have hdescent : baseEnd_8232748 < baseStart_8232748 := by decide
  rcases family_descends (prefixWord ++ tailWord_8232748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8232765 : List Nat := [1, 4, 1, 4, 1, 1, 2, 3, 1, 5]
def baseStart_8232765 : Nat := 118140960795 + 8232765 * 2 ^ 59
def prefixEnd_8232765 : Nat := 4983230072969 + 3 ^ 40 * 8232765 * 2
def baseEnd_8232765 : Nat := 1409121853504195667591903

theorem tailTrace_8232765 : CollatzResearch.WordTrace tailWord_8232765 prefixEnd_8232765 1409121853504195667591903 := by
  unfold tailWord_8232765
  simp only [CollatzResearch.WordTrace]
  refine ⟨300273608019105924166203749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200182405346070616110802499 300273608019105924166203749)
  ·
    refine ⟨56301301503582360781163203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 300273608019105924166203749 56301301503582360781163203)
    ·
      refine ⟨84451952255373541171744805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56301301503582360781163203 84451952255373541171744805)
      ·
        refine ⟨15834741047882538969702151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84451952255373541171744805 15834741047882538969702151)
        ·
          refine ⟨23752111571823808454553227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15834741047882538969702151 23752111571823808454553227)
          ·
            refine ⟨35628167357735712681829841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23752111571823808454553227 35628167357735712681829841)
            ·
              refine ⟨26721125518301784511372381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35628167357735712681829841 26721125518301784511372381)
              ·
                refine ⟨10020422069363169191764643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26721125518301784511372381 10020422069363169191764643)
                ·
                  refine ⟨15030633104044753787646965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10020422069363169191764643 15030633104044753787646965)
                  ·
                    refine ⟨1409121853504195667591903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15030633104044753787646965 1409121853504195667591903)
                    ·
                      rfl

theorem cell23_8232765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 3, 1, 5].length) (baseStart_8232765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8232765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8232765 prefixEnd_8232765 := by exact prefixLift 8232765
  have htrace : WordTrace (prefixWord ++ tailWord_8232765) baseStart_8232765 baseEnd_8232765 := by
    simpa [prefixWord, tailWord_8232765, baseEnd_8232765] using wordTrace_append hprefix tailTrace_8232765
  have hstable : (prefixWord ++ tailWord_8232765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8232765).length < 2 ^ (prefixWord ++ tailWord_8232765).sum := by decide
  have hdescent : baseEnd_8232765 < baseStart_8232765 := by decide
  rcases family_descends (prefixWord ++ tailWord_8232765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8232778 : List Nat := [3, 1, 2, 1, 1, 1, 3, 3, 4, 4]
def baseStart_8232778 : Nat := 118140960795 + 8232778 * 2 ^ 59
def prefixEnd_8232778 : Nat := 4983230072969 + 3 ^ 40 * 8232778 * 2
def baseEnd_8232778 : Nat := 1409124078587031817304383

theorem tailTrace_8232778 : CollatzResearch.WordTrace tailWord_8232778 prefixEnd_8232778 1409124078587031817304383 := by
  unfold tailWord_8232778
  simp only [CollatzResearch.WordTrace]
  refine ⟨75068520542014706846606747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200182721445372551590951325 75068520542014706846606747)
  ·
    refine ⟨112602780813022060269910121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75068520542014706846606747 112602780813022060269910121)
    ·
      refine ⟨84452085609766545202432591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112602780813022060269910121 84452085609766545202432591)
      ·
        refine ⟨126678128414649817803648887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84452085609766545202432591 126678128414649817803648887)
        ·
          refine ⟨190017192621974726705473331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126678128414649817803648887 190017192621974726705473331)
          ·
            refine ⟨285025788932962090058209997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190017192621974726705473331 285025788932962090058209997)
            ·
              refine ⟨106884670849860783771828749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 285025788932962090058209997 106884670849860783771828749)
              ·
                refine ⟨40081751568697793914435781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106884670849860783771828749 40081751568697793914435781)
                ·
                  refine ⟨7515328419130836358956709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40081751568697793914435781 7515328419130836358956709)
                  ·
                    refine ⟨1409124078587031817304383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7515328419130836358956709 1409124078587031817304383)
                    ·
                      rfl

theorem cell23_8232778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 3, 4, 4].length) (baseStart_8232778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8232778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8232778 prefixEnd_8232778 := by exact prefixLift 8232778
  have htrace : WordTrace (prefixWord ++ tailWord_8232778) baseStart_8232778 baseEnd_8232778 := by
    simpa [prefixWord, tailWord_8232778, baseEnd_8232778] using wordTrace_append hprefix tailTrace_8232778
  have hstable : (prefixWord ++ tailWord_8232778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8232778).length < 2 ^ (prefixWord ++ tailWord_8232778).sum := by decide
  have hdescent : baseEnd_8232778 < baseStart_8232778 := by decide
  rcases family_descends (prefixWord ++ tailWord_8232778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8232802 : List Nat := [3, 3, 2, 1, 2, 1, 3, 2, 1, 1, 4]
def baseStart_8232802 : Nat := 118140960795 + 8232802 * 2 ^ 59
def prefixEnd_8232802 : Nat := 4983230072969 + 3 ^ 40 * 8232802 * 2
def baseEnd_8232802 : Nat := 4227384559296803358013039

theorem tailTrace_8232802 : CollatzResearch.WordTrace tailWord_8232802 prefixEnd_8232802 4227384559296803358013039 := by
  unfold tailWord_8232802
  simp only [CollatzResearch.WordTrace]
  refine ⟨75068739379992969871325165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 200183305013314586323533773 75068739379992969871325165)
  ·
    refine ⟨28150777267497363701746937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75068739379992969871325165 28150777267497363701746937)
    ·
      refine ⟨21113082950623022776310203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28150777267497363701746937 21113082950623022776310203)
      ·
        refine ⟨31669624425934534164465305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21113082950623022776310203 31669624425934534164465305)
        ·
          refine ⟨23752218319450900623348979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31669624425934534164465305 23752218319450900623348979)
          ·
            refine ⟨35628327479176350935023469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23752218319450900623348979 35628327479176350935023469)
            ·
              refine ⟨13360622804691131600633801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35628327479176350935023469 13360622804691131600633801)
              ·
                refine ⟨10020467103518348700475351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13360622804691131600633801 10020467103518348700475351)
                ·
                  refine ⟨15030700655277523050713027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10020467103518348700475351 15030700655277523050713027)
                  ·
                    refine ⟨22546050982916284576069541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15030700655277523050713027 22546050982916284576069541)
                    ·
                      refine ⟨4227384559296803358013039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22546050982916284576069541 4227384559296803358013039)
                      ·
                        rfl

theorem cell23_8232802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 3, 2, 1, 1, 4].length) (baseStart_8232802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8232802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8232802 prefixEnd_8232802 := by exact prefixLift 8232802
  have htrace : WordTrace (prefixWord ++ tailWord_8232802) baseStart_8232802 baseEnd_8232802 := by
    simpa [prefixWord, tailWord_8232802, baseEnd_8232802] using wordTrace_append hprefix tailTrace_8232802
  have hstable : (prefixWord ++ tailWord_8232802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8232802).length < 2 ^ (prefixWord ++ tailWord_8232802).sum := by decide
  have hdescent : baseEnd_8232802 < baseStart_8232802 := by decide
  rcases family_descends (prefixWord ++ tailWord_8232802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
