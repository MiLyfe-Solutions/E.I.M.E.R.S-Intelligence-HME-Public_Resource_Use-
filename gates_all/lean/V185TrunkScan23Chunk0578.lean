import V185TrunkScan23Chunk0577

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3418309 : List Nat := [1, 3, 1, 1, 1, 1, 7, 1, 1, 3, 3]
def baseStart_3418309 : Nat := 118140960795 + 3418309 * 2 ^ 59
def prefixEnd_3418309 : Nat := 4983230072969 + 3 ^ 40 * 3418309 * 2
def baseEnd_3418309 : Nat := 1755235542589971584016989

theorem tailTrace_3418309 : CollatzResearch.WordTrace tailWord_3418309 prefixEnd_3418309 1755235542589971584016989 := by
  unfold tailWord_3418309
  simp only [CollatzResearch.WordTrace]
  refine ⟨124675971773057768543561981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83117314515371845695707987 124675971773057768543561981)
  ·
    refine ⟨46753489414896663203835743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124675971773057768543561981 46753489414896663203835743)
    ·
      refine ⟨70130234122344994805753615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46753489414896663203835743 70130234122344994805753615)
      ·
        refine ⟨105195351183517492208630423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70130234122344994805753615 105195351183517492208630423)
        ·
          refine ⟨157793026775276238312945635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105195351183517492208630423 157793026775276238312945635)
          ·
            refine ⟨236689540162914357469418453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157793026775276238312945635 236689540162914357469418453)
            ·
              refine ⟨5547411097568305253189495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 236689540162914357469418453 5547411097568305253189495)
              ·
                refine ⟨8321116646352457879784243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5547411097568305253189495 8321116646352457879784243)
                ·
                  refine ⟨12481674969528686819676365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8321116646352457879784243 12481674969528686819676365)
                  ·
                    refine ⟨4680628113573257557378637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12481674969528686819676365 4680628113573257557378637)
                    ·
                      refine ⟨1755235542589971584016989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4680628113573257557378637 1755235542589971584016989)
                      ·
                        rfl

theorem cell23_3418309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 7, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 7, 1, 1, 3, 3].length) (baseStart_3418309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3418309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3418309 prefixEnd_3418309 := by exact prefixLift 3418309
  have htrace : WordTrace (prefixWord ++ tailWord_3418309) baseStart_3418309 baseEnd_3418309 := by
    simpa [prefixWord, tailWord_3418309, baseEnd_3418309] using wordTrace_append hprefix tailTrace_3418309
  have hstable : (prefixWord ++ tailWord_3418309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3418309).length < 2 ^ (prefixWord ++ tailWord_3418309).sum := by decide
  have hdescent : baseEnd_3418309 < baseStart_3418309 := by decide
  rcases family_descends (prefixWord ++ tailWord_3418309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3418336 : List Nat := [2, 1, 1, 3, 1, 3, 1, 5, 1, 3, 2]
def baseStart_3418336 : Nat := 118140960795 + 3418336 * 2 ^ 59
def prefixEnd_3418336 : Nat := 4983230072969 + 3 ^ 40 * 3418336 * 2
def baseEnd_3418336 : Nat := 1755249406567642978379365

theorem tailTrace_3418336 : CollatzResearch.WordTrace tailWord_3418336 prefixEnd_3418336 1755249406567642978379365 := by
  unfold tailWord_3418336
  simp only [CollatzResearch.WordTrace]
  refine ⟨62338478271979976077397431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83117971029306634769863241 62338478271979976077397431)
  ·
    refine ⟨93507717407969964116096147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62338478271979976077397431 93507717407969964116096147)
    ·
      refine ⟨140261576111954946174144221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93507717407969964116096147 140261576111954946174144221)
      ·
        refine ⟨52598091041983104815304083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140261576111954946174144221 52598091041983104815304083)
        ·
          refine ⟨78897136562974657222956125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52598091041983104815304083 78897136562974657222956125)
          ·
            refine ⟨29586426211115496458608547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78897136562974657222956125 29586426211115496458608547)
            ·
              refine ⟨44379639316673244687912821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29586426211115496458608547 44379639316673244687912821)
              ·
                refine ⟨4160591185938116689491827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44379639316673244687912821 4160591185938116689491827)
                ·
                  refine ⟨6240886778907175034237741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4160591185938116689491827 6240886778907175034237741)
                  ·
                    refine ⟨2340332542090190637839153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6240886778907175034237741 2340332542090190637839153)
                    ·
                      refine ⟨1755249406567642978379365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2340332542090190637839153 1755249406567642978379365)
                      ·
                        rfl

theorem cell23_3418336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 5, 1, 3, 2].length) (baseStart_3418336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3418336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3418336 prefixEnd_3418336 := by exact prefixLift 3418336
  have htrace : WordTrace (prefixWord ++ tailWord_3418336) baseStart_3418336 baseEnd_3418336 := by
    simpa [prefixWord, tailWord_3418336, baseEnd_3418336] using wordTrace_append hprefix tailTrace_3418336
  have hstable : (prefixWord ++ tailWord_3418336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3418336).length < 2 ^ (prefixWord ++ tailWord_3418336).sum := by decide
  have hdescent : baseEnd_3418336 < baseStart_3418336 := by decide
  rcases family_descends (prefixWord ++ tailWord_3418336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3418370 : List Nat := [3, 4, 1, 1, 2, 1, 3, 2, 1, 3, 2]
def baseStart_3418370 : Nat := 118140960795 + 3418370 * 2 ^ 59
def prefixEnd_3418370 : Nat := 4983230072969 + 3 ^ 40 * 3418370 * 2
def baseEnd_3418370 : Nat := 1755266864909895845354209

theorem tailTrace_3418370 : CollatzResearch.WordTrace tailWord_3418370 prefixEnd_3418370 1755266864909895845354209 := by
  unfold tailWord_3418370
  simp only [CollatzResearch.WordTrace]
  refine ⟨31169549156459193990383141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83118797750557850641021709 31169549156459193990383141)
  ·
    refine ⟨5844290466836098873196839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31169549156459193990383141 5844290466836098873196839)
    ·
      refine ⟨8766435700254148309795259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5844290466836098873196839 8766435700254148309795259)
      ·
        refine ⟨13149653550381222464692889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8766435700254148309795259 13149653550381222464692889)
        ·
          refine ⟨9862240162785916848519667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13149653550381222464692889 9862240162785916848519667)
          ·
            refine ⟨14793360244178875272779501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9862240162785916848519667 14793360244178875272779501)
            ·
              refine ⟨5547510091567078227292313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14793360244178875272779501 5547510091567078227292313)
              ·
                refine ⟨4160632568675308670469235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5547510091567078227292313 4160632568675308670469235)
                ·
                  refine ⟨6240948853012963005703853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4160632568675308670469235 6240948853012963005703853)
                  ·
                    refine ⟨2340355819879861127138945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6240948853012963005703853 2340355819879861127138945)
                    ·
                      refine ⟨1755266864909895845354209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2340355819879861127138945 1755266864909895845354209)
                      ·
                        rfl

theorem cell23_3418370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 3, 2, 1, 3, 2].length) (baseStart_3418370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3418370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3418370 prefixEnd_3418370 := by exact prefixLift 3418370
  have htrace : WordTrace (prefixWord ++ tailWord_3418370) baseStart_3418370 baseEnd_3418370 := by
    simpa [prefixWord, tailWord_3418370, baseEnd_3418370] using wordTrace_append hprefix tailTrace_3418370
  have hstable : (prefixWord ++ tailWord_3418370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3418370).length < 2 ^ (prefixWord ++ tailWord_3418370).sum := by decide
  have hdescent : baseEnd_3418370 < baseStart_3418370 := by decide
  rcases family_descends (prefixWord ++ tailWord_3418370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3418400 : List Nat := [2, 1, 1, 5, 2, 2, 2, 2, 2, 2, 2]
def baseStart_3418400 : Nat := 118140960795 + 3418400 * 2 ^ 59
def prefixEnd_3418400 : Nat := 4983230072969 + 3 ^ 40 * 3418400 * 2
def baseEnd_3418400 : Nat := 1755282269329530727979071

theorem tailTrace_3418400 : CollatzResearch.WordTrace tailWord_3418400 prefixEnd_3418400 1755282269329530727979071 := by
  unfold tailWord_3418400
  simp only [CollatzResearch.WordTrace]
  refine ⟨62339645407864045542562327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83119527210485394056749769 62339645407864045542562327)
  ·
    refine ⟨93509468111796068313843491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62339645407864045542562327 93509468111796068313843491)
    ·
      refine ⟨140264202167694102470765237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93509468111796068313843491 140264202167694102470765237)
      ·
        refine ⟨13149768953221322106634241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 140264202167694102470765237 13149768953221322106634241)
        ·
          refine ⟨9862326714915991579975681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13149768953221322106634241 9862326714915991579975681)
          ·
            refine ⟨7396745036186993684981761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9862326714915991579975681 7396745036186993684981761)
            ·
              refine ⟨5547558777140245263736321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7396745036186993684981761 5547558777140245263736321)
              ·
                refine ⟨4160669082855183947802241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5547558777140245263736321 4160669082855183947802241)
                ·
                  refine ⟨3120501812141387960851681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4160669082855183947802241 3120501812141387960851681)
                  ·
                    refine ⟨2340376359106040970638761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3120501812141387960851681 2340376359106040970638761)
                    ·
                      refine ⟨1755282269329530727979071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2340376359106040970638761 1755282269329530727979071)
                      ·
                        rfl

theorem cell23_3418400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 2, 2, 2, 2, 2].length) (baseStart_3418400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3418400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3418400 prefixEnd_3418400 := by exact prefixLift 3418400
  have htrace : WordTrace (prefixWord ++ tailWord_3418400) baseStart_3418400 baseEnd_3418400 := by
    simpa [prefixWord, tailWord_3418400, baseEnd_3418400] using wordTrace_append hprefix tailTrace_3418400
  have hstable : (prefixWord ++ tailWord_3418400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3418400).length < 2 ^ (prefixWord ++ tailWord_3418400).sum := by decide
  have hdescent : baseEnd_3418400 < baseStart_3418400 := by decide
  rcases family_descends (prefixWord ++ tailWord_3418400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3418413 : List Nat := [1, 5, 3, 1, 2, 1, 1, 1, 2, 2, 4]
def baseStart_3418413 : Nat := 118140960795 + 3418413 * 2 ^ 59
def prefixEnd_3418413 : Nat := 4983230072969 + 3 ^ 40 * 3418413 * 2
def baseEnd_3418413 : Nat := 1755288944578039177116511

theorem tailTrace_3418413 : CollatzResearch.WordTrace tailWord_3418413 prefixEnd_3418413 1755288944578039177116511 := by
  unfold tailWord_3418413
  simp only [CollatzResearch.WordTrace]
  refine ⟨124679764964680994305347893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83119843309787329536898595 124679764964680994305347893)
  ·
    refine ⟨11688727965438843216126365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 124679764964680994305347893 11688727965438843216126365)
    ·
      refine ⟨4383272987039566206047387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11688727965438843216126365 4383272987039566206047387)
      ·
        refine ⟨6574909480559349309071081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4383272987039566206047387 6574909480559349309071081)
        ·
          refine ⟨4931182110419511981803311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6574909480559349309071081 4931182110419511981803311)
          ·
            refine ⟨7396773165629267972704967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4931182110419511981803311 7396773165629267972704967)
            ·
              refine ⟨11095159748443901959057451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7396773165629267972704967 11095159748443901959057451)
              ·
                refine ⟨16642739622665852938586177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11095159748443901959057451 16642739622665852938586177)
                ·
                  refine ⟨12482054716999389703939633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16642739622665852938586177 12482054716999389703939633)
                  ·
                    refine ⟨9361541037749542277954725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12482054716999389703939633 9361541037749542277954725)
                    ·
                      refine ⟨1755288944578039177116511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9361541037749542277954725 1755288944578039177116511)
                      ·
                        rfl

theorem cell23_3418413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_3418413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3418413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3418413 prefixEnd_3418413 := by exact prefixLift 3418413
  have htrace : WordTrace (prefixWord ++ tailWord_3418413) baseStart_3418413 baseEnd_3418413 := by
    simpa [prefixWord, tailWord_3418413, baseEnd_3418413] using wordTrace_append hprefix tailTrace_3418413
  have hstable : (prefixWord ++ tailWord_3418413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3418413).length < 2 ^ (prefixWord ++ tailWord_3418413).sum := by decide
  have hdescent : baseEnd_3418413 < baseStart_3418413 := by decide
  rcases family_descends (prefixWord ++ tailWord_3418413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3418432 : List Nat := [2, 1, 1, 2, 2, 1, 2, 1, 1, 10]
def baseStart_3418432 : Nat := 118140960795 + 3418432 * 2 ^ 59
def prefixEnd_3418432 : Nat := 4983230072969 + 3 ^ 40 * 3418432 * 2
def baseEnd_3418432 : Nat := 585099566903491534259641

theorem tailTrace_3418432 : CollatzResearch.WordTrace tailWord_3418432 prefixEnd_3418432 585099566903491534259641 := by
  unfold tailWord_3418432
  simp only [CollatzResearch.WordTrace]
  refine ⟨62340228975806080275144775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83120305301074773700193033 62340228975806080275144775)
  ·
    refine ⟨93510343463709120412717163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62340228975806080275144775 93510343463709120412717163)
    ·
      refine ⟨140265515195563680619075745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93510343463709120412717163 140265515195563680619075745)
      ·
        refine ⟨105199136396672760464306809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140265515195563680619075745 105199136396672760464306809)
        ·
          refine ⟨78899352297504570348230107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105199136396672760464306809 78899352297504570348230107)
          ·
            refine ⟨118349028446256855522345161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78899352297504570348230107 118349028446256855522345161)
            ·
              refine ⟨88761771334692641641758871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118349028446256855522345161 88761771334692641641758871)
              ·
                refine ⟨133142657002038962462638307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88761771334692641641758871 133142657002038962462638307)
                ·
                  refine ⟨199713985503058443693957461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 133142657002038962462638307 199713985503058443693957461)
                  ·
                    refine ⟨585099566903491534259641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 199713985503058443693957461 585099566903491534259641)
                    ·
                      rfl

theorem cell23_3418432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 1, 10].length) (baseStart_3418432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3418432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3418432 prefixEnd_3418432 := by exact prefixLift 3418432
  have htrace : WordTrace (prefixWord ++ tailWord_3418432) baseStart_3418432 baseEnd_3418432 := by
    simpa [prefixWord, tailWord_3418432, baseEnd_3418432] using wordTrace_append hprefix tailTrace_3418432
  have hstable : (prefixWord ++ tailWord_3418432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3418432).length < 2 ^ (prefixWord ++ tailWord_3418432).sum := by decide
  have hdescent : baseEnd_3418432 < baseStart_3418432 := by decide
  rcases family_descends (prefixWord ++ tailWord_3418432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3418439 : List Nat := [1, 1, 4, 1, 2, 2, 3, 1, 1, 3, 4]
def baseStart_3418439 : Nat := 118140960795 + 3418439 * 2 ^ 59
def prefixEnd_3418439 : Nat := 4983230072969 + 3 ^ 40 * 3418439 * 2
def baseEnd_3418439 : Nat := 1755302295075056075391391

theorem tailTrace_3418439 : CollatzResearch.WordTrace tailWord_3418439 prefixEnd_3418439 1755302295075056075391391 := by
  unfold tailWord_3418439
  simp only [CollatzResearch.WordTrace]
  refine ⟨124680713262586800745794371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83120475508391200497196247 124680713262586800745794371)
  ·
    refine ⟨187021069893880201118691557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124680713262586800745794371 187021069893880201118691557)
    ·
      refine ⟨35066450605102537709754667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 187021069893880201118691557 35066450605102537709754667)
      ·
        refine ⟨52599675907653806564632001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35066450605102537709754667 52599675907653806564632001)
        ·
          refine ⟨39449756930740354923474001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52599675907653806564632001 39449756930740354923474001)
          ·
            refine ⟨29587317698055266192605501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39449756930740354923474001 29587317698055266192605501)
            ·
              refine ⟨11095244136770724822227063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29587317698055266192605501 11095244136770724822227063)
              ·
                refine ⟨16642866205156087233340595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11095244136770724822227063 16642866205156087233340595)
                ·
                  refine ⟨24964299307734130850010893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16642866205156087233340595 24964299307734130850010893)
                  ·
                    refine ⟨9361612240400299068754085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24964299307734130850010893 9361612240400299068754085)
                    ·
                      refine ⟨1755302295075056075391391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9361612240400299068754085 1755302295075056075391391)
                      ·
                        rfl

theorem cell23_3418439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 1, 1, 3, 4].length) (baseStart_3418439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3418439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3418439 prefixEnd_3418439 := by exact prefixLift 3418439
  have htrace : WordTrace (prefixWord ++ tailWord_3418439) baseStart_3418439 baseEnd_3418439 := by
    simpa [prefixWord, tailWord_3418439, baseEnd_3418439] using wordTrace_append hprefix tailTrace_3418439
  have hstable : (prefixWord ++ tailWord_3418439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3418439).length < 2 ^ (prefixWord ++ tailWord_3418439).sum := by decide
  have hdescent : baseEnd_3418439 < baseStart_3418439 := by decide
  rcases family_descends (prefixWord ++ tailWord_3418439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3418489 : List Nat := [1, 2, 1, 3, 2, 1, 1, 1, 1, 7, 3]
def baseStart_3418489 : Nat := 118140960795 + 3418489 * 2 ^ 59
def prefixEnd_3418489 : Nat := 4983230072969 + 3 ^ 40 * 3418489 * 2
def baseEnd_3418489 : Nat := 1755327969107780879766161

theorem tailTrace_3418489 : CollatzResearch.WordTrace tailWord_3418489 prefixEnd_3418489 1755327969107780879766161 := by
  unfold tailWord_3418489
  simp only [CollatzResearch.WordTrace]
  refine ⟨124682536912405659285114521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83121691274937106190076347 124682536912405659285114521)
  ·
    refine ⟨93511902684304244463835891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124682536912405659285114521 93511902684304244463835891)
    ·
      refine ⟨140267854026456366695753837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93511902684304244463835891 140267854026456366695753837)
      ·
        refine ⟨52600445259921137510907689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140267854026456366695753837 52600445259921137510907689)
        ·
          refine ⟨39450333944940853133180767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52600445259921137510907689 39450333944940853133180767)
          ·
            refine ⟨59175500917411279699771151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39450333944940853133180767 59175500917411279699771151)
            ·
              refine ⟨88763251376116919549656727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59175500917411279699771151 88763251376116919549656727)
              ·
                refine ⟨133144877064175379324485091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88763251376116919549656727 133144877064175379324485091)
                ·
                  refine ⟨199717315596263068986727637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 133144877064175379324485091 199717315596263068986727637)
                  ·
                    refine ⟨4680874584287415679376429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 199717315596263068986727637 4680874584287415679376429)
                    ·
                      refine ⟨1755327969107780879766161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4680874584287415679376429 1755327969107780879766161)
                      ·
                        rfl

theorem cell23_3418489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 7, 3].length) (baseStart_3418489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3418489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3418489 prefixEnd_3418489 := by exact prefixLift 3418489
  have htrace : WordTrace (prefixWord ++ tailWord_3418489) baseStart_3418489 baseEnd_3418489 := by
    simpa [prefixWord, tailWord_3418489, baseEnd_3418489] using wordTrace_append hprefix tailTrace_3418489
  have hstable : (prefixWord ++ tailWord_3418489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3418489).length < 2 ^ (prefixWord ++ tailWord_3418489).sum := by decide
  have hdescent : baseEnd_3418489 < baseStart_3418489 := by decide
  rcases family_descends (prefixWord ++ tailWord_3418489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3418546 : List Nat := [3, 2, 1, 1, 1, 1, 5, 1, 3, 1, 4]
def baseStart_3418546 : Nat := 118140960795 + 3418546 * 2 ^ 59
def prefixEnd_3418546 : Nat := 4983230072969 + 3 ^ 40 * 3418546 * 2
def baseEnd_3418546 : Nat := 1755357237505087156753399

theorem tailTrace_3418546 : CollatzResearch.WordTrace tailWord_3418546 prefixEnd_3418546 1755357237505087156753399 := by
  unfold tailWord_3418546
  simp only [CollatzResearch.WordTrace]
  refine ⟨31171153968299789504984873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83123077248799438679959661 31171153968299789504984873)
  ·
    refine ⟨23378365476224842128738655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31171153968299789504984873 23378365476224842128738655)
    ·
      refine ⟨35067548214337263193107983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23378365476224842128738655 35067548214337263193107983)
      ·
        refine ⟨52601322321505894789661975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35067548214337263193107983 52601322321505894789661975)
        ·
          refine ⟨78901983482258842184492963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52601322321505894789661975 78901983482258842184492963)
          ·
            refine ⟨118352975223388263276739445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78901983482258842184492963 118352975223388263276739445)
            ·
              refine ⟨11095591427192649682194323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 118352975223388263276739445 11095591427192649682194323)
              ·
                refine ⟨16643387140788974523291485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11095591427192649682194323 16643387140788974523291485)
                ·
                  refine ⟨6241270177795865446234307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16643387140788974523291485 6241270177795865446234307)
                  ·
                    refine ⟨9361905266693798169351461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6241270177795865446234307 9361905266693798169351461)
                    ·
                      refine ⟨1755357237505087156753399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9361905266693798169351461 1755357237505087156753399)
                      ·
                        rfl

theorem cell23_3418546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 1, 3, 1, 4].length) (baseStart_3418546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3418546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3418546 prefixEnd_3418546 := by exact prefixLift 3418546
  have htrace : WordTrace (prefixWord ++ tailWord_3418546) baseStart_3418546 baseEnd_3418546 := by
    simpa [prefixWord, tailWord_3418546, baseEnd_3418546] using wordTrace_append hprefix tailTrace_3418546
  have hstable : (prefixWord ++ tailWord_3418546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3418546).length < 2 ^ (prefixWord ++ tailWord_3418546).sum := by decide
  have hdescent : baseEnd_3418546 < baseStart_3418546 := by decide
  rcases family_descends (prefixWord ++ tailWord_3418546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3418556 : List Nat := [2, 2, 2, 4, 1, 1, 1, 1, 3, 6]
def baseStart_3418556 : Nat := 118140960795 + 3418556 * 2 ^ 59
def prefixEnd_3418556 : Nat := 4983230072969 + 3 ^ 40 * 3418556 * 2
def baseEnd_3418556 : Nat := 585120790770544039209451

theorem tailTrace_3418556 : CollatzResearch.WordTrace tailWord_3418556 prefixEnd_3418556 585120790770544039209451 := by
  unfold tailWord_3418556
  simp only [CollatzResearch.WordTrace]
  refine ⟨62342490301581464863901761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83123320402108619818535681 62342490301581464863901761)
  ·
    refine ⟨46756867726186098647926321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62342490301581464863901761 46756867726186098647926321)
    ·
      refine ⟨35067650794639573985944741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46756867726186098647926321 35067650794639573985944741)
      ·
        refine ⟨6575184523994920122364639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35067650794639573985944741 6575184523994920122364639)
        ·
          refine ⟨9862776785992380183546959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6575184523994920122364639 9862776785992380183546959)
          ·
            refine ⟨14794165178988570275320439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9862776785992380183546959 14794165178988570275320439)
            ·
              refine ⟨22191247768482855412980659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14794165178988570275320439 22191247768482855412980659)
              ·
                refine ⟨33286871652724283119470989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22191247768482855412980659 33286871652724283119470989)
                ·
                  refine ⟨12482576869771606169801621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33286871652724283119470989 12482576869771606169801621)
                  ·
                    refine ⟨585120790770544039209451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12482576869771606169801621 585120790770544039209451)
                    ·
                      rfl

theorem cell23_3418556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 1, 3, 6].length) (baseStart_3418556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3418556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3418556 prefixEnd_3418556 := by exact prefixLift 3418556
  have htrace : WordTrace (prefixWord ++ tailWord_3418556) baseStart_3418556 baseEnd_3418556 := by
    simpa [prefixWord, tailWord_3418556, baseEnd_3418556] using wordTrace_append hprefix tailTrace_3418556
  have hstable : (prefixWord ++ tailWord_3418556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3418556).length < 2 ^ (prefixWord ++ tailWord_3418556).sum := by decide
  have hdescent : baseEnd_3418556 < baseStart_3418556 := by decide
  rcases family_descends (prefixWord ++ tailWord_3418556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3418597 : List Nat := [1, 3, 1, 5, 2, 1, 1, 2, 3, 2, 2]
def baseStart_3418597 : Nat := 118140960795 + 3418597 * 2 ^ 59
def prefixEnd_3418597 : Nat := 4983230072969 + 3 ^ 40 * 3418597 * 2
def baseEnd_3418597 : Nat := 1755383425018466457215665

theorem tailTrace_3418597 : CollatzResearch.WordTrace tailWord_3418597 prefixEnd_3418597 1755383425018466457215665 := by
  unfold tailWord_3418597
  simp only [CollatzResearch.WordTrace]
  refine ⟨124686475996014393730046045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83124317330676262486697363 124686475996014393730046045)
  ·
    refine ⟨46757428498505397648767267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124686475996014393730046045 46757428498505397648767267)
    ·
      refine ⟨70136142747758096473150901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46757428498505397648767267 70136142747758096473150901)
      ·
        refine ⟨6575263382602321544357897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 70136142747758096473150901 6575263382602321544357897)
        ·
          refine ⟨4931447536951741158268423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6575263382602321544357897 4931447536951741158268423)
          ·
            refine ⟨7397171305427611737402635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4931447536951741158268423 7397171305427611737402635)
            ·
              refine ⟨11095756958141417606103953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7397171305427611737402635 11095756958141417606103953)
              ·
                refine ⟨8321817718606063204577965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11095756958141417606103953 8321817718606063204577965)
                ·
                  refine ⟨3120681644477273701716737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8321817718606063204577965 3120681644477273701716737)
                  ·
                    refine ⟨2340511233357955276287553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3120681644477273701716737 2340511233357955276287553)
                    ·
                      refine ⟨1755383425018466457215665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2340511233357955276287553 1755383425018466457215665)
                      ·
                        rfl

theorem cell23_3418597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 2, 3, 2, 2].length) (baseStart_3418597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3418597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3418597 prefixEnd_3418597 := by exact prefixLift 3418597
  have htrace : WordTrace (prefixWord ++ tailWord_3418597) baseStart_3418597 baseEnd_3418597 := by
    simpa [prefixWord, tailWord_3418597, baseEnd_3418597] using wordTrace_append hprefix tailTrace_3418597
  have hstable : (prefixWord ++ tailWord_3418597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3418597).length < 2 ^ (prefixWord ++ tailWord_3418597).sum := by decide
  have hdescent : baseEnd_3418597 < baseStart_3418597 := by decide
  rcases family_descends (prefixWord ++ tailWord_3418597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3418614 : List Nat := [5, 1, 1, 1, 2, 1, 4, 3, 1, 2, 2]
def baseStart_3418614 : Nat := 118140960795 + 3418614 * 2 ^ 59
def prefixEnd_3418614 : Nat := 4983230072969 + 3 ^ 40 * 3418614 * 2
def baseEnd_3418614 : Nat := 1755392154189592890703087

theorem tailTrace_3418614 : CollatzResearch.WordTrace tailWord_3418614 prefixEnd_3418614 1755392154189592890703087 := by
  unfold tailWord_3418614
  simp only [CollatzResearch.WordTrace]
  refine ⟨7792943502309550352088431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 83124730691301870422276597 7792943502309550352088431)
  ·
    refine ⟨11689415253464325528132647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7792943502309550352088431 11689415253464325528132647)
    ·
      refine ⟨17534122880196488292198971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11689415253464325528132647 17534122880196488292198971)
      ·
        refine ⟨26301184320294732438298457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17534122880196488292198971 26301184320294732438298457)
        ·
          refine ⟨19725888240221049328723843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26301184320294732438298457 19725888240221049328723843)
          ·
            refine ⟨29588832360331573993085765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19725888240221049328723843 29588832360331573993085765)
            ·
              refine ⟨5547906067562170123703581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29588832360331573993085765 5547906067562170123703581)
              ·
                refine ⟨2080464775335813796388843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5547906067562170123703581 2080464775335813796388843)
                ·
                  refine ⟨3120697163003720694583265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2080464775335813796388843 3120697163003720694583265)
                  ·
                    refine ⟨2340522872252790520937449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3120697163003720694583265 2340522872252790520937449)
                    ·
                      refine ⟨1755392154189592890703087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2340522872252790520937449 1755392154189592890703087)
                      ·
                        rfl

theorem cell23_3418614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 4, 3, 1, 2, 2].length) (baseStart_3418614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3418614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3418614 prefixEnd_3418614 := by exact prefixLift 3418614
  have htrace : WordTrace (prefixWord ++ tailWord_3418614) baseStart_3418614 baseEnd_3418614 := by
    simpa [prefixWord, tailWord_3418614, baseEnd_3418614] using wordTrace_append hprefix tailTrace_3418614
  have hstable : (prefixWord ++ tailWord_3418614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3418614).length < 2 ^ (prefixWord ++ tailWord_3418614).sum := by decide
  have hdescent : baseEnd_3418614 < baseStart_3418614 := by decide
  rcases family_descends (prefixWord ++ tailWord_3418614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3418647 : List Nat := [1, 1, 3, 6, 1, 2, 1, 1, 1, 3, 3]
def baseStart_3418647 : Nat := 118140960795 + 3418647 * 2 ^ 59
def prefixEnd_3418647 : Nat := 4983230072969 + 3 ^ 40 * 3418647 * 2
def baseEnd_3418647 : Nat := 1755409099051191261590435

theorem tailTrace_3418647 : CollatzResearch.WordTrace tailWord_3418647 prefixEnd_3418647 1755409099051191261590435 := by
  unfold tailWord_3418647
  simp only [CollatzResearch.WordTrace]
  refine ⟨124688299645833252269366195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83125533097222168179577463 124688299645833252269366195)
  ·
    refine ⟨187032449468749878404049293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124688299645833252269366195 187032449468749878404049293)
    ·
      refine ⟨70137168550781204401518485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187032449468749878404049293 70137168550781204401518485)
      ·
        refine ⟨3287679775817868956321179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 70137168550781204401518485 3287679775817868956321179)
        ·
          refine ⟨4931519663726803434481769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3287679775817868956321179 4931519663726803434481769)
          ·
            refine ⟨3698639747795102575861327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4931519663726803434481769 3698639747795102575861327)
            ·
              refine ⟨5547959621692653863791991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3698639747795102575861327 5547959621692653863791991)
              ·
                refine ⟨8321939432538980795687987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5547959621692653863791991 8321939432538980795687987)
                ·
                  refine ⟨12482909148808471193531981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8321939432538980795687987 12482909148808471193531981)
                  ·
                    refine ⟨4681090930803176697574493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12482909148808471193531981 4681090930803176697574493)
                    ·
                      refine ⟨1755409099051191261590435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4681090930803176697574493 1755409099051191261590435)
                      ·
                        rfl

theorem cell23_3418647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_3418647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3418647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3418647 prefixEnd_3418647 := by exact prefixLift 3418647
  have htrace : WordTrace (prefixWord ++ tailWord_3418647) baseStart_3418647 baseEnd_3418647 := by
    simpa [prefixWord, tailWord_3418647, baseEnd_3418647] using wordTrace_append hprefix tailTrace_3418647
  have hstable : (prefixWord ++ tailWord_3418647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3418647).length < 2 ^ (prefixWord ++ tailWord_3418647).sum := by decide
  have hdescent : baseEnd_3418647 < baseStart_3418647 := by decide
  rcases family_descends (prefixWord ++ tailWord_3418647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3418693 : List Nat := [1, 3, 1, 1, 1, 7, 1, 1, 7]
def baseStart_3418693 : Nat := 118140960795 + 3418693 * 2 ^ 59
def prefixEnd_3418693 : Nat := 4983230072969 + 3 ^ 40 * 3418693 * 2
def baseEnd_3418693 : Nat := 195048079906810897957247

theorem tailTrace_3418693 : CollatzResearch.WordTrace tailWord_3418693 prefixEnd_3418693 195048079906810897957247 := by
  unfold tailWord_3418693
  simp only [CollatzResearch.WordTrace]
  refine ⟨124689977403666602125540733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83126651602444401417027155 124689977403666602125540733)
  ·
    refine ⟨46758741526374975797077775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124689977403666602125540733 46758741526374975797077775)
    ·
      refine ⟨70138112289562463695616663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46758741526374975797077775 70138112289562463695616663)
      ·
        refine ⟨105207168434343695543424995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70138112289562463695616663 105207168434343695543424995)
        ·
          refine ⟨157810752651515543315137493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105207168434343695543424995 157810752651515543315137493)
          ·
            refine ⟨3698689515269895546448535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 157810752651515543315137493 3698689515269895546448535)
            ·
              refine ⟨5548034272904843319672803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3698689515269895546448535 5548034272904843319672803)
              ·
                refine ⟨8322051409357264979509205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5548034272904843319672803 8322051409357264979509205)
                ·
                  refine ⟨195048079906810897957247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8322051409357264979509205 195048079906810897957247)
                  ·
                    rfl

theorem cell23_3418693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 1, 1, 7].length) (baseStart_3418693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3418693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3418693 prefixEnd_3418693 := by exact prefixLift 3418693
  have htrace : WordTrace (prefixWord ++ tailWord_3418693) baseStart_3418693 baseEnd_3418693 := by
    simpa [prefixWord, tailWord_3418693, baseEnd_3418693] using wordTrace_append hprefix tailTrace_3418693
  have hstable : (prefixWord ++ tailWord_3418693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3418693).length < 2 ^ (prefixWord ++ tailWord_3418693).sum := by decide
  have hdescent : baseEnd_3418693 < baseStart_3418693 := by decide
  rcases family_descends (prefixWord ++ tailWord_3418693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3418723 : List Nat := [1, 1, 1, 5, 1, 2, 4, 1, 2, 5]
def baseStart_3418723 : Nat := 118140960795 + 3418723 * 2 ^ 59
def prefixEnd_3418723 : Nat := 4983230072969 + 3 ^ 40 * 3418723 * 2
def baseEnd_3418723 : Nat := 585149374526977654746695

theorem tailTrace_3418723 : CollatzResearch.WordTrace tailWord_3418723 prefixEnd_3418723 585149374526977654746695 := by
  unfold tailWord_3418723
  simp only [CollatzResearch.WordTrace]
  refine ⟨124691071593557917249132823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83127381062371944832755215 124691071593557917249132823)
  ·
    refine ⟨187036607390336875873699235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124691071593557917249132823 187036607390336875873699235)
    ·
      refine ⟨280554911085505313810548853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187036607390336875873699235 280554911085505313810548853)
      ·
        refine ⟨26302022914266123169738955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 280554911085505313810548853 26302022914266123169738955)
        ·
          refine ⟨39453034371399184754608433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26302022914266123169738955 39453034371399184754608433)
          ·
            refine ⟨29589775778549388565956325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39453034371399184754608433 29589775778549388565956325)
            ·
              refine ⟨5548082958478010356116811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29589775778549388565956325 5548082958478010356116811)
              ·
                refine ⟨8322124437717015534175217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5548082958478010356116811 8322124437717015534175217)
                ·
                  refine ⟨6241593328287761650631413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8322124437717015534175217 6241593328287761650631413)
                  ·
                    refine ⟨585149374526977654746695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6241593328287761650631413 585149374526977654746695)
                    ·
                      rfl

theorem cell23_3418723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 4, 1, 2, 5].length) (baseStart_3418723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3418723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3418723 prefixEnd_3418723 := by exact prefixLift 3418723
  have htrace : WordTrace (prefixWord ++ tailWord_3418723) baseStart_3418723 baseEnd_3418723 := by
    simpa [prefixWord, tailWord_3418723, baseEnd_3418723] using wordTrace_append hprefix tailTrace_3418723
  have hstable : (prefixWord ++ tailWord_3418723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3418723).length < 2 ^ (prefixWord ++ tailWord_3418723).sum := by decide
  have hdescent : baseEnd_3418723 < baseStart_3418723 := by decide
  rcases family_descends (prefixWord ++ tailWord_3418723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3418733 : List Nat := [1, 5, 1, 1, 3, 1, 1, 2, 1, 2, 5]
def baseStart_3418733 : Nat := 118140960795 + 3418733 * 2 ^ 59
def prefixEnd_3418733 : Nat := 4983230072969 + 3 ^ 40 * 3418733 * 2
def baseEnd_3418733 : Nat := 1755453258387477925115039

theorem tailTrace_3418733 : CollatzResearch.WordTrace tailWord_3418733 prefixEnd_3418733 1755453258387477925115039 := by
  unfold tailWord_3418733
  simp only [CollatzResearch.WordTrace]
  refine ⟨124691436323521688956996853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83127624215681125971331235 124691436323521688956996853)
  ·
    refine ⟨11689822155330158339718455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 124691436323521688956996853 11689822155330158339718455)
    ·
      refine ⟨17534733232995237509577683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11689822155330158339718455 17534733232995237509577683)
      ·
        refine ⟨26302099849492856264366525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17534733232995237509577683 26302099849492856264366525)
        ·
          refine ⟨9863287443559821099137447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26302099849492856264366525 9863287443559821099137447)
          ·
            refine ⟨14794931165339731648706171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9863287443559821099137447 14794931165339731648706171)
            ·
              refine ⟨22192396748009597473059257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14794931165339731648706171 22192396748009597473059257)
              ·
                refine ⟨16644297561007198104794443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22192396748009597473059257 16644297561007198104794443)
                ·
                  refine ⟨24966446341510797157191665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16644297561007198104794443 24966446341510797157191665)
                  ·
                    refine ⟨18724834756133097867893749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24966446341510797157191665 18724834756133097867893749)
                    ·
                      refine ⟨1755453258387477925115039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18724834756133097867893749 1755453258387477925115039)
                      ·
                        rfl

theorem cell23_3418733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 2, 1, 2, 5].length) (baseStart_3418733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3418733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3418733 prefixEnd_3418733 := by exact prefixLift 3418733
  have htrace : WordTrace (prefixWord ++ tailWord_3418733) baseStart_3418733 baseEnd_3418733 := by
    simpa [prefixWord, tailWord_3418733, baseEnd_3418733] using wordTrace_append hprefix tailTrace_3418733
  have hstable : (prefixWord ++ tailWord_3418733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3418733).length < 2 ^ (prefixWord ++ tailWord_3418733).sum := by decide
  have hdescent : baseEnd_3418733 < baseStart_3418733 := by decide
  rcases family_descends (prefixWord ++ tailWord_3418733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3418743 : List Nat := [1, 1, 3, 1, 1, 3, 4, 2, 2, 1, 4]
def baseStart_3418743 : Nat := 118140960795 + 3418743 * 2 ^ 59
def prefixEnd_3418743 : Nat := 4983230072969 + 3 ^ 40 * 3418743 * 2
def baseEnd_3418743 : Nat := 1755458393194022885989993

theorem tailTrace_3418743 : CollatzResearch.WordTrace tailWord_3418743 prefixEnd_3418743 1755458393194022885989993 := by
  unfold tailWord_3418743
  simp only [CollatzResearch.WordTrace]
  refine ⟨124691801053485460664860883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83127867368990307109907255 124691801053485460664860883)
  ·
    refine ⟨187037701580228190997291325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124691801053485460664860883 187037701580228190997291325)
    ·
      refine ⟨70139138092585571623984247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187037701580228190997291325 70139138092585571623984247)
      ·
        refine ⟨105208707138878357435976371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70139138092585571623984247 105208707138878357435976371)
        ·
          refine ⟨157813060708317536153964557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105208707138878357435976371 157813060708317536153964557)
          ·
            refine ⟨59179897765619076057736709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 157813060708317536153964557 59179897765619076057736709)
            ·
              refine ⟨11096230831053576760825633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59179897765619076057736709 11096230831053576760825633)
              ·
                refine ⟨8322173123290182570619225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11096230831053576760825633 8322173123290182570619225)
                ·
                  refine ⟨6241629842467636927964419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8322173123290182570619225 6241629842467636927964419)
                  ·
                    refine ⟨9362444763701455391946629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6241629842467636927964419 9362444763701455391946629)
                    ·
                      refine ⟨1755458393194022885989993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9362444763701455391946629 1755458393194022885989993)
                      ·
                        rfl

theorem cell23_3418743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 2, 2, 1, 4].length) (baseStart_3418743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3418743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3418743 prefixEnd_3418743 := by exact prefixLift 3418743
  have htrace : WordTrace (prefixWord ++ tailWord_3418743) baseStart_3418743 baseEnd_3418743 := by
    simpa [prefixWord, tailWord_3418743, baseEnd_3418743] using wordTrace_append hprefix tailTrace_3418743
  have hstable : (prefixWord ++ tailWord_3418743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3418743).length < 2 ^ (prefixWord ++ tailWord_3418743).sum := by decide
  have hdescent : baseEnd_3418743 < baseStart_3418743 := by decide
  rcases family_descends (prefixWord ++ tailWord_3418743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3418770 : List Nat := [3, 2, 3, 1, 2, 1, 1, 1, 5, 4]
def baseStart_3418770 : Nat := 118140960795 + 3418770 * 2 ^ 59
def prefixEnd_3418770 : Nat := 4983230072969 + 3 ^ 40 * 3418770 * 2
def baseEnd_3418770 : Nat := 585157419057231426784123

theorem tailTrace_3418770 : CollatzResearch.WordTrace tailWord_3418770 prefixEnd_3418770 585157419057231426784123 := by
  unfold tailWord_3418770
  simp only [CollatzResearch.WordTrace]
  refine ⟨31173196456096911069023441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83128523882925096184062509 31173196456096911069023441)
  ·
    refine ⟨23379897342072683301767581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31173196456096911069023441 23379897342072683301767581)
    ·
      refine ⟨8767461503277256238162843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23379897342072683301767581 8767461503277256238162843)
      ·
        refine ⟨13151192254915884357244265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8767461503277256238162843 13151192254915884357244265)
        ·
          refine ⟨9863394191186913267933199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13151192254915884357244265 9863394191186913267933199)
          ·
            refine ⟨14795091286780369901899799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9863394191186913267933199 14795091286780369901899799)
            ·
              refine ⟨22192636930170554852849699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14795091286780369901899799 22192636930170554852849699)
              ·
                refine ⟨33288955395255832279274549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22192636930170554852849699 33288955395255832279274549)
                ·
                  refine ⟨3120839568305234276181989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33288955395255832279274549 3120839568305234276181989)
                  ·
                    refine ⟨585157419057231426784123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3120839568305234276181989 585157419057231426784123)
                    ·
                      rfl

theorem cell23_3418770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 1, 5, 4].length) (baseStart_3418770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3418770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3418770 prefixEnd_3418770 := by exact prefixLift 3418770
  have htrace : WordTrace (prefixWord ++ tailWord_3418770) baseStart_3418770 baseEnd_3418770 := by
    simpa [prefixWord, tailWord_3418770, baseEnd_3418770] using wordTrace_append hprefix tailTrace_3418770
  have hstable : (prefixWord ++ tailWord_3418770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3418770).length < 2 ^ (prefixWord ++ tailWord_3418770).sum := by decide
  have hdescent : baseEnd_3418770 < baseStart_3418770 := by decide
  rcases family_descends (prefixWord ++ tailWord_3418770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3418780 : List Nat := [2, 2, 3, 2, 2, 2, 1, 1, 1, 4, 3]
def baseStart_3418780 : Nat := 118140960795 + 3418780 * 2 ^ 59
def prefixEnd_3418780 : Nat := 4983230072969 + 3 ^ 40 * 3418780 * 2
def baseEnd_3418780 : Nat := 1755477391978239241227323

theorem tailTrace_3418780 : CollatzResearch.WordTrace tailWord_3418780 prefixEnd_3418780 1755477391978239241227323 := by
  unfold tailWord_3418780
  simp only [CollatzResearch.WordTrace]
  refine ⟨62346575277175707991978897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83128767036234277322638529 62346575277175707991978897)
  ·
    refine ⟨46759931457881780993984173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62346575277175707991978897 46759931457881780993984173)
    ·
      refine ⟨17534974296705667872744065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46759931457881780993984173 17534974296705667872744065)
      ·
        refine ⟨13151230722529250904558049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17534974296705667872744065 13151230722529250904558049)
        ·
          refine ⟨9863423041896938178418537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13151230722529250904558049 9863423041896938178418537)
          ·
            refine ⟨7397567281422703633813903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9863423041896938178418537 7397567281422703633813903)
            ·
              refine ⟨11096350922134055450720855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7397567281422703633813903 11096350922134055450720855)
              ·
                refine ⟨16644526383201083176081283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11096350922134055450720855 16644526383201083176081283)
                ·
                  refine ⟨24966789574801624764121925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16644526383201083176081283 24966789574801624764121925)
                  ·
                    refine ⟨4681273045275304643272861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24966789574801624764121925 4681273045275304643272861)
                    ·
                      refine ⟨1755477391978239241227323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4681273045275304643272861 1755477391978239241227323)
                      ·
                        rfl

theorem cell23_3418780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 1, 1, 4, 3].length) (baseStart_3418780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3418780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3418780 prefixEnd_3418780 := by exact prefixLift 3418780
  have htrace : WordTrace (prefixWord ++ tailWord_3418780) baseStart_3418780 baseEnd_3418780 := by
    simpa [prefixWord, tailWord_3418780, baseEnd_3418780] using wordTrace_append hprefix tailTrace_3418780
  have hstable : (prefixWord ++ tailWord_3418780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3418780).length < 2 ^ (prefixWord ++ tailWord_3418780).sum := by decide
  have hdescent : baseEnd_3418780 < baseStart_3418780 := by decide
  rcases family_descends (prefixWord ++ tailWord_3418780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3418830 : List Nat := [4, 1, 1, 1, 3, 2, 1, 4, 1, 5]
def baseStart_3418830 : Nat := 118140960795 + 3418830 * 2 ^ 59
def prefixEnd_3418830 : Nat := 4983230072969 + 3 ^ 40 * 3418830 * 2
def baseEnd_3418830 : Nat := 585167688670321348534031

theorem tailTrace_3418830 : CollatzResearch.WordTrace tailWord_3418830 prefixEnd_3418830 585167688670321348534031 := by
  unfold tailWord_3418830
  simp only [CollatzResearch.WordTrace]
  refine ⟨15586871775521284315409743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83129982802780183015518629 15586871775521284315409743)
  ·
    refine ⟨23380307663281926473114615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15586871775521284315409743 23380307663281926473114615)
    ·
      refine ⟨35070461494922889709671923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23380307663281926473114615 35070461494922889709671923)
      ·
        refine ⟨52605692242384334564507885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35070461494922889709671923 52605692242384334564507885)
        ·
          refine ⟨19727134590894125461690457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52605692242384334564507885 19727134590894125461690457)
          ·
            refine ⟨14795350943170594096267843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19727134590894125461690457 14795350943170594096267843)
            ·
              refine ⟨22193026414755891144401765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14795350943170594096267843 22193026414755891144401765)
              ·
                refine ⟨4161192452766729589575331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22193026414755891144401765 4161192452766729589575331)
                ·
                  refine ⟨6241788679150094384362997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4161192452766729589575331 6241788679150094384362997)
                  ·
                    refine ⟨585167688670321348534031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6241788679150094384362997 585167688670321348534031)
                    ·
                      rfl

theorem cell23_3418830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 4, 1, 5].length) (baseStart_3418830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3418830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3418830 prefixEnd_3418830 := by exact prefixLift 3418830
  have htrace : WordTrace (prefixWord ++ tailWord_3418830) baseStart_3418830 baseEnd_3418830 := by
    simpa [prefixWord, tailWord_3418830, baseEnd_3418830] using wordTrace_append hprefix tailTrace_3418830
  have hstable : (prefixWord ++ tailWord_3418830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3418830).length < 2 ^ (prefixWord ++ tailWord_3418830).sum := by decide
  have hdescent : baseEnd_3418830 < baseStart_3418830 := by decide
  rcases family_descends (prefixWord ++ tailWord_3418830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3418860 : List Nat := [2, 2, 1, 1, 2, 2, 1, 6, 2, 4]
def baseStart_3418860 : Nat := 118140960795 + 3418860 * 2 ^ 59
def prefixEnd_3418860 : Nat := 4983230072969 + 3 ^ 40 * 3418860 * 2
def baseEnd_3418860 : Nat := 585172823476866309408985

theorem tailTrace_3418860 : CollatzResearch.WordTrace tailWord_3418860 prefixEnd_3418860 585172823476866309408985 := by
  unfold tailWord_3418860
  simp only [CollatzResearch.WordTrace]
  refine ⟨62348034197030794823435017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83130712262707726431246689 62348034197030794823435017)
  ·
    refine ⟨46761025647773096117576263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62348034197030794823435017 46761025647773096117576263)
    ·
      refine ⟨70141538471659644176364395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46761025647773096117576263 70141538471659644176364395)
      ·
        refine ⟨105212307707489466264546593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70141538471659644176364395 105212307707489466264546593)
        ·
          refine ⟨78909230780617099698409945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105212307707489466264546593 78909230780617099698409945)
          ·
            refine ⟨59181923085462824773807459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78909230780617099698409945 59181923085462824773807459)
            ·
              refine ⟨88772884628194237160711189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59181923085462824773807459 88772884628194237160711189)
              ·
                refine ⟨4161228966946604866908337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 88772884628194237160711189 4161228966946604866908337)
                ·
                  refine ⟨3120921725209953650181253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4161228966946604866908337 3120921725209953650181253)
                  ·
                    refine ⟨585172823476866309408985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3120921725209953650181253 585172823476866309408985)
                    ·
                      rfl

theorem cell23_3418860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 4].length) (baseStart_3418860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3418860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3418860 prefixEnd_3418860 := by exact prefixLift 3418860
  have htrace : WordTrace (prefixWord ++ tailWord_3418860) baseStart_3418860 baseEnd_3418860 := by
    simpa [prefixWord, tailWord_3418860, baseEnd_3418860] using wordTrace_append hprefix tailTrace_3418860
  have hstable : (prefixWord ++ tailWord_3418860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3418860).length < 2 ^ (prefixWord ++ tailWord_3418860).sum := by decide
  have hdescent : baseEnd_3418860 < baseStart_3418860 := by decide
  rcases family_descends (prefixWord ++ tailWord_3418860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3418861 : List Nat := [1, 5, 1, 2, 1, 1, 5, 2, 1, 1, 3]
def baseStart_3418861 : Nat := 118140960795 + 3418861 * 2 ^ 59
def prefixEnd_3418861 : Nat := 4983230072969 + 3 ^ 40 * 3418861 * 2
def baseEnd_3418861 : Nat := 1755518983911253424314451

theorem tailTrace_3418861 : CollatzResearch.WordTrace tailWord_3418861 prefixEnd_3418861 1755518983911253424314451 := by
  unfold tailWord_3418861
  simp only [CollatzResearch.WordTrace]
  refine ⟨124696104867057966817656437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83130736578038644545104291 124696104867057966817656437)
  ·
    refine ⟨11690259831286684389155291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 124696104867057966817656437 11690259831286684389155291)
    ·
      refine ⟨17535389746930026583732937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11690259831286684389155291 17535389746930026583732937)
      ·
        refine ⟨13151542310197519937799703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17535389746930026583732937 13151542310197519937799703)
        ·
          refine ⟨19727313465296279906699555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13151542310197519937799703 19727313465296279906699555)
          ·
            refine ⟨29590970197944419860049333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19727313465296279906699555 29590970197944419860049333)
            ·
              refine ⟨2774153456057289361879625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29590970197944419860049333 2774153456057289361879625)
              ·
                refine ⟨2080615092042967021409719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2774153456057289361879625 2080615092042967021409719)
                ·
                  refine ⟨3120922638064450532114579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2080615092042967021409719 3120922638064450532114579)
                  ·
                    refine ⟨4681383957096675798171869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3120922638064450532114579 4681383957096675798171869)
                    ·
                      refine ⟨1755518983911253424314451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4681383957096675798171869 1755518983911253424314451)
                      ·
                        rfl

theorem cell23_3418861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 5, 2, 1, 1, 3].length) (baseStart_3418861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3418861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3418861 prefixEnd_3418861 := by exact prefixLift 3418861
  have htrace : WordTrace (prefixWord ++ tailWord_3418861) baseStart_3418861 baseEnd_3418861 := by
    simpa [prefixWord, tailWord_3418861, baseEnd_3418861] using wordTrace_append hprefix tailTrace_3418861
  have hstable : (prefixWord ++ tailWord_3418861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3418861).length < 2 ^ (prefixWord ++ tailWord_3418861).sum := by decide
  have hdescent : baseEnd_3418861 < baseStart_3418861 := by decide
  rcases family_descends (prefixWord ++ tailWord_3418861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3418863 : List Nat := [1, 1, 2, 1, 5, 2, 1, 2, 1, 1, 6]
def baseStart_3418863 : Nat := 118140960795 + 3418863 * 2 ^ 59
def prefixEnd_3418863 : Nat := 4983230072969 + 3 ^ 40 * 3418863 * 2
def baseEnd_3418863 : Nat := 1755520010872562416489441

theorem tailTrace_3418863 : CollatzResearch.WordTrace tailWord_3418863 prefixEnd_3418863 1755520010872562416489441 := by
  unfold tailWord_3418863
  simp only [CollatzResearch.WordTrace]
  refine ⟨124696177813050721159229243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83130785208700480772819495 124696177813050721159229243)
  ·
    refine ⟨187044266719576081738843865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124696177813050721159229243 187044266719576081738843865)
    ·
      refine ⟨140283200039682061304132899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187044266719576081738843865 140283200039682061304132899)
      ·
        refine ⟨210424800059523091956199349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140283200039682061304132899 210424800059523091956199349)
        ·
          refine ⟨19727325005580289870893689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 210424800059523091956199349 19727325005580289870893689)
          ·
            refine ⟨14795493754185217403170267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19727325005580289870893689 14795493754185217403170267)
            ·
              refine ⟨22193240631277826104755401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14795493754185217403170267 22193240631277826104755401)
              ·
                refine ⟨16644930473458369578566551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22193240631277826104755401 16644930473458369578566551)
                ·
                  refine ⟨24967395710187554367849827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16644930473458369578566551 24967395710187554367849827)
                  ·
                    refine ⟨37451093565281331551774741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24967395710187554367849827 37451093565281331551774741)
                    ·
                      refine ⟨1755520010872562416489441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37451093565281331551774741 1755520010872562416489441)
                      ·
                        rfl

theorem cell23_3418863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 2, 1, 1, 6].length) (baseStart_3418863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3418863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3418863 prefixEnd_3418863 := by exact prefixLift 3418863
  have htrace : WordTrace (prefixWord ++ tailWord_3418863) baseStart_3418863 baseEnd_3418863 := by
    simpa [prefixWord, tailWord_3418863, baseEnd_3418863] using wordTrace_append hprefix tailTrace_3418863
  have hstable : (prefixWord ++ tailWord_3418863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3418863).length < 2 ^ (prefixWord ++ tailWord_3418863).sum := by decide
  have hdescent : baseEnd_3418863 < baseStart_3418863 := by decide
  rcases family_descends (prefixWord ++ tailWord_3418863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3418868 : List Nat := [2, 6, 1, 1, 3, 1, 2, 1, 6]
def baseStart_3418868 : Nat := 118140960795 + 3418868 * 2 ^ 59
def prefixEnd_3418868 : Nat := 4983230072969 + 3 ^ 40 * 3418868 * 2
def baseEnd_3418868 : Nat := 195058064252870544102991

theorem tailTrace_3418868 : CollatzResearch.WordTrace tailWord_3418868 prefixEnd_3418868 195058064252870544102991 := by
  unfold tailWord_3418868
  simp only [CollatzResearch.WordTrace]
  refine ⟨62348180089016303506580629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83130906785355071342107505 62348180089016303506580629)
  ·
    refine ⟨2922570941672639226870967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 62348180089016303506580629 2922570941672639226870967)
    ·
      refine ⟨4383856412508958840306451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2922570941672639226870967 4383856412508958840306451)
      ·
        refine ⟨6575784618763438260459677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4383856412508958840306451 6575784618763438260459677)
        ·
          refine ⟨2465919232036289347672379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6575784618763438260459677 2465919232036289347672379)
          ·
            refine ⟨3698878848054434021508569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2465919232036289347672379 3698878848054434021508569)
            ·
              refine ⟨2774159136040825516131427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3698878848054434021508569 2774159136040825516131427)
              ·
                refine ⟨4161238704061238274197141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2774159136040825516131427 4161238704061238274197141)
                ·
                  refine ⟨195058064252870544102991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4161238704061238274197141 195058064252870544102991)
                  ·
                    rfl

theorem cell23_3418868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 2, 1, 6].length) (baseStart_3418868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3418868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3418868 prefixEnd_3418868 := by exact prefixLift 3418868
  have htrace : WordTrace (prefixWord ++ tailWord_3418868) baseStart_3418868 baseEnd_3418868 := by
    simpa [prefixWord, tailWord_3418868, baseEnd_3418868] using wordTrace_append hprefix tailTrace_3418868
  have hstable : (prefixWord ++ tailWord_3418868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3418868).length < 2 ^ (prefixWord ++ tailWord_3418868).sum := by decide
  have hdescent : baseEnd_3418868 < baseStart_3418868 := by decide
  rcases family_descends (prefixWord ++ tailWord_3418868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3418870 : List Nat := [5, 1, 1, 1, 1, 2, 1, 4, 1, 1, 5]
def baseStart_3418870 : Nat := 118140960795 + 3418870 * 2 ^ 59
def prefixEnd_3418870 : Nat := 4983230072969 + 3 ^ 40 * 3418870 * 2
def baseEnd_3418870 : Nat := 1755523605237143889101909

theorem tailTrace_3418870 : CollatzResearch.WordTrace tailWord_3418870 prefixEnd_3418870 1755523605237143889101909 := by
  unfold tailWord_3418870
  simp only [CollatzResearch.WordTrace]
  refine ⟨7793527070251585084670879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 83130955416016907569822709 7793527070251585084670879)
  ·
    refine ⟨11690290605377377627006319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7793527070251585084670879 11690290605377377627006319)
    ·
      refine ⟨17535435908066066440509479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11690290605377377627006319 17535435908066066440509479)
      ·
        refine ⟨26303153862099099660764219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17535435908066066440509479 26303153862099099660764219)
        ·
          refine ⟨39454730793148649491146329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26303153862099099660764219 39454730793148649491146329)
          ·
            refine ⟨29591048094861487118359747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39454730793148649491146329 29591048094861487118359747)
            ·
              refine ⟨44386572142292230677539621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29591048094861487118359747 44386572142292230677539621)
              ·
                refine ⟨8322482276679793252038679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44386572142292230677539621 8322482276679793252038679)
                ·
                  refine ⟨12483723415019689878058019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8322482276679793252038679 12483723415019689878058019)
                  ·
                    refine ⟨18725585122529534817087029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12483723415019689878058019 18725585122529534817087029)
                    ·
                      refine ⟨1755523605237143889101909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18725585122529534817087029 1755523605237143889101909)
                      ·
                        rfl

theorem cell23_3418870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 4, 1, 1, 5].length) (baseStart_3418870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3418870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3418870 prefixEnd_3418870 := by exact prefixLift 3418870
  have htrace : WordTrace (prefixWord ++ tailWord_3418870) baseStart_3418870 baseEnd_3418870 := by
    simpa [prefixWord, tailWord_3418870, baseEnd_3418870] using wordTrace_append hprefix tailTrace_3418870
  have hstable : (prefixWord ++ tailWord_3418870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3418870).length < 2 ^ (prefixWord ++ tailWord_3418870).sum := by decide
  have hdescent : baseEnd_3418870 < baseStart_3418870 := by decide
  rcases family_descends (prefixWord ++ tailWord_3418870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3418887 : List Nat := [1, 1, 4, 4, 1, 2, 1, 1, 3, 2, 3]
def baseStart_3418887 : Nat := 118140960795 + 3418887 * 2 ^ 59
def prefixEnd_3418887 : Nat := 4983230072969 + 3 ^ 40 * 3418887 * 2
def baseEnd_3418887 : Nat := 1755532334408270322589331

theorem tailTrace_3418887 : CollatzResearch.WordTrace tailWord_3418887 prefixEnd_3418887 1755532334408270322589331 := by
  unfold tailWord_3418887
  simp only [CollatzResearch.WordTrace]
  refine ⟨124697053164963773258102915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83131368776642515505401943 124697053164963773258102915)
  ·
    refine ⟨187045579747445659887154373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124697053164963773258102915 187045579747445659887154373)
    ·
      refine ⟨35071046202646061228841445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 187045579747445659887154373 35071046202646061228841445)
      ·
        refine ⟨6575821162996136480407771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35071046202646061228841445 6575821162996136480407771)
        ·
          refine ⟨9863731744494204720611657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6575821162996136480407771 9863731744494204720611657)
          ·
            refine ⟨7397798808370653540458743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9863731744494204720611657 7397798808370653540458743)
            ·
              refine ⟨11096698212555980310688115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7397798808370653540458743 11096698212555980310688115)
              ·
                refine ⟨16645047318833970466032173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11096698212555980310688115 16645047318833970466032173)
                ·
                  refine ⟨6241892744562738924762065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16645047318833970466032173 6241892744562738924762065)
                  ·
                    refine ⟨4681419558422054193571549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6241892744562738924762065 4681419558422054193571549)
                    ·
                      refine ⟨1755532334408270322589331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4681419558422054193571549 1755532334408270322589331)
                      ·
                        rfl

theorem cell23_3418887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_3418887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3418887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3418887 prefixEnd_3418887 := by exact prefixLift 3418887
  have htrace : WordTrace (prefixWord ++ tailWord_3418887) baseStart_3418887 baseEnd_3418887 := by
    simpa [prefixWord, tailWord_3418887, baseEnd_3418887] using wordTrace_append hprefix tailTrace_3418887
  have hstable : (prefixWord ++ tailWord_3418887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3418887).length < 2 ^ (prefixWord ++ tailWord_3418887).sum := by decide
  have hdescent : baseEnd_3418887 < baseStart_3418887 := by decide
  rcases family_descends (prefixWord ++ tailWord_3418887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3418923 : List Nat := [1, 1, 1, 1, 2, 1, 2, 5, 2, 3, 4]
def baseStart_3418923 : Nat := 118140960795 + 3418923 * 2 ^ 59
def prefixEnd_3418923 : Nat := 4983230072969 + 3 ^ 40 * 3418923 * 2
def baseEnd_3418923 : Nat := 1755550819711832181739165

theorem tailTrace_3418923 : CollatzResearch.WordTrace tailWord_3418923 prefixEnd_3418923 1755550819711832181739165 := by
  unfold tailWord_3418923
  simp only [CollatzResearch.WordTrace]
  refine ⟨124698366192833351406413423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83132244128555567604275615 124698366192833351406413423)
  ·
    refine ⟨187047549289250027109620135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124698366192833351406413423 187047549289250027109620135)
    ·
      refine ⟨280571323933875040664430203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187047549289250027109620135 280571323933875040664430203)
      ·
        refine ⟨420856985900812560996645305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280571323933875040664430203 420856985900812560996645305)
        ·
          refine ⟨315642739425609420747483979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 420856985900812560996645305 315642739425609420747483979)
          ·
            refine ⟨473464109138414131121225969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 315642739425609420747483979 473464109138414131121225969)
            ·
              refine ⟨355098081853810598340919477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 473464109138414131121225969 355098081853810598340919477)
              ·
                refine ⟨33290445173794743594461201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 355098081853810598340919477 33290445173794743594461201)
                ·
                  refine ⟨24967833880346057695845901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33290445173794743594461201 24967833880346057695845901)
                  ·
                    refine ⟨9362937705129771635942213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24967833880346057695845901 9362937705129771635942213)
                    ·
                      refine ⟨1755550819711832181739165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9362937705129771635942213 1755550819711832181739165)
                      ·
                        rfl

theorem cell23_3418923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 5, 2, 3, 4].length) (baseStart_3418923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3418923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3418923 prefixEnd_3418923 := by exact prefixLift 3418923
  have htrace : WordTrace (prefixWord ++ tailWord_3418923) baseStart_3418923 baseEnd_3418923 := by
    simpa [prefixWord, tailWord_3418923, baseEnd_3418923] using wordTrace_append hprefix tailTrace_3418923
  have hstable : (prefixWord ++ tailWord_3418923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3418923).length < 2 ^ (prefixWord ++ tailWord_3418923).sum := by decide
  have hdescent : baseEnd_3418923 < baseStart_3418923 := by decide
  rcases family_descends (prefixWord ++ tailWord_3418923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3418970 : List Nat := [3, 1, 1, 2, 1, 4, 1, 2, 2, 2, 4]
def baseStart_3418970 : Nat := 118140960795 + 3418970 * 2 ^ 59
def prefixEnd_3418970 : Nat := 4983230072969 + 3 ^ 40 * 3418970 * 2
def baseEnd_3418970 : Nat := 1755574953302593497851449

theorem tailTrace_3418970 : CollatzResearch.WordTrace tailWord_3418970 prefixEnd_3418970 1755574953302593497851449 := by
  unfold tailWord_3418970
  simp only [CollatzResearch.WordTrace]
  refine ⟨31175020105915769608343591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83133386949108718955582909 31175020105915769608343591)
  ·
    refine ⟨46762530158873654412515387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31175020105915769608343591 46762530158873654412515387)
    ·
      refine ⟨70143795238310481618773081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46762530158873654412515387 70143795238310481618773081)
      ·
        refine ⟨52607846428732861214079811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70143795238310481618773081 52607846428732861214079811)
        ·
          refine ⟨78911769643099291821119717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52607846428732861214079811 78911769643099291821119717)
          ·
            refine ⟨14795956808081117216459947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78911769643099291821119717 14795956808081117216459947)
            ·
              refine ⟨22193935212121675824689921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14795956808081117216459947 22193935212121675824689921)
              ·
                refine ⟨16645451409091256868517441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22193935212121675824689921 16645451409091256868517441)
                ·
                  refine ⟨12484088556818442651388081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16645451409091256868517441 12484088556818442651388081)
                  ·
                    refine ⟨9363066417613831988541061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12484088556818442651388081 9363066417613831988541061)
                    ·
                      refine ⟨1755574953302593497851449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9363066417613831988541061 1755574953302593497851449)
                      ·
                        rfl

theorem cell23_3418970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 2, 2, 2, 4].length) (baseStart_3418970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3418970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3418970 prefixEnd_3418970 := by exact prefixLift 3418970
  have htrace : WordTrace (prefixWord ++ tailWord_3418970) baseStart_3418970 baseEnd_3418970 := by
    simpa [prefixWord, tailWord_3418970, baseEnd_3418970] using wordTrace_append hprefix tailTrace_3418970
  have hstable : (prefixWord ++ tailWord_3418970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3418970).length < 2 ^ (prefixWord ++ tailWord_3418970).sum := by decide
  have hdescent : baseEnd_3418970 < baseStart_3418970 := by decide
  rcases family_descends (prefixWord ++ tailWord_3418970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3418980 : List Nat := [2, 3, 1, 1, 4, 1, 1, 3, 7]
def baseStart_3418980 : Nat := 118140960795 + 3418980 * 2 ^ 59
def prefixEnd_3418980 : Nat := 4983230072969 + 3 ^ 40 * 3418980 * 2
def baseEnd_3418980 : Nat := 195064454234348717636267

theorem tailTrace_3418980 : CollatzResearch.WordTrace tailWord_3418980 prefixEnd_3418980 195064454234348717636267 := by
  unfold tailWord_3418980
  simp only [CollatzResearch.WordTrace]
  refine ⟨62350222576813425070619197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83133630102417900094158929 62350222576813425070619197)
  ·
    refine ⟨23381333466305034401482199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62350222576813425070619197 23381333466305034401482199)
    ·
      refine ⟨35072000199457551602223299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23381333466305034401482199 35072000199457551602223299)
      ·
        refine ⟨52608000299186327403334949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35072000199457551602223299 52608000299186327403334949)
        ·
          refine ⟨9864000056097436388125303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52608000299186327403334949 9864000056097436388125303)
          ·
            refine ⟨14796000084146154582187955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9864000056097436388125303 14796000084146154582187955)
            ·
              refine ⟨22194000126219231873281933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14796000084146154582187955 22194000126219231873281933)
              ·
                refine ⟨8322750047332211952480725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22194000126219231873281933 8322750047332211952480725)
                ·
                  refine ⟨195064454234348717636267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8322750047332211952480725 195064454234348717636267)
                  ·
                    rfl

theorem cell23_3418980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 3, 7].length) (baseStart_3418980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3418980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3418980 prefixEnd_3418980 := by exact prefixLift 3418980
  have htrace : WordTrace (prefixWord ++ tailWord_3418980) baseStart_3418980 baseEnd_3418980 := by
    simpa [prefixWord, tailWord_3418980, baseEnd_3418980] using wordTrace_append hprefix tailTrace_3418980
  have hstable : (prefixWord ++ tailWord_3418980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3418980).length < 2 ^ (prefixWord ++ tailWord_3418980).sum := by decide
  have hdescent : baseEnd_3418980 < baseStart_3418980 := by decide
  rcases family_descends (prefixWord ++ tailWord_3418980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3419087 : List Nat := [1, 1, 2, 1, 1, 7, 2, 2, 6]
def baseStart_3419087 : Nat := 118140960795 + 3419087 * 2 ^ 59
def prefixEnd_3419087 : Nat := 4983230072969 + 3 ^ 40 * 3419087 * 2
def baseEnd_3419087 : Nat := 195070558948796615565379

theorem tailTrace_3419087 : CollatzResearch.WordTrace tailWord_3419087 prefixEnd_3419087 195070558948796615565379 := by
  unfold tailWord_3419087
  simp only [CollatzResearch.WordTrace]
  refine ⟨124704347764239207415383515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83136231842826138276922343 124704347764239207415383515)
  ·
    refine ⟨187056521646358811123075273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124704347764239207415383515 187056521646358811123075273)
    ·
      refine ⟨140292391234769108342306455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187056521646358811123075273 140292391234769108342306455)
      ·
        refine ⟨210438586852153662513459683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140292391234769108342306455 210438586852153662513459683)
        ·
          refine ⟨315657880278230493770189525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210438586852153662513459683 315657880278230493770189525)
          ·
            refine ⟨7398231569021027197738817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 315657880278230493770189525 7398231569021027197738817)
            ·
              refine ⟨5548673676765770398304113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7398231569021027197738817 5548673676765770398304113)
              ·
                refine ⟨4161505257574327798728085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5548673676765770398304113 4161505257574327798728085)
                ·
                  refine ⟨195070558948796615565379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4161505257574327798728085 195070558948796615565379)
                  ·
                    rfl

theorem cell23_3419087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 2, 2, 6].length) (baseStart_3419087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3419087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3419087 prefixEnd_3419087 := by exact prefixLift 3419087
  have htrace : WordTrace (prefixWord ++ tailWord_3419087) baseStart_3419087 baseEnd_3419087 := by
    simpa [prefixWord, tailWord_3419087, baseEnd_3419087] using wordTrace_append hprefix tailTrace_3419087
  have hstable : (prefixWord ++ tailWord_3419087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3419087).length < 2 ^ (prefixWord ++ tailWord_3419087).sum := by decide
  have hdescent : baseEnd_3419087 < baseStart_3419087 := by decide
  rcases family_descends (prefixWord ++ tailWord_3419087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3419114 : List Nat := [3, 1, 3, 1, 2, 2, 1, 1, 5, 1, 3]
def baseStart_3419114 : Nat := 118140960795 + 3419114 * 2 ^ 59
def prefixEnd_3419114 : Nat := 4983230072969 + 3 ^ 40 * 3419114 * 2
def baseEnd_3419114 : Nat := 1755648894516840934450787

theorem tailTrace_3419114 : CollatzResearch.WordTrace tailWord_3419114 prefixEnd_3419114 1755648894516840934450787 := by
  unfold tailWord_3419114
  simp only [CollatzResearch.WordTrace]
  refine ⟨31176333133785347756654099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83136888356760927351077597 31176333133785347756654099)
  ·
    refine ⟨46764499700678021634981149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31176333133785347756654099 46764499700678021634981149)
    ·
      refine ⟨17536687387754258113117931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46764499700678021634981149 17536687387754258113117931)
      ·
        refine ⟨26305031081631387169676897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17536687387754258113117931 26305031081631387169676897)
        ·
          refine ⟨19728773311223540377257673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26305031081631387169676897 19728773311223540377257673)
          ·
            refine ⟨14796579983417655282943255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19728773311223540377257673 14796579983417655282943255)
            ·
              refine ⟨22194869975126482924414883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14796579983417655282943255 22194869975126482924414883)
              ·
                refine ⟨33292304962689724386622325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22194869975126482924414883 33292304962689724386622325)
                ·
                  refine ⟨3121153590252161661245843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33292304962689724386622325 3121153590252161661245843)
                  ·
                    refine ⟨4681730385378242491868765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3121153590252161661245843 4681730385378242491868765)
                    ·
                      refine ⟨1755648894516840934450787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4681730385378242491868765 1755648894516840934450787)
                      ·
                        rfl

theorem cell23_3419114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 1, 5, 1, 3].length) (baseStart_3419114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3419114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3419114 prefixEnd_3419114 := by exact prefixLift 3419114
  have htrace : WordTrace (prefixWord ++ tailWord_3419114) baseStart_3419114 baseEnd_3419114 := by
    simpa [prefixWord, tailWord_3419114, baseEnd_3419114] using wordTrace_append hprefix tailTrace_3419114
  have hstable : (prefixWord ++ tailWord_3419114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3419114).length < 2 ^ (prefixWord ++ tailWord_3419114).sum := by decide
  have hdescent : baseEnd_3419114 < baseStart_3419114 := by decide
  rcases family_descends (prefixWord ++ tailWord_3419114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3419118 : List Nat := [4, 1, 2, 1, 5, 1, 1, 1, 2, 2, 3]
def baseStart_3419118 : Nat := 118140960795 + 3419118 * 2 ^ 59
def prefixEnd_3419118 : Nat := 4983230072969 + 3 ^ 40 * 3419118 * 2
def baseEnd_3419118 : Nat := 1755650948439458918800769

theorem tailTrace_3419118 : CollatzResearch.WordTrace tailWord_3419118 prefixEnd_3419118 1755650948439458918800769 := by
  unfold tailWord_3419118
  simp only [CollatzResearch.WordTrace]
  refine ⟨15588184803390862463720251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83136985618084599806508005 15588184803390862463720251)
  ·
    refine ⟨23382277205086293695580377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15588184803390862463720251 23382277205086293695580377)
    ·
      refine ⟨17536707903814720271685283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23382277205086293695580377 17536707903814720271685283)
      ·
        refine ⟨26305061855722080407527925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17536707903814720271685283 26305061855722080407527925)
        ·
          refine ⟨2466099548973945038205743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26305061855722080407527925 2466099548973945038205743)
          ·
            refine ⟨3699149323460917557308615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2466099548973945038205743 3699149323460917557308615)
            ·
              refine ⟨5548723985191376335962923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3699149323460917557308615 5548723985191376335962923)
              ·
                refine ⟨8323085977787064503944385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5548723985191376335962923 8323085977787064503944385)
                ·
                  refine ⟨6242314483340298377958289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8323085977787064503944385 6242314483340298377958289)
                  ·
                    refine ⟨4681735862505223783468717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6242314483340298377958289 4681735862505223783468717)
                    ·
                      refine ⟨1755650948439458918800769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4681735862505223783468717 1755650948439458918800769)
                      ·
                        rfl

theorem cell23_3419118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 1, 1, 2, 2, 3].length) (baseStart_3419118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3419118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3419118 prefixEnd_3419118 := by exact prefixLift 3419118
  have htrace : WordTrace (prefixWord ++ tailWord_3419118) baseStart_3419118 baseEnd_3419118 := by
    simpa [prefixWord, tailWord_3419118, baseEnd_3419118] using wordTrace_append hprefix tailTrace_3419118
  have hstable : (prefixWord ++ tailWord_3419118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3419118).length < 2 ^ (prefixWord ++ tailWord_3419118).sum := by decide
  have hdescent : baseEnd_3419118 < baseStart_3419118 := by decide
  rcases family_descends (prefixWord ++ tailWord_3419118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3419125 : List Nat := [1, 3, 5, 2, 1, 1, 2, 3, 1, 4]
def baseStart_3419125 : Nat := 118140960795 + 3419125 * 2 ^ 59
def prefixEnd_3419125 : Nat := 4983230072969 + 3 ^ 40 * 3419125 * 2
def baseEnd_3419125 : Nat := 585218180934680130471079

theorem tailTrace_3419125 : CollatzResearch.WordTrace tailWord_3419125 prefixEnd_3419125 585218180934680130471079 := by
  unfold tailWord_3419125
  simp only [CollatzResearch.WordTrace]
  refine ⟨124705733738101539905266829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83137155825401026603511219 124705733738101539905266829)
  ·
    refine ⟨46764650151788077464475061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124705733738101539905266829 46764650151788077464475061)
    ·
      refine ⟨4384185951730132262294537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46764650151788077464475061 4384185951730132262294537)
      ·
        refine ⟨3288139463797599196720903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4384185951730132262294537 3288139463797599196720903)
        ·
          refine ⟨4932209195696398795081355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3288139463797599196720903 4932209195696398795081355)
          ·
            refine ⟨7398313793544598192622033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4932209195696398795081355 7398313793544598192622033)
            ·
              refine ⟨5548735345158448644466525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7398313793544598192622033 5548735345158448644466525)
              ·
                refine ⟨2080775754434418241674947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5548735345158448644466525 2080775754434418241674947)
                ·
                  refine ⟨3121163631651627362512421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2080775754434418241674947 3121163631651627362512421)
                  ·
                    refine ⟨585218180934680130471079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3121163631651627362512421 585218180934680130471079)
                    ·
                      rfl

theorem cell23_3419125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_3419125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3419125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3419125 prefixEnd_3419125 := by exact prefixLift 3419125
  have htrace : WordTrace (prefixWord ++ tailWord_3419125) baseStart_3419125 baseEnd_3419125 := by
    simpa [prefixWord, tailWord_3419125, baseEnd_3419125] using wordTrace_append hprefix tailTrace_3419125
  have hstable : (prefixWord ++ tailWord_3419125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3419125).length < 2 ^ (prefixWord ++ tailWord_3419125).sum := by decide
  have hdescent : baseEnd_3419125 < baseStart_3419125 := by decide
  rcases family_descends (prefixWord ++ tailWord_3419125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3419138 : List Nat := [3, 4, 1, 3, 1, 2, 1, 2, 6]
def baseStart_3419138 : Nat := 118140960795 + 3419138 * 2 ^ 59
def prefixEnd_3419138 : Nat := 4983230072969 + 3 ^ 40 * 3419138 * 2
def baseEnd_3419138 : Nat := 195073468672505426727853

theorem tailTrace_3419138 : CollatzResearch.WordTrace tailWord_3419138 prefixEnd_3419138 195073468672505426727853 := by
  unfold tailWord_3419138
  simp only [CollatzResearch.WordTrace]
  refine ⟨31176551971763610781372517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83137471924702962083660045 31176551971763610781372517)
  ·
    refine ⟨5845603494705677021507347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31176551971763610781372517 5845603494705677021507347)
    ·
      refine ⟨8768405242058515532261021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5845603494705677021507347 8768405242058515532261021)
      ·
        refine ⟨3288151965771943324597883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8768405242058515532261021 3288151965771943324597883)
        ·
          refine ⟨4932227948657914986896825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3288151965771943324597883 4932227948657914986896825)
          ·
            refine ⟨3699170961493436240172619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4932227948657914986896825 3699170961493436240172619)
            ·
              refine ⟨5548756442240154360258929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3699170961493436240172619 5548756442240154360258929)
              ·
                refine ⟨4161567331680115770194197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5548756442240154360258929 4161567331680115770194197)
                ·
                  refine ⟨195073468672505426727853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4161567331680115770194197 195073468672505426727853)
                  ·
                    rfl

theorem cell23_3419138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 1, 2, 6].length) (baseStart_3419138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3419138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3419138 prefixEnd_3419138 := by exact prefixLift 3419138
  have htrace : WordTrace (prefixWord ++ tailWord_3419138) baseStart_3419138 baseEnd_3419138 := by
    simpa [prefixWord, tailWord_3419138, baseEnd_3419138] using wordTrace_append hprefix tailTrace_3419138
  have hstable : (prefixWord ++ tailWord_3419138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3419138).length < 2 ^ (prefixWord ++ tailWord_3419138).sum := by decide
  have hdescent : baseEnd_3419138 < baseStart_3419138 := by decide
  rcases family_descends (prefixWord ++ tailWord_3419138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3419157 : List Nat := [1, 3, 2, 1, 4, 1, 1, 1, 3, 1, 5]
def baseStart_3419157 : Nat := 118140960795 + 3419157 * 2 ^ 59
def prefixEnd_3419157 : Nat := 4983230072969 + 3 ^ 40 * 3419157 * 2
def baseEnd_3419157 : Nat := 1755670974184984266213089

theorem tailTrace_3419157 : CollatzResearch.WordTrace tailWord_3419157 prefixEnd_3419157 1755670974184984266213089 := by
  unfold tailWord_3419157
  simp only [CollatzResearch.WordTrace]
  refine ⟨124706900873985609370431725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83137933915990406246954483 124706900873985609370431725)
  ·
    refine ⟨46765087827744603513911897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124706900873985609370431725 46765087827744603513911897)
    ·
      refine ⟨35073815870808452635433923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46765087827744603513911897 35073815870808452635433923)
      ·
        refine ⟨52610723806212678953150885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35073815870808452635433923 52610723806212678953150885)
        ·
          refine ⟨9864510713664877303715791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52610723806212678953150885 9864510713664877303715791)
          ·
            refine ⟨14796766070497315955573687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9864510713664877303715791 14796766070497315955573687)
            ·
              refine ⟨22195149105745973933360531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14796766070497315955573687 22195149105745973933360531)
              ·
                refine ⟨33292723658618960900040797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22195149105745973933360531 33292723658618960900040797)
                ·
                  refine ⟨12484771371982110337515299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33292723658618960900040797 12484771371982110337515299)
                  ·
                    refine ⟨18727157057973165506272949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12484771371982110337515299 18727157057973165506272949)
                    ·
                      refine ⟨1755670974184984266213089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18727157057973165506272949 1755670974184984266213089)
                      ·
                        rfl

theorem cell23_3419157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 1, 3, 1, 5].length) (baseStart_3419157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3419157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3419157 prefixEnd_3419157 := by exact prefixLift 3419157
  have htrace : WordTrace (prefixWord ++ tailWord_3419157) baseStart_3419157 baseEnd_3419157 := by
    simpa [prefixWord, tailWord_3419157, baseEnd_3419157] using wordTrace_append hprefix tailTrace_3419157
  have hstable : (prefixWord ++ tailWord_3419157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3419157).length < 2 ^ (prefixWord ++ tailWord_3419157).sum := by decide
  have hdescent : baseEnd_3419157 < baseStart_3419157 := by decide
  rcases family_descends (prefixWord ++ tailWord_3419157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3419167 : List Nat := [1, 1, 2, 4, 1, 4, 1, 1, 1, 1, 6]
def baseStart_3419167 : Nat := 118140960795 + 3419167 * 2 ^ 59
def prefixEnd_3419167 : Nat := 4983230072969 + 3 ^ 40 * 3419167 * 2
def baseEnd_3419167 : Nat := 1755676108991529227088043

theorem tailTrace_3419167 : CollatzResearch.WordTrace tailWord_3419167 prefixEnd_3419167 1755676108991529227088043 := by
  unfold tailWord_3419167
  simp only [CollatzResearch.WordTrace]
  refine ⟨124707265603949381078295755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83138177069299587385530503 124707265603949381078295755)
  ·
    refine ⟨187060898405924071617443633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124707265603949381078295755 187060898405924071617443633)
    ·
      refine ⟨140295673804443053713082725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187060898405924071617443633 140295673804443053713082725)
      ·
        refine ⟨26305438838333072571203011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 140295673804443053713082725 26305438838333072571203011)
        ·
          refine ⟨39458158257499608856804517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26305438838333072571203011 39458158257499608856804517)
          ·
            refine ⟨7398404673281176660650847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39458158257499608856804517 7398404673281176660650847)
            ·
              refine ⟨11097607009921764990976271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7398404673281176660650847 11097607009921764990976271)
              ·
                refine ⟨16646410514882647486464407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11097607009921764990976271 16646410514882647486464407)
                ·
                  refine ⟨24969615772323971229696611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16646410514882647486464407 24969615772323971229696611)
                  ·
                    refine ⟨37454423658485956844544917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24969615772323971229696611 37454423658485956844544917)
                    ·
                      refine ⟨1755676108991529227088043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37454423658485956844544917 1755676108991529227088043)
                      ·
                        rfl

theorem cell23_3419167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 1, 1, 1, 6].length) (baseStart_3419167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3419167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3419167 prefixEnd_3419167 := by exact prefixLift 3419167
  have htrace : WordTrace (prefixWord ++ tailWord_3419167) baseStart_3419167 baseEnd_3419167 := by
    simpa [prefixWord, tailWord_3419167, baseEnd_3419167] using wordTrace_append hprefix tailTrace_3419167
  have hstable : (prefixWord ++ tailWord_3419167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3419167).length < 2 ^ (prefixWord ++ tailWord_3419167).sum := by decide
  have hdescent : baseEnd_3419167 < baseStart_3419167 := by decide
  rcases family_descends (prefixWord ++ tailWord_3419167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3419171 : List Nat := [1, 1, 1, 4, 3, 2, 2, 2, 3, 2, 2]
def baseStart_3419171 : Nat := 118140960795 + 3419171 * 2 ^ 59
def prefixEnd_3419171 : Nat := 4983230072969 + 3 ^ 40 * 3419171 * 2
def baseEnd_3419171 : Nat := 1755678162914147211438025

theorem tailTrace_3419171 : CollatzResearch.WordTrace tailWord_3419171 prefixEnd_3419171 1755678162914147211438025 := by
  unfold tailWord_3419171
  simp only [CollatzResearch.WordTrace]
  refine ⟨124707411495934889761441367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83138274330623259840960911 124707411495934889761441367)
  ·
    refine ⟨187061117243902334642162051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124707411495934889761441367 187061117243902334642162051)
    ·
      refine ⟨280591675865853501963243077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187061117243902334642162051 280591675865853501963243077)
      ·
        refine ⟨52610939224847531618108077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 280591675865853501963243077 52610939224847531618108077)
        ·
          refine ⟨19729102209317824356790529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52610939224847531618108077 19729102209317824356790529)
          ·
            refine ⟨14796826656988368267592897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19729102209317824356790529 14796826656988368267592897)
            ·
              refine ⟨11097619992741276200694673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14796826656988368267592897 11097619992741276200694673)
              ·
                refine ⟨8323214994555957150521005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11097619992741276200694673 8323214994555957150521005)
                ·
                  refine ⟨3121205622958483931445377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8323214994555957150521005 3121205622958483931445377)
                  ·
                    refine ⟨2340904217218862948584033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3121205622958483931445377 2340904217218862948584033)
                    ·
                      refine ⟨1755678162914147211438025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2340904217218862948584033 1755678162914147211438025)
                      ·
                        rfl

theorem cell23_3419171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 2, 3, 2, 2].length) (baseStart_3419171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3419171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3419171 prefixEnd_3419171 := by exact prefixLift 3419171
  have htrace : WordTrace (prefixWord ++ tailWord_3419171) baseStart_3419171 baseEnd_3419171 := by
    simpa [prefixWord, tailWord_3419171, baseEnd_3419171] using wordTrace_append hprefix tailTrace_3419171
  have hstable : (prefixWord ++ tailWord_3419171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3419171).length < 2 ^ (prefixWord ++ tailWord_3419171).sum := by decide
  have hdescent : baseEnd_3419171 < baseStart_3419171 := by decide
  rcases family_descends (prefixWord ++ tailWord_3419171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3419187 : List Nat := [1, 1, 1, 2, 4, 1, 1, 3, 3, 3, 3]
def baseStart_3419187 : Nat := 118140960795 + 3419187 * 2 ^ 59
def prefixEnd_3419187 : Nat := 4983230072969 + 3 ^ 40 * 3419187 * 2
def baseEnd_3419187 : Nat := 1755686378604619148837951

theorem tailTrace_3419187 : CollatzResearch.WordTrace tailWord_3419187 prefixEnd_3419187 1755686378604619148837951 := by
  unfold tailWord_3419187
  simp only [CollatzResearch.WordTrace]
  refine ⟨124707995063876924494023815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83138663375917949662682543 124707995063876924494023815)
  ·
    refine ⟨187061992595815386741035723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124707995063876924494023815 187061992595815386741035723)
    ·
      refine ⟨280592988893723080111553585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187061992595815386741035723 280592988893723080111553585)
      ·
        refine ⟨210444741670292310083665189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 280592988893723080111553585 210444741670292310083665189)
        ·
          refine ⟨39458389063179808140687223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 210444741670292310083665189 39458389063179808140687223)
          ·
            refine ⟨59187583594769712211030835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39458389063179808140687223 59187583594769712211030835)
            ·
              refine ⟨88781375392154568316546253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59187583594769712211030835 88781375392154568316546253)
              ·
                refine ⟨33293015772057963118704845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88781375392154568316546253 33293015772057963118704845)
                ·
                  refine ⟨12484880914521736169514317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33293015772057963118704845 12484880914521736169514317)
                  ·
                    refine ⟨4681830342945651063567869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12484880914521736169514317 4681830342945651063567869)
                    ·
                      refine ⟨1755686378604619148837951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4681830342945651063567869 1755686378604619148837951)
                      ·
                        rfl

theorem cell23_3419187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 3, 3, 3, 3].length) (baseStart_3419187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3419187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3419187 prefixEnd_3419187 := by exact prefixLift 3419187
  have htrace : WordTrace (prefixWord ++ tailWord_3419187) baseStart_3419187 baseEnd_3419187 := by
    simpa [prefixWord, tailWord_3419187, baseEnd_3419187] using wordTrace_append hprefix tailTrace_3419187
  have hstable : (prefixWord ++ tailWord_3419187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3419187).length < 2 ^ (prefixWord ++ tailWord_3419187).sum := by decide
  have hdescent : baseEnd_3419187 < baseStart_3419187 := by decide
  rcases family_descends (prefixWord ++ tailWord_3419187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3419221 : List Nat := [1, 3, 2, 2, 1, 2, 3, 3, 2, 1, 3]
def baseStart_3419221 : Nat := 118140960795 + 3419221 * 2 ^ 59
def prefixEnd_3419221 : Nat := 4983230072969 + 3 ^ 40 * 3419221 * 2
def baseEnd_3419221 : Nat := 1755703836946872015812795

theorem tailTrace_3419221 : CollatzResearch.WordTrace tailWord_3419221 prefixEnd_3419221 1755703836946872015812795 := by
  unfold tailWord_3419221
  simp only [CollatzResearch.WordTrace]
  refine ⟨124709235145753748300761517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83139490097169165533841011 124709235145753748300761517)
  ·
    refine ⟨46765963179657655612785569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124709235145753748300761517 46765963179657655612785569)
    ·
      refine ⟨35074472384743241709589177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46765963179657655612785569 35074472384743241709589177)
      ·
        refine ⟨26305854288557431282191883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35074472384743241709589177 26305854288557431282191883)
        ·
          refine ⟨39458781432836146923287825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26305854288557431282191883 39458781432836146923287825)
          ·
            refine ⟨29594086074627110192465869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39458781432836146923287825 29594086074627110192465869)
            ·
              refine ⟨11097782277985166322174701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29594086074627110192465869 11097782277985166322174701)
              ·
                refine ⟨4161668354244437370815513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11097782277985166322174701 4161668354244437370815513)
                ·
                  refine ⟨3121251265683328028111635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4161668354244437370815513 3121251265683328028111635)
                  ·
                    refine ⟨4681876898524992042167453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3121251265683328028111635 4681876898524992042167453)
                    ·
                      refine ⟨1755703836946872015812795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4681876898524992042167453 1755703836946872015812795)
                      ·
                        rfl

theorem cell23_3419221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 3, 2, 1, 3].length) (baseStart_3419221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3419221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3419221 prefixEnd_3419221 := by exact prefixLift 3419221
  have htrace : WordTrace (prefixWord ++ tailWord_3419221) baseStart_3419221 baseEnd_3419221 := by
    simpa [prefixWord, tailWord_3419221, baseEnd_3419221] using wordTrace_append hprefix tailTrace_3419221
  have hstable : (prefixWord ++ tailWord_3419221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3419221).length < 2 ^ (prefixWord ++ tailWord_3419221).sum := by decide
  have hdescent : baseEnd_3419221 < baseStart_3419221 := by decide
  rcases family_descends (prefixWord ++ tailWord_3419221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3419222 : List Nat := [5, 2, 2, 1, 3, 1, 1, 2, 1, 1, 4]
def baseStart_3419222 : Nat := 118140960795 + 3419222 * 2 ^ 59
def prefixEnd_3419222 : Nat := 4983230072969 + 3 ^ 40 * 3419222 * 2
def baseEnd_3419222 : Nat := 1755704350427526511900291

theorem tailTrace_3419222 : CollatzResearch.WordTrace tailWord_3419222 prefixEnd_3419222 1755704350427526511900291 := by
  unfold tailWord_3419222
  simp only [CollatzResearch.WordTrace]
  refine ⟨7794329476171882841971745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 83139514412500083647698613 7794329476171882841971745)
  ·
    refine ⟨5845747107128912131478809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7794329476171882841971745 5845747107128912131478809)
    ·
      refine ⟨4384310330346684098609107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5845747107128912131478809 4384310330346684098609107)
      ·
        refine ⟨6576465495520026147913661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4384310330346684098609107 6576465495520026147913661)
        ·
          refine ⟨2466174560820009805467623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6576465495520026147913661 2466174560820009805467623)
          ·
            refine ⟨3699261841230014708201435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2466174560820009805467623 3699261841230014708201435)
            ·
              refine ⟨5548892761845022062302153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3699261841230014708201435 5548892761845022062302153)
              ·
                refine ⟨4161669571383766546726615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5548892761845022062302153 4161669571383766546726615)
                ·
                  refine ⟨6242504357075649820089923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4161669571383766546726615 6242504357075649820089923)
                  ·
                    refine ⟨9363756535613474730134885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6242504357075649820089923 9363756535613474730134885)
                    ·
                      refine ⟨1755704350427526511900291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9363756535613474730134885 1755704350427526511900291)
                      ·
                        rfl

theorem cell23_3419222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 1, 2, 1, 1, 4].length) (baseStart_3419222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3419222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3419222 prefixEnd_3419222 := by exact prefixLift 3419222
  have htrace : WordTrace (prefixWord ++ tailWord_3419222) baseStart_3419222 baseEnd_3419222 := by
    simpa [prefixWord, tailWord_3419222, baseEnd_3419222] using wordTrace_append hprefix tailTrace_3419222
  have hstable : (prefixWord ++ tailWord_3419222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3419222).length < 2 ^ (prefixWord ++ tailWord_3419222).sum := by decide
  have hdescent : baseEnd_3419222 < baseStart_3419222 := by decide
  rcases family_descends (prefixWord ++ tailWord_3419222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3419247 : List Nat := [1, 1, 2, 1, 3, 3, 1, 3, 2, 1, 5]
def baseStart_3419247 : Nat := 118140960795 + 3419247 * 2 ^ 59
def prefixEnd_3419247 : Nat := 4983230072969 + 3 ^ 40 * 3419247 * 2
def baseEnd_3419247 : Nat := 1755717187443888914087675

theorem tailTrace_3419247 : CollatzResearch.WordTrace tailWord_3419247 prefixEnd_3419247 1755717187443888914087675 := by
  unfold tailWord_3419247
  simp only [CollatzResearch.WordTrace]
  refine ⟨124710183443659554741207995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83140122295773036494138663 124710183443659554741207995)
  ·
    refine ⟨187065275165489332111811993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124710183443659554741207995 187065275165489332111811993)
    ·
      refine ⟨140298956374116999083858995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187065275165489332111811993 140298956374116999083858995)
      ·
        refine ⟨210448434561175498625788493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140298956374116999083858995 210448434561175498625788493)
        ·
          refine ⟨78918162960440811984670685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 210448434561175498625788493 78918162960440811984670685)
          ·
            refine ⟨29594311110165304494251507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78918162960440811984670685 29594311110165304494251507)
            ·
              refine ⟨44391466665247956741377261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29594311110165304494251507 44391466665247956741377261)
              ·
                refine ⟨16646799999467983778016473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44391466665247956741377261 16646799999467983778016473)
                ·
                  refine ⟨12485099999600987833512355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16646799999467983778016473 12485099999600987833512355)
                  ·
                    refine ⟨18727649999401481750268533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12485099999600987833512355 18727649999401481750268533)
                    ·
                      refine ⟨1755717187443888914087675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18727649999401481750268533 1755717187443888914087675)
                      ·
                        rfl

theorem cell23_3419247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 3, 2, 1, 5].length) (baseStart_3419247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3419247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3419247 prefixEnd_3419247 := by exact prefixLift 3419247
  have htrace : WordTrace (prefixWord ++ tailWord_3419247) baseStart_3419247 baseEnd_3419247 := by
    simpa [prefixWord, tailWord_3419247, baseEnd_3419247] using wordTrace_append hprefix tailTrace_3419247
  have hstable : (prefixWord ++ tailWord_3419247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3419247).length < 2 ^ (prefixWord ++ tailWord_3419247).sum := by decide
  have hdescent : baseEnd_3419247 < baseStart_3419247 := by decide
  rcases family_descends (prefixWord ++ tailWord_3419247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3419248 : List Nat := [2, 1, 1, 1, 5, 1, 5, 1, 1, 3, 2]
def baseStart_3419248 : Nat := 118140960795 + 3419248 * 2 ^ 59
def prefixEnd_3419248 : Nat := 4983230072969 + 3 ^ 40 * 3419248 * 2
def baseEnd_3419248 : Nat := 1755717700924543410175171

theorem tailTrace_3419248 : CollatzResearch.WordTrace tailWord_3419248 prefixEnd_3419248 1755717700924543410175171 := by
  unfold tailWord_3419248
  simp only [CollatzResearch.WordTrace]
  refine ⟨62355109958327965955997199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83140146611103954607996265 62355109958327965955997199)
  ·
    refine ⟨93532664937491948933995799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62355109958327965955997199 93532664937491948933995799)
    ·
      refine ⟨140298997406237923400993699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93532664937491948933995799 140298997406237923400993699)
      ·
        refine ⟨210448496109356885101490549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140298997406237923400993699 210448496109356885101490549)
        ·
          refine ⟨19729546510252207978264739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 210448496109356885101490549 19729546510252207978264739)
          ·
            refine ⟨29594319765378311967397109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19729546510252207978264739 29594319765378311967397109)
            ·
              refine ⟨2774467478004216746943479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29594319765378311967397109 2774467478004216746943479)
              ·
                refine ⟨4161701217006325120415219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2774467478004216746943479 4161701217006325120415219)
                ·
                  refine ⟨6242551825509487680622829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4161701217006325120415219 6242551825509487680622829)
                  ·
                    refine ⟨2340956934566057880233561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6242551825509487680622829 2340956934566057880233561)
                    ·
                      refine ⟨1755717700924543410175171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2340956934566057880233561 1755717700924543410175171)
                      ·
                        rfl

theorem cell23_3419248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 5, 1, 1, 3, 2].length) (baseStart_3419248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3419248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3419248 prefixEnd_3419248 := by exact prefixLift 3419248
  have htrace : WordTrace (prefixWord ++ tailWord_3419248) baseStart_3419248 baseEnd_3419248 := by
    simpa [prefixWord, tailWord_3419248, baseEnd_3419248] using wordTrace_append hprefix tailTrace_3419248
  have hstable : (prefixWord ++ tailWord_3419248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3419248).length < 2 ^ (prefixWord ++ tailWord_3419248).sum := by decide
  have hdescent : baseEnd_3419248 < baseStart_3419248 := by decide
  rcases family_descends (prefixWord ++ tailWord_3419248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3419254 : List Nat := [5, 1, 1, 2, 1, 1, 2, 2, 2, 6]
def baseStart_3419254 : Nat := 118140960795 + 3419254 * 2 ^ 59
def prefixEnd_3419254 : Nat := 4983230072969 + 3 ^ 40 * 3419254 * 2
def baseEnd_3419254 : Nat := 585240260602823462233381

theorem tailTrace_3419254 : CollatzResearch.WordTrace tailWord_3419254 prefixEnd_3419254 585240260602823462233381 := by
  unfold tailWord_3419254
  simp only [CollatzResearch.WordTrace]
  refine ⟨7794402422164637183544551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 83140292503089463291141877 7794402422164637183544551)
  ·
    refine ⟨11691603633246955775316827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7794402422164637183544551 11691603633246955775316827)
    ·
      refine ⟨17537405449870433662975241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11691603633246955775316827 17537405449870433662975241)
      ·
        refine ⟨13153054087402825247231431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17537405449870433662975241 13153054087402825247231431)
        ·
          refine ⟨19729581131104237870847147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13153054087402825247231431 19729581131104237870847147)
          ·
            refine ⟨29594371696656356806270721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19729581131104237870847147 29594371696656356806270721)
            ·
              refine ⟨22195778772492267604703041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29594371696656356806270721 22195778772492267604703041)
              ·
                refine ⟨16646834079369200703527281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22195778772492267604703041 16646834079369200703527281)
                ·
                  refine ⟨12485125559526900527645461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16646834079369200703527281 12485125559526900527645461)
                  ·
                    refine ⟨585240260602823462233381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12485125559526900527645461 585240260602823462233381)
                    ·
                      rfl

theorem cell23_3419254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 2, 2, 6].length) (baseStart_3419254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3419254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3419254 prefixEnd_3419254 := by exact prefixLift 3419254
  have htrace : WordTrace (prefixWord ++ tailWord_3419254) baseStart_3419254 baseEnd_3419254 := by
    simpa [prefixWord, tailWord_3419254, baseEnd_3419254] using wordTrace_append hprefix tailTrace_3419254
  have hstable : (prefixWord ++ tailWord_3419254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3419254).length < 2 ^ (prefixWord ++ tailWord_3419254).sum := by decide
  have hdescent : baseEnd_3419254 < baseStart_3419254 := by decide
  rcases family_descends (prefixWord ++ tailWord_3419254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3419267 : List Nat := [1, 1, 1, 3, 3, 2, 2, 3, 7]
def baseStart_3419267 : Nat := 118140960795 + 3419267 * 2 ^ 59
def prefixEnd_3419267 : Nat := 4983230072969 + 3 ^ 40 * 3419267 * 2
def baseEnd_3419267 : Nat := 195080828561886537315287

theorem tailTrace_3419267 : CollatzResearch.WordTrace tailWord_3419267 prefixEnd_3419267 195080828561886537315287 := by
  unfold tailWord_3419267
  simp only [CollatzResearch.WordTrace]
  refine ⟨124710912903587098156936055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83140608602391398771290703 124710912903587098156936055)
  ·
    refine ⟨187066369355380647235404083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124710912903587098156936055 187066369355380647235404083)
    ·
      refine ⟨280599554033070970853106125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187066369355380647235404083 280599554033070970853106125)
      ·
        refine ⟨105224832762401614069914797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 280599554033070970853106125 105224832762401614069914797)
        ·
          refine ⟨39459312285900605276218049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105224832762401614069914797 39459312285900605276218049)
          ·
            refine ⟨29594484214425453957163537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39459312285900605276218049 29594484214425453957163537)
            ·
              refine ⟨22195863160819090467872653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29594484214425453957163537 22195863160819090467872653)
              ·
                refine ⟨8323448685307158925452245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22195863160819090467872653 8323448685307158925452245)
                ·
                  refine ⟨195080828561886537315287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8323448685307158925452245 195080828561886537315287)
                  ·
                    rfl

theorem cell23_3419267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 3, 7].length) (baseStart_3419267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3419267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3419267 prefixEnd_3419267 := by exact prefixLift 3419267
  have htrace : WordTrace (prefixWord ++ tailWord_3419267) baseStart_3419267 baseEnd_3419267 := by
    simpa [prefixWord, tailWord_3419267, baseEnd_3419267] using wordTrace_append hprefix tailTrace_3419267
  have hstable : (prefixWord ++ tailWord_3419267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3419267).length < 2 ^ (prefixWord ++ tailWord_3419267).sum := by decide
  have hdescent : baseEnd_3419267 < baseStart_3419267 := by decide
  rcases family_descends (prefixWord ++ tailWord_3419267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3419274 : List Nat := [3, 1, 2, 3, 1, 1, 3, 1, 2, 2, 4]
def baseStart_3419274 : Nat := 118140960795 + 3419274 * 2 ^ 59
def prefixEnd_3419274 : Nat := 4983230072969 + 3 ^ 40 * 3419274 * 2
def baseEnd_3419274 : Nat := 1755731051421560308450051

theorem tailTrace_3419274 : CollatzResearch.WordTrace tailWord_3419274 prefixEnd_3419274 1755731051421560308450051 := by
  unfold tailWord_3419274
  simp only [CollatzResearch.WordTrace]
  refine ⟨31177792053640434588110219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83140778809707825568293917 31177792053640434588110219)
  ·
    refine ⟨46766688080460651882165329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31177792053640434588110219 46766688080460651882165329)
    ·
      refine ⟨35075016060345488911623997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46766688080460651882165329 35075016060345488911623997)
      ·
        refine ⟨13153131022629558341858999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35075016060345488911623997 13153131022629558341858999)
        ·
          refine ⟨19729696533944337512788499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13153131022629558341858999 19729696533944337512788499)
          ·
            refine ⟨29594544800916506269182749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19729696533944337512788499 29594544800916506269182749)
            ·
              refine ⟨11097954300343689850943531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29594544800916506269182749 11097954300343689850943531)
              ·
                refine ⟨16646931450515534776415297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11097954300343689850943531 16646931450515534776415297)
                ·
                  refine ⟨12485198587886651082311473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16646931450515534776415297 12485198587886651082311473)
                  ·
                    refine ⟨9363898940914988311733605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12485198587886651082311473 9363898940914988311733605)
                    ·
                      refine ⟨1755731051421560308450051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9363898940914988311733605 1755731051421560308450051)
                      ·
                        rfl

theorem cell23_3419274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_3419274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3419274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3419274 prefixEnd_3419274 := by exact prefixLift 3419274
  have htrace : WordTrace (prefixWord ++ tailWord_3419274) baseStart_3419274 baseEnd_3419274 := by
    simpa [prefixWord, tailWord_3419274, baseEnd_3419274] using wordTrace_append hprefix tailTrace_3419274
  have hstable : (prefixWord ++ tailWord_3419274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3419274).length < 2 ^ (prefixWord ++ tailWord_3419274).sum := by decide
  have hdescent : baseEnd_3419274 < baseStart_3419274 := by decide
  rcases family_descends (prefixWord ++ tailWord_3419274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3419278 : List Nat := [4, 1, 1, 3, 2, 2, 2, 1, 1, 4, 2]
def baseStart_3419278 : Nat := 118140960795 + 3419278 * 2 ^ 59
def prefixEnd_3419278 : Nat := 4983230072969 + 3 ^ 40 * 3419278 * 2
def baseEnd_3419278 : Nat := 1755733105344178292800033

theorem tailTrace_3419278 : CollatzResearch.WordTrace tailWord_3419278 prefixEnd_3419278 1755733105344178292800033 := by
  unfold tailWord_3419278
  simp only [CollatzResearch.WordTrace]
  refine ⟨15588914263318405879448311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83140876071031498023724325 15588914263318405879448311)
  ·
    refine ⟨23383371394977608819172467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15588914263318405879448311 23383371394977608819172467)
    ·
      refine ⟨35075057092466413228758701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23383371394977608819172467 35075057092466413228758701)
      ·
        refine ⟨13153146409674904960784513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35075057092466413228758701 13153146409674904960784513)
        ·
          refine ⟨9864859807256178720588385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13153146409674904960784513 9864859807256178720588385)
          ·
            refine ⟨7398644855442134040441289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9864859807256178720588385 7398644855442134040441289)
            ·
              refine ⟨5548983641581600530330967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7398644855442134040441289 5548983641581600530330967)
              ·
                refine ⟨8323475462372400795496451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5548983641581600530330967 8323475462372400795496451)
                ·
                  refine ⟨12485213193558601193244677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8323475462372400795496451 12485213193558601193244677)
                  ·
                    refine ⟨2340977473792237723733377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12485213193558601193244677 2340977473792237723733377)
                    ·
                      refine ⟨1755733105344178292800033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2340977473792237723733377 1755733105344178292800033)
                      ·
                        rfl

theorem cell23_3419278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 2, 1, 1, 4, 2].length) (baseStart_3419278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3419278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3419278 prefixEnd_3419278 := by exact prefixLift 3419278
  have htrace : WordTrace (prefixWord ++ tailWord_3419278) baseStart_3419278 baseEnd_3419278 := by
    simpa [prefixWord, tailWord_3419278, baseEnd_3419278] using wordTrace_append hprefix tailTrace_3419278
  have hstable : (prefixWord ++ tailWord_3419278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3419278).length < 2 ^ (prefixWord ++ tailWord_3419278).sum := by decide
  have hdescent : baseEnd_3419278 < baseStart_3419278 := by decide
  rcases family_descends (prefixWord ++ tailWord_3419278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3419301 : List Nat := [1, 3, 1, 2, 1, 5, 2, 3, 5]
def baseStart_3419301 : Nat := 118140960795 + 3419301 * 2 ^ 59
def prefixEnd_3419301 : Nat := 4983230072969 + 3 ^ 40 * 3419301 * 2
def baseEnd_3419301 : Nat := 195082768377692411423603

theorem tailTrace_3419301 : CollatzResearch.WordTrace tailWord_3419301 prefixEnd_3419301 195082768377692411423603 := by
  unfold tailWord_3419301
  simp only [CollatzResearch.WordTrace]
  refine ⟨124712152985463921963673757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83141435323642614642449171 124712152985463921963673757)
  ·
    refine ⟨46767057369548970736377659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124712152985463921963673757 46767057369548970736377659)
    ·
      refine ⟨70150586054323456104566489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46767057369548970736377659 70150586054323456104566489)
      ·
        refine ⟨52612939540742592078424867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70150586054323456104566489 52612939540742592078424867)
        ·
          refine ⟨78919409311113888117637301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52612939540742592078424867 78919409311113888117637301)
          ·
            refine ⟨7398694622916927011028497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 78919409311113888117637301 7398694622916927011028497)
            ·
              refine ⟨5549020967187695258271373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7398694622916927011028497 5549020967187695258271373)
              ·
                refine ⟨2080882862695385721851765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5549020967187695258271373 2080882862695385721851765)
                ·
                  refine ⟨195082768377692411423603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2080882862695385721851765 195082768377692411423603)
                  ·
                    rfl

theorem cell23_3419301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 2, 3, 5].length) (baseStart_3419301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3419301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3419301 prefixEnd_3419301 := by exact prefixLift 3419301
  have htrace : WordTrace (prefixWord ++ tailWord_3419301) baseStart_3419301 baseEnd_3419301 := by
    simpa [prefixWord, tailWord_3419301, baseEnd_3419301] using wordTrace_append hprefix tailTrace_3419301
  have hstable : (prefixWord ++ tailWord_3419301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3419301).length < 2 ^ (prefixWord ++ tailWord_3419301).sum := by decide
  have hdescent : baseEnd_3419301 < baseStart_3419301 := by decide
  rcases family_descends (prefixWord ++ tailWord_3419301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3419337 : List Nat := [1, 2, 1, 1, 2, 1, 1, 2, 4, 3, 5]
def baseStart_3419337 : Nat := 118140960795 + 3419337 * 2 ^ 59
def prefixEnd_3419337 : Nat := 4983230072969 + 3 ^ 40 * 3419337 * 2
def baseEnd_3419337 : Nat := 1755763400702793561962261

theorem tailTrace_3419337 : CollatzResearch.WordTrace tailWord_3419337 prefixEnd_3419337 1755763400702793561962261 := by
  unfold tailWord_3419337
  simp only [CollatzResearch.WordTrace]
  refine ⟨124713466013333500111984265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83142310675555666741322843 124713466013333500111984265)
  ·
    refine ⟨93535099510000125083988199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124713466013333500111984265 93535099510000125083988199)
    ·
      refine ⟨140302649265000187625982299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93535099510000125083988199 140302649265000187625982299)
      ·
        refine ⟨210453973897500281438973449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140302649265000187625982299 210453973897500281438973449)
        ·
          refine ⟨157840480423125211079230087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210453973897500281438973449 157840480423125211079230087)
          ·
            refine ⟨236760720634687816618845131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157840480423125211079230087 236760720634687816618845131)
            ·
              refine ⟨355141080952031724928267697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 236760720634687816618845131 355141080952031724928267697)
              ·
                refine ⟨266355810714023793696200773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 355141080952031724928267697 266355810714023793696200773)
                ·
                  refine ⟨49941714508879461318037645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 266355810714023793696200773 49941714508879461318037645)
                  ·
                    refine ⟨18728142940829797994264117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49941714508879461318037645 18728142940829797994264117)
                    ·
                      refine ⟨1755763400702793561962261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18728142940829797994264117 1755763400702793561962261)
                      ·
                        rfl

theorem cell23_3419337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 4, 3, 5].length) (baseStart_3419337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3419337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3419337 prefixEnd_3419337 := by exact prefixLift 3419337
  have htrace : WordTrace (prefixWord ++ tailWord_3419337) baseStart_3419337 baseEnd_3419337 := by
    simpa [prefixWord, tailWord_3419337, baseEnd_3419337] using wordTrace_append hprefix tailTrace_3419337
  have hstable : (prefixWord ++ tailWord_3419337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3419337).length < 2 ^ (prefixWord ++ tailWord_3419337).sum := by decide
  have hdescent : baseEnd_3419337 < baseStart_3419337 := by decide
  rcases family_descends (prefixWord ++ tailWord_3419337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3419347 : List Nat := [1, 1, 1, 2, 1, 1, 1, 4, 4, 1, 6]
def baseStart_3419347 : Nat := 118140960795 + 3419347 * 2 ^ 59
def prefixEnd_3419347 : Nat := 4983230072969 + 3 ^ 40 * 3419347 * 2
def baseEnd_3419347 : Nat := 1755768535509338522837215

theorem tailTrace_3419347 : CollatzResearch.WordTrace tailWord_3419347 prefixEnd_3419347 1755768535509338522837215 := by
  unfold tailWord_3419347
  simp only [CollatzResearch.WordTrace]
  refine ⟨124713830743297271819848295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83142553828864847879898863 124713830743297271819848295)
  ·
    refine ⟨187070746114945907729772443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124713830743297271819848295 187070746114945907729772443)
    ·
      refine ⟨280606119172418861594658665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187070746114945907729772443 280606119172418861594658665)
      ·
        refine ⟨210454589379314146195993999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 280606119172418861594658665 210454589379314146195993999)
        ·
          refine ⟨315681884068971219293990999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210454589379314146195993999 315681884068971219293990999)
          ·
            refine ⟨473522826103456828940986499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 315681884068971219293990999 473522826103456828940986499)
            ·
              refine ⟨710284239155185243411479749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 473522826103456828940986499 710284239155185243411479749)
              ·
                refine ⟨133178294841597233139652453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 710284239155185243411479749 133178294841597233139652453)
                ·
                  refine ⟨24970930282799481213684835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 133178294841597233139652453 24970930282799481213684835)
                  ·
                    refine ⟨37456395424199221820527253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24970930282799481213684835 37456395424199221820527253)
                    ·
                      refine ⟨1755768535509338522837215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37456395424199221820527253 1755768535509338522837215)
                      ·
                        rfl

theorem cell23_3419347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 4, 1, 6].length) (baseStart_3419347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3419347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3419347 prefixEnd_3419347 := by exact prefixLift 3419347
  have htrace : WordTrace (prefixWord ++ tailWord_3419347) baseStart_3419347 baseEnd_3419347 := by
    simpa [prefixWord, tailWord_3419347, baseEnd_3419347] using wordTrace_append hprefix tailTrace_3419347
  have hstable : (prefixWord ++ tailWord_3419347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3419347).length < 2 ^ (prefixWord ++ tailWord_3419347).sum := by decide
  have hdescent : baseEnd_3419347 < baseStart_3419347 := by decide
  rcases family_descends (prefixWord ++ tailWord_3419347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3419371 : List Nat := [1, 1, 1, 1, 2, 7, 1, 2, 2, 2, 3]
def baseStart_3419371 : Nat := 118140960795 + 3419371 * 2 ^ 59
def prefixEnd_3419371 : Nat := 4983230072969 + 3 ^ 40 * 3419371 * 2
def baseEnd_3419371 : Nat := 1755780859045046428937105

theorem tailTrace_3419371 : CollatzResearch.WordTrace tailWord_3419371 prefixEnd_3419371 1755780859045046428937105 := by
  unfold tailWord_3419371
  simp only [CollatzResearch.WordTrace]
  refine ⟨124714706095210323918721967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83143137396806882612481311 124714706095210323918721967)
  ·
    refine ⟨187072059142815485878082951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124714706095210323918721967 187072059142815485878082951)
    ·
      refine ⟨280608088714223228817124427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187072059142815485878082951 280608088714223228817124427)
      ·
        refine ⟨420912133071334843225686641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280608088714223228817124427 420912133071334843225686641)
        ·
          refine ⟨315684099803501132419264981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 420912133071334843225686641 315684099803501132419264981)
          ·
            refine ⟨7398846089144557791076523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 315684099803501132419264981 7398846089144557791076523)
            ·
              refine ⟨11098269133716836686614785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7398846089144557791076523 11098269133716836686614785)
              ·
                refine ⟨8323701850287627514961089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11098269133716836686614785 8323701850287627514961089)
                ·
                  refine ⟨6242776387715720636220817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8323701850287627514961089 6242776387715720636220817)
                  ·
                    refine ⟨4682082290786790477165613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6242776387715720636220817 4682082290786790477165613)
                    ·
                      refine ⟨1755780859045046428937105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4682082290786790477165613 1755780859045046428937105)
                      ·
                        rfl

theorem cell23_3419371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 2, 2, 2, 3].length) (baseStart_3419371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3419371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3419371 prefixEnd_3419371 := by exact prefixLift 3419371
  have htrace : WordTrace (prefixWord ++ tailWord_3419371) baseStart_3419371 baseEnd_3419371 := by
    simpa [prefixWord, tailWord_3419371, baseEnd_3419371] using wordTrace_append hprefix tailTrace_3419371
  have hstable : (prefixWord ++ tailWord_3419371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3419371).length < 2 ^ (prefixWord ++ tailWord_3419371).sum := by decide
  have hdescent : baseEnd_3419371 < baseStart_3419371 := by decide
  rcases family_descends (prefixWord ++ tailWord_3419371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3419374 : List Nat := [4, 1, 2, 1, 1, 1, 4, 1, 8]
def baseStart_3419374 : Nat := 118140960795 + 3419374 * 2 ^ 59
def prefixEnd_3419374 : Nat := 4983230072969 + 3 ^ 40 * 3419374 * 2
def baseEnd_3419374 : Nat := 195086933276334435244399

theorem tailTrace_3419374 : CollatzResearch.WordTrace tailWord_3419374 prefixEnd_3419374 195086933276334435244399 := by
  unfold tailWord_3419374
  simp only [CollatzResearch.WordTrace]
  refine ⟨15589351939274931928885147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83143210342799636954054117 15589351939274931928885147)
  ·
    refine ⟨23384027908912397893327721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15589351939274931928885147 23384027908912397893327721)
    ·
      refine ⟨17538020931684298419995791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23384027908912397893327721 17538020931684298419995791)
      ·
        refine ⟨26307031397526447629993687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17538020931684298419995791 26307031397526447629993687)
        ·
          refine ⟨39460547096289671444990531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26307031397526447629993687 39460547096289671444990531)
          ·
            refine ⟨59190820644434507167485797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39460547096289671444990531 59190820644434507167485797)
            ·
              refine ⟨11098278870831470093903587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59190820644434507167485797 11098278870831470093903587)
              ·
                refine ⟨16647418306247205140855381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11098278870831470093903587 16647418306247205140855381)
                ·
                  refine ⟨195086933276334435244399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16647418306247205140855381 195086933276334435244399)
                  ·
                    rfl

theorem cell23_3419374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 1, 8].length) (baseStart_3419374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3419374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3419374 prefixEnd_3419374 := by exact prefixLift 3419374
  have htrace : WordTrace (prefixWord ++ tailWord_3419374) baseStart_3419374 baseEnd_3419374 := by
    simpa [prefixWord, tailWord_3419374, baseEnd_3419374] using wordTrace_append hprefix tailTrace_3419374
  have hstable : (prefixWord ++ tailWord_3419374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3419374).length < 2 ^ (prefixWord ++ tailWord_3419374).sum := by decide
  have hdescent : baseEnd_3419374 < baseStart_3419374 := by decide
  rcases family_descends (prefixWord ++ tailWord_3419374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3419391 : List Nat := [1, 1, 2, 2, 1, 5, 4, 1, 6]
def baseStart_3419391 : Nat := 118140960795 + 3419391 * 2 ^ 59
def prefixEnd_3419391 : Nat := 4983230072969 + 3 ^ 40 * 3419391 * 2
def baseEnd_3419391 : Nat := 195087903184237372298557

theorem tailTrace_3419391 : CollatzResearch.WordTrace tailWord_3419391 prefixEnd_3419391 195087903184237372298557 := by
  unfold tailWord_3419391
  simp only [CollatzResearch.WordTrace]
  refine ⟨124715435555137867334450027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83143623703425244889633351 124715435555137867334450027)
  ·
    refine ⟨187073153332706801001675041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124715435555137867334450027 187073153332706801001675041)
    ·
      refine ⟨140304864999530100751256281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187073153332706801001675041 140304864999530100751256281)
      ·
        refine ⟨105228648749647575563442211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140304864999530100751256281 105228648749647575563442211)
        ·
          refine ⟨157842973124471363345163317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105228648749647575563442211 157842973124471363345163317)
          ·
            refine ⟨14797778730419190313609061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 157842973124471363345163317 14797778730419190313609061)
            ·
              refine ⟨2774583511953598183801699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14797778730419190313609061 2774583511953598183801699)
              ·
                refine ⟨4161875267930397275702549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2774583511953598183801699 4161875267930397275702549)
                ·
                  refine ⟨195087903184237372298557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4161875267930397275702549 195087903184237372298557)
                  ·
                    rfl

theorem cell23_3419391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 4, 1, 6].length) (baseStart_3419391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3419391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3419391 prefixEnd_3419391 := by exact prefixLift 3419391
  have htrace : WordTrace (prefixWord ++ tailWord_3419391) baseStart_3419391 baseEnd_3419391 := by
    simpa [prefixWord, tailWord_3419391, baseEnd_3419391] using wordTrace_append hprefix tailTrace_3419391
  have hstable : (prefixWord ++ tailWord_3419391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3419391).length < 2 ^ (prefixWord ++ tailWord_3419391).sum := by decide
  have hdescent : baseEnd_3419391 < baseStart_3419391 := by decide
  rcases family_descends (prefixWord ++ tailWord_3419391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3419401 : List Nat := [1, 2, 1, 1, 3, 3, 2, 1, 5, 1, 3]
def baseStart_3419401 : Nat := 118140960795 + 3419401 * 2 ^ 59
def prefixEnd_3419401 : Nat := 4983230072969 + 3 ^ 40 * 3419401 * 2
def baseEnd_3419401 : Nat := 1755796263464681311561967

theorem tailTrace_3419401 : CollatzResearch.WordTrace tailWord_3419401 prefixEnd_3419401 1755796263464681311561967 := by
  unfold tailWord_3419401
  simp only [CollatzResearch.WordTrace]
  refine ⟨124715800285101639042314057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83143866856734426028209371 124715800285101639042314057)
  ·
    refine ⟨93536850213826229281735543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124715800285101639042314057 93536850213826229281735543)
    ·
      refine ⟨140305275320739343922603315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93536850213826229281735543 140305275320739343922603315)
      ·
        refine ⟨210457912981109015883904973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140305275320739343922603315 210457912981109015883904973)
        ·
          refine ⟨78921717367915880956464365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 210457912981109015883904973 78921717367915880956464365)
          ·
            refine ⟨29595644012968455358674137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78921717367915880956464365 29595644012968455358674137)
            ·
              refine ⟨22196733009726341519005603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29595644012968455358674137 22196733009726341519005603)
              ·
                refine ⟨33295099514589512278508405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22196733009726341519005603 33295099514589512278508405)
                ·
                  refine ⟨3121415579492766776110163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33295099514589512278508405 3121415579492766776110163)
                  ·
                    refine ⟨4682123369239150164165245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3121415579492766776110163 4682123369239150164165245)
                    ·
                      refine ⟨1755796263464681311561967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4682123369239150164165245 1755796263464681311561967)
                      ·
                        rfl

theorem cell23_3419401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 1, 5, 1, 3].length) (baseStart_3419401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3419401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3419401 prefixEnd_3419401 := by exact prefixLift 3419401
  have htrace : WordTrace (prefixWord ++ tailWord_3419401) baseStart_3419401 baseEnd_3419401 := by
    simpa [prefixWord, tailWord_3419401, baseEnd_3419401] using wordTrace_append hprefix tailTrace_3419401
  have hstable : (prefixWord ++ tailWord_3419401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3419401).length < 2 ^ (prefixWord ++ tailWord_3419401).sum := by decide
  have hdescent : baseEnd_3419401 < baseStart_3419401 := by decide
  rcases family_descends (prefixWord ++ tailWord_3419401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3419428 : List Nat := [2, 3, 1, 3, 1, 1, 1, 4, 2, 3, 2]
def baseStart_3419428 : Nat := 118140960795 + 3419428 * 2 ^ 59
def prefixEnd_3419428 : Nat := 4983230072969 + 3 ^ 40 * 3419428 * 2
def baseEnd_3419428 : Nat := 1755810127442352705924343

theorem tailTrace_3419428 : CollatzResearch.WordTrace tailWord_3419428 prefixEnd_3419428 1755810127442352705924343 := by
  unfold tailWord_3419428
  simp only [CollatzResearch.WordTrace]
  refine ⟨62358392528001911326773469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83144523370669215102364625 62358392528001911326773469)
  ·
    refine ⟨23384397198000716747540051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62358392528001911326773469 23384397198000716747540051)
    ·
      refine ⟨35076595797001075121310077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23384397198000716747540051 35076595797001075121310077)
      ·
        refine ⟨13153723423875403170491279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35076595797001075121310077 13153723423875403170491279)
        ·
          refine ⟨19730585135813104755736919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13153723423875403170491279 19730585135813104755736919)
          ·
            refine ⟨29595877703719657133605379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19730585135813104755736919 29595877703719657133605379)
            ·
              refine ⟨44393816555579485700408069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29595877703719657133605379 44393816555579485700408069)
              ·
                refine ⟨8323840604171153568826513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44393816555579485700408069 8323840604171153568826513)
                ·
                  refine ⟨6242880453128365176619885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8323840604171153568826513 6242880453128365176619885)
                  ·
                    refine ⟨2341080169923136941232457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6242880453128365176619885 2341080169923136941232457)
                    ·
                      refine ⟨1755810127442352705924343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2341080169923136941232457 1755810127442352705924343)
                      ·
                        rfl

theorem cell23_3419428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 4, 2, 3, 2].length) (baseStart_3419428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3419428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3419428 prefixEnd_3419428 := by exact prefixLift 3419428
  have htrace : WordTrace (prefixWord ++ tailWord_3419428) baseStart_3419428 baseEnd_3419428 := by
    simpa [prefixWord, tailWord_3419428, baseEnd_3419428] using wordTrace_append hprefix tailTrace_3419428
  have hstable : (prefixWord ++ tailWord_3419428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3419428).length < 2 ^ (prefixWord ++ tailWord_3419428).sum := by decide
  have hdescent : baseEnd_3419428 < baseStart_3419428 := by decide
  rcases family_descends (prefixWord ++ tailWord_3419428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3419441 : List Nat := [1, 2, 2, 3, 3, 1, 1, 2, 3, 1, 4]
def baseStart_3419441 : Nat := 118140960795 + 3419441 * 2 ^ 59
def prefixEnd_3419441 : Nat := 4983230072969 + 3 ^ 40 * 3419441 * 2
def baseEnd_3419441 : Nat := 1755816802690861155061783

theorem tailTrace_3419441 : CollatzResearch.WordTrace tailWord_3419441 prefixEnd_3419441 1755816802690861155061783 := by
  unfold tailWord_3419441
  simp only [CollatzResearch.WordTrace]
  refine ⟨124717259204956725873770177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83144839469971150582513451 124717259204956725873770177)
  ·
    refine ⟨93537944403717544405327633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124717259204956725873770177 93537944403717544405327633)
    ·
      refine ⟨70153458302788158303995725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93537944403717544405327633 70153458302788158303995725)
      ·
        refine ⟨26307546863545559363998397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70153458302788158303995725 26307546863545559363998397)
        ·
          refine ⟨9865330073829584761499399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26307546863545559363998397 9865330073829584761499399)
          ·
            refine ⟨14797995110744377142249099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9865330073829584761499399 14797995110744377142249099)
            ·
              refine ⟨22196992666116565713373649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14797995110744377142249099 22196992666116565713373649)
              ·
                refine ⟨16647744499587424285030237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22196992666116565713373649 16647744499587424285030237)
                ·
                  refine ⟨6242904187345284106886339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16647744499587424285030237 6242904187345284106886339)
                  ·
                    refine ⟨9364356281017926160329509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6242904187345284106886339 9364356281017926160329509)
                    ·
                      refine ⟨1755816802690861155061783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9364356281017926160329509 1755816802690861155061783)
                      ·
                        rfl

theorem cell23_3419441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 2, 3, 1, 4].length) (baseStart_3419441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3419441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3419441 prefixEnd_3419441 := by exact prefixLift 3419441
  have htrace : WordTrace (prefixWord ++ tailWord_3419441) baseStart_3419441 baseEnd_3419441 := by
    simpa [prefixWord, tailWord_3419441, baseEnd_3419441] using wordTrace_append hprefix tailTrace_3419441
  have hstable : (prefixWord ++ tailWord_3419441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3419441).length < 2 ^ (prefixWord ++ tailWord_3419441).sum := by decide
  have hdescent : baseEnd_3419441 < baseStart_3419441 := by decide
  rcases family_descends (prefixWord ++ tailWord_3419441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3419492 : List Nat := [2, 3, 1, 1, 3, 2, 2, 4, 1, 2, 2]
def baseStart_3419492 : Nat := 118140960795 + 3419492 * 2 ^ 59
def prefixEnd_3419492 : Nat := 4983230072969 + 3 ^ 40 * 3419492 * 2
def baseEnd_3419492 : Nat := 1755842990204240455524049

theorem tailTrace_3419492 : CollatzResearch.WordTrace tailWord_3419492 prefixEnd_3419492 1755842990204240455524049 := by
  unfold tailWord_3419492
  simp only [CollatzResearch.WordTrace]
  refine ⟨62359559663885980791938365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83146079551847974389251153 62359559663885980791938365)
  ·
    refine ⟨23384834873957242796976887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62359559663885980791938365 23384834873957242796976887)
    ·
      refine ⟨35077252310935864195465331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23384834873957242796976887 35077252310935864195465331)
      ·
        refine ⟨52615878466403796293197997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35077252310935864195465331 52615878466403796293197997)
        ·
          refine ⟨19730954424901423609949249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52615878466403796293197997 19730954424901423609949249)
          ·
            refine ⟨14798215818676067707461937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19730954424901423609949249 14798215818676067707461937)
            ·
              refine ⟨11098661864007050780596453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14798215818676067707461937 11098661864007050780596453)
              ·
                refine ⟨2080999099501322021361835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11098661864007050780596453 2080999099501322021361835)
                ·
                  refine ⟨3121498649251983032042753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2080999099501322021361835 3121498649251983032042753)
                  ·
                    refine ⟨2341123986938987274032065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3121498649251983032042753 2341123986938987274032065)
                    ·
                      refine ⟨1755842990204240455524049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2341123986938987274032065 1755842990204240455524049)
                      ·
                        rfl

theorem cell23_3419492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 4, 1, 2, 2].length) (baseStart_3419492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3419492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3419492 prefixEnd_3419492 := by exact prefixLift 3419492
  have htrace : WordTrace (prefixWord ++ tailWord_3419492) baseStart_3419492 baseEnd_3419492 := by
    simpa [prefixWord, tailWord_3419492, baseEnd_3419492] using wordTrace_append hprefix tailTrace_3419492
  have hstable : (prefixWord ++ tailWord_3419492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3419492).length < 2 ^ (prefixWord ++ tailWord_3419492).sum := by decide
  have hdescent : baseEnd_3419492 < baseStart_3419492 := by decide
  rcases family_descends (prefixWord ++ tailWord_3419492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3419502 : List Nat := [4, 1, 2, 4, 2, 1, 1, 1, 1, 6]
def baseStart_3419502 : Nat := 118140960795 + 3419502 * 2 ^ 59
def prefixEnd_3419502 : Nat := 4983230072969 + 3 ^ 40 * 3419502 * 2
def baseEnd_3419502 : Nat := 585282708336928472133001

theorem tailTrace_3419502 : CollatzResearch.WordTrace tailWord_3419502 prefixEnd_3419502 585282708336928472133001 := by
  unfold tailWord_3419502
  simp only [CollatzResearch.WordTrace]
  refine ⟨15589935507216966661467595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83146322705157155527827173 15589935507216966661467595)
  ·
    refine ⟨23384903260825449992201393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15589935507216966661467595 23384903260825449992201393)
    ·
      refine ⟨17538677445619087494151045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23384903260825449992201393 17538677445619087494151045)
      ·
        refine ⟨3288502021053578905153321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17538677445619087494151045 3288502021053578905153321)
        ·
          refine ⟨2466376515790184178864991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3288502021053578905153321 2466376515790184178864991)
          ·
            refine ⟨3699564773685276268297487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2466376515790184178864991 3699564773685276268297487)
            ·
              refine ⟨5549347160527914402446231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3699564773685276268297487 5549347160527914402446231)
              ·
                refine ⟨8324020740791871603669347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5549347160527914402446231 8324020740791871603669347)
                ·
                  refine ⟨12486031111187807405504021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8324020740791871603669347 12486031111187807405504021)
                  ·
                    refine ⟨585282708336928472133001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12486031111187807405504021 585282708336928472133001)
                    ·
                      rfl

theorem cell23_3419502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 1, 1, 1, 6].length) (baseStart_3419502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3419502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3419502 prefixEnd_3419502 := by exact prefixLift 3419502
  have htrace : WordTrace (prefixWord ++ tailWord_3419502) baseStart_3419502 baseEnd_3419502 := by
    simpa [prefixWord, tailWord_3419502, baseEnd_3419502] using wordTrace_append hprefix tailTrace_3419502
  have hstable : (prefixWord ++ tailWord_3419502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3419502).length < 2 ^ (prefixWord ++ tailWord_3419502).sum := by decide
  have hdescent : baseEnd_3419502 < baseStart_3419502 := by decide
  rcases family_descends (prefixWord ++ tailWord_3419502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3419608 : List Nat := [2, 1, 2, 2, 2, 1, 3, 1, 2, 5, 2]
def baseStart_3419608 : Nat := 118140960795 + 3419608 * 2 ^ 59
def prefixEnd_3419608 : Nat := 4983230072969 + 3 ^ 40 * 3419608 * 2
def baseEnd_3419608 : Nat := 1755902553960162001673515

theorem tailTrace_3419608 : CollatzResearch.WordTrace tailWord_3419608 prefixEnd_3419608 1755902553960162001673515 := by
  unfold tailWord_3419608
  simp only [CollatzResearch.WordTrace]
  refine ⟨62361675097675856697549739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83148900130234475596732985 62361675097675856697549739)
  ·
    refine ⟨93542512646513785046324609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62361675097675856697549739 93542512646513785046324609)
    ·
      refine ⟨70156884484885338784743457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93542512646513785046324609 70156884484885338784743457)
      ·
        refine ⟨52617663363664004088557593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70156884484885338784743457 52617663363664004088557593)
        ·
          refine ⟨39463247522748003066418195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52617663363664004088557593 39463247522748003066418195)
          ·
            refine ⟨59194871284122004599627293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39463247522748003066418195 59194871284122004599627293)
            ·
              refine ⟨22198076731545751724860235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59194871284122004599627293 22198076731545751724860235)
              ·
                refine ⟨33297115097318627587290353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22198076731545751724860235 33297115097318627587290353)
                ·
                  refine ⟨24972836322988970690467765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33297115097318627587290353 24972836322988970690467765)
                  ·
                    refine ⟨2341203405280216002231353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24972836322988970690467765 2341203405280216002231353)
                    ·
                      refine ⟨1755902553960162001673515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2341203405280216002231353 1755902553960162001673515)
                      ·
                        rfl

theorem cell23_3419608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 1, 2, 5, 2].length) (baseStart_3419608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3419608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3419608 prefixEnd_3419608 := by exact prefixLift 3419608
  have htrace : WordTrace (prefixWord ++ tailWord_3419608) baseStart_3419608 baseEnd_3419608 := by
    simpa [prefixWord, tailWord_3419608, baseEnd_3419608] using wordTrace_append hprefix tailTrace_3419608
  have hstable : (prefixWord ++ tailWord_3419608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3419608).length < 2 ^ (prefixWord ++ tailWord_3419608).sum := by decide
  have hdescent : baseEnd_3419608 < baseStart_3419608 := by decide
  rcases family_descends (prefixWord ++ tailWord_3419608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3419655 : List Nat := [1, 1, 4, 3, 2, 1, 1, 2, 2, 4, 2]
def baseStart_3419655 : Nat := 118140960795 + 3419655 * 2 ^ 59
def prefixEnd_3419655 : Nat := 4983230072969 + 3 ^ 40 * 3419655 * 2
def baseEnd_3419655 : Nat := 1755926687550923317785799

theorem tailTrace_3419655 : CollatzResearch.WordTrace tailWord_3419655 prefixEnd_3419655 1755926687550923317785799 := by
  unfold tailWord_3419655
  simp only [CollatzResearch.WordTrace]
  refine ⟨124725064426181440422060419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83150042950787626948040279 124725064426181440422060419)
  ·
    refine ⟨187087596639272160633090629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124725064426181440422060419 187087596639272160633090629)
    ·
      refine ⟨35078924369863530118704493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 187087596639272160633090629 35078924369863530118704493)
      ·
        refine ⟨13154596638698823794514185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35078924369863530118704493 13154596638698823794514185)
        ·
          refine ⟨9865947479024117845885639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13154596638698823794514185 9865947479024117845885639)
          ·
            refine ⟨14798921218536176768828459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9865947479024117845885639 14798921218536176768828459)
            ·
              refine ⟨22198381827804265153242689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14798921218536176768828459 22198381827804265153242689)
              ·
                refine ⟨16648786370853198864932017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22198381827804265153242689 16648786370853198864932017)
                ·
                  refine ⟨12486589778139899148699013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16648786370853198864932017 12486589778139899148699013)
                  ·
                    refine ⟨2341235583401231090381065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12486589778139899148699013 2341235583401231090381065)
                    ·
                      refine ⟨1755926687550923317785799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2341235583401231090381065 1755926687550923317785799)
                      ·
                        rfl

theorem cell23_3419655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 2, 2, 4, 2].length) (baseStart_3419655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3419655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3419655 prefixEnd_3419655 := by exact prefixLift 3419655
  have htrace : WordTrace (prefixWord ++ tailWord_3419655) baseStart_3419655 baseEnd_3419655 := by
    simpa [prefixWord, tailWord_3419655, baseEnd_3419655] using wordTrace_append hprefix tailTrace_3419655
  have hstable : (prefixWord ++ tailWord_3419655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3419655).length < 2 ^ (prefixWord ++ tailWord_3419655).sum := by decide
  have hdescent : baseEnd_3419655 < baseStart_3419655 := by decide
  rcases family_descends (prefixWord ++ tailWord_3419655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3419665 : List Nat := [1, 2, 2, 1, 1, 2, 3, 6, 1, 4]
def baseStart_3419665 : Nat := 118140960795 + 3419665 * 2 ^ 59
def prefixEnd_3419665 : Nat := 4983230072969 + 3 ^ 40 * 3419665 * 2
def baseEnd_3419665 : Nat := 585310607452489426220251

theorem tailTrace_3419665 : CollatzResearch.WordTrace tailWord_3419665 prefixEnd_3419665 585310607452489426220251 := by
  unfold tailWord_3419665
  simp only [CollatzResearch.WordTrace]
  refine ⟨124725429156145212129924449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83150286104096808086616299 124725429156145212129924449)
  ·
    refine ⟨93544071867108909097443337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124725429156145212129924449 93544071867108909097443337)
    ·
      refine ⟨70158053900331681823082503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93544071867108909097443337 70158053900331681823082503)
      ·
        refine ⟨105237080850497522734623755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70158053900331681823082503 105237080850497522734623755)
        ·
          refine ⟨157855621275746284101935633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105237080850497522734623755 157855621275746284101935633)
          ·
            refine ⟨118391715956809713076451725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157855621275746284101935633 118391715956809713076451725)
            ·
              refine ⟨44396893483803642403669397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118391715956809713076451725 44396893483803642403669397)
              ·
                refine ⟨2081104382053295737672003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 44396893483803642403669397 2081104382053295737672003)
                ·
                  refine ⟨3121656573079943606508005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2081104382053295737672003 3121656573079943606508005)
                  ·
                    refine ⟨585310607452489426220251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3121656573079943606508005 585310607452489426220251)
                    ·
                      rfl

theorem cell23_3419665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 6, 1, 4].length) (baseStart_3419665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3419665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3419665 prefixEnd_3419665 := by exact prefixLift 3419665
  have htrace : WordTrace (prefixWord ++ tailWord_3419665) baseStart_3419665 baseEnd_3419665 := by
    simpa [prefixWord, tailWord_3419665, baseEnd_3419665] using wordTrace_append hprefix tailTrace_3419665
  have hstable : (prefixWord ++ tailWord_3419665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3419665).length < 2 ^ (prefixWord ++ tailWord_3419665).sum := by decide
  have hdescent : baseEnd_3419665 < baseStart_3419665 := by decide
  rcases family_descends (prefixWord ++ tailWord_3419665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3419728 : List Nat := [2, 1, 1, 1, 1, 3, 4, 2, 3, 1, 4]
def baseStart_3419728 : Nat := 118140960795 + 3419728 * 2 ^ 59
def prefixEnd_3419728 : Nat := 4983230072969 + 3 ^ 40 * 3419728 * 2
def baseEnd_3419728 : Nat := 1755964171638701532172963

theorem tailTrace_3419728 : CollatzResearch.WordTrace tailWord_3419728 prefixEnd_3419728 1755964171638701532172963 := by
  unfold tailWord_3419728
  simp only [CollatzResearch.WordTrace]
  refine ⟨62363863477458486944733919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83151817969944649259645225 62363863477458486944733919)
  ·
    refine ⟨93545795216187730417100879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62363863477458486944733919 93545795216187730417100879)
    ·
      refine ⟨140318692824281595625651319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93545795216187730417100879 140318692824281595625651319)
      ·
        refine ⟨210478039236422393438476979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140318692824281595625651319 210478039236422393438476979)
        ·
          refine ⟨315717058854633590157715469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210478039236422393438476979 315717058854633590157715469)
          ·
            refine ⟨118393897070487596309143301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 315717058854633590157715469 118393897070487596309143301)
            ·
              refine ⟨22198855700716424307964369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 118393897070487596309143301 22198855700716424307964369)
              ·
                refine ⟨16649141775537318230973277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22198855700716424307964369 16649141775537318230973277)
                ·
                  refine ⟨6243428165826494336614979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16649141775537318230973277 6243428165826494336614979)
                  ·
                    refine ⟨9365142248739741504922469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6243428165826494336614979 9365142248739741504922469)
                    ·
                      refine ⟨1755964171638701532172963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9365142248739741504922469 1755964171638701532172963)
                      ·
                        rfl

theorem cell23_3419728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 2, 3, 1, 4].length) (baseStart_3419728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3419728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3419728 prefixEnd_3419728 := by exact prefixLift 3419728
  have htrace : WordTrace (prefixWord ++ tailWord_3419728) baseStart_3419728 baseEnd_3419728 := by
    simpa [prefixWord, tailWord_3419728, baseEnd_3419728] using wordTrace_append hprefix tailTrace_3419728
  have hstable : (prefixWord ++ tailWord_3419728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3419728).length < 2 ^ (prefixWord ++ tailWord_3419728).sum := by decide
  have hdescent : baseEnd_3419728 < baseStart_3419728 := by decide
  rcases family_descends (prefixWord ++ tailWord_3419728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3419796 : List Nat := [2, 4, 2, 2, 2, 1, 1, 2, 3, 2, 2]
def baseStart_3419796 : Nat := 118140960795 + 3419796 * 2 ^ 59
def prefixEnd_3419796 : Nat := 4983230072969 + 3 ^ 40 * 3419796 * 2
def baseEnd_3419796 : Nat := 1755999088323207266122651

theorem tailTrace_3419796 : CollatzResearch.WordTrace tailWord_3419796 prefixEnd_3419796 1755999088323207266122651 := by
  unfold tailWord_3419796
  simp only [CollatzResearch.WordTrace]
  refine ⟨62365103559335310751471621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83153471412447081001962161 62365103559335310751471621)
  ·
    refine ⟨11693456917375370765900929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62365103559335310751471621 11693456917375370765900929)
    ·
      refine ⟨8770092688031528074425697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11693456917375370765900929 8770092688031528074425697)
      ·
        refine ⟨6577569516023646055819273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8770092688031528074425697 6577569516023646055819273)
        ·
          refine ⟨4933177137017734541864455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6577569516023646055819273 4933177137017734541864455)
          ·
            refine ⟨7399765705526601812796683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4933177137017734541864455 7399765705526601812796683)
            ·
              refine ⟨11099648558289902719195025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7399765705526601812796683 11099648558289902719195025)
              ·
                refine ⟨8324736418717427039396269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11099648558289902719195025 8324736418717427039396269)
                ·
                  refine ⟨3121776157019035139773601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8324736418717427039396269 3121776157019035139773601)
                  ·
                    refine ⟨2341332117764276354830201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3121776157019035139773601 2341332117764276354830201)
                    ·
                      refine ⟨1755999088323207266122651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2341332117764276354830201 1755999088323207266122651)
                      ·
                        rfl

theorem cell23_3419796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 2, 3, 2, 2].length) (baseStart_3419796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3419796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3419796 prefixEnd_3419796 := by exact prefixLift 3419796
  have htrace : WordTrace (prefixWord ++ tailWord_3419796) baseStart_3419796 baseEnd_3419796 := by
    simpa [prefixWord, tailWord_3419796, baseEnd_3419796] using wordTrace_append hprefix tailTrace_3419796
  have hstable : (prefixWord ++ tailWord_3419796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3419796).length < 2 ^ (prefixWord ++ tailWord_3419796).sum := by decide
  have hdescent : baseEnd_3419796 < baseStart_3419796 := by decide
  rcases family_descends (prefixWord ++ tailWord_3419796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3419829 : List Nat := [1, 3, 3, 3, 2, 1, 1, 1, 4, 1, 3]
def baseStart_3419829 : Nat := 118140960795 + 3419829 * 2 ^ 59
def prefixEnd_3419829 : Nat := 4983230072969 + 3 ^ 40 * 3419829 * 2
def baseEnd_3419829 : Nat := 1756016033184805637009999

theorem tailTrace_3419829 : CollatzResearch.WordTrace tailWord_3419829 prefixEnd_3419829 1756016033184805637009999 := by
  unfold tailWord_3419829
  simp only [CollatzResearch.WordTrace]
  refine ⟨124731410727551068138894541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83154273818367378759263027 124731410727551068138894541)
  ·
    refine ⟨46774279022831650552085453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124731410727551068138894541 46774279022831650552085453)
    ·
      refine ⟨17540354633561868957032045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46774279022831650552085453 17540354633561868957032045)
      ·
        refine ⟨6577632987585700858887017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17540354633561868957032045 6577632987585700858887017)
        ·
          refine ⟨4933224740689275644165263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6577632987585700858887017 4933224740689275644165263)
          ·
            refine ⟨7399837111033913466247895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4933224740689275644165263 7399837111033913466247895)
            ·
              refine ⟨11099755666550870199371843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7399837111033913466247895 11099755666550870199371843)
              ·
                refine ⟨16649633499826305299057765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11099755666550870199371843 16649633499826305299057765)
                ·
                  refine ⟨3121806281217432243573331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16649633499826305299057765 3121806281217432243573331)
                  ·
                    refine ⟨4682709421826148365359997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3121806281217432243573331 4682709421826148365359997)
                    ·
                      refine ⟨1756016033184805637009999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4682709421826148365359997 1756016033184805637009999)
                      ·
                        rfl

theorem cell23_3419829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_3419829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3419829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3419829 prefixEnd_3419829 := by exact prefixLift 3419829
  have htrace : WordTrace (prefixWord ++ tailWord_3419829) baseStart_3419829 baseEnd_3419829 := by
    simpa [prefixWord, tailWord_3419829, baseEnd_3419829] using wordTrace_append hprefix tailTrace_3419829
  have hstable : (prefixWord ++ tailWord_3419829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3419829).length < 2 ^ (prefixWord ++ tailWord_3419829).sum := by decide
  have hdescent : baseEnd_3419829 < baseStart_3419829 := by decide
  rcases family_descends (prefixWord ++ tailWord_3419829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3419835 : List Nat := [1, 1, 1, 1, 1, 2, 3, 4, 3, 4, 2]
def baseStart_3419835 : Nat := 118140960795 + 3419835 * 2 ^ 59
def prefixEnd_3419835 : Nat := 4983230072969 + 3 ^ 40 * 3419835 * 2
def baseEnd_3419835 : Nat := 1756019114068732613534971

theorem tailTrace_3419835 : CollatzResearch.WordTrace tailWord_3419835 prefixEnd_3419835 1756019114068732613534971 := by
  unfold tailWord_3419835
  simp only [CollatzResearch.WordTrace]
  refine ⟨124731629565529331163612959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83154419710352887442408639 124731629565529331163612959)
  ·
    refine ⟨187097444348293996745419439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124731629565529331163612959 187097444348293996745419439)
    ·
      refine ⟨280646166522440995118129159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187097444348293996745419439 280646166522440995118129159)
      ·
        refine ⟨420969249783661492677193739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280646166522440995118129159 420969249783661492677193739)
        ·
          refine ⟨631453874675492239015790609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 420969249783661492677193739 631453874675492239015790609)
          ·
            refine ⟨473590406006619179261842957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 631453874675492239015790609 473590406006619179261842957)
            ·
              refine ⟨177596402252482192223191109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 473590406006619179261842957 177596402252482192223191109)
              ·
                refine ⟨33299325422340411041848333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 177596402252482192223191109 33299325422340411041848333)
                ·
                  refine ⟨12487247033377654140693125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33299325422340411041848333 12487247033377654140693125)
                  ·
                    refine ⟨2341358818758310151379961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12487247033377654140693125 2341358818758310151379961)
                    ·
                      refine ⟨1756019114068732613534971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2341358818758310151379961 1756019114068732613534971)
                      ·
                        rfl

theorem cell23_3419835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 3, 4, 2].length) (baseStart_3419835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3419835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3419835 prefixEnd_3419835 := by exact prefixLift 3419835
  have htrace : WordTrace (prefixWord ++ tailWord_3419835) baseStart_3419835 baseEnd_3419835 := by
    simpa [prefixWord, tailWord_3419835, baseEnd_3419835] using wordTrace_append hprefix tailTrace_3419835
  have hstable : (prefixWord ++ tailWord_3419835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3419835).length < 2 ^ (prefixWord ++ tailWord_3419835).sum := by decide
  have hdescent : baseEnd_3419835 < baseStart_3419835 := by decide
  rcases family_descends (prefixWord ++ tailWord_3419835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3419846 : List Nat := [6, 1, 2, 1, 1, 1, 3, 1, 1, 3, 3]
def baseStart_3419846 : Nat := 118140960795 + 3419846 * 2 ^ 59
def prefixEnd_3419846 : Nat := 4983230072969 + 3 ^ 40 * 3419846 * 2
def baseEnd_3419846 : Nat := 1756024762355932070497421

theorem tailTrace_3419846 : CollatzResearch.WordTrace tailWord_3419846 prefixEnd_3419846 1756024762355932070497421 := by
  unfold tailWord_3419846
  simp only [CollatzResearch.WordTrace]
  refine ⟨3897875961515296251320731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 83154687178992986694842261 3897875961515296251320731)
  ·
    refine ⟨5846813942272944376981097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3897875961515296251320731 5846813942272944376981097)
    ·
      refine ⟨4385110456704708282735823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5846813942272944376981097 4385110456704708282735823)
      ·
        refine ⟨6577665685057062424103735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4385110456704708282735823 6577665685057062424103735)
        ·
          refine ⟨9866498527585593636155603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6577665685057062424103735 9866498527585593636155603)
          ·
            refine ⟨14799747791378390454233405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9866498527585593636155603 14799747791378390454233405)
            ·
              refine ⟨5549905421766896420337527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14799747791378390454233405 5549905421766896420337527)
              ·
                refine ⟨8324858132650344630506291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5549905421766896420337527 8324858132650344630506291)
                ·
                  refine ⟨12487287198975516945759437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8324858132650344630506291 12487287198975516945759437)
                  ·
                    refine ⟨4682732699615818854659789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12487287198975516945759437 4682732699615818854659789)
                    ·
                      refine ⟨1756024762355932070497421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4682732699615818854659789 1756024762355932070497421)
                      ·
                        rfl

theorem cell23_3419846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_3419846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3419846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3419846 prefixEnd_3419846 := by exact prefixLift 3419846
  have htrace : WordTrace (prefixWord ++ tailWord_3419846) baseStart_3419846 baseEnd_3419846 := by
    simpa [prefixWord, tailWord_3419846, baseEnd_3419846] using wordTrace_append hprefix tailTrace_3419846
  have hstable : (prefixWord ++ tailWord_3419846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3419846).length < 2 ^ (prefixWord ++ tailWord_3419846).sum := by decide
  have hdescent : baseEnd_3419846 < baseStart_3419846 := by decide
  rcases family_descends (prefixWord ++ tailWord_3419846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3419888 : List Nat := [2, 1, 1, 1, 3, 1, 2, 2, 3, 7]
def baseStart_3419888 : Nat := 118140960795 + 3419888 * 2 ^ 59
def prefixEnd_3419888 : Nat := 4983230072969 + 3 ^ 40 * 3419888 * 2
def baseEnd_3419888 : Nat := 585348776181140302057409

theorem tailTrace_3419888 : CollatzResearch.WordTrace tailWord_3419888 prefixEnd_3419888 585348776181140302057409 := by
  unfold tailWord_3419888
  simp only [CollatzResearch.WordTrace]
  refine ⟨62366781317168660607646159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83155708422891547476861545 62366781317168660607646159)
  ·
    refine ⟨93550171975752990911469239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62366781317168660607646159 93550171975752990911469239)
    ·
      refine ⟨140325257963629486367203859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93550171975752990911469239 140325257963629486367203859)
      ·
        refine ⟨210487886945444229550805789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140325257963629486367203859 210487886945444229550805789)
        ·
          refine ⟨78932957604541586081552171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 210487886945444229550805789 78932957604541586081552171)
          ·
            refine ⟨118399436406812379122328257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78932957604541586081552171 118399436406812379122328257)
            ·
              refine ⟨88799577305109284341746193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118399436406812379122328257 88799577305109284341746193)
              ·
                refine ⟨66599682978831963256309645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88799577305109284341746193 66599682978831963256309645)
                ·
                  refine ⟨24974881117061986221116117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66599682978831963256309645 24974881117061986221116117)
                  ·
                    refine ⟨585348776181140302057409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24974881117061986221116117 585348776181140302057409)
                    ·
                      rfl

theorem cell23_3419888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 3, 7].length) (baseStart_3419888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3419888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3419888 prefixEnd_3419888 := by exact prefixLift 3419888
  have htrace : WordTrace (prefixWord ++ tailWord_3419888) baseStart_3419888 baseEnd_3419888 := by
    simpa [prefixWord, tailWord_3419888, baseEnd_3419888] using wordTrace_append hprefix tailTrace_3419888
  have hstable : (prefixWord ++ tailWord_3419888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3419888).length < 2 ^ (prefixWord ++ tailWord_3419888).sum := by decide
  have hdescent : baseEnd_3419888 < baseStart_3419888 := by decide
  rcases family_descends (prefixWord ++ tailWord_3419888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3419986 : List Nat := [3, 2, 2, 1, 1, 4, 2, 3, 1, 4]
def baseStart_3419986 : Nat := 118140960795 + 3419986 * 2 ^ 59
def prefixEnd_3419986 : Nat := 4983230072969 + 3 ^ 40 * 3419986 * 2
def baseEnd_3419986 : Nat := 585365549882520507582259

theorem tailTrace_3419986 : CollatzResearch.WordTrace tailWord_3419986 prefixEnd_3419986 585365549882520507582259 := by
  unfold tailWord_3419986
  simp only [CollatzResearch.WordTrace]
  refine ⟨31184284246995570988089953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83158091325321522634906541 31184284246995570988089953)
  ·
    refine ⟨23388213185246678241067465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31184284246995570988089953 23388213185246678241067465)
    ·
      refine ⟨17541159888935008680800599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23388213185246678241067465 17541159888935008680800599)
      ·
        refine ⟨26311739833402513021200899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17541159888935008680800599 26311739833402513021200899)
        ·
          refine ⟨39467609750103769531801349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26311739833402513021200899 39467609750103769531801349)
          ·
            refine ⟨7400176828144456787212753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39467609750103769531801349 7400176828144456787212753)
            ·
              refine ⟨5550132621108342590409565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7400176828144456787212753 5550132621108342590409565)
              ·
                refine ⟨2081299732915628471403587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5550132621108342590409565 2081299732915628471403587)
                ·
                  refine ⟨3121949599373442707105381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2081299732915628471403587 3121949599373442707105381)
                  ·
                    refine ⟨585365549882520507582259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3121949599373442707105381 585365549882520507582259)
                    ·
                      rfl

theorem cell23_3419986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 2, 3, 1, 4].length) (baseStart_3419986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3419986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3419986 prefixEnd_3419986 := by exact prefixLift 3419986
  have htrace : WordTrace (prefixWord ++ tailWord_3419986) baseStart_3419986 baseEnd_3419986 := by
    simpa [prefixWord, tailWord_3419986, baseEnd_3419986] using wordTrace_append hprefix tailTrace_3419986
  have hstable : (prefixWord ++ tailWord_3419986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3419986).length < 2 ^ (prefixWord ++ tailWord_3419986).sum := by decide
  have hdescent : baseEnd_3419986 < baseStart_3419986 := by decide
  rcases family_descends (prefixWord ++ tailWord_3419986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3420002 : List Nat := [3, 3, 2, 1, 2, 1, 1, 1, 1, 2, 6]
def baseStart_3420002 : Nat := 118140960795 + 3420002 * 2 ^ 59
def prefixEnd_3420002 : Nat := 4983230072969 + 3 ^ 40 * 3420002 * 2
def baseEnd_3420002 : Nat := 1756104865338033460146703

theorem tailTrace_3420002 : CollatzResearch.WordTrace tailWord_3420002 prefixEnd_3420002 1756104865338033460146703 := by
  unfold tailWord_3420002
  simp only [CollatzResearch.WordTrace]
  refine ⟨31184430138981079671235565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83158480370616212456628173 31184430138981079671235565)
  ·
    refine ⟨11694161302117904876713337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31184430138981079671235565 11694161302117904876713337)
    ·
      refine ⟨8770620976588428657535003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11694161302117904876713337 8770620976588428657535003)
      ·
        refine ⟨13155931464882642986302505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8770620976588428657535003 13155931464882642986302505)
        ·
          refine ⟨9866948598661982239726879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13155931464882642986302505 9866948598661982239726879)
          ·
            refine ⟨14800422897992973359590319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9866948598661982239726879 14800422897992973359590319)
            ·
              refine ⟨22200634346989460039385479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14800422897992973359590319 22200634346989460039385479)
              ·
                refine ⟨33300951520484190059078219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22200634346989460039385479 33300951520484190059078219)
                ·
                  refine ⟨49951427280726285088617329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33300951520484190059078219 49951427280726285088617329)
                  ·
                    refine ⟨37463570460544713816462997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49951427280726285088617329 37463570460544713816462997)
                    ·
                      refine ⟨1756104865338033460146703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37463570460544713816462997 1756104865338033460146703)
                      ·
                        rfl

theorem cell23_3420002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_3420002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3420002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3420002 prefixEnd_3420002 := by exact prefixLift 3420002
  have htrace : WordTrace (prefixWord ++ tailWord_3420002) baseStart_3420002 baseEnd_3420002 := by
    simpa [prefixWord, tailWord_3420002, baseEnd_3420002] using wordTrace_append hprefix tailTrace_3420002
  have hstable : (prefixWord ++ tailWord_3420002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3420002).length < 2 ^ (prefixWord ++ tailWord_3420002).sum := by decide
  have hdescent : baseEnd_3420002 < baseStart_3420002 := by decide
  rcases family_descends (prefixWord ++ tailWord_3420002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3420032 : List Nat := [2, 1, 1, 2, 1, 2, 3, 1, 2, 6, 2]
def baseStart_3420032 : Nat := 118140960795 + 3420032 * 2 ^ 59
def prefixEnd_3420032 : Nat := 4983230072969 + 3 ^ 40 * 3420032 * 2
def baseEnd_3420032 : Nat := 1756120269757668342771565

theorem tailTrace_3420032 : CollatzResearch.WordTrace tailWord_3420032 prefixEnd_3420032 1756120269757668342771565 := by
  unfold tailWord_3420032
  simp only [CollatzResearch.WordTrace]
  refine ⟨62369407372907816904267175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83159209830543755872356233 62369407372907816904267175)
  ·
    refine ⟨93554111059361725356400763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62369407372907816904267175 93554111059361725356400763)
    ·
      refine ⟨140331166589042588034601145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93554111059361725356400763 140331166589042588034601145)
      ·
        refine ⟨105248374941781941025950859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140331166589042588034601145 105248374941781941025950859)
        ·
          refine ⟨157872562412672911538926289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105248374941781941025950859 157872562412672911538926289)
          ·
            refine ⟨118404421809504683654194717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157872562412672911538926289 118404421809504683654194717)
            ·
              refine ⟨44401658178564256370323019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118404421809504683654194717 44401658178564256370323019)
              ·
                refine ⟨66602487267846384555484529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44401658178564256370323019 66602487267846384555484529)
                ·
                  refine ⟨49951865450884788416613397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66602487267846384555484529 49951865450884788416613397)
                  ·
                    refine ⟨2341493693010224457028753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 49951865450884788416613397 2341493693010224457028753)
                    ·
                      refine ⟨1756120269757668342771565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2341493693010224457028753 1756120269757668342771565)
                      ·
                        rfl

theorem cell23_3420032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 2, 6, 2].length) (baseStart_3420032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3420032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3420032 prefixEnd_3420032 := by exact prefixLift 3420032
  have htrace : WordTrace (prefixWord ++ tailWord_3420032) baseStart_3420032 baseEnd_3420032 := by
    simpa [prefixWord, tailWord_3420032, baseEnd_3420032] using wordTrace_append hprefix tailTrace_3420032
  have hstable : (prefixWord ++ tailWord_3420032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3420032).length < 2 ^ (prefixWord ++ tailWord_3420032).sum := by decide
  have hdescent : baseEnd_3420032 < baseStart_3420032 := by decide
  rcases family_descends (prefixWord ++ tailWord_3420032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3420049 : List Nat := [1, 2, 2, 1, 1, 1, 4, 2, 5, 2, 2]
def baseStart_3420049 : Nat := 118140960795 + 3420049 * 2 ^ 59
def prefixEnd_3420049 : Nat := 4983230072969 + 3 ^ 40 * 3420049 * 2
def baseEnd_3420049 : Nat := 1756128998928794776258987

theorem tailTrace_3420049 : CollatzResearch.WordTrace tailWord_3420049 prefixEnd_3420049 1756128998928794776258987 := by
  unfold tailWord_3420049
  simp only [CollatzResearch.WordTrace]
  refine ⟨124739434786754045711903201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83159623191169363807935467 124739434786754045711903201)
  ·
    refine ⟨93554576090065534283927401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124739434786754045711903201 93554576090065534283927401)
    ·
      refine ⟨70165932067549150712945551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93554576090065534283927401 70165932067549150712945551)
      ·
        refine ⟨105248898101323726069418327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70165932067549150712945551 105248898101323726069418327)
        ·
          refine ⟨157873347151985589104127491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105248898101323726069418327 157873347151985589104127491)
          ·
            refine ⟨236810020727978383656191237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157873347151985589104127491 236810020727978383656191237)
            ·
              refine ⟨44401878886495946935535857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 236810020727978383656191237 44401878886495946935535857)
              ·
                refine ⟨33301409164871960201651893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44401878886495946935535857 33301409164871960201651893)
                ·
                  refine ⟨3122007109206746268904865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33301409164871960201651893 3122007109206746268904865)
                  ·
                    refine ⟨2341505331905059701678649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3122007109206746268904865 2341505331905059701678649)
                    ·
                      refine ⟨1756128998928794776258987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2341505331905059701678649 1756128998928794776258987)
                      ·
                        rfl

theorem cell23_3420049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 2, 5, 2, 2].length) (baseStart_3420049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3420049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3420049 prefixEnd_3420049 := by exact prefixLift 3420049
  have htrace : WordTrace (prefixWord ++ tailWord_3420049) baseStart_3420049 baseEnd_3420049 := by
    simpa [prefixWord, tailWord_3420049, baseEnd_3420049] using wordTrace_append hprefix tailTrace_3420049
  have hstable : (prefixWord ++ tailWord_3420049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3420049).length < 2 ^ (prefixWord ++ tailWord_3420049).sum := by decide
  have hdescent : baseEnd_3420049 < baseStart_3420049 := by decide
  rcases family_descends (prefixWord ++ tailWord_3420049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3420055 : List Nat := [1, 1, 3, 3, 1, 3, 11]
def baseStart_3420055 : Nat := 118140960795 + 3420055 * 2 ^ 59
def prefixEnd_3420055 : Nat := 4983230072969 + 3 ^ 40 * 3420055 * 2
def baseEnd_3420055 : Nat := 21680642960650885836839

theorem tailTrace_3420055 : CollatzResearch.WordTrace tailWord_3420055 prefixEnd_3420055 21680642960650885836839 := by
  unfold tailWord_3420055
  simp only [CollatzResearch.WordTrace]
  refine ⟨124739653624732308736621619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83159769083154872491081079 124739653624732308736621619)
  ·
    refine ⟨187109480437098463104932429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124739653624732308736621619 187109480437098463104932429)
    ·
      refine ⟨70166055163911923664349661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187109480437098463104932429 70166055163911923664349661)
      ·
        refine ⟨26312270686466971374131123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70166055163911923664349661 26312270686466971374131123)
        ·
          refine ⟨39468406029700457061196685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26312270686466971374131123 39468406029700457061196685)
          ·
            refine ⟨14800652261137671397948757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39468406029700457061196685 14800652261137671397948757)
            ·
              refine ⟨21680642960650885836839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 14800652261137671397948757 21680642960650885836839)
              ·
                rfl

theorem cell23_3420055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 11].length) (baseStart_3420055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3420055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3420055 prefixEnd_3420055 := by exact prefixLift 3420055
  have htrace : WordTrace (prefixWord ++ tailWord_3420055) baseStart_3420055 baseEnd_3420055 := by
    simpa [prefixWord, tailWord_3420055, baseEnd_3420055] using wordTrace_append hprefix tailTrace_3420055
  have hstable : (prefixWord ++ tailWord_3420055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3420055).length < 2 ^ (prefixWord ++ tailWord_3420055).sum := by decide
  have hdescent : baseEnd_3420055 < baseStart_3420055 := by decide
  rcases family_descends (prefixWord ++ tailWord_3420055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3420060 : List Nat := [2, 2, 3, 3, 1, 2, 3, 2, 1, 1, 3]
def baseStart_3420060 : Nat := 118140960795 + 3420060 * 2 ^ 59
def prefixEnd_3420060 : Nat := 4983230072969 + 3 ^ 40 * 3420060 * 2
def baseEnd_3420060 : Nat := 1756134647215994233221437

theorem tailTrace_3420060 : CollatzResearch.WordTrace tailWord_3420060 prefixEnd_3420060 1756134647215994233221437 := by
  unfold tailWord_3420060
  simp only [CollatzResearch.WordTrace]
  refine ⟨62369917994857097295276817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83159890659809463060369089 62369917994857097295276817)
  ·
    refine ⟨46777438496142822971457613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62369917994857097295276817 46777438496142822971457613)
    ·
      refine ⟨17541539436053558614296605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46777438496142822971457613 17541539436053558614296605)
      ·
        refine ⟨6578077288520084480361227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17541539436053558614296605 6578077288520084480361227)
        ·
          refine ⟨9867115932780126720541841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6578077288520084480361227 9867115932780126720541841)
          ·
            refine ⟨7400336949585095040406381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9867115932780126720541841 7400336949585095040406381)
            ·
              refine ⟨2775126356094410640152393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7400336949585095040406381 2775126356094410640152393)
              ·
                refine ⟨2081344767070807980114295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2775126356094410640152393 2081344767070807980114295)
                ·
                  refine ⟨3122017150606211970171443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2081344767070807980114295 3122017150606211970171443)
                  ·
                    refine ⟨4683025725909317955257165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3122017150606211970171443 4683025725909317955257165)
                    ·
                      refine ⟨1756134647215994233221437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4683025725909317955257165 1756134647215994233221437)
                      ·
                        rfl

theorem cell23_3420060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 3, 2, 1, 1, 3].length) (baseStart_3420060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3420060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3420060 prefixEnd_3420060 := by exact prefixLift 3420060
  have htrace : WordTrace (prefixWord ++ tailWord_3420060) baseStart_3420060 baseEnd_3420060 := by
    simpa [prefixWord, tailWord_3420060, baseEnd_3420060] using wordTrace_append hprefix tailTrace_3420060
  have hstable : (prefixWord ++ tailWord_3420060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3420060).length < 2 ^ (prefixWord ++ tailWord_3420060).sum := by decide
  have hdescent : baseEnd_3420060 < baseStart_3420060 := by decide
  rcases family_descends (prefixWord ++ tailWord_3420060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3420082 : List Nat := [3, 2, 1, 1, 1, 1, 1, 2, 5, 3, 3]
def baseStart_3420082 : Nat := 118140960795 + 3420082 * 2 ^ 59
def prefixEnd_3420082 : Nat := 4983230072969 + 3 ^ 40 * 3420082 * 2
def baseEnd_3420082 : Nat := 1756145943790393147146335

theorem tailTrace_3420082 : CollatzResearch.WordTrace tailWord_3420082 prefixEnd_3420082 1756145943790393147146335 := by
  unfold tailWord_3420082
  simp only [CollatzResearch.WordTrace]
  refine ⟨31185159598908623086963625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83160425597089661565236333 31185159598908623086963625)
  ·
    refine ⟨23388869699181467315222719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31185159598908623086963625 23388869699181467315222719)
    ·
      refine ⟨35083304548772200972834079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23388869699181467315222719 35083304548772200972834079)
      ·
        refine ⟨52624956823158301459251119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35083304548772200972834079 52624956823158301459251119)
        ·
          refine ⟨78937435234737452188876679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52624956823158301459251119 78937435234737452188876679)
          ·
            refine ⟨118406152852106178283315019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78937435234737452188876679 118406152852106178283315019)
            ·
              refine ⟨177609229278159267424972529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118406152852106178283315019 177609229278159267424972529)
              ·
                refine ⟨133206921958619450568729397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 177609229278159267424972529 133206921958619450568729397)
                ·
                  refine ⟨12488148933620573490818381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 133206921958619450568729397 12488148933620573490818381)
                  ·
                    refine ⟨4683055850107715059056893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12488148933620573490818381 4683055850107715059056893)
                    ·
                      refine ⟨1756145943790393147146335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4683055850107715059056893 1756145943790393147146335)
                      ·
                        rfl

theorem cell23_3420082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 5, 3, 3].length) (baseStart_3420082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3420082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3420082 prefixEnd_3420082 := by exact prefixLift 3420082
  have htrace : WordTrace (prefixWord ++ tailWord_3420082) baseStart_3420082 baseEnd_3420082 := by
    simpa [prefixWord, tailWord_3420082, baseEnd_3420082] using wordTrace_append hprefix tailTrace_3420082
  have hstable : (prefixWord ++ tailWord_3420082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3420082).length < 2 ^ (prefixWord ++ tailWord_3420082).sum := by decide
  have hdescent : baseEnd_3420082 < baseStart_3420082 := by decide
  rcases family_descends (prefixWord ++ tailWord_3420082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3420105 : List Nat := [1, 2, 1, 1, 2, 1, 2, 2, 1, 2, 8]
def baseStart_3420105 : Nat := 118140960795 + 3420105 * 2 ^ 59
def prefixEnd_3420105 : Nat := 4983230072969 + 3 ^ 40 * 3420105 * 2
def baseEnd_3420105 : Nat := 1756157753845446557158729

theorem tailTrace_3420105 : CollatzResearch.WordTrace tailWord_3420105 prefixEnd_3420105 1756157753845446557158729 := by
  unfold tailWord_3420105
  simp only [CollatzResearch.WordTrace]
  refine ⟨124741477274551167275941769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83160984849700778183961179 124741477274551167275941769)
  ·
    refine ⟨93556107955913375456956327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124741477274551167275941769 93556107955913375456956327)
    ·
      refine ⟨140334161933870063185434491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93556107955913375456956327 140334161933870063185434491)
      ·
        refine ⟨210501242900805094778151737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140334161933870063185434491 210501242900805094778151737)
        ·
          refine ⟨157875932175603821083613803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210501242900805094778151737 157875932175603821083613803)
          ·
            refine ⟨236813898263405731625420705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157875932175603821083613803 236813898263405731625420705)
            ·
              refine ⟨177610423697554298719065529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 236813898263405731625420705 177610423697554298719065529)
              ·
                refine ⟨133207817773165724039299147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 177610423697554298719065529 133207817773165724039299147)
                ·
                  refine ⟨199811726659748586058948721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 133207817773165724039299147 199811726659748586058948721)
                  ·
                    refine ⟨149858794994811439544211541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 199811726659748586058948721 149858794994811439544211541)
                    ·
                      refine ⟨1756157753845446557158729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 149858794994811439544211541 1756157753845446557158729)
                      ·
                        rfl

theorem cell23_3420105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 2, 8].length) (baseStart_3420105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3420105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3420105 prefixEnd_3420105 := by exact prefixLift 3420105
  have htrace : WordTrace (prefixWord ++ tailWord_3420105) baseStart_3420105 baseEnd_3420105 := by
    simpa [prefixWord, tailWord_3420105, baseEnd_3420105] using wordTrace_append hprefix tailTrace_3420105
  have hstable : (prefixWord ++ tailWord_3420105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3420105).length < 2 ^ (prefixWord ++ tailWord_3420105).sum := by decide
  have hdescent : baseEnd_3420105 < baseStart_3420105 := by decide
  rcases family_descends (prefixWord ++ tailWord_3420105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3420117 : List Nat := [1, 3, 2, 3, 2, 3, 2, 2, 1, 2, 2]
def baseStart_3420117 : Nat := 118140960795 + 3420117 * 2 ^ 59
def prefixEnd_3420117 : Nat := 4983230072969 + 3 ^ 40 * 3420117 * 2
def baseEnd_3420117 : Nat := 1756163915613300510208675

theorem tailTrace_3420117 : CollatzResearch.WordTrace tailWord_3420117 prefixEnd_3420117 1756163915613300510208675 := by
  unfold tailWord_3420117
  simp only [CollatzResearch.WordTrace]
  refine ⟨124741914950507693325378605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83161276633671795550252403 124741914950507693325378605)
  ·
    refine ⟨46778218106440384997016977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124741914950507693325378605 46778218106440384997016977)
    ·
      refine ⟨35083663579830288747762733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46778218106440384997016977 35083663579830288747762733)
      ·
        refine ⟨13156373842436358280411025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35083663579830288747762733 13156373842436358280411025)
        ·
          refine ⟨9867280381827268710308269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13156373842436358280411025 9867280381827268710308269)
          ·
            refine ⟨3700230143185225766365601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9867280381827268710308269 3700230143185225766365601)
            ·
              refine ⟨2775172607388919324774201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3700230143185225766365601 2775172607388919324774201)
              ·
                refine ⟨2081379455541689493580651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2775172607388919324774201 2081379455541689493580651)
                ·
                  refine ⟨3122069183312534240370977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2081379455541689493580651 3122069183312534240370977)
                  ·
                    refine ⟨2341551887484400680278233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3122069183312534240370977 2341551887484400680278233)
                    ·
                      refine ⟨1756163915613300510208675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2341551887484400680278233 1756163915613300510208675)
                      ·
                        rfl

theorem cell23_3420117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 2, 2, 1, 2, 2].length) (baseStart_3420117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3420117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3420117 prefixEnd_3420117 := by exact prefixLift 3420117
  have htrace : WordTrace (prefixWord ++ tailWord_3420117) baseStart_3420117 baseEnd_3420117 := by
    simpa [prefixWord, tailWord_3420117, baseEnd_3420117] using wordTrace_append hprefix tailTrace_3420117
  have hstable : (prefixWord ++ tailWord_3420117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3420117).length < 2 ^ (prefixWord ++ tailWord_3420117).sum := by decide
  have hdescent : baseEnd_3420117 < baseStart_3420117 := by decide
  rcases family_descends (prefixWord ++ tailWord_3420117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3420132 : List Nat := [2, 3, 1, 1, 1, 1, 5, 1, 2, 6]
def baseStart_3420132 : Nat := 118140960795 + 3420132 * 2 ^ 59
def prefixEnd_3420132 : Nat := 4983230072969 + 3 ^ 40 * 3420132 * 2
def baseEnd_3420132 : Nat := 585390539274372650507035

theorem tailTrace_3420132 : CollatzResearch.WordTrace tailWord_3420132 prefixEnd_3420132 585390539274372650507035 := by
  unfold tailWord_3420132
  simp only [CollatzResearch.WordTrace]
  refine ⟨62371231022726675443587325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83161641363635567258116433 62371231022726675443587325)
  ·
    refine ⟨23389211633522503291345247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62371231022726675443587325 23389211633522503291345247)
    ·
      refine ⟨35083817450283754937017871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23389211633522503291345247 35083817450283754937017871)
      ·
        refine ⟨52625726175425632405526807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35083817450283754937017871 52625726175425632405526807)
        ·
          refine ⟨78938589263138448608290211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52625726175425632405526807 78938589263138448608290211)
          ·
            refine ⟨118407883894707672912435317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78938589263138448608290211 118407883894707672912435317)
            ·
              refine ⟨11100739115128844335540811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 118407883894707672912435317 11100739115128844335540811)
              ·
                refine ⟨16651108672693266503311217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11100739115128844335540811 16651108672693266503311217)
                ·
                  refine ⟨12488331504519949877483413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16651108672693266503311217 12488331504519949877483413)
                  ·
                    refine ⟨585390539274372650507035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12488331504519949877483413 585390539274372650507035)
                    ·
                      rfl

theorem cell23_3420132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 1, 2, 6].length) (baseStart_3420132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3420132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3420132 prefixEnd_3420132 := by exact prefixLift 3420132
  have htrace : WordTrace (prefixWord ++ tailWord_3420132) baseStart_3420132 baseEnd_3420132 := by
    simpa [prefixWord, tailWord_3420132, baseEnd_3420132] using wordTrace_append hprefix tailTrace_3420132
  have hstable : (prefixWord ++ tailWord_3420132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3420132).length < 2 ^ (prefixWord ++ tailWord_3420132).sum := by decide
  have hdescent : baseEnd_3420132 < baseStart_3420132 := by decide
  rcases family_descends (prefixWord ++ tailWord_3420132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3420156 : List Nat := [2, 2, 2, 1, 2, 2, 2, 2, 4, 2, 2]
def baseStart_3420156 : Nat := 118140960795 + 3420156 * 2 ^ 59
def prefixEnd_3420156 : Nat := 4983230072969 + 3 ^ 40 * 3420156 * 2
def baseEnd_3420156 : Nat := 1756183941358825857620995

theorem tailTrace_3420156 : CollatzResearch.WordTrace tailWord_3420156 prefixEnd_3420156 1756183941358825857620995 := by
  unfold tailWord_3420156
  simp only [CollatzResearch.WordTrace]
  refine ⟨62371668698683201493024161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83162224931577601990698881 62371668698683201493024161)
  ·
    refine ⟨46778751524012401119768121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62371668698683201493024161 46778751524012401119768121)
    ·
      refine ⟨35084063643009300839826091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46778751524012401119768121 35084063643009300839826091)
      ·
        refine ⟨52626095464513951259739137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35084063643009300839826091 52626095464513951259739137)
        ·
          refine ⟨39469571598385463444804353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52626095464513951259739137 39469571598385463444804353)
          ·
            refine ⟨29602178698789097583603265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39469571598385463444804353 29602178698789097583603265)
            ·
              refine ⟨22201634024091823187702449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29602178698789097583603265 22201634024091823187702449)
              ·
                refine ⟨16651225518068867390776837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22201634024091823187702449 16651225518068867390776837)
                ·
                  refine ⟨3122104784637912635770657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16651225518068867390776837 3122104784637912635770657)
                  ·
                    refine ⟨2341578588478434476827993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3122104784637912635770657 2341578588478434476827993)
                    ·
                      refine ⟨1756183941358825857620995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2341578588478434476827993 1756183941358825857620995)
                      ·
                        rfl

theorem cell23_3420156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 2, 4, 2, 2].length) (baseStart_3420156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3420156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3420156 prefixEnd_3420156 := by exact prefixLift 3420156
  have htrace : WordTrace (prefixWord ++ tailWord_3420156) baseStart_3420156 baseEnd_3420156 := by
    simpa [prefixWord, tailWord_3420156, baseEnd_3420156] using wordTrace_append hprefix tailTrace_3420156
  have hstable : (prefixWord ++ tailWord_3420156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3420156).length < 2 ^ (prefixWord ++ tailWord_3420156).sum := by decide
  have hdescent : baseEnd_3420156 < baseStart_3420156 := by decide
  rcases family_descends (prefixWord ++ tailWord_3420156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3420179 : List Nat := [1, 1, 1, 2, 1, 4, 4, 4, 5]
def baseStart_3420179 : Nat := 118140960795 + 3420179 * 2 ^ 59
def prefixEnd_3420179 : Nat := 4983230072969 + 3 ^ 40 * 3420179 * 2
def baseEnd_3420179 : Nat := 195132861268208807514821

theorem tailTrace_3420179 : CollatzResearch.WordTrace tailWord_3420179 prefixEnd_3420179 195132861268208807514821 := by
  unfold tailWord_3420179
  simp only [CollatzResearch.WordTrace]
  refine ⟨124744176276283077914135591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83162784184188718609423727 124744176276283077914135591)
  ·
    refine ⟨187116264414424616871203387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124744176276283077914135591 187116264414424616871203387)
    ·
      refine ⟨280674396621636925306805081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187116264414424616871203387 280674396621636925306805081)
      ·
        refine ⟨210505797466227693980103811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 280674396621636925306805081 210505797466227693980103811)
        ·
          refine ⟨315758696199341540970155717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210505797466227693980103811 315758696199341540970155717)
          ·
            refine ⟨59204755537376538931904197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 315758696199341540970155717 59204755537376538931904197)
            ·
              refine ⟨11100891663258101049732037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59204755537376538931904197 11100891663258101049732037)
              ·
                refine ⟨2081417186860893946824757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11100891663258101049732037 2081417186860893946824757)
                ·
                  refine ⟨195132861268208807514821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2081417186860893946824757 195132861268208807514821)
                  ·
                    rfl

theorem cell23_3420179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 4, 5].length) (baseStart_3420179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3420179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3420179 prefixEnd_3420179 := by exact prefixLift 3420179
  have htrace : WordTrace (prefixWord ++ tailWord_3420179) baseStart_3420179 baseEnd_3420179 := by
    simpa [prefixWord, tailWord_3420179, baseEnd_3420179] using wordTrace_append hprefix tailTrace_3420179
  have hstable : (prefixWord ++ tailWord_3420179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3420179).length < 2 ^ (prefixWord ++ tailWord_3420179).sum := by decide
  have hdescent : baseEnd_3420179 < baseStart_3420179 := by decide
  rcases family_descends (prefixWord ++ tailWord_3420179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3420230 : List Nat := [6, 1, 1, 1, 1, 1, 5, 2, 5]
def baseStart_3420230 : Nat := 118140960795 + 3420230 * 2 ^ 59
def prefixEnd_3420230 : Nat := 4983230072969 + 3 ^ 40 * 3420230 * 2
def baseEnd_3420230 : Nat := 195135770991917618677295

theorem tailTrace_3420230 : CollatzResearch.WordTrace tailWord_3420230 prefixEnd_3420230 195135770991917618677295 := by
  unfold tailWord_3420230
  simp only [CollatzResearch.WordTrace]
  refine ⟨3898313637471822300757567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 83164024266065542416161429 3898313637471822300757567)
  ·
    refine ⟨5847470456207733451136351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3898313637471822300757567 5847470456207733451136351)
    ·
      refine ⟨8771205684311600176704527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5847470456207733451136351 8771205684311600176704527)
      ·
        refine ⟨13156808526467400265056791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8771205684311600176704527 13156808526467400265056791)
        ·
          refine ⟨19735212789701100397585187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13156808526467400265056791 19735212789701100397585187)
          ·
            refine ⟨29602819184551650596377781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19735212789701100397585187 29602819184551650596377781)
            ·
              refine ⟨2775264298551717243410417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29602819184551650596377781 2775264298551717243410417)
              ·
                refine ⟨2081448223913787932557813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2775264298551717243410417 2081448223913787932557813)
                ·
                  refine ⟨195135770991917618677295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2081448223913787932557813 195135770991917618677295)
                  ·
                    rfl

theorem cell23_3420230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 5, 2, 5].length) (baseStart_3420230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3420230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3420230 prefixEnd_3420230 := by exact prefixLift 3420230
  have htrace : WordTrace (prefixWord ++ tailWord_3420230) baseStart_3420230 baseEnd_3420230 := by
    simpa [prefixWord, tailWord_3420230, baseEnd_3420230] using wordTrace_append hprefix tailTrace_3420230
  have hstable : (prefixWord ++ tailWord_3420230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3420230).length < 2 ^ (prefixWord ++ tailWord_3420230).sum := by decide
  have hdescent : baseEnd_3420230 < baseStart_3420230 := by decide
  rcases family_descends (prefixWord ++ tailWord_3420230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3420232 : List Nat := [2, 1, 3, 1, 1, 1, 2, 1, 1, 5, 5]
def baseStart_3420232 : Nat := 118140960795 + 3420232 * 2 ^ 59
def prefixEnd_3420232 : Nat := 4983230072969 + 3 ^ 40 * 3420232 * 2
def baseEnd_3420232 : Nat := 1756222965888567560270645

theorem tailTrace_3420232 : CollatzResearch.WordTrace tailWord_3420232 prefixEnd_3420232 1756222965888567560270645 := by
  unfold tailWord_3420232
  simp only [CollatzResearch.WordTrace]
  refine ⟨62373054672545533982907475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83164072896727378643876633 62373054672545533982907475)
  ·
    refine ⟨93559582008818300974361213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62373054672545533982907475 93559582008818300974361213)
    ·
      refine ⟨35084843253306862865385455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93559582008818300974361213 35084843253306862865385455)
      ·
        refine ⟨52627264879960294298078183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35084843253306862865385455 52627264879960294298078183)
        ·
          refine ⟨78940897319940441447117275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52627264879960294298078183 78940897319940441447117275)
          ·
            refine ⟨118411345979910662170675913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78940897319940441447117275 118411345979910662170675913)
            ·
              refine ⟨88808509484932996628006935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118411345979910662170675913 88808509484932996628006935)
              ·
                refine ⟨133212764227399494942010403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88808509484932996628006935 133212764227399494942010403)
                ·
                  refine ⟨199819146341099242413015605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 133212764227399494942010403 199819146341099242413015605)
                  ·
                    refine ⟨18733044969478053976220213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 199819146341099242413015605 18733044969478053976220213)
                    ·
                      refine ⟨1756222965888567560270645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18733044969478053976220213 1756222965888567560270645)
                      ·
                        rfl

theorem cell23_3420232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 1, 5, 5].length) (baseStart_3420232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3420232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3420232 prefixEnd_3420232 := by exact prefixLift 3420232
  have htrace : WordTrace (prefixWord ++ tailWord_3420232) baseStart_3420232 baseEnd_3420232 := by
    simpa [prefixWord, tailWord_3420232, baseEnd_3420232] using wordTrace_append hprefix tailTrace_3420232
  have hstable : (prefixWord ++ tailWord_3420232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3420232).length < 2 ^ (prefixWord ++ tailWord_3420232).sum := by decide
  have hdescent : baseEnd_3420232 < baseStart_3420232 := by decide
  rcases family_descends (prefixWord ++ tailWord_3420232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3420249 : List Nat := [1, 2, 1, 2, 2, 1, 3, 2, 4, 2, 3]
def baseStart_3420249 : Nat := 118140960795 + 3420249 * 2 ^ 59
def prefixEnd_3420249 : Nat := 4983230072969 + 3 ^ 40 * 3420249 * 2
def baseEnd_3420249 : Nat := 1756231695059693993758067

theorem tailTrace_3420249 : CollatzResearch.WordTrace tailWord_3420249 prefixEnd_3420249 1756231695059693993758067 := by
  unfold tailWord_3420249
  simp only [CollatzResearch.WordTrace]
  refine ⟨124746729386029479869183801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83164486257352986579455867 124746729386029479869183801)
  ·
    refine ⟨93560047039522109901887851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124746729386029479869183801 93560047039522109901887851)
    ·
      refine ⟨140340070559283164852831777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93560047039522109901887851 140340070559283164852831777)
      ·
        refine ⟨105255052919462373639623833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140340070559283164852831777 105255052919462373639623833)
        ·
          refine ⟨78941289689596780229717875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105255052919462373639623833 78941289689596780229717875)
          ·
            refine ⟨118411934534395170344576813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78941289689596780229717875 118411934534395170344576813)
            ·
              refine ⟨44404475450398188879216305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118411934534395170344576813 44404475450398188879216305)
              ·
                refine ⟨33303356587798641659412229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44404475450398188879216305 33303356587798641659412229)
                ·
                  refine ⟨6244379360212245311139793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33303356587798641659412229 6244379360212245311139793)
                  ·
                    refine ⟨4683284520159183983354845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6244379360212245311139793 4683284520159183983354845)
                    ·
                      refine ⟨1756231695059693993758067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4683284520159183983354845 1756231695059693993758067)
                      ·
                        rfl

theorem cell23_3420249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 2, 4, 2, 3].length) (baseStart_3420249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3420249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3420249 prefixEnd_3420249 := by exact prefixLift 3420249
  have htrace : WordTrace (prefixWord ++ tailWord_3420249) baseStart_3420249 baseEnd_3420249 := by
    simpa [prefixWord, tailWord_3420249, baseEnd_3420249] using wordTrace_append hprefix tailTrace_3420249
  have hstable : (prefixWord ++ tailWord_3420249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3420249).length < 2 ^ (prefixWord ++ tailWord_3420249).sum := by decide
  have hdescent : baseEnd_3420249 < baseStart_3420249 := by decide
  rcases family_descends (prefixWord ++ tailWord_3420249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3420316 : List Nat := [2, 2, 3, 2, 1, 1, 2, 4, 1, 5]
def baseStart_3420316 : Nat := 118140960795 + 3420316 * 2 ^ 59
def prefixEnd_3420316 : Nat := 4983230072969 + 3 ^ 40 * 3420316 * 2
def baseEnd_3420316 : Nat := 585422032754515077206753

theorem tailTrace_3420316 : CollatzResearch.WordTrace tailWord_3420316 prefixEnd_3420316 585422032754515077206753 := by
  unfold tailWord_3420316
  simp only [CollatzResearch.WordTrace]
  refine ⟨62374586538393375155936401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83166115384524500207915201 62374586538393375155936401)
  ·
    refine ⟨46780939903795031366952301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62374586538393375155936401 46780939903795031366952301)
    ·
      refine ⟨17542852463923136762607113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46780939903795031366952301 17542852463923136762607113)
      ·
        refine ⟨13157139347942352571955335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17542852463923136762607113 13157139347942352571955335)
        ·
          refine ⟨19735709021913528857933003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13157139347942352571955335 19735709021913528857933003)
          ·
            refine ⟨29603563532870293286899505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19735709021913528857933003 29603563532870293286899505)
            ·
              refine ⟨22202672649652719965174629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29603563532870293286899505 22202672649652719965174629)
              ·
                refine ⟨4163001121809884993470243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22202672649652719965174629 4163001121809884993470243)
                ·
                  refine ⟨6244501682714827490205365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4163001121809884993470243 6244501682714827490205365)
                  ·
                    refine ⟨585422032754515077206753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6244501682714827490205365 585422032754515077206753)
                    ·
                      rfl

theorem cell23_3420316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 4, 1, 5].length) (baseStart_3420316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3420316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3420316 prefixEnd_3420316 := by exact prefixLift 3420316
  have htrace : WordTrace (prefixWord ++ tailWord_3420316) baseStart_3420316 baseEnd_3420316 := by
    simpa [prefixWord, tailWord_3420316, baseEnd_3420316] using wordTrace_append hprefix tailTrace_3420316
  have hstable : (prefixWord ++ tailWord_3420316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3420316).length < 2 ^ (prefixWord ++ tailWord_3420316).sum := by decide
  have hdescent : baseEnd_3420316 < baseStart_3420316 := by decide
  rcases family_descends (prefixWord ++ tailWord_3420316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3420333 : List Nat := [1, 5, 2, 1, 2, 2, 1, 3, 1, 5]
def baseStart_3420333 : Nat := 118140960795 + 3420333 * 2 ^ 59
def prefixEnd_3420333 : Nat := 4983230072969 + 3 ^ 40 * 3420333 * 2
def baseEnd_3420333 : Nat := 585424942478223888369227

theorem tailTrace_3420333 : CollatzResearch.WordTrace tailWord_3420333 prefixEnd_3420333 585424942478223888369227 := by
  unfold tailWord_3420333
  simp only [CollatzResearch.WordTrace]
  refine ⟨124749793117725162215241653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83166528745150108143494435 124749793117725162215241653)
  ·
    refine ⟨11695293104786733957678905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 124749793117725162215241653 11695293104786733957678905)
    ·
      refine ⟨8771469828590050468259179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11695293104786733957678905 8771469828590050468259179)
      ·
        refine ⟨13157204742885075702388769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8771469828590050468259179 13157204742885075702388769)
        ·
          refine ⟨9867903557163806776791577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13157204742885075702388769 9867903557163806776791577)
          ·
            refine ⟨7400927667872855082593683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9867903557163806776791577 7400927667872855082593683)
            ·
              refine ⟨11101391501809282623890525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7400927667872855082593683 11101391501809282623890525)
              ·
                refine ⟨4163021813178480983958947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11101391501809282623890525 4163021813178480983958947)
                ·
                  refine ⟨6244532719767721475938421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4163021813178480983958947 6244532719767721475938421)
                  ·
                    refine ⟨585424942478223888369227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6244532719767721475938421 585424942478223888369227)
                    ·
                      rfl

theorem cell23_3420333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 3, 1, 5].length) (baseStart_3420333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3420333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3420333 prefixEnd_3420333 := by exact prefixLift 3420333
  have htrace : WordTrace (prefixWord ++ tailWord_3420333) baseStart_3420333 baseEnd_3420333 := by
    simpa [prefixWord, tailWord_3420333, baseEnd_3420333] using wordTrace_append hprefix tailTrace_3420333
  have hstable : (prefixWord ++ tailWord_3420333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3420333).length < 2 ^ (prefixWord ++ tailWord_3420333).sum := by decide
  have hdescent : baseEnd_3420333 < baseStart_3420333 := by decide
  rcases family_descends (prefixWord ++ tailWord_3420333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3420339 : List Nat := [1, 1, 1, 2, 3, 2, 1, 5, 1, 1, 5]
def baseStart_3420339 : Nat := 118140960795 + 3420339 * 2 ^ 59
def prefixEnd_3420339 : Nat := 4983230072969 + 3 ^ 40 * 3420339 * 2
def baseEnd_3420339 : Nat := 1756277908318598641632653

theorem tailTrace_3420339 : CollatzResearch.WordTrace tailWord_3420339 prefixEnd_3420339 1756277908318598641632653 := by
  unfold tailWord_3420339
  simp only [CollatzResearch.WordTrace]
  refine ⟨124750011955703425239960071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83166674637135616826640047 124750011955703425239960071)
  ·
    refine ⟨187125017933555137859940107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124750011955703425239960071 187125017933555137859940107)
    ·
      refine ⟨280687526900332706789910161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187125017933555137859940107 280687526900332706789910161)
      ·
        refine ⟨210515645175249530092432621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 280687526900332706789910161 210515645175249530092432621)
        ·
          refine ⟨78943366940718573784662233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 210515645175249530092432621 78943366940718573784662233)
          ·
            refine ⟨59207525205538930338496675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78943366940718573784662233 59207525205538930338496675)
            ·
              refine ⟨88811287808308395507745013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59207525205538930338496675 88811287808308395507745013)
              ·
                refine ⟨8326058232028912078851095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 88811287808308395507745013 8326058232028912078851095)
                ·
                  refine ⟨12489087348043368118276643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8326058232028912078851095 12489087348043368118276643)
                  ·
                    refine ⟨18733631022065052177414965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12489087348043368118276643 18733631022065052177414965)
                    ·
                      refine ⟨1756277908318598641632653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18733631022065052177414965 1756277908318598641632653)
                      ·
                        rfl

theorem cell23_3420339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 5, 1, 1, 5].length) (baseStart_3420339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3420339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3420339 prefixEnd_3420339 := by exact prefixLift 3420339
  have htrace : WordTrace (prefixWord ++ tailWord_3420339) baseStart_3420339 baseEnd_3420339 := by
    simpa [prefixWord, tailWord_3420339, baseEnd_3420339] using wordTrace_append hprefix tailTrace_3420339
  have hstable : (prefixWord ++ tailWord_3420339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3420339).length < 2 ^ (prefixWord ++ tailWord_3420339).sum := by decide
  have hdescent : baseEnd_3420339 < baseStart_3420339 := by decide
  rcases family_descends (prefixWord ++ tailWord_3420339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3420349 : List Nat := [1, 4, 1, 2, 1, 1, 1, 4, 1, 1, 6]
def baseStart_3420349 : Nat := 118140960795 + 3420349 * 2 ^ 59
def prefixEnd_3420349 : Nat := 4983230072969 + 3 ^ 40 * 3420349 * 2
def baseEnd_3420349 : Nat := 1756283043125143602507607

theorem tailTrace_3420349 : CollatzResearch.WordTrace tailWord_3420349 prefixEnd_3420349 1756283043125143602507607 := by
  unfold tailWord_3420349
  simp only [CollatzResearch.WordTrace]
  refine ⟨124750376685667196947824101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83166917790444797965216067 124750376685667196947824101)
  ·
    refine ⟨23390695628562599427717019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124750376685667196947824101 23390695628562599427717019)
    ·
      refine ⟨35086043442843899141575529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23390695628562599427717019 35086043442843899141575529)
      ·
        refine ⟨26314532582132924356181647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35086043442843899141575529 26314532582132924356181647)
        ·
          refine ⟨39471798873199386534272471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26314532582132924356181647 39471798873199386534272471)
          ·
            refine ⟨59207698309799079801408707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39471798873199386534272471 59207698309799079801408707)
            ·
              refine ⟨88811547464698619702113061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59207698309799079801408707 88811547464698619702113061)
              ·
                refine ⟨16652165149630991194146199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88811547464698619702113061 16652165149630991194146199)
                ·
                  refine ⟨24978247724446486791219299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16652165149630991194146199 24978247724446486791219299)
                  ·
                    refine ⟨37467371586669730186828949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24978247724446486791219299 37467371586669730186828949)
                    ·
                      refine ⟨1756283043125143602507607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37467371586669730186828949 1756283043125143602507607)
                      ·
                        rfl

theorem cell23_3420349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 4, 1, 1, 6].length) (baseStart_3420349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3420349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3420349 prefixEnd_3420349 := by exact prefixLift 3420349
  have htrace : WordTrace (prefixWord ++ tailWord_3420349) baseStart_3420349 baseEnd_3420349 := by
    simpa [prefixWord, tailWord_3420349, baseEnd_3420349] using wordTrace_append hprefix tailTrace_3420349
  have hstable : (prefixWord ++ tailWord_3420349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3420349).length < 2 ^ (prefixWord ++ tailWord_3420349).sum := by decide
  have hdescent : baseEnd_3420349 < baseStart_3420349 := by decide
  rcases family_descends (prefixWord ++ tailWord_3420349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3420356 : List Nat := [2, 3, 3, 1, 2, 1, 1, 1, 3, 1, 5]
def baseStart_3420356 : Nat := 118140960795 + 3420356 * 2 ^ 59
def prefixEnd_3420356 : Nat := 4983230072969 + 3 ^ 40 * 3420356 * 2
def baseEnd_3420356 : Nat := 1756286637489725075120075

theorem tailTrace_3420356 : CollatzResearch.WordTrace tailWord_3420356 prefixEnd_3420356 1756286637489725075120075 := by
  unfold tailWord_3420356
  simp only [CollatzResearch.WordTrace]
  refine ⟨62375315998320918571664461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83167087997761224762219281 62375315998320918571664461)
  ·
    refine ⟨23390743499370344464374173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62375315998320918571664461 23390743499370344464374173)
    ·
      refine ⟨8771528812263879174140315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23390743499370344464374173 8771528812263879174140315)
      ·
        refine ⟨13157293218395818761210473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8771528812263879174140315 13157293218395818761210473)
        ·
          refine ⟨9867969913796864070907855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13157293218395818761210473 9867969913796864070907855)
          ·
            refine ⟨14801954870695296106361783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9867969913796864070907855 14801954870695296106361783)
            ·
              refine ⟨22202932306042944159542675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14801954870695296106361783 22202932306042944159542675)
              ·
                refine ⟨33304398459064416239314013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22202932306042944159542675 33304398459064416239314013)
                ·
                  refine ⟨12489149422149156089742755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33304398459064416239314013 12489149422149156089742755)
                  ·
                    refine ⟨18733724133223734134614133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12489149422149156089742755 18733724133223734134614133)
                    ·
                      refine ⟨1756286637489725075120075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18733724133223734134614133 1756286637489725075120075)
                      ·
                        rfl

theorem cell23_3420356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_3420356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3420356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3420356 prefixEnd_3420356 := by exact prefixLift 3420356
  have htrace : WordTrace (prefixWord ++ tailWord_3420356) baseStart_3420356 baseEnd_3420356 := by
    simpa [prefixWord, tailWord_3420356, baseEnd_3420356] using wordTrace_append hprefix tailTrace_3420356
  have hstable : (prefixWord ++ tailWord_3420356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3420356).length < 2 ^ (prefixWord ++ tailWord_3420356).sum := by decide
  have hdescent : baseEnd_3420356 < baseStart_3420356 := by decide
  rcases family_descends (prefixWord ++ tailWord_3420356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3420363 : List Nat := [1, 1, 1, 1, 3, 2, 7, 1, 2, 4]
def baseStart_3420363 : Nat := 118140960795 + 3420363 * 2 ^ 59
def prefixEnd_3420363 : Nat := 4983230072969 + 3 ^ 40 * 3420363 * 2
def baseEnd_3420363 : Nat := 585430077284768849244181

theorem tailTrace_3420363 : CollatzResearch.WordTrace tailWord_3420363 prefixEnd_3420363 585430077284768849244181 := by
  unfold tailWord_3420363
  simp only [CollatzResearch.WordTrace]
  refine ⟨124750887307616477338833743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83167258205077651559222495 124750887307616477338833743)
  ·
    refine ⟨187126330961424716008250615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124750887307616477338833743 187126330961424716008250615)
    ·
      refine ⟨280689496442137074012375923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187126330961424716008250615 280689496442137074012375923)
      ·
        refine ⟨421034244663205611018563885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280689496442137074012375923 421034244663205611018563885)
        ·
          refine ⟨157887841748702104131961457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 421034244663205611018563885 157887841748702104131961457)
          ·
            refine ⟨118415881311526578098971093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157887841748702104131961457 118415881311526578098971093)
            ·
              refine ⟨2775372218238904174194635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 118415881311526578098971093 2775372218238904174194635)
              ·
                refine ⟨4163058327358356261291953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2775372218238904174194635 4163058327358356261291953)
                ·
                  refine ⟨3122293745518767195968965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4163058327358356261291953 3122293745518767195968965)
                  ·
                    refine ⟨585430077284768849244181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3122293745518767195968965 585430077284768849244181)
                    ·
                      rfl

theorem cell23_3420363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 7, 1, 2, 4].length) (baseStart_3420363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3420363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3420363 prefixEnd_3420363 := by exact prefixLift 3420363
  have htrace : WordTrace (prefixWord ++ tailWord_3420363) baseStart_3420363 baseEnd_3420363 := by
    simpa [prefixWord, tailWord_3420363, baseEnd_3420363] using wordTrace_append hprefix tailTrace_3420363
  have hstable : (prefixWord ++ tailWord_3420363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3420363).length < 2 ^ (prefixWord ++ tailWord_3420363).sum := by decide
  have hdescent : baseEnd_3420363 < baseStart_3420363 := by decide
  rcases family_descends (prefixWord ++ tailWord_3420363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3420366 : List Nat := [4, 1, 1, 1, 4, 2, 1, 1, 1, 1, 6]
def baseStart_3420366 : Nat := 118140960795 + 3420366 * 2 ^ 59
def prefixEnd_3420366 : Nat := 4983230072969 + 3 ^ 40 * 3420366 * 2
def baseEnd_3420366 : Nat := 1756291772296270035995029

theorem tailTrace_3420366 : CollatzResearch.WordTrace tailWord_3420366 prefixEnd_3420366 1756291772296270035995029 := by
  unfold tailWord_3420366
  simp only [CollatzResearch.WordTrace]
  refine ⟨15593874590825701106399119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83167331151070405900795301 15593874590825701106399119)
  ·
    refine ⟨23390811886238551659598679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15593874590825701106399119 23390811886238551659598679)
    ·
      refine ⟨35086217829357827489398019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23390811886238551659598679 35086217829357827489398019)
      ·
        refine ⟨52629326744036741234097029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35086217829357827489398019 52629326744036741234097029)
        ·
          refine ⟨9867998764506888981393193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52629326744036741234097029 9867998764506888981393193)
          ·
            refine ⟨7400999073380166736044895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9867998764506888981393193 7400999073380166736044895)
            ·
              refine ⟨11101498610070250104067343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7400999073380166736044895 11101498610070250104067343)
              ·
                refine ⟨16652247915105375156101015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11101498610070250104067343 16652247915105375156101015)
                ·
                  refine ⟨24978371872658062734151523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16652247915105375156101015 24978371872658062734151523)
                  ·
                    refine ⟨37467557808987094101227285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24978371872658062734151523 37467557808987094101227285)
                    ·
                      refine ⟨1756291772296270035995029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37467557808987094101227285 1756291772296270035995029)
                      ·
                        rfl

theorem cell23_3420366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 1, 1, 1, 6].length) (baseStart_3420366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3420366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3420366 prefixEnd_3420366 := by exact prefixLift 3420366
  have htrace : WordTrace (prefixWord ++ tailWord_3420366) baseStart_3420366 baseEnd_3420366 := by
    simpa [prefixWord, tailWord_3420366, baseEnd_3420366] using wordTrace_append hprefix tailTrace_3420366
  have hstable : (prefixWord ++ tailWord_3420366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3420366).length < 2 ^ (prefixWord ++ tailWord_3420366).sum := by decide
  have hdescent : baseEnd_3420366 < baseStart_3420366 := by decide
  rcases family_descends (prefixWord ++ tailWord_3420366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3420370 : List Nat := [3, 2, 2, 2, 1, 2, 2, 2, 3, 2, 2]
def baseStart_3420370 : Nat := 118140960795 + 3420370 * 2 ^ 59
def prefixEnd_3420370 : Nat := 4983230072969 + 3 ^ 40 * 3420370 * 2
def baseEnd_3420370 : Nat := 1756293826218888020345011

theorem tailTrace_3420370 : CollatzResearch.WordTrace tailWord_3420370 prefixEnd_3420370 1756293826218888020345011 := by
  unfold tailWord_3420370
  simp only [CollatzResearch.WordTrace]
  refine ⟨31187785654647779383584641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83167428412394078356225709 31187785654647779383584641)
  ·
    refine ⟨23390839240985834537688481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31187785654647779383584641 23390839240985834537688481)
    ·
      refine ⟨17543129430739375903266361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23390839240985834537688481 17543129430739375903266361)
      ·
        refine ⟨13157347073054531927449771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17543129430739375903266361 13157347073054531927449771)
        ·
          refine ⟨19736020609581797891174657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13157347073054531927449771 19736020609581797891174657)
          ·
            refine ⟨14802015457186348418380993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19736020609581797891174657 14802015457186348418380993)
            ·
              refine ⟨11101511592889761313785745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14802015457186348418380993 11101511592889761313785745)
              ·
                refine ⟨8326133694667320985339309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11101511592889761313785745 8326133694667320985339309)
                ·
                  refine ⟨3122300135500245369502241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8326133694667320985339309 3122300135500245369502241)
                  ·
                    refine ⟨2341725101625184027126681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3122300135500245369502241 2341725101625184027126681)
                    ·
                      refine ⟨1756293826218888020345011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2341725101625184027126681 1756293826218888020345011)
                      ·
                        rfl

theorem cell23_3420370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 2, 3, 2, 2].length) (baseStart_3420370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3420370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3420370 prefixEnd_3420370 := by exact prefixLift 3420370
  have htrace : WordTrace (prefixWord ++ tailWord_3420370) baseStart_3420370 baseEnd_3420370 := by
    simpa [prefixWord, tailWord_3420370, baseEnd_3420370] using wordTrace_append hprefix tailTrace_3420370
  have hstable : (prefixWord ++ tailWord_3420370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3420370).length < 2 ^ (prefixWord ++ tailWord_3420370).sum := by decide
  have hdescent : baseEnd_3420370 < baseStart_3420370 := by decide
  rcases family_descends (prefixWord ++ tailWord_3420370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3420376 : List Nat := [2, 1, 2, 2, 4, 1, 4, 7]
def baseStart_3420376 : Nat := 118140960795 + 3420376 * 2 ^ 59
def prefixEnd_3420376 : Nat := 4983230072969 + 3 ^ 40 * 3420376 * 2
def baseEnd_3420376 : Nat := 65048033596400555439629

theorem tailTrace_3420376 : CollatzResearch.WordTrace tailWord_3420376 prefixEnd_3420376 65048033596400555439629 := by
  unfold tailWord_3420376
  simp only [CollatzResearch.WordTrace]
  refine ⟨62375680728284690279528491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83167574304379587039371321 62375680728284690279528491)
  ·
    refine ⟨93563521092427035419292737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62375680728284690279528491 93563521092427035419292737)
    ·
      refine ⟨70172640819320276564469553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93563521092427035419292737 70172640819320276564469553)
      ·
        refine ⟨52629480614490207423352165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70172640819320276564469553 52629480614490207423352165)
        ·
          refine ⟨9868027615216913891878531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52629480614490207423352165 9868027615216913891878531)
          ·
            refine ⟨14802041422825370837817797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9868027615216913891878531 14802041422825370837817797)
            ·
              refine ⟨2775382766779757032090837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14802041422825370837817797 2775382766779757032090837)
              ·
                refine ⟨65048033596400555439629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2775382766779757032090837 65048033596400555439629)
                ·
                  rfl

theorem cell23_3420376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 4, 7].length) (baseStart_3420376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3420376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3420376 prefixEnd_3420376 := by exact prefixLift 3420376
  have htrace : WordTrace (prefixWord ++ tailWord_3420376) baseStart_3420376 baseEnd_3420376 := by
    simpa [prefixWord, tailWord_3420376, baseEnd_3420376] using wordTrace_append hprefix tailTrace_3420376
  have hstable : (prefixWord ++ tailWord_3420376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3420376).length < 2 ^ (prefixWord ++ tailWord_3420376).sum := by decide
  have hdescent : baseEnd_3420376 < baseStart_3420376 := by decide
  rcases family_descends (prefixWord ++ tailWord_3420376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3420403 : List Nat := [1, 1, 1, 2, 2, 4, 2, 4, 2, 1, 3]
def baseStart_3420403 : Nat := 118140960795 + 3420403 * 2 ^ 59
def prefixEnd_3420403 : Nat := 4983230072969 + 3 ^ 40 * 3420403 * 2
def baseEnd_3420403 : Nat := 1756310771080486391232359

theorem tailTrace_3420403 : CollatzResearch.WordTrace tailWord_3420403 prefixEnd_3420403 1756310771080486391232359 := by
  unfold tailWord_3420403
  simp only [CollatzResearch.WordTrace]
  refine ⟨124752346227471564170289863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83168230818314376113526575 124752346227471564170289863)
  ·
    refine ⟨187128519341207346255434795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124752346227471564170289863 187128519341207346255434795)
    ·
      refine ⟨280692779011811019383152193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187128519341207346255434795 280692779011811019383152193)
      ·
        refine ⟨210519584258858264537364145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 280692779011811019383152193 210519584258858264537364145)
        ·
          refine ⟨157889688194143698403023109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210519584258858264537364145 157889688194143698403023109)
          ·
            refine ⟨29604316536401943450566833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 157889688194143698403023109 29604316536401943450566833)
            ·
              refine ⟨22203237402301457587925125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29604316536401943450566833 22203237402301457587925125)
              ·
                refine ⟨4163107012931523297735961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22203237402301457587925125 4163107012931523297735961)
                ·
                  refine ⟨3122330259698642473301971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4163107012931523297735961 3122330259698642473301971)
                  ·
                    refine ⟨4683495389547963709952957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3122330259698642473301971 4683495389547963709952957)
                    ·
                      refine ⟨1756310771080486391232359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4683495389547963709952957 1756310771080486391232359)
                      ·
                        rfl

theorem cell23_3420403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 4, 2, 1, 3].length) (baseStart_3420403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3420403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3420403 prefixEnd_3420403 := by exact prefixLift 3420403
  have htrace : WordTrace (prefixWord ++ tailWord_3420403) baseStart_3420403 baseEnd_3420403 := by
    simpa [prefixWord, tailWord_3420403, baseEnd_3420403] using wordTrace_append hprefix tailTrace_3420403
  have hstable : (prefixWord ++ tailWord_3420403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3420403).length < 2 ^ (prefixWord ++ tailWord_3420403).sum := by decide
  have hdescent : baseEnd_3420403 < baseStart_3420403 := by decide
  rcases family_descends (prefixWord ++ tailWord_3420403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3420419 : List Nat := [1, 1, 1, 3, 2, 3, 2, 1, 1, 8]
def baseStart_3420419 : Nat := 118140960795 + 3420419 * 2 ^ 59
def prefixEnd_3420419 : Nat := 4983230072969 + 3 ^ 40 * 3420419 * 2
def baseEnd_3420419 : Nat := 585439662256986109544095

theorem tailTrace_3420419 : CollatzResearch.WordTrace tailWord_3420419 prefixEnd_3420419 585439662256986109544095 := by
  unfold tailWord_3420419
  simp only [CollatzResearch.WordTrace]
  refine ⟨124752929795413598902872311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83168619863609065935248207 124752929795413598902872311)
  ·
    refine ⟨187129394693120398354308467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124752929795413598902872311 187129394693120398354308467)
    ·
      refine ⟨280694092039680597531462701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187129394693120398354308467 280694092039680597531462701)
      ·
        refine ⟨105260284514880224074298513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 280694092039680597531462701 105260284514880224074298513)
        ·
          refine ⟨78945213386160168055723885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105260284514880224074298513 78945213386160168055723885)
          ·
            refine ⟨29604455019810063020896457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78945213386160168055723885 29604455019810063020896457)
            ·
              refine ⟨22203341264857547265672343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29604455019810063020896457 22203341264857547265672343)
              ·
                refine ⟨33305011897286320898508515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22203341264857547265672343 33305011897286320898508515)
                ·
                  refine ⟨49957517845929481347762773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33305011897286320898508515 49957517845929481347762773)
                  ·
                    refine ⟨585439662256986109544095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 49957517845929481347762773 585439662256986109544095)
                    ·
                      rfl

theorem cell23_3420419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 1, 1, 8].length) (baseStart_3420419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3420419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3420419 prefixEnd_3420419 := by exact prefixLift 3420419
  have htrace : WordTrace (prefixWord ++ tailWord_3420419) baseStart_3420419 baseEnd_3420419 := by
    simpa [prefixWord, tailWord_3420419, baseEnd_3420419] using wordTrace_append hprefix tailTrace_3420419
  have hstable : (prefixWord ++ tailWord_3420419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3420419).length < 2 ^ (prefixWord ++ tailWord_3420419).sum := by decide
  have hdescent : baseEnd_3420419 < baseStart_3420419 := by decide
  rcases family_descends (prefixWord ++ tailWord_3420419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3420443 : List Nat := [1, 1, 1, 1, 1, 1, 6, 1, 6, 2, 2]
def baseStart_3420443 : Nat := 118140960795 + 3420443 * 2 ^ 59
def prefixEnd_3420443 : Nat := 4983230072969 + 3 ^ 40 * 3420443 * 2
def baseEnd_3420443 : Nat := 1756331310306666234732175

theorem tailTrace_3420443 : CollatzResearch.WordTrace tailWord_3420443 prefixEnd_3420443 1756331310306666234732175 := by
  unfold tailWord_3420443
  simp only [CollatzResearch.WordTrace]
  refine ⟨124753805147326651001745983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83169203431551100667830655 124753805147326651001745983)
  ·
    refine ⟨187130707720989976502618975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124753805147326651001745983 187130707720989976502618975)
    ·
      refine ⟨280696061581484964753928463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187130707720989976502618975 280696061581484964753928463)
      ·
        refine ⟨421044092372227447130892695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280696061581484964753928463 421044092372227447130892695)
        ·
          refine ⟨631566138558341170696339043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 421044092372227447130892695 631566138558341170696339043)
          ·
            refine ⟨947349207837511756044508565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 631566138558341170696339043 947349207837511756044508565)
            ·
              refine ⟨44406994117383363564586339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 947349207837511756044508565 44406994117383363564586339)
              ·
                refine ⟨66610491176075045346879509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44406994117383363564586339 66610491176075045346879509)
                ·
                  refine ⟨3122366773878517750634977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 66610491176075045346879509 3122366773878517750634977)
                  ·
                    refine ⟨2341775080408888312976233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3122366773878517750634977 2341775080408888312976233)
                    ·
                      refine ⟨1756331310306666234732175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2341775080408888312976233 1756331310306666234732175)
                      ·
                        rfl

theorem cell23_3420443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 6, 2, 2].length) (baseStart_3420443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3420443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3420443 prefixEnd_3420443 := by exact prefixLift 3420443
  have htrace : WordTrace (prefixWord ++ tailWord_3420443) baseStart_3420443 baseEnd_3420443 := by
    simpa [prefixWord, tailWord_3420443, baseEnd_3420443] using wordTrace_append hprefix tailTrace_3420443
  have hstable : (prefixWord ++ tailWord_3420443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3420443).length < 2 ^ (prefixWord ++ tailWord_3420443).sum := by decide
  have hdescent : baseEnd_3420443 < baseStart_3420443 := by decide
  rcases family_descends (prefixWord ++ tailWord_3420443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3420447 : List Nat := [1, 1, 2, 4, 3, 2, 3, 1, 1, 3, 2]
def baseStart_3420447 : Nat := 118140960795 + 3420447 * 2 ^ 59
def prefixEnd_3420447 : Nat := 4983230072969 + 3 ^ 40 * 3420447 * 2
def baseEnd_3420447 : Nat := 1756333364229284219082157

theorem tailTrace_3420447 : CollatzResearch.WordTrace tailWord_3420447 prefixEnd_3420447 1756333364229284219082157 := by
  unfold tailWord_3420447
  simp only [CollatzResearch.WordTrace]
  refine ⟨124753951039312159684891595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83169300692874773123261063 124753951039312159684891595)
  ·
    refine ⟨187130926558968239527337393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124753951039312159684891595 187130926558968239527337393)
    ·
      refine ⟨140348194919226179645503045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187130926558968239527337393 140348194919226179645503045)
      ·
        refine ⟨26315286547354908683531821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 140348194919226179645503045 26315286547354908683531821)
        ·
          refine ⟨9868232455258090756324433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26315286547354908683531821 9868232455258090756324433)
          ·
            refine ⟨7401174341443568067243325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9868232455258090756324433 7401174341443568067243325)
            ·
              refine ⟨2775440378041338025216247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7401174341443568067243325 2775440378041338025216247)
              ·
                refine ⟨4163160567062007037824371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2775440378041338025216247 4163160567062007037824371)
                ·
                  refine ⟨6244740850593010556736557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4163160567062007037824371 6244740850593010556736557)
                  ·
                    refine ⟨2341777818972378958776209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6244740850593010556736557 2341777818972378958776209)
                    ·
                      refine ⟨1756333364229284219082157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2341777818972378958776209 1756333364229284219082157)
                      ·
                        rfl

theorem cell23_3420447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 3, 1, 1, 3, 2].length) (baseStart_3420447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3420447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3420447 prefixEnd_3420447 := by exact prefixLift 3420447
  have htrace : WordTrace (prefixWord ++ tailWord_3420447) baseStart_3420447 baseEnd_3420447 := by
    simpa [prefixWord, tailWord_3420447, baseEnd_3420447] using wordTrace_append hprefix tailTrace_3420447
  have hstable : (prefixWord ++ tailWord_3420447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3420447).length < 2 ^ (prefixWord ++ tailWord_3420447).sum := by decide
  have hdescent : baseEnd_3420447 < baseStart_3420447 := by decide
  rcases family_descends (prefixWord ++ tailWord_3420447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3420455 : List Nat := [1, 1, 8, 1, 1, 2, 2, 2, 1, 2, 2]
def baseStart_3420455 : Nat := 118140960795 + 3420455 * 2 ^ 59
def prefixEnd_3420455 : Nat := 4983230072969 + 3 ^ 40 * 3420455 * 2
def baseEnd_3420455 : Nat := 1756337472074520187782121

theorem tailTrace_3420455 : CollatzResearch.WordTrace tailWord_3420455 prefixEnd_3420455 1756337472074520187782121 := by
  unfold tailWord_3420455
  simp only [CollatzResearch.WordTrace]
  refine ⟨124754242823283177051182819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83169495215522118034121879 124754242823283177051182819)
  ·
    refine ⟨187131364234924765576774229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124754242823283177051182819 187131364234924765576774229)
    ·
      refine ⟨2192945674628024596602823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 187131364234924765576774229 2192945674628024596602823)
      ·
        refine ⟨3289418511942036894904235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2192945674628024596602823 3289418511942036894904235)
        ·
          refine ⟨4934127767913055342356353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3289418511942036894904235 4934127767913055342356353)
          ·
            refine ⟨3700595825934791506767265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4934127767913055342356353 3700595825934791506767265)
            ·
              refine ⟨2775446869451093630075449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3700595825934791506767265 2775446869451093630075449)
              ·
                refine ⟨2081585152088320222556587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2775446869451093630075449 2081585152088320222556587)
                ·
                  refine ⟨3122377728132480333834881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2081585152088320222556587 3122377728132480333834881)
                  ·
                    refine ⟨2341783296099360250376161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3122377728132480333834881 2341783296099360250376161)
                    ·
                      refine ⟨1756337472074520187782121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2341783296099360250376161 1756337472074520187782121)
                      ·
                        rfl

theorem cell23_3420455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_3420455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3420455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3420455 prefixEnd_3420455 := by exact prefixLift 3420455
  have htrace : WordTrace (prefixWord ++ tailWord_3420455) baseStart_3420455 baseEnd_3420455 := by
    simpa [prefixWord, tailWord_3420455, baseEnd_3420455] using wordTrace_append hprefix tailTrace_3420455
  have hstable : (prefixWord ++ tailWord_3420455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3420455).length < 2 ^ (prefixWord ++ tailWord_3420455).sum := by decide
  have hdescent : baseEnd_3420455 < baseStart_3420455 := by decide
  rcases family_descends (prefixWord ++ tailWord_3420455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3420460 : List Nat := [2, 2, 1, 1, 1, 3, 3, 4, 2, 2, 2]
def baseStart_3420460 : Nat := 118140960795 + 3420460 * 2 ^ 59
def prefixEnd_3420460 : Nat := 4983230072969 + 3 ^ 40 * 3420460 * 2
def baseEnd_3420460 : Nat := 1756340039477792668219597

theorem tailTrace_3420460 : CollatzResearch.WordTrace tailWord_3420460 prefixEnd_3420460 1756340039477792668219597 := by
  unfold tailWord_3420460
  simp only [CollatzResearch.WordTrace]
  refine ⟨62377212594132531452557417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83169616792176708603409889 62377212594132531452557417)
  ·
    refine ⟨46782909445599398589418063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62377212594132531452557417 46782909445599398589418063)
    ·
      refine ⟨70174364168399097884127095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46782909445599398589418063 70174364168399097884127095)
      ·
        refine ⟨105261546252598646826190643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70174364168399097884127095 105261546252598646826190643)
        ·
          refine ⟨157892319378897970239285965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105261546252598646826190643 157892319378897970239285965)
          ·
            refine ⟨59209619767086738839732237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 157892319378897970239285965 59209619767086738839732237)
            ·
              refine ⟨22203607412657527064899589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59209619767086738839732237 22203607412657527064899589)
              ·
                refine ⟨4163176389873286324668673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22203607412657527064899589 4163176389873286324668673)
                ·
                  refine ⟨3122382292404964743501505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4163176389873286324668673 3122382292404964743501505)
                  ·
                    refine ⟨2341786719303723557626129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3122382292404964743501505 2341786719303723557626129)
                    ·
                      refine ⟨1756340039477792668219597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2341786719303723557626129 1756340039477792668219597)
                      ·
                        rfl

theorem cell23_3420460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 2, 2].length) (baseStart_3420460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3420460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3420460 prefixEnd_3420460 := by exact prefixLift 3420460
  have htrace : WordTrace (prefixWord ++ tailWord_3420460) baseStart_3420460 baseEnd_3420460 := by
    simpa [prefixWord, tailWord_3420460, baseEnd_3420460] using wordTrace_append hprefix tailTrace_3420460
  have hstable : (prefixWord ++ tailWord_3420460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3420460).length < 2 ^ (prefixWord ++ tailWord_3420460).sum := by decide
  have hdescent : baseEnd_3420460 < baseStart_3420460 := by decide
  rcases family_descends (prefixWord ++ tailWord_3420460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3420473 : List Nat := [1, 2, 1, 6, 1, 2, 1, 1, 2, 2, 4]
def baseStart_3420473 : Nat := 118140960795 + 3420473 * 2 ^ 59
def prefixEnd_3420473 : Nat := 4983230072969 + 3 ^ 40 * 3420473 * 2
def baseEnd_3420473 : Nat := 1756346714726301117357037

theorem tailTrace_3420473 : CollatzResearch.WordTrace tailWord_3420473 prefixEnd_3420473 1756346714726301117357037 := by
  unfold tailWord_3420473
  simp only [CollatzResearch.WordTrace]
  refine ⟨124754899337217966125338073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83169932891478644083558715 124754899337217966125338073)
  ·
    refine ⟨93566174502913474594003555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124754899337217966125338073 93566174502913474594003555)
    ·
      refine ⟨140349261754370211891005333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93566174502913474594003555 140349261754370211891005333)
      ·
        refine ⟨6578871644736103682390875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 140349261754370211891005333 6578871644736103682390875)
        ·
          refine ⟨9868307467104155523586313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6578871644736103682390875 9868307467104155523586313)
          ·
            refine ⟨7401230600328116642689735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9868307467104155523586313 7401230600328116642689735)
            ·
              refine ⟨11101845900492174964034603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7401230600328116642689735 11101845900492174964034603)
              ·
                refine ⟨16652768850738262446051905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11101845900492174964034603 16652768850738262446051905)
                ·
                  refine ⟨12489576638053696834538929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16652768850738262446051905 12489576638053696834538929)
                  ·
                    refine ⟨9367182478540272625904197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12489576638053696834538929 9367182478540272625904197)
                    ·
                      refine ⟨1756346714726301117357037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9367182478540272625904197 1756346714726301117357037)
                      ·
                        rfl

theorem cell23_3420473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_3420473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3420473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3420473 prefixEnd_3420473 := by exact prefixLift 3420473
  have htrace : WordTrace (prefixWord ++ tailWord_3420473) baseStart_3420473 baseEnd_3420473 := by
    simpa [prefixWord, tailWord_3420473, baseEnd_3420473] using wordTrace_append hprefix tailTrace_3420473
  have hstable : (prefixWord ++ tailWord_3420473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3420473).length < 2 ^ (prefixWord ++ tailWord_3420473).sum := by decide
  have hdescent : baseEnd_3420473 < baseStart_3420473 := by decide
  rcases family_descends (prefixWord ++ tailWord_3420473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3420496 : List Nat := [2, 1, 1, 1, 1, 7, 1, 1, 1, 7]
def baseStart_3420496 : Nat := 118140960795 + 3420496 * 2 ^ 59
def prefixEnd_3420496 : Nat := 4983230072969 + 3 ^ 40 * 3420496 * 2
def baseEnd_3420496 : Nat := 585452841593784842456477

theorem tailTrace_3420496 : CollatzResearch.WordTrace tailWord_3420496 prefixEnd_3420496 585452841593784842456477 := by
  unfold tailWord_3420496
  simp only [CollatzResearch.WordTrace]
  refine ⟨62377869108067320526712671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83170492144089760702283561 62377869108067320526712671)
  ·
    refine ⟨93566803662100980790069007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62377869108067320526712671 93566803662100980790069007)
    ·
      refine ⟨140350205493151471185103511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93566803662100980790069007 140350205493151471185103511)
      ·
        refine ⟨210525308239727206777655267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140350205493151471185103511 210525308239727206777655267)
        ·
          refine ⟨315787962359590810166482901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210525308239727206777655267 315787962359590810166482901)
          ·
            refine ⟨7401280367802909613276943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 315787962359590810166482901 7401280367802909613276943)
            ·
              refine ⟨11101920551704364419915415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7401280367802909613276943 11101920551704364419915415)
              ·
                refine ⟨16652880827556546629873123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11101920551704364419915415 16652880827556546629873123)
                ·
                  refine ⟨24979321241334819944809685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16652880827556546629873123 24979321241334819944809685)
                  ·
                    refine ⟨585452841593784842456477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24979321241334819944809685 585452841593784842456477)
                    ·
                      rfl

theorem cell23_3420496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 1, 1, 7].length) (baseStart_3420496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3420496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3420496 prefixEnd_3420496 := by exact prefixLift 3420496
  have htrace : WordTrace (prefixWord ++ tailWord_3420496) baseStart_3420496 baseEnd_3420496 := by
    simpa [prefixWord, tailWord_3420496, baseEnd_3420496] using wordTrace_append hprefix tailTrace_3420496
  have hstable : (prefixWord ++ tailWord_3420496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3420496).length < 2 ^ (prefixWord ++ tailWord_3420496).sum := by decide
  have hdescent : baseEnd_3420496 < baseStart_3420496 := by decide
  rcases family_descends (prefixWord ++ tailWord_3420496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3420500 : List Nat := [2, 4, 1, 1, 2, 3, 2, 3, 5]
def baseStart_3420500 : Nat := 118140960795 + 3420500 * 2 ^ 59
def prefixEnd_3420500 : Nat := 4983230072969 + 3 ^ 40 * 3420500 * 2
def baseEnd_3420500 : Nat := 195151175411552501302157

theorem tailTrace_3420500 : CollatzResearch.WordTrace tailWord_3420500 prefixEnd_3420500 195151175411552501302157 := by
  unfold tailWord_3420500
  simp only [CollatzResearch.WordTrace]
  refine ⟨62377942054060074868285477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83170589405413433157713969 62377942054060074868285477)
  ·
    refine ⟨11695864135136264037803527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62377942054060074868285477 11695864135136264037803527)
    ·
      refine ⟨17543796202704396056705291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11695864135136264037803527 17543796202704396056705291)
      ·
        refine ⟨26315694304056594085057937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17543796202704396056705291 26315694304056594085057937)
        ·
          refine ⟨19736770728042445563793453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26315694304056594085057937 19736770728042445563793453)
          ·
            refine ⟨7401289023015917086422545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19736770728042445563793453 7401289023015917086422545)
            ·
              refine ⟨5550966767261937814816909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7401289023015917086422545 5550966767261937814816909)
              ·
                refine ⟨2081612537723226680556341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5550966767261937814816909 2081612537723226680556341)
                ·
                  refine ⟨195151175411552501302157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2081612537723226680556341 195151175411552501302157)
                  ·
                    rfl

theorem cell23_3420500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 2, 3, 5].length) (baseStart_3420500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3420500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3420500 prefixEnd_3420500 := by exact prefixLift 3420500
  have htrace : WordTrace (prefixWord ++ tailWord_3420500) baseStart_3420500 baseEnd_3420500 := by
    simpa [prefixWord, tailWord_3420500, baseEnd_3420500] using wordTrace_append hprefix tailTrace_3420500
  have hstable : (prefixWord ++ tailWord_3420500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3420500).length < 2 ^ (prefixWord ++ tailWord_3420500).sum := by decide
  have hdescent : baseEnd_3420500 < baseStart_3420500 := by decide
  rcases family_descends (prefixWord ++ tailWord_3420500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3420533 : List Nat := [1, 3, 4, 1, 2, 1, 1, 2, 1, 3, 4]
def baseStart_3420533 : Nat := 118140960795 + 3420533 * 2 ^ 59
def prefixEnd_3420533 : Nat := 4983230072969 + 3 ^ 40 * 3420533 * 2
def baseEnd_3420533 : Nat := 1756377523565570882606761

theorem tailTrace_3420533 : CollatzResearch.WordTrace tailWord_3420533 prefixEnd_3420533 1756377523565570882606761 := by
  unfold tailWord_3420533
  simp only [CollatzResearch.WordTrace]
  refine ⟨124757087717000596372522253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83171391811333730915014835 124757087717000596372522253)
  ·
    refine ⟨46783907893875223639695845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124757087717000596372522253 46783907893875223639695845)
    ·
      refine ⟨8771982730101604432442971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46783907893875223639695845 8771982730101604432442971)
      ·
        refine ⟨13157974095152406648664457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8771982730101604432442971 13157974095152406648664457)
        ·
          refine ⟨9868480571364304986498343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13157974095152406648664457 9868480571364304986498343)
          ·
            refine ⟨14802720857046457479747515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9868480571364304986498343 14802720857046457479747515)
            ·
              refine ⟨22204081285569686219621273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14802720857046457479747515 22204081285569686219621273)
              ·
                refine ⟨16653060964177264664715955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22204081285569686219621273 16653060964177264664715955)
                ·
                  refine ⟨24979591446265896997073933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16653060964177264664715955 24979591446265896997073933)
                  ·
                    refine ⟨9367346792349711373902725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24979591446265896997073933 9367346792349711373902725)
                    ·
                      refine ⟨1756377523565570882606761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9367346792349711373902725 1756377523565570882606761)
                      ·
                        rfl

theorem cell23_3420533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_3420533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3420533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3420533 prefixEnd_3420533 := by exact prefixLift 3420533
  have htrace : WordTrace (prefixWord ++ tailWord_3420533) baseStart_3420533 baseEnd_3420533 := by
    simpa [prefixWord, tailWord_3420533, baseEnd_3420533] using wordTrace_append hprefix tailTrace_3420533
  have hstable : (prefixWord ++ tailWord_3420533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3420533).length < 2 ^ (prefixWord ++ tailWord_3420533).sum := by decide
  have hdescent : baseEnd_3420533 < baseStart_3420533 := by decide
  rcases family_descends (prefixWord ++ tailWord_3420533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3420553 : List Nat := [1, 2, 1, 1, 6, 1, 2, 1, 1, 4, 3]
def baseStart_3420553 : Nat := 118140960795 + 3420553 * 2 ^ 59
def prefixEnd_3420553 : Nat := 4983230072969 + 3 ^ 40 * 3420553 * 2
def baseEnd_3420553 : Nat := 1756387793178660804356669

theorem tailTrace_3420553 : CollatzResearch.WordTrace tailWord_3420553 prefixEnd_3420553 1756387793178660804356669 := by
  unfold tailWord_3420553
  simp only [CollatzResearch.WordTrace]
  refine ⟨124757817176928139788250313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83171878117952093192166875 124757817176928139788250313)
  ·
    refine ⟨93568362882696104841187735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124757817176928139788250313 93568362882696104841187735)
    ·
      refine ⟨140352544324044157261781603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93568362882696104841187735 140352544324044157261781603)
      ·
        refine ⟨210528816486066235892672405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140352544324044157261781603 210528816486066235892672405)
        ·
          refine ⟨9868538272784354807469019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 210528816486066235892672405 9868538272784354807469019)
          ·
            refine ⟨14802807409176532211203529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9868538272784354807469019 14802807409176532211203529)
            ·
              refine ⟨11102105556882399158402647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14802807409176532211203529 11102105556882399158402647)
              ·
                refine ⟨16653158335323598737603971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11102105556882399158402647 16653158335323598737603971)
                ·
                  refine ⟨24979737502985398106405957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16653158335323598737603971 24979737502985398106405957)
                  ·
                    refine ⟨4683700781809762144951117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24979737502985398106405957 4683700781809762144951117)
                    ·
                      refine ⟨1756387793178660804356669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4683700781809762144951117 1756387793178660804356669)
                      ·
                        rfl

theorem cell23_3420553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 1, 1, 4, 3].length) (baseStart_3420553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3420553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3420553 prefixEnd_3420553 := by exact prefixLift 3420553
  have htrace : WordTrace (prefixWord ++ tailWord_3420553) baseStart_3420553 baseEnd_3420553 := by
    simpa [prefixWord, tailWord_3420553, baseEnd_3420553] using wordTrace_append hprefix tailTrace_3420553
  have hstable : (prefixWord ++ tailWord_3420553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3420553).length < 2 ^ (prefixWord ++ tailWord_3420553).sum := by decide
  have hdescent : baseEnd_3420553 < baseStart_3420553 := by decide
  rcases family_descends (prefixWord ++ tailWord_3420553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3420556 : List Nat := [2, 2, 1, 2, 1, 4, 1, 2, 8]
def baseStart_3420556 : Nat := 118140960795 + 3420556 * 2 ^ 59
def prefixEnd_3420556 : Nat := 4983230072969 + 3 ^ 40 * 3420556 * 2
def baseEnd_3420556 : Nat := 195154370402291588068795

theorem tailTrace_3420556 : CollatzResearch.WordTrace tailWord_3420556 prefixEnd_3420556 195154370402291588068795 := by
  unfold tailWord_3420556
  simp only [CollatzResearch.WordTrace]
  refine ⟨62378963297958635650304761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83171951063944847533739681 62378963297958635650304761)
  ·
    refine ⟨46784222473468976737728571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62378963297958635650304761 46784222473468976737728571)
    ·
      refine ⟨70176333710203465106592857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46784222473468976737728571 70176333710203465106592857)
      ·
        refine ⟨52632250282652598829944643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70176333710203465106592857 52632250282652598829944643)
        ·
          refine ⟨78948375423978898244916965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52632250282652598829944643 78948375423978898244916965)
          ·
            refine ⟨14802820391996043420921931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78948375423978898244916965 14802820391996043420921931)
            ·
              refine ⟨22204230587994065131382897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14802820391996043420921931 22204230587994065131382897)
              ·
                refine ⟨16653172940995548848537173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22204230587994065131382897 16653172940995548848537173)
                ·
                  refine ⟨195154370402291588068795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16653172940995548848537173 195154370402291588068795)
                  ·
                    rfl

theorem cell23_3420556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 2, 8].length) (baseStart_3420556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3420556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3420556 prefixEnd_3420556 := by exact prefixLift 3420556
  have htrace : WordTrace (prefixWord ++ tailWord_3420556) baseStart_3420556 baseEnd_3420556 := by
    simpa [prefixWord, tailWord_3420556, baseEnd_3420556] using wordTrace_append hprefix tailTrace_3420556
  have hstable : (prefixWord ++ tailWord_3420556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3420556).length < 2 ^ (prefixWord ++ tailWord_3420556).sum := by decide
  have hdescent : baseEnd_3420556 < baseStart_3420556 := by decide
  rcases family_descends (prefixWord ++ tailWord_3420556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3420570 : List Nat := [3, 1, 1, 4, 1, 3, 1, 2, 2, 2, 3]
def baseStart_3420570 : Nat := 118140960795 + 3420570 * 2 ^ 59
def prefixEnd_3420570 : Nat := 4983230072969 + 3 ^ 40 * 3420570 * 2
def baseEnd_3420570 : Nat := 1756396522349787237844091

theorem tailTrace_3420570 : CollatzResearch.WordTrace tailWord_3420570 prefixEnd_3420570 1756396522349787237844091 := by
  unfold tailWord_3420570
  simp only [CollatzResearch.WordTrace]
  refine ⟨31189609304466637922904791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83172291478577701127746109 31189609304466637922904791)
  ·
    refine ⟨46784413956699956884357187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31189609304466637922904791 46784413956699956884357187)
    ·
      refine ⟨70176620935049935326535781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46784413956699956884357187 70176620935049935326535781)
      ·
        refine ⟨13158116425321862873725459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70176620935049935326535781 13158116425321862873725459)
        ·
          refine ⟨19737174637982794310588189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13158116425321862873725459 19737174637982794310588189)
          ·
            refine ⟨7401440489243547866470571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19737174637982794310588189 7401440489243547866470571)
            ·
              refine ⟨11102160733865321799705857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7401440489243547866470571 11102160733865321799705857)
              ·
                refine ⟨8326620550398991349779393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11102160733865321799705857 8326620550398991349779393)
                ·
                  refine ⟨6244965412799243512334545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8326620550398991349779393 6244965412799243512334545)
                  ·
                    refine ⟨4683724059599432634250909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6244965412799243512334545 4683724059599432634250909)
                    ·
                      refine ⟨1756396522349787237844091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4683724059599432634250909 1756396522349787237844091)
                      ·
                        rfl

theorem cell23_3420570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 2, 2, 2, 3].length) (baseStart_3420570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3420570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3420570 prefixEnd_3420570 := by exact prefixLift 3420570
  have htrace : WordTrace (prefixWord ++ tailWord_3420570) baseStart_3420570 baseEnd_3420570 := by
    simpa [prefixWord, tailWord_3420570, baseEnd_3420570] using wordTrace_append hprefix tailTrace_3420570
  have hstable : (prefixWord ++ tailWord_3420570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3420570).length < 2 ^ (prefixWord ++ tailWord_3420570).sum := by decide
  have hdescent : baseEnd_3420570 < baseStart_3420570 := by decide
  rcases family_descends (prefixWord ++ tailWord_3420570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3420650 : List Nat := [3, 1, 3, 1, 3, 2, 2, 1, 1, 6]
def baseStart_3420650 : Nat := 118140960795 + 3420650 * 2 ^ 59
def prefixEnd_3420650 : Nat := 4983230072969 + 3 ^ 40 * 3420650 * 2
def baseEnd_3420650 : Nat := 585479200267382308281241

theorem tailTrace_3420650 : CollatzResearch.WordTrace tailWord_3420650 prefixEnd_3420650 585479200267382308281241 := by
  unfold tailWord_3420650
  simp only [CollatzResearch.WordTrace]
  refine ⟨31190338764394181338632851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83174236705051150236354269 31190338764394181338632851)
  ·
    refine ⟨46785508146591272007949277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31190338764394181338632851 46785508146591272007949277)
    ·
      refine ⟨17544565554971727002980979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46785508146591272007949277 17544565554971727002980979)
      ·
        refine ⟨26316848332457590504471469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17544565554971727002980979 26316848332457590504471469)
        ·
          refine ⟨9868818124671596439176801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26316848332457590504471469 9868818124671596439176801)
          ·
            refine ⟨7401613593503697329382601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9868818124671596439176801 7401613593503697329382601)
            ·
              refine ⟨5551210195127772997036951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7401613593503697329382601 5551210195127772997036951)
              ·
                refine ⟨8326815292691659495555427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5551210195127772997036951 8326815292691659495555427)
                ·
                  refine ⟨12490222939037489243333141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8326815292691659495555427 12490222939037489243333141)
                  ·
                    refine ⟨585479200267382308281241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12490222939037489243333141 585479200267382308281241)
                    ·
                      rfl

theorem cell23_3420650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 2, 1, 1, 6].length) (baseStart_3420650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3420650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3420650 prefixEnd_3420650 := by exact prefixLift 3420650
  have htrace : WordTrace (prefixWord ++ tailWord_3420650) baseStart_3420650 baseEnd_3420650 := by
    simpa [prefixWord, tailWord_3420650, baseEnd_3420650] using wordTrace_append hprefix tailTrace_3420650
  have hstable : (prefixWord ++ tailWord_3420650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3420650).length < 2 ^ (prefixWord ++ tailWord_3420650).sum := by decide
  have hdescent : baseEnd_3420650 < baseStart_3420650 := by decide
  rcases family_descends (prefixWord ++ tailWord_3420650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3420657 : List Nat := [1, 2, 2, 2, 3, 1, 3, 2, 3, 2, 2]
def baseStart_3420657 : Nat := 118140960795 + 3420657 * 2 ^ 59
def prefixEnd_3420657 : Nat := 4983230072969 + 3 ^ 40 * 3420657 * 2
def baseEnd_3420657 : Nat := 1756441195166728397456191

theorem tailTrace_3420657 : CollatzResearch.WordTrace tailWord_3420657 prefixEnd_3420657 1756441195166728397456191 := by
  unfold tailWord_3420657
  simp only [CollatzResearch.WordTrace]
  refine ⟨124761610368551365550036225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83174406912367577033357483 124761610368551365550036225)
  ·
    refine ⟨93571207776413524162527169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124761610368551365550036225 93571207776413524162527169)
    ·
      refine ⟨70178405832310143121895377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93571207776413524162527169 70178405832310143121895377)
      ·
        refine ⟨52633804374232607341421533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70178405832310143121895377 52633804374232607341421533)
        ·
          refine ⟨19737676640337227753033075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52633804374232607341421533 19737676640337227753033075)
          ·
            refine ⟨29606514960505841629549613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19737676640337227753033075 29606514960505841629549613)
            ·
              refine ⟨11102443110189690611081105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29606514960505841629549613 11102443110189690611081105)
              ·
                refine ⟨8326832332642267958310829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11102443110189690611081105 8326832332642267958310829)
                ·
                  refine ⟨3122562124740850484366561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8326832332642267958310829 3122562124740850484366561)
                  ·
                    refine ⟨2341921593555637863274921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3122562124740850484366561 2341921593555637863274921)
                    ·
                      refine ⟨1756441195166728397456191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2341921593555637863274921 1756441195166728397456191)
                      ·
                        rfl

theorem cell23_3420657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 2, 3, 2, 2].length) (baseStart_3420657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3420657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3420657 prefixEnd_3420657 := by exact prefixLift 3420657
  have htrace : WordTrace (prefixWord ++ tailWord_3420657) baseStart_3420657 baseEnd_3420657 := by
    simpa [prefixWord, tailWord_3420657, baseEnd_3420657] using wordTrace_append hprefix tailTrace_3420657
  have hstable : (prefixWord ++ tailWord_3420657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3420657).length < 2 ^ (prefixWord ++ tailWord_3420657).sum := by decide
  have hdescent : baseEnd_3420657 < baseStart_3420657 := by decide
  rcases family_descends (prefixWord ++ tailWord_3420657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3420661 : List Nat := [1, 3, 5, 1, 2, 2, 1, 1, 2, 3, 2]
def baseStart_3420661 : Nat := 118140960795 + 3420661 * 2 ^ 59
def prefixEnd_3420661 : Nat := 4983230072969 + 3 ^ 40 * 3420661 * 2
def baseEnd_3420661 : Nat := 1756443249089346381806173

theorem tailTrace_3420661 : CollatzResearch.WordTrace tailWord_3420661 prefixEnd_3420661 1756443249089346381806173 := by
  unfold tailWord_3420661
  simp only [CollatzResearch.WordTrace]
  refine ⟨124761756260536874233181837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83174504173691249488787891 124761756260536874233181837)
  ·
    refine ⟨46785658597701327837443189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124761756260536874233181837 46785658597701327837443189)
    ·
      refine ⟨4386155493534499484760299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46785658597701327837443189 4386155493534499484760299)
      ·
        refine ⟨6579233240301749227140449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4386155493534499484760299 6579233240301749227140449)
        ·
          refine ⟨4934424930226311920355337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6579233240301749227140449 4934424930226311920355337)
          ·
            refine ⟨3700818697669733940266503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4934424930226311920355337 3700818697669733940266503)
            ·
              refine ⟨5551228046504600910399755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3700818697669733940266503 5551228046504600910399755)
              ·
                refine ⟨8326842069756901365599633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5551228046504600910399755 8326842069756901365599633)
                ·
                  refine ⟨6245131552317676024199725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8326842069756901365599633 6245131552317676024199725)
                  ·
                    refine ⟨2341924332119128509074897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6245131552317676024199725 2341924332119128509074897)
                    ·
                      refine ⟨1756443249089346381806173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2341924332119128509074897 1756443249089346381806173)
                      ·
                        rfl

theorem cell23_3420661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 1, 1, 2, 3, 2].length) (baseStart_3420661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3420661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3420661 prefixEnd_3420661 := by exact prefixLift 3420661
  have htrace : WordTrace (prefixWord ++ tailWord_3420661) baseStart_3420661 baseEnd_3420661 := by
    simpa [prefixWord, tailWord_3420661, baseEnd_3420661] using wordTrace_append hprefix tailTrace_3420661
  have hstable : (prefixWord ++ tailWord_3420661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3420661).length < 2 ^ (prefixWord ++ tailWord_3420661).sum := by decide
  have hdescent : baseEnd_3420661 < baseStart_3420661 := by decide
  rcases family_descends (prefixWord ++ tailWord_3420661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3420674 : List Nat := [3, 4, 1, 2, 2, 1, 1, 3, 1, 1, 4]
def baseStart_3420674 : Nat := 118140960795 + 3420674 * 2 ^ 59
def prefixEnd_3420674 : Nat := 4983230072969 + 3 ^ 40 * 3420674 * 2
def baseEnd_3420674 : Nat := 1756449924337854830943613

theorem tailTrace_3420674 : CollatzResearch.WordTrace tailWord_3420674 prefixEnd_3420674 1756449924337854830943613 := by
  unfold tailWord_3420674
  simp only [CollatzResearch.WordTrace]
  refine ⟨31190557602372444363351269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83174820272993184968936717 31190557602372444363351269)
  ·
    refine ⟨5848229550444833318128363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31190557602372444363351269 5848229550444833318128363)
    ·
      refine ⟨8772344325667249977192545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5848229550444833318128363 8772344325667249977192545)
      ·
        refine ⟨6579258244250437482894409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8772344325667249977192545 6579258244250437482894409)
        ·
          refine ⟨4934443683187828112170807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6579258244250437482894409 4934443683187828112170807)
          ·
            refine ⟨7401665524781742168256211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4934443683187828112170807 7401665524781742168256211)
            ·
              refine ⟨11102498287172613252384317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7401665524781742168256211 11102498287172613252384317)
              ·
                refine ⟨4163436857689729969644119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11102498287172613252384317 4163436857689729969644119)
                ·
                  refine ⟨6245155286534594954466179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4163436857689729969644119 6245155286534594954466179)
                  ·
                    refine ⟨9367732929801892431699269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6245155286534594954466179 9367732929801892431699269)
                    ·
                      refine ⟨1756449924337854830943613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9367732929801892431699269 1756449924337854830943613)
                      ·
                        rfl

theorem cell23_3420674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_3420674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3420674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3420674 prefixEnd_3420674 := by exact prefixLift 3420674
  have htrace : WordTrace (prefixWord ++ tailWord_3420674) baseStart_3420674 baseEnd_3420674 := by
    simpa [prefixWord, tailWord_3420674, baseEnd_3420674] using wordTrace_append hprefix tailTrace_3420674
  have hstable : (prefixWord ++ tailWord_3420674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3420674).length < 2 ^ (prefixWord ++ tailWord_3420674).sum := by decide
  have hdescent : baseEnd_3420674 < baseStart_3420674 := by decide
  rcases family_descends (prefixWord ++ tailWord_3420674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3420677 : List Nat := [1, 3, 1, 1, 2, 2, 6, 1, 1, 2, 3]
def baseStart_3420677 : Nat := 118140960795 + 3420677 * 2 ^ 59
def prefixEnd_3420677 : Nat := 4983230072969 + 3 ^ 40 * 3420677 * 2
def baseEnd_3420677 : Nat := 1756451464779818319206099

theorem tailTrace_3420677 : CollatzResearch.WordTrace tailWord_3420677 prefixEnd_3420677 1756451464779818319206099 := by
  unfold tailWord_3420677
  simp only [CollatzResearch.WordTrace]
  refine ⟨124762339828478908965764285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83174893218985939310509523 124762339828478908965764285)
  ·
    refine ⟨46785877435679590862161607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124762339828478908965764285 46785877435679590862161607)
    ·
      refine ⟨70178816153519386293242411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46785877435679590862161607 70178816153519386293242411)
      ·
        refine ⟨105268224230279079439863617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70178816153519386293242411 105268224230279079439863617)
        ·
          refine ⟨78951168172709309579897713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105268224230279079439863617 78951168172709309579897713)
          ·
            refine ⟨59213376129531982184923285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78951168172709309579897713 59213376129531982184923285)
            ·
              refine ⟨2775627006071811664918279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 59213376129531982184923285 2775627006071811664918279)
              ·
                refine ⟨4163440509107717497377419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2775627006071811664918279 4163440509107717497377419)
                ·
                  refine ⟨6245160763661576246066129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4163440509107717497377419 6245160763661576246066129)
                  ·
                    refine ⟨4683870572746182184549597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6245160763661576246066129 4683870572746182184549597)
                    ·
                      refine ⟨1756451464779818319206099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4683870572746182184549597 1756451464779818319206099)
                      ·
                        rfl

theorem cell23_3420677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 6, 1, 1, 2, 3].length) (baseStart_3420677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3420677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3420677 prefixEnd_3420677 := by exact prefixLift 3420677
  have htrace : WordTrace (prefixWord ++ tailWord_3420677) baseStart_3420677 baseEnd_3420677 := by
    simpa [prefixWord, tailWord_3420677, baseEnd_3420677] using wordTrace_append hprefix tailTrace_3420677
  have hstable : (prefixWord ++ tailWord_3420677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3420677).length < 2 ^ (prefixWord ++ tailWord_3420677).sum := by decide
  have hdescent : baseEnd_3420677 < baseStart_3420677 := by decide
  rcases family_descends (prefixWord ++ tailWord_3420677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3420704 : List Nat := [2, 1, 1, 6, 3, 1, 1, 1, 1, 2, 4]
def baseStart_3420704 : Nat := 118140960795 + 3420704 * 2 ^ 59
def prefixEnd_3420704 : Nat := 4983230072969 + 3 ^ 40 * 3420704 * 2
def baseEnd_3420704 : Nat := 1756465328757489713568475

theorem tailTrace_3420704 : CollatzResearch.WordTrace tailWord_3420704 prefixEnd_3420704 1756465328757489713568475 := by
  unfold tailWord_3420704
  simp only [CollatzResearch.WordTrace]
  refine ⟨62381662299690546288498583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83175549732920728384664777 62381662299690546288498583)
  ·
    refine ⟨93572493449535819432747875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62381662299690546288498583 93572493449535819432747875)
    ·
      refine ⟨140358740174303729149121813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93572493449535819432747875 140358740174303729149121813)
      ·
        refine ⟨6579315945670487303865085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 140358740174303729149121813 6579315945670487303865085)
        ·
          refine ⟨2467243479626432738949407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6579315945670487303865085 2467243479626432738949407)
          ·
            refine ⟨3700865219439649108424111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2467243479626432738949407 3700865219439649108424111)
            ·
              refine ⟨5551297829159473662636167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3700865219439649108424111 5551297829159473662636167)
              ·
                refine ⟨8326946743739210493954251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5551297829159473662636167 8326946743739210493954251)
                ·
                  refine ⟨12490420115608815740931377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8326946743739210493954251 12490420115608815740931377)
                  ·
                    refine ⟨9367815086706611805698533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12490420115608815740931377 9367815086706611805698533)
                    ·
                      refine ⟨1756465328757489713568475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9367815086706611805698533 1756465328757489713568475)
                      ·
                        rfl

theorem cell23_3420704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 1, 1, 1, 2, 4].length) (baseStart_3420704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3420704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3420704 prefixEnd_3420704 := by exact prefixLift 3420704
  have htrace : WordTrace (prefixWord ++ tailWord_3420704) baseStart_3420704 baseEnd_3420704 := by
    simpa [prefixWord, tailWord_3420704, baseEnd_3420704] using wordTrace_append hprefix tailTrace_3420704
  have hstable : (prefixWord ++ tailWord_3420704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3420704).length < 2 ^ (prefixWord ++ tailWord_3420704).sum := by decide
  have hdescent : baseEnd_3420704 < baseStart_3420704 := by decide
  rcases family_descends (prefixWord ++ tailWord_3420704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3420707 : List Nat := [1, 1, 1, 4, 4, 3, 1, 1, 1, 3, 3]
def baseStart_3420707 : Nat := 118140960795 + 3420707 * 2 ^ 59
def prefixEnd_3420707 : Nat := 4983230072969 + 3 ^ 40 * 3420707 * 2
def baseEnd_3420707 : Nat := 1756466869199453201830961

theorem tailTrace_3420707 : CollatzResearch.WordTrace tailWord_3420707 prefixEnd_3420707 1756466869199453201830961 := by
  unfold tailWord_3420707
  simp only [CollatzResearch.WordTrace]
  refine ⟨124763434018370224089356375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83175622678913482726237583 124763434018370224089356375)
  ·
    refine ⟨187145151027555336134034563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124763434018370224089356375 187145151027555336134034563)
    ·
      refine ⟨280717726541333004201051845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187145151027555336134034563 280717726541333004201051845)
      ·
        refine ⟨52634573726499938287697221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 280717726541333004201051845 52634573726499938287697221)
        ·
          refine ⟨9868982573718738428943229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52634573726499938287697221 9868982573718738428943229)
          ·
            refine ⟨3700868465144526910853711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9868982573718738428943229 3700868465144526910853711)
            ·
              refine ⟨5551302697716790366280567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3700868465144526910853711 5551302697716790366280567)
              ·
                refine ⟨8326954046575185549420851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5551302697716790366280567 8326954046575185549420851)
                ·
                  refine ⟨12490431069862778324131277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8326954046575185549420851 12490431069862778324131277)
                  ·
                    refine ⟨4683911651198541871549229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12490431069862778324131277 4683911651198541871549229)
                    ·
                      refine ⟨1756466869199453201830961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4683911651198541871549229 1756466869199453201830961)
                      ·
                        rfl

theorem cell23_3420707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 1, 1, 1, 3, 3].length) (baseStart_3420707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3420707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3420707 prefixEnd_3420707 := by exact prefixLift 3420707
  have htrace : WordTrace (prefixWord ++ tailWord_3420707) baseStart_3420707 baseEnd_3420707 := by
    simpa [prefixWord, tailWord_3420707, baseEnd_3420707] using wordTrace_append hprefix tailTrace_3420707
  have hstable : (prefixWord ++ tailWord_3420707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3420707).length < 2 ^ (prefixWord ++ tailWord_3420707).sum := by decide
  have hdescent : baseEnd_3420707 < baseStart_3420707 := by decide
  rcases family_descends (prefixWord ++ tailWord_3420707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3420711 : List Nat := [1, 1, 7, 2, 1, 1, 2, 2, 1, 2, 3]
def baseStart_3420711 : Nat := 118140960795 + 3420711 * 2 ^ 59
def prefixEnd_3420711 : Nat := 4983230072969 + 3 ^ 40 * 3420711 * 2
def baseEnd_3420711 : Nat := 1756468923122071186180943

theorem tailTrace_3420711 : CollatzResearch.WordTrace tailWord_3420711 prefixEnd_3420711 1756468923122071186180943 := by
  unfold tailWord_3420711
  simp only [CollatzResearch.WordTrace]
  refine ⟨124763579910355732772501987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83175719940237155181667991 124763579910355732772501987)
  ·
    refine ⟨187145369865533599158752981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124763579910355732772501987 187145369865533599158752981)
    ·
      refine ⟨4386219606223443730283273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 187145369865533599158752981 4386219606223443730283273)
      ·
        refine ⟨3289664704667582797712455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4386219606223443730283273 3289664704667582797712455)
        ·
          refine ⟨4934497057001374196568683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3289664704667582797712455 4934497057001374196568683)
          ·
            refine ⟨7401745585502061294853025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4934497057001374196568683 7401745585502061294853025)
            ·
              refine ⟨5551309189126545971139769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7401745585502061294853025 5551309189126545971139769)
              ·
                refine ⟨4163481891844909478354827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5551309189126545971139769 4163481891844909478354827)
                ·
                  refine ⟨6245222837767364217532241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4163481891844909478354827 6245222837767364217532241)
                  ·
                    refine ⟨4683917128325523163149181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6245222837767364217532241 4683917128325523163149181)
                    ·
                      refine ⟨1756468923122071186180943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4683917128325523163149181 1756468923122071186180943)
                      ·
                        rfl

theorem cell23_3420711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_3420711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3420711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3420711 prefixEnd_3420711 := by exact prefixLift 3420711
  have htrace : WordTrace (prefixWord ++ tailWord_3420711) baseStart_3420711 baseEnd_3420711 := by
    simpa [prefixWord, tailWord_3420711, baseEnd_3420711] using wordTrace_append hprefix tailTrace_3420711
  have hstable : (prefixWord ++ tailWord_3420711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3420711).length < 2 ^ (prefixWord ++ tailWord_3420711).sum := by decide
  have hdescent : baseEnd_3420711 < baseStart_3420711 := by decide
  rcases family_descends (prefixWord ++ tailWord_3420711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3420747 : List Nat := [1, 1, 1, 1, 3, 1, 6, 1, 4, 2, 2]
def baseStart_3420747 : Nat := 118140960795 + 3420747 * 2 ^ 59
def prefixEnd_3420747 : Nat := 4983230072969 + 3 ^ 40 * 3420747 * 2
def baseEnd_3420747 : Nat := 1756487408425633045330777

theorem tailTrace_3420747 : CollatzResearch.WordTrace tailWord_3420747 prefixEnd_3420747 1756487408425633045330777 := by
  unfold tailWord_3420747
  simp only [CollatzResearch.WordTrace]
  refine ⟨124764892938225310920812495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83176595292150207280541663 124764892938225310920812495)
  ·
    refine ⟨187147339407337966381218743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124764892938225310920812495 187147339407337966381218743)
    ·
      refine ⟨280721009111006949571828115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187147339407337966381218743 280721009111006949571828115)
      ·
        refine ⟨421081513666510424357742173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280721009111006949571828115 421081513666510424357742173)
        ·
          refine ⟨157905567624941409134153315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 421081513666510424357742173 157905567624941409134153315)
          ·
            refine ⟨236858351437412113701229973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157905567624941409134153315 236858351437412113701229973)
            ·
              refine ⟨11102735223628692829745155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 236858351437412113701229973 11102735223628692829745155)
              ·
                refine ⟨16654102835443039244617733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11102735223628692829745155 16654102835443039244617733)
                ·
                  refine ⟨3122644281645569858365825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16654102835443039244617733 3122644281645569858365825)
                  ·
                    refine ⟨2341983211234177393774369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3122644281645569858365825 2341983211234177393774369)
                    ·
                      refine ⟨1756487408425633045330777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2341983211234177393774369 1756487408425633045330777)
                      ·
                        rfl

theorem cell23_3420747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 1, 4, 2, 2].length) (baseStart_3420747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3420747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3420747 prefixEnd_3420747 := by exact prefixLift 3420747
  have htrace : WordTrace (prefixWord ++ tailWord_3420747) baseStart_3420747 baseEnd_3420747 := by
    simpa [prefixWord, tailWord_3420747, baseEnd_3420747] using wordTrace_append hprefix tailTrace_3420747
  have hstable : (prefixWord ++ tailWord_3420747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3420747).length < 2 ^ (prefixWord ++ tailWord_3420747).sum := by decide
  have hdescent : baseEnd_3420747 < baseStart_3420747 := by decide
  rcases family_descends (prefixWord ++ tailWord_3420747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3420783 : List Nat := [1, 1, 2, 1, 3, 2, 2, 3, 1, 7]
def baseStart_3420783 : Nat := 118140960795 + 3420783 * 2 ^ 59
def prefixEnd_3420783 : Nat := 4983230072969 + 3 ^ 40 * 3420783 * 2
def baseEnd_3420783 : Nat := 585501964576398301493537

theorem tailTrace_3420783 : CollatzResearch.WordTrace tailWord_3420783 prefixEnd_3420783 585501964576398301493537 := by
  unfold tailWord_3420783
  simp only [CollatzResearch.WordTrace]
  refine ⟨124766205966094889069123003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83177470644063259379415335 124766205966094889069123003)
  ·
    refine ⟨187149308949142333603684505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124766205966094889069123003 187149308949142333603684505)
    ·
      refine ⟨140361981711856750202763379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187149308949142333603684505 140361981711856750202763379)
      ·
        refine ⟨210542972567785125304145069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140361981711856750202763379 210542972567785125304145069)
        ·
          refine ⟨78953614712919421989054401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 210542972567785125304145069 78953614712919421989054401)
          ·
            refine ⟨59215211034689566491790801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78953614712919421989054401 59215211034689566491790801)
            ·
              refine ⟨44411408276017174868843101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59215211034689566491790801 44411408276017174868843101)
              ·
                refine ⟨16654278103506440575816163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44411408276017174868843101 16654278103506440575816163)
                ·
                  refine ⟨24981417155259660863724245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16654278103506440575816163 24981417155259660863724245)
                  ·
                    refine ⟨585501964576398301493537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24981417155259660863724245 585501964576398301493537)
                    ·
                      rfl

theorem cell23_3420783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 3, 1, 7].length) (baseStart_3420783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3420783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3420783 prefixEnd_3420783 := by exact prefixLift 3420783
  have htrace : WordTrace (prefixWord ++ tailWord_3420783) baseStart_3420783 baseEnd_3420783 := by
    simpa [prefixWord, tailWord_3420783, baseEnd_3420783] using wordTrace_append hprefix tailTrace_3420783
  have hstable : (prefixWord ++ tailWord_3420783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3420783).length < 2 ^ (prefixWord ++ tailWord_3420783).sum := by decide
  have hdescent : baseEnd_3420783 < baseStart_3420783 := by decide
  rcases family_descends (prefixWord ++ tailWord_3420783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3420800 : List Nat := [2, 1, 1, 2, 1, 5, 2, 2, 2, 5]
def baseStart_3420800 : Nat := 118140960795 + 3420800 * 2 ^ 59
def prefixEnd_3420800 : Nat := 4983230072969 + 3 ^ 40 * 3420800 * 2
def baseEnd_3420800 : Nat := 585504874300107112656011

theorem tailTrace_3420800 : CollatzResearch.WordTrace tailWord_3420800 prefixEnd_3420800 585504874300107112656011 := by
  unfold tailWord_3420800
  simp only [CollatzResearch.WordTrace]
  refine ⟨62383413003516650486245927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83177884004688867314994569 62383413003516650486245927)
  ·
    refine ⟨93575119505274975729368891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62383413003516650486245927 93575119505274975729368891)
    ·
      refine ⟨140362679257912463594053337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93575119505274975729368891 140362679257912463594053337)
      ·
        refine ⟨105272009443434347695540003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140362679257912463594053337 105272009443434347695540003)
        ·
          refine ⟨157908014165151521543310005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105272009443434347695540003 157908014165151521543310005)
          ·
            refine ⟨14803876327982955144685313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 157908014165151521543310005 14803876327982955144685313)
            ·
              refine ⟨11102907245987216358513985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14803876327982955144685313 11102907245987216358513985)
              ·
                refine ⟨8327180434490412268885489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11102907245987216358513985 8327180434490412268885489)
                ·
                  refine ⟨6245385325867809201664117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8327180434490412268885489 6245385325867809201664117)
                  ·
                    refine ⟨585504874300107112656011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6245385325867809201664117 585504874300107112656011)
                    ·
                      rfl

theorem cell23_3420800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 2, 2, 5].length) (baseStart_3420800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3420800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3420800 prefixEnd_3420800 := by exact prefixLift 3420800
  have htrace : WordTrace (prefixWord ++ tailWord_3420800) baseStart_3420800 baseEnd_3420800 := by
    simpa [prefixWord, tailWord_3420800, baseEnd_3420800] using wordTrace_append hprefix tailTrace_3420800
  have hstable : (prefixWord ++ tailWord_3420800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3420800).length < 2 ^ (prefixWord ++ tailWord_3420800).sum := by decide
  have hdescent : baseEnd_3420800 < baseStart_3420800 := by decide
  rcases family_descends (prefixWord ++ tailWord_3420800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3420804 : List Nat := [2, 3, 2, 1, 3, 1, 4, 2, 5]
def baseStart_3420804 : Nat := 118140960795 + 3420804 * 2 ^ 59
def prefixEnd_3420804 : Nat := 4983230072969 + 3 ^ 40 * 3420804 * 2
def baseEnd_3420804 : Nat := 195168519646993258035335

theorem tailTrace_3420804 : CollatzResearch.WordTrace tailWord_3420804 prefixEnd_3420804 195168519646993258035335 := by
  unfold tailWord_3420804
  simp only [CollatzResearch.WordTrace]
  refine ⟨62383485949509404827818733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83177981266012539770424977 62383485949509404827818733)
  ·
    refine ⟨23393807231066026810432025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62383485949509404827818733 23393807231066026810432025)
    ·
      refine ⟨17545355423299520107824019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23393807231066026810432025 17545355423299520107824019)
      ·
        refine ⟨26318033134949280161736029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17545355423299520107824019 26318033134949280161736029)
        ·
          refine ⟨9869262425605980060651011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26318033134949280161736029 9869262425605980060651011)
          ·
            refine ⟨14803893638408970090976517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9869262425605980060651011 14803893638408970090976517)
            ·
              refine ⟨2775730057201681892058097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14803893638408970090976517 2775730057201681892058097)
              ·
                refine ⟨2081797542901261419043573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2775730057201681892058097 2081797542901261419043573)
                ·
                  refine ⟨195168519646993258035335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2081797542901261419043573 195168519646993258035335)
                  ·
                    rfl

theorem cell23_3420804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 4, 2, 5].length) (baseStart_3420804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3420804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3420804 prefixEnd_3420804 := by exact prefixLift 3420804
  have htrace : WordTrace (prefixWord ++ tailWord_3420804) baseStart_3420804 baseEnd_3420804 := by
    simpa [prefixWord, tailWord_3420804, baseEnd_3420804] using wordTrace_append hprefix tailTrace_3420804
  have hstable : (prefixWord ++ tailWord_3420804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3420804).length < 2 ^ (prefixWord ++ tailWord_3420804).sum := by decide
  have hdescent : baseEnd_3420804 < baseStart_3420804 := by decide
  rcases family_descends (prefixWord ++ tailWord_3420804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3420860 : List Nat := [2, 2, 2, 3, 1, 1, 3, 1, 8]
def baseStart_3420860 : Nat := 118140960795 + 3420860 * 2 ^ 59
def prefixEnd_3420860 : Nat := 4983230072969 + 3 ^ 40 * 3420860 * 2
def baseEnd_3420860 : Nat := 195171714637732344801973

theorem tailTrace_3420860 : CollatzResearch.WordTrace tailWord_3420860 prefixEnd_3420860 195171714637732344801973 := by
  unfold tailWord_3420860
  simp only [CollatzResearch.WordTrace]
  refine ⟨62384507193407965609838017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83179342924543954146450689 62384507193407965609838017)
  ·
    refine ⟨46788380395055974207378513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62384507193407965609838017 46788380395055974207378513)
    ·
      refine ⟨35091285296291980655533885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46788380395055974207378513 35091285296291980655533885)
      ·
        refine ⟨13159231986109492745825207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35091285296291980655533885 13159231986109492745825207)
        ·
          refine ⟨19738847979164239118737811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13159231986109492745825207 19738847979164239118737811)
          ·
            refine ⟨29608271968746358678106717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19738847979164239118737811 29608271968746358678106717)
            ·
              refine ⟨11103101988279884504290019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29608271968746358678106717 11103101988279884504290019)
              ·
                refine ⟨16654652982419826756435029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11103101988279884504290019 16654652982419826756435029)
                ·
                  refine ⟨195171714637732344801973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16654652982419826756435029 195171714637732344801973)
                  ·
                    rfl

theorem cell23_3420860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 1, 8].length) (baseStart_3420860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3420860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3420860 prefixEnd_3420860 := by exact prefixLift 3420860
  have htrace : WordTrace (prefixWord ++ tailWord_3420860) baseStart_3420860 baseEnd_3420860 := by
    simpa [prefixWord, tailWord_3420860, baseEnd_3420860] using wordTrace_append hprefix tailTrace_3420860
  have hstable : (prefixWord ++ tailWord_3420860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3420860).length < 2 ^ (prefixWord ++ tailWord_3420860).sum := by decide
  have hdescent : baseEnd_3420860 < baseStart_3420860 := by decide
  rcases family_descends (prefixWord ++ tailWord_3420860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3420864 : List Nat := [2, 1, 1, 2, 4, 2, 2, 4, 1, 4]
def baseStart_3420864 : Nat := 118140960795 + 3420864 * 2 ^ 59
def prefixEnd_3420864 : Nat := 4983230072969 + 3 ^ 40 * 3420864 * 2
def baseEnd_3420864 : Nat := 585515828554069695855913

theorem tailTrace_3420864 : CollatzResearch.WordTrace tailWord_3420864 prefixEnd_3420864 585515828554069695855913 := by
  unfold tailWord_3420864
  simp only [CollatzResearch.WordTrace]
  refine ⟨62384580139400719951410823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83179440185867626601881097 62384580139400719951410823)
  ·
    refine ⟨93576870209101079927116235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62384580139400719951410823 93576870209101079927116235)
    ·
      refine ⟨140365305313651619890674353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93576870209101079927116235 140365305313651619890674353)
      ·
        refine ⟨105273978985238714918005765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140365305313651619890674353 105273978985238714918005765)
        ·
          refine ⟨19738871059732259047126081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 105273978985238714918005765 19738871059732259047126081)
          ·
            refine ⟨14804153294799194285344561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19738871059732259047126081 14804153294799194285344561)
            ·
              refine ⟨11103114971099395714008421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14804153294799194285344561 11103114971099395714008421)
              ·
                refine ⟨2081834057081136696376579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11103114971099395714008421 2081834057081136696376579)
                ·
                  refine ⟨3122751085621705044564869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2081834057081136696376579 3122751085621705044564869)
                  ·
                    refine ⟨585515828554069695855913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3122751085621705044564869 585515828554069695855913)
                    ·
                      rfl

theorem cell23_3420864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 4, 1, 4].length) (baseStart_3420864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3420864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3420864 prefixEnd_3420864 := by exact prefixLift 3420864
  have htrace : WordTrace (prefixWord ++ tailWord_3420864) baseStart_3420864 baseEnd_3420864 := by
    simpa [prefixWord, tailWord_3420864, baseEnd_3420864] using wordTrace_append hprefix tailTrace_3420864
  have hstable : (prefixWord ++ tailWord_3420864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3420864).length < 2 ^ (prefixWord ++ tailWord_3420864).sum := by decide
  have hdescent : baseEnd_3420864 < baseStart_3420864 := by decide
  rcases family_descends (prefixWord ++ tailWord_3420864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3420914 : List Nat := [3, 2, 1, 3, 1, 2, 1, 1, 4, 3, 2]
def baseStart_3420914 : Nat := 118140960795 + 3420914 * 2 ^ 59
def prefixEnd_3420914 : Nat := 4983230072969 + 3 ^ 40 * 3420914 * 2
def baseEnd_3420914 : Nat := 1756573159694933891942509

theorem tailTrace_3420914 : CollatzResearch.WordTrace tailWord_3420914 prefixEnd_3420914 1756573159694933891942509 := by
  unfold tailWord_3420914
  simp only [CollatzResearch.WordTrace]
  refine ⟨31192745982155074610535449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83180655952413532294761197 31192745982155074610535449)
  ·
    refine ⟨23394559486616305957901587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31192745982155074610535449 23394559486616305957901587)
    ·
      refine ⟨35091839229924458936852381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23394559486616305957901587 35091839229924458936852381)
      ·
        refine ⟨13159439711221672101319643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35091839229924458936852381 13159439711221672101319643)
        ·
          refine ⟨19739159566832508151979465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13159439711221672101319643 19739159566832508151979465)
          ·
            refine ⟨14804369675124381113984599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19739159566832508151979465 14804369675124381113984599)
            ·
              refine ⟨22206554512686571670976899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14804369675124381113984599 22206554512686571670976899)
              ·
                refine ⟨33309831769029857506465349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22206554512686571670976899 33309831769029857506465349)
                ·
                  refine ⟨6245593456693098282462253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33309831769029857506465349 6245593456693098282462253)
                  ·
                    refine ⟨2342097546259911855923345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6245593456693098282462253 2342097546259911855923345)
                    ·
                      refine ⟨1756573159694933891942509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2342097546259911855923345 1756573159694933891942509)
                      ·
                        rfl

theorem cell23_3420914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 1, 4, 3, 2].length) (baseStart_3420914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3420914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3420914 prefixEnd_3420914 := by exact prefixLift 3420914
  have htrace : WordTrace (prefixWord ++ tailWord_3420914) baseStart_3420914 baseEnd_3420914 := by
    simpa [prefixWord, tailWord_3420914, baseEnd_3420914] using wordTrace_append hprefix tailTrace_3420914
  have hstable : (prefixWord ++ tailWord_3420914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3420914).length < 2 ^ (prefixWord ++ tailWord_3420914).sum := by decide
  have hdescent : baseEnd_3420914 < baseStart_3420914 := by decide
  rcases family_descends (prefixWord ++ tailWord_3420914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3420947 : List Nat := [1, 1, 1, 2, 1, 3, 5, 1, 3, 2, 3]
def baseStart_3420947 : Nat := 118140960795 + 3420947 * 2 ^ 59
def prefixEnd_3420947 : Nat := 4983230072969 + 3 ^ 40 * 3420947 * 2
def baseEnd_3420947 : Nat := 1756590104556532262829857

theorem tailTrace_3420947 : CollatzResearch.WordTrace tailWord_3420947 prefixEnd_3420947 1756590104556532262829857 := by
  unfold tailWord_3420947
  simp only [CollatzResearch.WordTrace]
  refine ⟨124772187537500745078093095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83181458358333830052062063 124772187537500745078093095)
  ·
    refine ⟨187158281306251117617139643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124772187537500745078093095 187158281306251117617139643)
    ·
      refine ⟨280737421959376676425709465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187158281306251117617139643 280737421959376676425709465)
      ·
        refine ⟨210553066469532507319282099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 280737421959376676425709465 210553066469532507319282099)
        ·
          refine ⟨315829599704298760978923149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210553066469532507319282099 315829599704298760978923149)
          ·
            refine ⟨118436099889112035367096181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 315829599704298760978923149 118436099889112035367096181)
            ·
              refine ⟨11103384364604253315665267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 118436099889112035367096181 11103384364604253315665267)
              ·
                refine ⟨16655076546906379973497901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11103384364604253315665267 16655076546906379973497901)
                ·
                  refine ⟨6245653705089892490061713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16655076546906379973497901 6245653705089892490061713)
                  ·
                    refine ⟨4684240278817419367546285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6245653705089892490061713 4684240278817419367546285)
                    ·
                      refine ⟨1756590104556532262829857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4684240278817419367546285 1756590104556532262829857)
                      ·
                        rfl

theorem cell23_3420947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 1, 3, 2, 3].length) (baseStart_3420947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3420947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3420947 prefixEnd_3420947 := by exact prefixLift 3420947
  have htrace : WordTrace (prefixWord ++ tailWord_3420947) baseStart_3420947 baseEnd_3420947 := by
    simpa [prefixWord, tailWord_3420947, baseEnd_3420947] using wordTrace_append hprefix tailTrace_3420947
  have hstable : (prefixWord ++ tailWord_3420947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3420947).length < 2 ^ (prefixWord ++ tailWord_3420947).sum := by decide
  have hdescent : baseEnd_3420947 < baseStart_3420947 := by decide
  rcases family_descends (prefixWord ++ tailWord_3420947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3420977 : List Nat := [1, 2, 2, 3, 2, 1, 1, 2, 3, 3, 3]
def baseStart_3420977 : Nat := 118140960795 + 3420977 * 2 ^ 59
def prefixEnd_3420977 : Nat := 4983230072969 + 3 ^ 40 * 3420977 * 2
def baseEnd_3420977 : Nat := 1756605508976167145454719

theorem tailTrace_3420977 : CollatzResearch.WordTrace tailWord_3420977 prefixEnd_3420977 1756605508976167145454719 := by
  unfold tailWord_3420977
  simp only [CollatzResearch.WordTrace]
  refine ⟨124773281727392060201685185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83182187818261373467790123 124773281727392060201685185)
  ·
    refine ⟨93579961295544045151263889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124773281727392060201685185 93579961295544045151263889)
    ·
      refine ⟨70184970971658033863447917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93579961295544045151263889 70184970971658033863447917)
      ·
        refine ⟨26319364114371762698792969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70184970971658033863447917 26319364114371762698792969)
        ·
          refine ⟨19739523085778822024094727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26319364114371762698792969 19739523085778822024094727)
          ·
            refine ⟨29609284628668233036142091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19739523085778822024094727 29609284628668233036142091)
            ·
              refine ⟨44413926943002349554213137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29609284628668233036142091 44413926943002349554213137)
              ·
                refine ⟨33310445207251762165659853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44413926943002349554213137 33310445207251762165659853)
                ·
                  refine ⟨12491416952719410812122445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33310445207251762165659853 12491416952719410812122445)
                  ·
                    refine ⟨4684281357269779054545917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12491416952719410812122445 4684281357269779054545917)
                    ·
                      refine ⟨1756605508976167145454719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4684281357269779054545917 1756605508976167145454719)
                      ·
                        rfl

theorem cell23_3420977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 2, 3, 3, 3].length) (baseStart_3420977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3420977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3420977 prefixEnd_3420977 := by exact prefixLift 3420977
  have htrace : WordTrace (prefixWord ++ tailWord_3420977) baseStart_3420977 baseEnd_3420977 := by
    simpa [prefixWord, tailWord_3420977, baseEnd_3420977] using wordTrace_append hprefix tailTrace_3420977
  have hstable : (prefixWord ++ tailWord_3420977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3420977).length < 2 ^ (prefixWord ++ tailWord_3420977).sum := by decide
  have hdescent : baseEnd_3420977 < baseStart_3420977 := by decide
  rcases family_descends (prefixWord ++ tailWord_3420977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3420978 : List Nat := [3, 2, 1, 1, 3, 1, 3, 4, 1, 2, 2]
def baseStart_3420978 : Nat := 118140960795 + 3420978 * 2 ^ 59
def prefixEnd_3420978 : Nat := 4983230072969 + 3 ^ 40 * 3420978 * 2
def baseEnd_3420978 : Nat := 1756606022456821641542215

theorem tailTrace_3420978 : CollatzResearch.WordTrace tailWord_3420978 prefixEnd_3420978 1756606022456821641542215 := by
  unfold tailWord_3420978
  simp only [CollatzResearch.WordTrace]
  refine ⟨31193329550097109343117897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83182212133592291581647725 31193329550097109343117897)
  ·
    refine ⟨23394997162572832007338423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31193329550097109343117897 23394997162572832007338423)
    ·
      refine ⟨35092495743859248011007635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23394997162572832007338423 35092495743859248011007635)
      ·
        refine ⟨52638743615788872016511453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35092495743859248011007635 52638743615788872016511453)
        ·
          refine ⟨19739528855920827006191795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52638743615788872016511453 19739528855920827006191795)
          ·
            refine ⟨29609293283881240509287693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19739528855920827006191795 29609293283881240509287693)
            ·
              refine ⟨11103484981455465190982885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29609293283881240509287693 11103484981455465190982885)
              ·
                refine ⟨2081903434022899723309291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11103484981455465190982885 2081903434022899723309291)
                ·
                  refine ⟨3122855151034349584963937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2081903434022899723309291 3122855151034349584963937)
                  ·
                    refine ⟨2342141363275762188722953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3122855151034349584963937 2342141363275762188722953)
                    ·
                      refine ⟨1756606022456821641542215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2342141363275762188722953 1756606022456821641542215)
                      ·
                        rfl

theorem cell23_3420978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 4, 1, 2, 2].length) (baseStart_3420978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3420978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3420978 prefixEnd_3420978 := by exact prefixLift 3420978
  have htrace : WordTrace (prefixWord ++ tailWord_3420978) baseStart_3420978 baseEnd_3420978 := by
    simpa [prefixWord, tailWord_3420978, baseEnd_3420978] using wordTrace_append hprefix tailTrace_3420978
  have hstable : (prefixWord ++ tailWord_3420978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3420978).length < 2 ^ (prefixWord ++ tailWord_3420978).sum := by decide
  have hdescent : baseEnd_3420978 < baseStart_3420978 := by decide
  rcases family_descends (prefixWord ++ tailWord_3420978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3421027 : List Nat := [1, 1, 1, 5, 3, 1, 1, 2, 2, 6]
def baseStart_3421027 : Nat := 118140960795 + 3421027 * 2 ^ 59
def prefixEnd_3421027 : Nat := 4983230072969 + 3 ^ 40 * 3421027 * 2
def baseEnd_3421027 : Nat := 585543727669630649943163

theorem tailTrace_3421027 : CollatzResearch.WordTrace tailWord_3421027 prefixEnd_3421027 585543727669630649943163 := by
  unfold tailWord_3421027
  simp only [CollatzResearch.WordTrace]
  refine ⟨124775105377210918741005335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83183403584807279160670223 124775105377210918741005335)
  ·
    refine ⟨187162658065816378111508003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124775105377210918741005335 187162658065816378111508003)
    ·
      refine ⟨280743987098724567167262005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187162658065816378111508003 280743987098724567167262005)
      ·
        refine ⟨26319748790505428171930813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 280743987098724567167262005 26319748790505428171930813)
        ·
          refine ⟨9869905796439535564474055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26319748790505428171930813 9869905796439535564474055)
          ·
            refine ⟨14804858694659303346711083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9869905796439535564474055 14804858694659303346711083)
            ·
              refine ⟨22207288041988955020066625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14804858694659303346711083 22207288041988955020066625)
              ·
                refine ⟨16655466031491716265049969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22207288041988955020066625 16655466031491716265049969)
                ·
                  refine ⟨12491599523618787198787477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16655466031491716265049969 12491599523618787198787477)
                  ·
                    refine ⟨585543727669630649943163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12491599523618787198787477 585543727669630649943163)
                    ·
                      rfl

theorem cell23_3421027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 2, 2, 6].length) (baseStart_3421027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3421027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3421027 prefixEnd_3421027 := by exact prefixLift 3421027
  have htrace : WordTrace (prefixWord ++ tailWord_3421027) baseStart_3421027 baseEnd_3421027 := by
    simpa [prefixWord, tailWord_3421027, baseEnd_3421027] using wordTrace_append hprefix tailTrace_3421027
  have hstable : (prefixWord ++ tailWord_3421027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3421027).length < 2 ^ (prefixWord ++ tailWord_3421027).sum := by decide
  have hdescent : baseEnd_3421027 < baseStart_3421027 := by decide
  rcases family_descends (prefixWord ++ tailWord_3421027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3421028 : List Nat := [2, 3, 1, 1, 4, 3, 1, 2, 2, 1, 3]
def baseStart_3421028 : Nat := 118140960795 + 3421028 * 2 ^ 59
def prefixEnd_3421028 : Nat := 4983230072969 + 3 ^ 40 * 3421028 * 2
def baseEnd_3421028 : Nat := 1756631696489546445916985

theorem tailTrace_3421028 : CollatzResearch.WordTrace tailWord_3421028 prefixEnd_3421028 1756631696489546445916985 := by
  unfold tailWord_3421028
  simp only [CollatzResearch.WordTrace]
  refine ⟨62387570925103647955895869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83183427900138197274527825 62387570925103647955895869)
  ·
    refine ⟨23395339096913867983460951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62387570925103647955895869 23395339096913867983460951)
    ·
      refine ⟨35093008645370801975191427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23395339096913867983460951 35093008645370801975191427)
      ·
        refine ⟨52639512968056202962787141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35093008645370801975191427 52639512968056202962787141)
        ·
          refine ⟨9869908681510538055522589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52639512968056202962787141 9869908681510538055522589)
          ·
            refine ⟨3701215755566451770820971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9869908681510538055522589 3701215755566451770820971)
            ·
              refine ⟨5551823633349677656231457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3701215755566451770820971 5551823633349677656231457)
              ·
                refine ⟨4163867725012258242173593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5551823633349677656231457 4163867725012258242173593)
                ·
                  refine ⟨3122900793759193681630195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4163867725012258242173593 3122900793759193681630195)
                  ·
                    refine ⟨4684351190638790522445293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3122900793759193681630195 4684351190638790522445293)
                    ·
                      refine ⟨1756631696489546445916985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4684351190638790522445293 1756631696489546445916985)
                      ·
                        rfl

theorem cell23_3421028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 1, 2, 2, 1, 3].length) (baseStart_3421028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3421028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3421028 prefixEnd_3421028 := by exact prefixLift 3421028
  have htrace : WordTrace (prefixWord ++ tailWord_3421028) baseStart_3421028 baseEnd_3421028 := by
    simpa [prefixWord, tailWord_3421028, baseEnd_3421028] using wordTrace_append hprefix tailTrace_3421028
  have hstable : (prefixWord ++ tailWord_3421028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3421028).length < 2 ^ (prefixWord ++ tailWord_3421028).sum := by decide
  have hdescent : baseEnd_3421028 < baseStart_3421028 := by decide
  rcases family_descends (prefixWord ++ tailWord_3421028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3421037 : List Nat := [1, 5, 1, 1, 1, 1, 1, 2, 4, 1, 5]
def baseStart_3421037 : Nat := 118140960795 + 3421037 * 2 ^ 59
def prefixEnd_3421037 : Nat := 4983230072969 + 3 ^ 40 * 3421037 * 2
def baseEnd_3421037 : Nat := 1756636317815436910704443

theorem tailTrace_3421037 : CollatzResearch.WordTrace tailWord_3421037 prefixEnd_3421037 1756636317815436910704443 := by
  unfold tailWord_3421037
  simp only [CollatzResearch.WordTrace]
  refine ⟨124775470107174690448869365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83183646738116460299246243 124775470107174690448869365)
  ·
    refine ⟨11697700322547627229581503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 124775470107174690448869365 11697700322547627229581503)
    ·
      refine ⟨17546550483821440844372255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11697700322547627229581503 17546550483821440844372255)
      ·
        refine ⟨26319825725732161266558383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17546550483821440844372255 26319825725732161266558383)
        ·
          refine ⟨39479738588598241899837575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26319825725732161266558383 39479738588598241899837575)
          ·
            refine ⟨59219607882897362849756363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39479738588598241899837575 59219607882897362849756363)
            ·
              refine ⟨88829411824346044274634545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59219607882897362849756363 88829411824346044274634545)
              ·
                refine ⟨66622058868259533205975909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88829411824346044274634545 66622058868259533205975909)
                ·
                  refine ⟨12491636037798662476120483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66622058868259533205975909 12491636037798662476120483)
                  ·
                    refine ⟨18737454056697993714180725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12491636037798662476120483 18737454056697993714180725)
                    ·
                      refine ⟨1756636317815436910704443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18737454056697993714180725 1756636317815436910704443)
                      ·
                        rfl

theorem cell23_3421037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 4, 1, 5].length) (baseStart_3421037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3421037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3421037 prefixEnd_3421037 := by exact prefixLift 3421037
  have htrace : WordTrace (prefixWord ++ tailWord_3421037) baseStart_3421037 baseEnd_3421037 := by
    simpa [prefixWord, tailWord_3421037, baseEnd_3421037] using wordTrace_append hprefix tailTrace_3421037
  have hstable : (prefixWord ++ tailWord_3421037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3421037).length < 2 ^ (prefixWord ++ tailWord_3421037).sum := by decide
  have hdescent : baseEnd_3421037 < baseStart_3421037 := by decide
  rcases family_descends (prefixWord ++ tailWord_3421037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3421051 : List Nat := [1, 1, 1, 1, 1, 5, 2, 5, 2, 2, 2]
def baseStart_3421051 : Nat := 118140960795 + 3421051 * 2 ^ 59
def prefixEnd_3421051 : Nat := 4983230072969 + 3 ^ 40 * 3421051 * 2
def baseEnd_3421051 : Nat := 1756643506544599855929379

theorem tailTrace_3421051 : CollatzResearch.WordTrace tailWord_3421051 prefixEnd_3421051 1756643506544599855929379 := by
  unfold tailWord_3421051
  simp only [CollatzResearch.WordTrace]
  refine ⟨124775980729123970839879007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83183987152749313893252671 124775980729123970839879007)
  ·
    refine ⟨187163971093685956259818511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124775980729123970839879007 187163971093685956259818511)
    ·
      refine ⟨280745956640528934389727767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187163971093685956259818511 280745956640528934389727767)
      ·
        refine ⟨421118934960793401584591651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280745956640528934389727767 421118934960793401584591651)
        ·
          refine ⟨631678402441190102376887477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 421118934960793401584591651 631678402441190102376887477)
          ·
            refine ⟨59219850228861572097833201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 631678402441190102376887477 59219850228861572097833201)
            ·
              refine ⟨44414887671646179073374901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59219850228861572097833201 44414887671646179073374901)
              ·
                refine ⟨4163895719216829288128897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44414887671646179073374901 4163895719216829288128897)
                ·
                  refine ⟨3122921789412621966096673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4163895719216829288128897 3122921789412621966096673)
                  ·
                    refine ⟨2342191342059466474572505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3122921789412621966096673 2342191342059466474572505)
                    ·
                      refine ⟨1756643506544599855929379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2342191342059466474572505 1756643506544599855929379)
                      ·
                        rfl

theorem cell23_3421051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 5, 2, 2, 2].length) (baseStart_3421051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3421051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3421051 prefixEnd_3421051 := by exact prefixLift 3421051
  have htrace : WordTrace (prefixWord ++ tailWord_3421051) baseStart_3421051 baseEnd_3421051 := by
    simpa [prefixWord, tailWord_3421051, baseEnd_3421051] using wordTrace_append hprefix tailTrace_3421051
  have hstable : (prefixWord ++ tailWord_3421051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3421051).length < 2 ^ (prefixWord ++ tailWord_3421051).sum := by decide
  have hdescent : baseEnd_3421051 < baseStart_3421051 := by decide
  rcases family_descends (prefixWord ++ tailWord_3421051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3421067 : List Nat := [1, 1, 1, 1, 4, 2, 2, 2, 1, 5, 3]
def baseStart_3421067 : Nat := 118140960795 + 3421067 * 2 ^ 59
def prefixEnd_3421067 : Nat := 4983230072969 + 3 ^ 40 * 3421067 * 2
def baseEnd_3421067 : Nat := 1756651722235071793329305

theorem tailTrace_3421067 : CollatzResearch.WordTrace tailWord_3421067 prefixEnd_3421067 1756651722235071793329305 := by
  unfold tailWord_3421067
  simp only [CollatzResearch.WordTrace]
  refine ⟨124776564297066005572461455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83184376198044003714974303 124776564297066005572461455)
  ·
    refine ⟨187164846445599008358692183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124776564297066005572461455 187164846445599008358692183)
    ·
      refine ⟨280747269668398512538038275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187164846445599008358692183 280747269668398512538038275)
      ·
        refine ⟨421120904502597768807057413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280747269668398512538038275 421120904502597768807057413)
        ·
          refine ⟨78960169594237081651323265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 421120904502597768807057413 78960169594237081651323265)
          ·
            refine ⟨59220127195677811238492449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78960169594237081651323265 59220127195677811238492449)
            ·
              refine ⟨44415095396758358428869337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59220127195677811238492449 44415095396758358428869337)
              ·
                refine ⟨33311321547568768821652003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44415095396758358428869337 33311321547568768821652003)
                ·
                  refine ⟨49966982321353153232478005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33311321547568768821652003 49966982321353153232478005)
                  ·
                    refine ⟨4684404592626858115544813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49966982321353153232478005 4684404592626858115544813)
                    ·
                      refine ⟨1756651722235071793329305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4684404592626858115544813 1756651722235071793329305)
                      ·
                        rfl

theorem cell23_3421067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 2, 1, 5, 3].length) (baseStart_3421067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3421067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3421067 prefixEnd_3421067 := by exact prefixLift 3421067
  have htrace : WordTrace (prefixWord ++ tailWord_3421067) baseStart_3421067 baseEnd_3421067 := by
    simpa [prefixWord, tailWord_3421067, baseEnd_3421067] using wordTrace_append hprefix tailTrace_3421067
  have hstable : (prefixWord ++ tailWord_3421067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3421067).length < 2 ^ (prefixWord ++ tailWord_3421067).sum := by decide
  have hdescent : baseEnd_3421067 < baseStart_3421067 := by decide
  rcases family_descends (prefixWord ++ tailWord_3421067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3421097 : List Nat := [1, 2, 1, 1, 1, 1, 7, 1, 1, 2, 5]
def baseStart_3421097 : Nat := 118140960795 + 3421097 * 2 ^ 59
def prefixEnd_3421097 : Nat := 4983230072969 + 3 ^ 40 * 3421097 * 2
def baseEnd_3421097 : Nat := 1756667126654706675954167

theorem tailTrace_3421097 : CollatzResearch.WordTrace tailWord_3421097 prefixEnd_3421097 1756667126654706675954167 := by
  unfold tailWord_3421097
  simp only [CollatzResearch.WordTrace]
  refine ⟨124777658486957320696053545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83185105657971547130702363 124777658486957320696053545)
  ·
    refine ⟨93583243865217990522040159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124777658486957320696053545 93583243865217990522040159)
    ·
      refine ⟨140374865797826985783060239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93583243865217990522040159 140374865797826985783060239)
      ·
        refine ⟨210562298696740478674590359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140374865797826985783060239 210562298696740478674590359)
        ·
          refine ⟨315843448045110718011885539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210562298696740478674590359 315843448045110718011885539)
          ·
            refine ⟨473765172067666077017828309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 315843448045110718011885539 473765172067666077017828309)
            ·
              refine ⟨11103871220335923680105351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 473765172067666077017828309 11103871220335923680105351)
              ·
                refine ⟨16655806830503885520158027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11103871220335923680105351 16655806830503885520158027)
                ·
                  refine ⟨24983710245755828280237041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16655806830503885520158027 24983710245755828280237041)
                  ·
                    refine ⟨18737782684316871210177781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24983710245755828280237041 18737782684316871210177781)
                    ·
                      refine ⟨1756667126654706675954167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18737782684316871210177781 1756667126654706675954167)
                      ·
                        rfl

theorem cell23_3421097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 1, 1, 2, 5].length) (baseStart_3421097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3421097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3421097 prefixEnd_3421097 := by exact prefixLift 3421097
  have htrace : WordTrace (prefixWord ++ tailWord_3421097) baseStart_3421097 baseEnd_3421097 := by
    simpa [prefixWord, tailWord_3421097, baseEnd_3421097] using wordTrace_append hprefix tailTrace_3421097
  have hstable : (prefixWord ++ tailWord_3421097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3421097).length < 2 ^ (prefixWord ++ tailWord_3421097).sum := by decide
  have hdescent : baseEnd_3421097 < baseStart_3421097 := by decide
  rcases family_descends (prefixWord ++ tailWord_3421097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3421107 : List Nat := [1, 1, 1, 2, 3, 1, 2, 4, 1, 3, 4]
def baseStart_3421107 : Nat := 118140960795 + 3421107 * 2 ^ 59
def prefixEnd_3421107 : Nat := 4983230072969 + 3 ^ 40 * 3421107 * 2
def baseEnd_3421107 : Nat := 1756672261461251636829121

theorem tailTrace_3421107 : CollatzResearch.WordTrace tailWord_3421107 prefixEnd_3421107 1756672261461251636829121 := by
  unfold tailWord_3421107
  simp only [CollatzResearch.WordTrace]
  refine ⟨124778023216921092403917575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83185348811280728269278383 124778023216921092403917575)
  ·
    refine ⟨187167034825381638605876363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124778023216921092403917575 187167034825381638605876363)
    ·
      refine ⟨280750552238072457908814545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187167034825381638605876363 280750552238072457908814545)
      ·
        refine ⟨210562914178554343431610909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 280750552238072457908814545 210562914178554343431610909)
        ·
          refine ⟨78961092816957878786854091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 210562914178554343431610909 78961092816957878786854091)
          ·
            refine ⟨118441639225436818180281137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78961092816957878786854091 118441639225436818180281137)
            ·
              refine ⟨88831229419077613635210853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118441639225436818180281137 88831229419077613635210853)
              ·
                refine ⟨16655855516077052556602035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88831229419077613635210853 16655855516077052556602035)
                ·
                  refine ⟨24983783274115578834903053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16655855516077052556602035 24983783274115578834903053)
                  ·
                    refine ⟨9368918727793342063088645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24983783274115578834903053 9368918727793342063088645)
                    ·
                      refine ⟨1756672261461251636829121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9368918727793342063088645 1756672261461251636829121)
                      ·
                        rfl

theorem cell23_3421107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 4, 1, 3, 4].length) (baseStart_3421107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3421107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3421107 prefixEnd_3421107 := by exact prefixLift 3421107
  have htrace : WordTrace (prefixWord ++ tailWord_3421107) baseStart_3421107 baseEnd_3421107 := by
    simpa [prefixWord, tailWord_3421107, baseEnd_3421107] using wordTrace_append hprefix tailTrace_3421107
  have hstable : (prefixWord ++ tailWord_3421107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3421107).length < 2 ^ (prefixWord ++ tailWord_3421107).sum := by decide
  have hdescent : baseEnd_3421107 < baseStart_3421107 := by decide
  rcases family_descends (prefixWord ++ tailWord_3421107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3421137 : List Nat := [1, 2, 2, 1, 2, 1, 4, 1, 2, 1, 6]
def baseStart_3421137 : Nat := 118140960795 + 3421137 * 2 ^ 59
def prefixEnd_3421137 : Nat := 4983230072969 + 3 ^ 40 * 3421137 * 2
def baseEnd_3421137 : Nat := 1756687665880886519453983

theorem tailTrace_3421137 : CollatzResearch.WordTrace tailWord_3421137 prefixEnd_3421137 1756687665880886519453983 := by
  unfold tailWord_3421137
  simp only [CollatzResearch.WordTrace]
  refine ⟨124779117406812407527509665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83186078271208271685006443 124779117406812407527509665)
  ·
    refine ⟨93584338055109305645632249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124779117406812407527509665 93584338055109305645632249)
    ·
      refine ⟨70188253541331979234224187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93584338055109305645632249 70188253541331979234224187)
      ·
        refine ⟨105282380311997968851336281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70188253541331979234224187 105282380311997968851336281)
        ·
          refine ⟨78961785233998476638502211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105282380311997968851336281 78961785233998476638502211)
          ·
            refine ⟨118442677850997714957753317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78961785233998476638502211 118442677850997714957753317)
            ·
              refine ⟨22208002097062071554578747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 118442677850997714957753317 22208002097062071554578747)
              ·
                refine ⟨33312003145593107331868121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22208002097062071554578747 33312003145593107331868121)
                ·
                  refine ⟨24984002359194830498901091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33312003145593107331868121 24984002359194830498901091)
                  ·
                    refine ⟨37476003538792245748351637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24984002359194830498901091 37476003538792245748351637)
                    ·
                      refine ⟨1756687665880886519453983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37476003538792245748351637 1756687665880886519453983)
                      ·
                        rfl

theorem cell23_3421137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 1, 2, 1, 6].length) (baseStart_3421137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3421137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3421137 prefixEnd_3421137 := by exact prefixLift 3421137
  have htrace : WordTrace (prefixWord ++ tailWord_3421137) baseStart_3421137 baseEnd_3421137 := by
    simpa [prefixWord, tailWord_3421137, baseEnd_3421137] using wordTrace_append hprefix tailTrace_3421137
  have hstable : (prefixWord ++ tailWord_3421137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3421137).length < 2 ^ (prefixWord ++ tailWord_3421137).sum := by decide
  have hdescent : baseEnd_3421137 < baseStart_3421137 := by decide
  rcases family_descends (prefixWord ++ tailWord_3421137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3421187 : List Nat := [1, 1, 1, 3, 2, 1, 1, 1, 1, 6, 5]
def baseStart_3421187 : Nat := 118140960795 + 3421187 * 2 ^ 59
def prefixEnd_3421187 : Nat := 4983230072969 + 3 ^ 40 * 3421187 * 2
def baseEnd_3421187 : Nat := 1756713339913611323828753

theorem tailTrace_3421187 : CollatzResearch.WordTrace tailWord_3421187 prefixEnd_3421187 1756713339913611323828753 := by
  unfold tailWord_3421187
  simp only [CollatzResearch.WordTrace]
  refine ⟨124780941056631266066829815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83187294037754177377886543 124780941056631266066829815)
  ·
    refine ⟨187171411584946899100244723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124780941056631266066829815 187171411584946899100244723)
    ·
      refine ⟨280757117377420348650367085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187171411584946899100244723 280757117377420348650367085)
      ·
        refine ⟨105283919016532630743887657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 280757117377420348650367085 105283919016532630743887657)
        ·
          refine ⟨78962939262399473057915743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105283919016532630743887657 78962939262399473057915743)
          ·
            refine ⟨118444408893599209586873615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78962939262399473057915743 118444408893599209586873615)
            ·
              refine ⟨177666613340398814380310423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118444408893599209586873615 177666613340398814380310423)
              ·
                refine ⟨266499920010598221570465635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 177666613340398814380310423 266499920010598221570465635)
                ·
                  refine ⟨399749880015897332355698453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 266499920010598221570465635 399749880015897332355698453)
                  ·
                    refine ⟨18738275625745187454173365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 399749880015897332355698453 18738275625745187454173365)
                    ·
                      refine ⟨1756713339913611323828753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18738275625745187454173365 1756713339913611323828753)
                      ·
                        rfl

theorem cell23_3421187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 6, 5].length) (baseStart_3421187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3421187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3421187 prefixEnd_3421187 := by exact prefixLift 3421187
  have htrace : WordTrace (prefixWord ++ tailWord_3421187) baseStart_3421187 baseEnd_3421187 := by
    simpa [prefixWord, tailWord_3421187, baseEnd_3421187] using wordTrace_append hprefix tailTrace_3421187
  have hstable : (prefixWord ++ tailWord_3421187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3421187).length < 2 ^ (prefixWord ++ tailWord_3421187).sum := by decide
  have hdescent : baseEnd_3421187 < baseStart_3421187 := by decide
  rcases family_descends (prefixWord ++ tailWord_3421187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3421191 : List Nat := [1, 1, 4, 3, 1, 1, 1, 2, 5, 1, 3]
def baseStart_3421191 : Nat := 118140960795 + 3421191 * 2 ^ 59
def prefixEnd_3421191 : Nat := 4983230072969 + 3 ^ 40 * 3421191 * 2
def baseEnd_3421191 : Nat := 1756715393836229308178735

theorem tailTrace_3421191 : CollatzResearch.WordTrace tailWord_3421191 prefixEnd_3421191 1756715393836229308178735 := by
  unfold tailWord_3421191
  simp only [CollatzResearch.WordTrace]
  refine ⟨124781086948616774749975427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83187391299077849833316951 124781086948616774749975427)
  ·
    refine ⟨187171630422925162124963141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124781086948616774749975427 187171630422925162124963141)
    ·
      refine ⟨35094680704298467898430589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 187171630422925162124963141 35094680704298467898430589)
      ·
        refine ⟨13160505264111925461911471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35094680704298467898430589 13160505264111925461911471)
        ·
          refine ⟨19740757896167888192867207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13160505264111925461911471 19740757896167888192867207)
          ·
            refine ⟨29611136844251832289300811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19740757896167888192867207 29611136844251832289300811)
            ·
              refine ⟨44416705266377748433951217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29611136844251832289300811 44416705266377748433951217)
              ·
                refine ⟨33312528949783311325463413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44416705266377748433951217 33312528949783311325463413)
                ·
                  refine ⟨3123049589042185436762195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33312528949783311325463413 3123049589042185436762195)
                  ·
                    refine ⟨4684574383563278155143293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3123049589042185436762195 4684574383563278155143293)
                    ·
                      refine ⟨1756715393836229308178735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4684574383563278155143293 1756715393836229308178735)
                      ·
                        rfl

theorem cell23_3421191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 2, 5, 1, 3].length) (baseStart_3421191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3421191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3421191 prefixEnd_3421191 := by exact prefixLift 3421191
  have htrace : WordTrace (prefixWord ++ tailWord_3421191) baseStart_3421191 baseEnd_3421191 := by
    simpa [prefixWord, tailWord_3421191, baseEnd_3421191] using wordTrace_append hprefix tailTrace_3421191
  have hstable : (prefixWord ++ tailWord_3421191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3421191).length < 2 ^ (prefixWord ++ tailWord_3421191).sum := by decide
  have hdescent : baseEnd_3421191 < baseStart_3421191 := by decide
  rcases family_descends (prefixWord ++ tailWord_3421191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3421201 : List Nat := [1, 2, 2, 1, 1, 2, 1, 6, 2, 3, 2]
def baseStart_3421201 : Nat := 118140960795 + 3421201 * 2 ^ 59
def prefixEnd_3421201 : Nat := 4983230072969 + 3 ^ 40 * 3421201 * 2
def baseEnd_3421201 : Nat := 1756720528642774269053689

theorem tailTrace_3421201 : CollatzResearch.WordTrace tailWord_3421201 prefixEnd_3421201 1756720528642774269053689 := by
  unfold tailWord_3421201
  simp only [CollatzResearch.WordTrace]
  refine ⟨124781451678580546457839457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83187634452387030971892971 124781451678580546457839457)
  ·
    refine ⟨93586088758935409843379593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124781451678580546457839457 93586088758935409843379593)
    ·
      refine ⟨70189566569201557382534695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93586088758935409843379593 70189566569201557382534695)
      ·
        refine ⟨105284349853802336073802043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70189566569201557382534695 105284349853802336073802043)
        ·
          refine ⟨157926524780703504110703065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105284349853802336073802043 157926524780703504110703065)
          ·
            refine ⟨118444893585527628083027299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157926524780703504110703065 118444893585527628083027299)
            ·
              refine ⟨177667340378291442124540949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118444893585527628083027299 177667340378291442124540949)
              ·
                refine ⟨8328156580232411349587857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 177667340378291442124540949 8328156580232411349587857)
                ·
                  refine ⟨6246117435174308512190893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8328156580232411349587857 6246117435174308512190893)
                  ·
                    refine ⟨2342294038190365692071585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6246117435174308512190893 2342294038190365692071585)
                    ·
                      refine ⟨1756720528642774269053689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2342294038190365692071585 1756720528642774269053689)
                      ·
                        rfl

theorem cell23_3421201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 3, 2].length) (baseStart_3421201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3421201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3421201 prefixEnd_3421201 := by exact prefixLift 3421201
  have htrace : WordTrace (prefixWord ++ tailWord_3421201) baseStart_3421201 baseEnd_3421201 := by
    simpa [prefixWord, tailWord_3421201, baseEnd_3421201] using wordTrace_append hprefix tailTrace_3421201
  have hstable : (prefixWord ++ tailWord_3421201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3421201).length < 2 ^ (prefixWord ++ tailWord_3421201).sum := by decide
  have hdescent : baseEnd_3421201 < baseStart_3421201 := by decide
  rcases family_descends (prefixWord ++ tailWord_3421201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3421202 : List Nat := [3, 2, 5, 1, 1, 1, 2, 1, 3, 4]
def baseStart_3421202 : Nat := 118140960795 + 3421202 * 2 ^ 59
def prefixEnd_3421202 : Nat := 4983230072969 + 3 ^ 40 * 3421202 * 2
def baseEnd_3421202 : Nat := 585573680707809588380395

theorem tailTrace_3421202 : CollatzResearch.WordTrace tailWord_3421202 prefixEnd_3421202 585573680707809588380395 := by
  unfold tailWord_3421202
  simp only [CollatzResearch.WordTrace]
  refine ⟨31195372037894230907156465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83187658767717949085750573 31195372037894230907156465)
  ·
    refine ⟨23396529028420673180367349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31195372037894230907156465 23396529028420673180367349)
    ·
      refine ⟨2193424596414438110659439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23396529028420673180367349 2193424596414438110659439)
      ·
        refine ⟨3290136894621657165989159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2193424596414438110659439 3290136894621657165989159)
        ·
          refine ⟨4935205341932485748983739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3290136894621657165989159 4935205341932485748983739)
          ·
            refine ⟨7402808012898728623475609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4935205341932485748983739 7402808012898728623475609)
            ·
              refine ⟨5552106009674046467606707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7402808012898728623475609 5552106009674046467606707)
              ·
                refine ⟨8328159014511069701410061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5552106009674046467606707 8328159014511069701410061)
                ·
                  refine ⟨3123059630441651138028773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8328159014511069701410061 3123059630441651138028773)
                  ·
                    refine ⟨585573680707809588380395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3123059630441651138028773 585573680707809588380395)
                    ·
                      rfl

theorem cell23_3421202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_3421202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3421202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3421202 prefixEnd_3421202 := by exact prefixLift 3421202
  have htrace : WordTrace (prefixWord ++ tailWord_3421202) baseStart_3421202 baseEnd_3421202 := by
    simpa [prefixWord, tailWord_3421202, baseEnd_3421202] using wordTrace_append hprefix tailTrace_3421202
  have hstable : (prefixWord ++ tailWord_3421202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3421202).length < 2 ^ (prefixWord ++ tailWord_3421202).sum := by decide
  have hdescent : baseEnd_3421202 < baseStart_3421202 := by decide
  rcases family_descends (prefixWord ++ tailWord_3421202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3421208 : List Nat := [2, 1, 2, 3, 2, 3, 2, 1, 3, 1, 3]
def baseStart_3421208 : Nat := 118140960795 + 3421208 * 2 ^ 59
def prefixEnd_3421208 : Nat := 4983230072969 + 3 ^ 40 * 3421208 * 2
def baseEnd_3421208 : Nat := 1756724123007355741666157

theorem tailTrace_3421208 : CollatzResearch.WordTrace tailWord_3421208 prefixEnd_3421208 1756724123007355741666157 := by
  unfold tailWord_3421208
  simp only [CollatzResearch.WordTrace]
  refine ⟨62390853494777593326672139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83187804659703457768896185 62390853494777593326672139)
  ·
    refine ⟨93586280242166389990008209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62390853494777593326672139 93586280242166389990008209)
    ·
      refine ⟨70189710181624792492506157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93586280242166389990008209 70189710181624792492506157)
      ·
        refine ⟨26321141318109297184689809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70189710181624792492506157 26321141318109297184689809)
        ·
          refine ⟨19740855988581972888517357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26321141318109297184689809 19740855988581972888517357)
          ·
            refine ⟨7402820995718239833194009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19740855988581972888517357 7402820995718239833194009)
            ·
              refine ⟨5552115746788679874895507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7402820995718239833194009 5552115746788679874895507)
              ·
                refine ⟨8328173620183019812343261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5552115746788679874895507 8328173620183019812343261)
                ·
                  refine ⟨3123065107568632429628723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8328173620183019812343261 3123065107568632429628723)
                  ·
                    refine ⟨4684597661352948644443085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3123065107568632429628723 4684597661352948644443085)
                    ·
                      refine ⟨1756724123007355741666157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4684597661352948644443085 1756724123007355741666157)
                      ·
                        rfl

theorem cell23_3421208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 2, 1, 3, 1, 3].length) (baseStart_3421208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3421208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3421208 prefixEnd_3421208 := by exact prefixLift 3421208
  have htrace : WordTrace (prefixWord ++ tailWord_3421208) baseStart_3421208 baseEnd_3421208 := by
    simpa [prefixWord, tailWord_3421208, baseEnd_3421208] using wordTrace_append hprefix tailTrace_3421208
  have hstable : (prefixWord ++ tailWord_3421208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3421208).length < 2 ^ (prefixWord ++ tailWord_3421208).sum := by decide
  have hdescent : baseEnd_3421208 < baseStart_3421208 := by decide
  rcases family_descends (prefixWord ++ tailWord_3421208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3421234 : List Nat := [3, 2, 1, 1, 2, 2, 1, 2, 3, 1, 5]
def baseStart_3421234 : Nat := 118140960795 + 3421234 * 2 ^ 59
def prefixEnd_3421234 : Nat := 4983230072969 + 3 ^ 40 * 3421234 * 2
def baseEnd_3421234 : Nat := 1756737473504372639941037

theorem tailTrace_3421234 : CollatzResearch.WordTrace tailWord_3421234 prefixEnd_3421234 1756737473504372639941037 := by
  unfold tailWord_3421234
  simp only [CollatzResearch.WordTrace]
  refine ⟨31195663821865248273447689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83188436858307328729193837 31195663821865248273447689)
  ·
    refine ⟨23396747866398936205085767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31195663821865248273447689 23396747866398936205085767)
    ·
      refine ⟨35095121799598404307628651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23396747866398936205085767 35095121799598404307628651)
      ·
        refine ⟨52642682699397606461442977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35095121799598404307628651 52642682699397606461442977)
        ·
          refine ⟨39482012024548204846082233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52642682699397606461442977 39482012024548204846082233)
          ·
            refine ⟨29611509018411153634561675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39482012024548204846082233 29611509018411153634561675)
            ·
              refine ⟨44417263527616730451842513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29611509018411153634561675 44417263527616730451842513)
              ·
                refine ⟨33312947645712547838881885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44417263527616730451842513 33312947645712547838881885)
                ·
                  refine ⟨12492355367142205439580707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33312947645712547838881885 12492355367142205439580707)
                  ·
                    refine ⟨18738533050713308159371061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12492355367142205439580707 18738533050713308159371061)
                    ·
                      refine ⟨1756737473504372639941037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18738533050713308159371061 1756737473504372639941037)
                      ·
                        rfl

theorem cell23_3421234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 2, 3, 1, 5].length) (baseStart_3421234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3421234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3421234 prefixEnd_3421234 := by exact prefixLift 3421234
  have htrace : WordTrace (prefixWord ++ tailWord_3421234) baseStart_3421234 baseEnd_3421234 := by
    simpa [prefixWord, tailWord_3421234, baseEnd_3421234] using wordTrace_append hprefix tailTrace_3421234
  have hstable : (prefixWord ++ tailWord_3421234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3421234).length < 2 ^ (prefixWord ++ tailWord_3421234).sum := by decide
  have hdescent : baseEnd_3421234 < baseStart_3421234 := by decide
  rcases family_descends (prefixWord ++ tailWord_3421234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3421241 : List Nat := [1, 2, 1, 5, 2, 1, 1, 2, 4, 4]
def baseStart_3421241 : Nat := 118140960795 + 3421241 * 2 ^ 59
def prefixEnd_3421241 : Nat := 4983230072969 + 3 ^ 40 * 3421241 * 2
def baseEnd_3421241 : Nat := 585580355956318037517835

theorem tailTrace_3421241 : CollatzResearch.WordTrace tailWord_3421241 prefixEnd_3421241 585580355956318037517835 := by
  unfold tailWord_3421241
  simp only [CollatzResearch.WordTrace]
  refine ⟨124782910598435633289295577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83188607065623755526197051 124782910598435633289295577)
  ·
    refine ⟨93587182948826724966971683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124782910598435633289295577 93587182948826724966971683)
    ·
      refine ⟨140380774423240087450457525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93587182948826724966971683 140380774423240087450457525)
      ·
        refine ⟨13160697602178758198480393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 140380774423240087450457525 13160697602178758198480393)
        ·
          refine ⟨9870523201634068648860295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13160697602178758198480393 9870523201634068648860295)
          ·
            refine ⟨14805784802451102973290443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9870523201634068648860295 14805784802451102973290443)
            ·
              refine ⟨22208677203676654459935665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14805784802451102973290443 22208677203676654459935665)
              ·
                refine ⟨16656507902757490844951749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22208677203676654459935665 16656507902757490844951749)
                ·
                  refine ⟨3123095231767029533428453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16656507902757490844951749 3123095231767029533428453)
                  ·
                    refine ⟨585580355956318037517835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3123095231767029533428453 585580355956318037517835)
                    ·
                      rfl

theorem cell23_3421241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 2, 4, 4].length) (baseStart_3421241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3421241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3421241 prefixEnd_3421241 := by exact prefixLift 3421241
  have htrace : WordTrace (prefixWord ++ tailWord_3421241) baseStart_3421241 baseEnd_3421241 := by
    simpa [prefixWord, tailWord_3421241, baseEnd_3421241] using wordTrace_append hprefix tailTrace_3421241
  have hstable : (prefixWord ++ tailWord_3421241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3421241).length < 2 ^ (prefixWord ++ tailWord_3421241).sum := by decide
  have hdescent : baseEnd_3421241 < baseStart_3421241 := by decide
  rcases family_descends (prefixWord ++ tailWord_3421241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3421251 : List Nat := [1, 1, 1, 3, 1, 2, 3, 5, 1, 2, 3]
def baseStart_3421251 : Nat := 118140960795 + 3421251 * 2 ^ 59
def prefixEnd_3421251 : Nat := 4983230072969 + 3 ^ 40 * 3421251 * 2
def baseEnd_3421251 : Nat := 1756746202675499073428459

theorem tailTrace_3421251 : CollatzResearch.WordTrace tailWord_3421251 prefixEnd_3421251 1756746202675499073428459 := by
  unfold tailWord_3421251
  simp only [CollatzResearch.WordTrace]
  refine ⟨124783275328399404997159607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83188850218932936664773071 124783275328399404997159607)
  ·
    refine ⟨187174912992599107495739411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124783275328399404997159607 187174912992599107495739411)
    ·
      refine ⟨280762369488898661243609117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187174912992599107495739411 280762369488898661243609117)
      ·
        refine ⟨105285888558336997966353419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 280762369488898661243609117 105285888558336997966353419)
        ·
          refine ⟨157928832837505496949530129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105285888558336997966353419 157928832837505496949530129)
          ·
            refine ⟨118446624628129122712147597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157928832837505496949530129 118446624628129122712147597)
            ·
              refine ⟨44417484235548421017055349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118446624628129122712147597 44417484235548421017055349)
              ·
                refine ⟨4164139147082664470348939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44417484235548421017055349 4164139147082664470348939)
                ·
                  refine ⟨6246208720623996705523409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4164139147082664470348939 6246208720623996705523409)
                  ·
                    refine ⟨4684656540467997529142557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6246208720623996705523409 4684656540467997529142557)
                    ·
                      refine ⟨1756746202675499073428459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4684656540467997529142557 1756746202675499073428459)
                      ·
                        rfl

theorem cell23_3421251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 5, 1, 2, 3].length) (baseStart_3421251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3421251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3421251 prefixEnd_3421251 := by exact prefixLift 3421251
  have htrace : WordTrace (prefixWord ++ tailWord_3421251) baseStart_3421251 baseEnd_3421251 := by
    simpa [prefixWord, tailWord_3421251, baseEnd_3421251] using wordTrace_append hprefix tailTrace_3421251
  have hstable : (prefixWord ++ tailWord_3421251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3421251).length < 2 ^ (prefixWord ++ tailWord_3421251).sum := by decide
  have hdescent : baseEnd_3421251 < baseStart_3421251 := by decide
  rcases family_descends (prefixWord ++ tailWord_3421251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3421261 : List Nat := [1, 6, 1, 1, 1, 2, 1, 2, 1, 1, 6]
def baseStart_3421261 : Nat := 118140960795 + 3421261 * 2 ^ 59
def prefixEnd_3421261 : Nat := 4983230072969 + 3 ^ 40 * 3421261 * 2
def baseEnd_3421261 : Nat := 1756751337482044034303413

theorem tailTrace_3421261 : CollatzResearch.WordTrace tailWord_3421261 prefixEnd_3421261 1756751337482044034303413 := by
  unfold tailWord_3421261
  simp only [CollatzResearch.WordTrace]
  refine ⟨124783640058363176705023637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83189093372242117803349091 124783640058363176705023637)
  ·
    refine ⟨5849233127735773908047983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 124783640058363176705023637 5849233127735773908047983)
    ·
      refine ⟨8773849691603660862071975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5849233127735773908047983 8773849691603660862071975)
      ·
        refine ⟨13160774537405491293107963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8773849691603660862071975 13160774537405491293107963)
        ·
          refine ⟨19741161806108236939661945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13160774537405491293107963 19741161806108236939661945)
          ·
            refine ⟨14805871354581177704746459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19741161806108236939661945 14805871354581177704746459)
            ·
              refine ⟨22208807031871766557119689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14805871354581177704746459 22208807031871766557119689)
              ·
                refine ⟨16656605273903824917839767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22208807031871766557119689 16656605273903824917839767)
                ·
                  refine ⟨24984907910855737376759651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16656605273903824917839767 24984907910855737376759651)
                  ·
                    refine ⟨37477361866283606065139477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24984907910855737376759651 37477361866283606065139477)
                    ·
                      refine ⟨1756751337482044034303413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37477361866283606065139477 1756751337482044034303413)
                      ·
                        rfl

theorem cell23_3421261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_3421261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3421261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3421261 prefixEnd_3421261 := by exact prefixLift 3421261
  have htrace : WordTrace (prefixWord ++ tailWord_3421261) baseStart_3421261 baseEnd_3421261 := by
    simpa [prefixWord, tailWord_3421261, baseEnd_3421261] using wordTrace_append hprefix tailTrace_3421261
  have hstable : (prefixWord ++ tailWord_3421261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3421261).length < 2 ^ (prefixWord ++ tailWord_3421261).sum := by decide
  have hdescent : baseEnd_3421261 < baseStart_3421261 := by decide
  rcases family_descends (prefixWord ++ tailWord_3421261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3421265 : List Nat := [1, 2, 2, 1, 3, 1, 2, 6, 1, 2, 2]
def baseStart_3421265 : Nat := 118140960795 + 3421265 * 2 ^ 59
def prefixEnd_3421265 : Nat := 4983230072969 + 3 ^ 40 * 3421265 * 2
def baseEnd_3421265 : Nat := 1756753391404662018653395

theorem tailTrace_3421265 : CollatzResearch.WordTrace tailWord_3421265 prefixEnd_3421265 1756753391404662018653395 := by
  unfold tailWord_3421265
  simp only [CollatzResearch.WordTrace]
  refine ⟨124783785950348685388169249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83189190633565790258779499 124783785950348685388169249)
  ·
    refine ⟨93587839462761514041126937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124783785950348685388169249 93587839462761514041126937)
    ·
      refine ⟨70190879597071135530845203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93587839462761514041126937 70190879597071135530845203)
      ·
        refine ⟨105286319395606703296267805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70190879597071135530845203 105286319395606703296267805)
        ·
          refine ⟨39482369773352513736100427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105286319395606703296267805 39482369773352513736100427)
          ·
            refine ⟨59223554660028770604150641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39482369773352513736100427 59223554660028770604150641)
            ·
              refine ⟨44417665995021577953112981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59223554660028770604150641 44417665995021577953112981)
              ·
                refine ⟨2082078093516636466552171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 44417665995021577953112981 2082078093516636466552171)
                ·
                  refine ⟨3123117140274954699828257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2082078093516636466552171 3123117140274954699828257)
                  ·
                    refine ⟨2342337855206216024871193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3123117140274954699828257 2342337855206216024871193)
                    ·
                      refine ⟨1756753391404662018653395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2342337855206216024871193 1756753391404662018653395)
                      ·
                        rfl

theorem cell23_3421265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 6, 1, 2, 2].length) (baseStart_3421265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3421265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3421265 prefixEnd_3421265 := by exact prefixLift 3421265
  have htrace : WordTrace (prefixWord ++ tailWord_3421265) baseStart_3421265 baseEnd_3421265 := by
    simpa [prefixWord, tailWord_3421265, baseEnd_3421265] using wordTrace_append hprefix tailTrace_3421265
  have hstable : (prefixWord ++ tailWord_3421265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3421265).length < 2 ^ (prefixWord ++ tailWord_3421265).sum := by decide
  have hdescent : baseEnd_3421265 < baseStart_3421265 := by decide
  rcases family_descends (prefixWord ++ tailWord_3421265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3421310 : List Nat := [4, 2, 4, 1, 2, 1, 2, 2, 1, 1, 3]
def baseStart_3421310 : Nat := 118140960795 + 3421310 * 2 ^ 59
def prefixEnd_3421310 : Nat := 4983230072969 + 3 ^ 40 * 3421310 * 2
def baseEnd_3421310 : Nat := 1756776498034114342590689

theorem tailTrace_3421310 : CollatzResearch.WordTrace tailWord_3421310 prefixEnd_3421310 1756776498034114342590689 := by
  unfold tailWord_3421310
  simp only [CollatzResearch.WordTrace]
  refine ⟨15598178404398207259194673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83190284823457105382371589 15598178404398207259194673)
  ·
    refine ⟨11698633803298655444396005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15598178404398207259194673 11698633803298655444396005)
    ·
      refine ⟨2193493838118497895824251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11698633803298655444396005 2193493838118497895824251)
      ·
        refine ⟨3290240757177746843736377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2193493838118497895824251 3290240757177746843736377)
        ·
          refine ⟨2467680567883310132802283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3290240757177746843736377 2467680567883310132802283)
          ·
            refine ⟨3701520851824965199203425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2467680567883310132802283 3701520851824965199203425)
            ·
              refine ⟨2776140638868723899402569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3701520851824965199203425 2776140638868723899402569)
              ·
                refine ⟨2082105479151542924551927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2776140638868723899402569 2082105479151542924551927)
                ·
                  refine ⟨3123158218727314386827891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2082105479151542924551927 3123158218727314386827891)
                  ·
                    refine ⟨4684737328090971580241837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3123158218727314386827891 4684737328090971580241837)
                    ·
                      refine ⟨1756776498034114342590689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4684737328090971580241837 1756776498034114342590689)
                      ·
                        rfl

theorem cell23_3421310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_3421310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3421310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3421310 prefixEnd_3421310 := by exact prefixLift 3421310
  have htrace : WordTrace (prefixWord ++ tailWord_3421310) baseStart_3421310 baseEnd_3421310 := by
    simpa [prefixWord, tailWord_3421310, baseEnd_3421310] using wordTrace_append hprefix tailTrace_3421310
  have hstable : (prefixWord ++ tailWord_3421310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3421310).length < 2 ^ (prefixWord ++ tailWord_3421310).sum := by decide
  have hdescent : baseEnd_3421310 < baseStart_3421310 := by decide
  rcases family_descends (prefixWord ++ tailWord_3421310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3421324 : List Nat := [2, 2, 1, 2, 1, 1, 1, 4, 1, 3, 5]
def baseStart_3421324 : Nat := 118140960795 + 3421324 * 2 ^ 59
def prefixEnd_3421324 : Nat := 4983230072969 + 3 ^ 40 * 3421324 * 2
def baseEnd_3421324 : Nat := 1756783686763277287815623

theorem tailTrace_3421324 : CollatzResearch.WordTrace tailWord_3421324 prefixEnd_3421324 1756783686763277287815623 := by
  unfold tailWord_3421324
  simp only [CollatzResearch.WordTrace]
  refine ⟨62392968928567469232283513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83190625238089958976378017 62392968928567469232283513)
  ·
    refine ⟨46794726696425601924212635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62392968928567469232283513 46794726696425601924212635)
    ·
      refine ⟨70192090044638402886318953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46794726696425601924212635 70192090044638402886318953)
      ·
        refine ⟨52644067533478802164739215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70192090044638402886318953 52644067533478802164739215)
        ·
          refine ⟨78966101300218203247108823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52644067533478802164739215 78966101300218203247108823)
          ·
            refine ⟨118449151950327304870663235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78966101300218203247108823 118449151950327304870663235)
            ·
              refine ⟨177673727925490957305994853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118449151950327304870663235 177673727925490957305994853)
              ·
                refine ⟨33313823986029554494874035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 177673727925490957305994853 33313823986029554494874035)
                ·
                  refine ⟨49970735979044331742311053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33313823986029554494874035 49970735979044331742311053)
                  ·
                    refine ⟨18739025992141624403366645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49970735979044331742311053 18739025992141624403366645)
                    ·
                      refine ⟨1756783686763277287815623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18739025992141624403366645 1756783686763277287815623)
                      ·
                        rfl

theorem cell23_3421324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 4, 1, 3, 5].length) (baseStart_3421324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3421324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3421324 prefixEnd_3421324 := by exact prefixLift 3421324
  have htrace : WordTrace (prefixWord ++ tailWord_3421324) baseStart_3421324 baseEnd_3421324 := by
    simpa [prefixWord, tailWord_3421324, baseEnd_3421324] using wordTrace_append hprefix tailTrace_3421324
  have hstable : (prefixWord ++ tailWord_3421324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3421324).length < 2 ^ (prefixWord ++ tailWord_3421324).sum := by decide
  have hdescent : baseEnd_3421324 < baseStart_3421324 := by decide
  rcases family_descends (prefixWord ++ tailWord_3421324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3421341 : List Nat := [1, 4, 2, 1, 1, 2, 1, 2, 2, 4, 3]
def baseStart_3421341 : Nat := 118140960795 + 3421341 * 2 ^ 59
def prefixEnd_3421341 : Nat := 4983230072969 + 3 ^ 40 * 3421341 * 2
def baseEnd_3421341 : Nat := 1756792415934403721303045

theorem tailTrace_3421341 : CollatzResearch.WordTrace tailWord_3421341 prefixEnd_3421341 1756792415934403721303045 := by
  unfold tailWord_3421341
  simp only [CollatzResearch.WordTrace]
  refine ⟨124786557898073350367935877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83191038598715566911957251 124786557898073350367935877)
  ·
    refine ⟨23397479605888753193987977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124786557898073350367935877 23397479605888753193987977)
    ·
      refine ⟨17548109704416564895490983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23397479605888753193987977 17548109704416564895490983)
      ·
        refine ⟨26322164556624847343236475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17548109704416564895490983 26322164556624847343236475)
        ·
          refine ⟨39483246834937271014854713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26322164556624847343236475 39483246834937271014854713)
          ·
            refine ⟨29612435126202953261141035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39483246834937271014854713 29612435126202953261141035)
            ·
              refine ⟨44418652689304429891711553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29612435126202953261141035 44418652689304429891711553)
              ·
                refine ⟨33313989516978322418783665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44418652689304429891711553 33313989516978322418783665)
                ·
                  refine ⟨24985492137733741814087749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33313989516978322418783665 24985492137733741814087749)
                  ·
                    refine ⟨4684779775825076590141453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24985492137733741814087749 4684779775825076590141453)
                    ·
                      refine ⟨1756792415934403721303045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4684779775825076590141453 1756792415934403721303045)
                      ·
                        rfl

theorem cell23_3421341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 2, 2, 4, 3].length) (baseStart_3421341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3421341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3421341 prefixEnd_3421341 := by exact prefixLift 3421341
  have htrace : WordTrace (prefixWord ++ tailWord_3421341) baseStart_3421341 baseEnd_3421341 := by
    simpa [prefixWord, tailWord_3421341, baseEnd_3421341] using wordTrace_append hprefix tailTrace_3421341
  have hstable : (prefixWord ++ tailWord_3421341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3421341).length < 2 ^ (prefixWord ++ tailWord_3421341).sum := by decide
  have hdescent : baseEnd_3421341 < baseStart_3421341 := by decide
  rcases family_descends (prefixWord ++ tailWord_3421341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3421366 : List Nat := [5, 1, 3, 2, 1, 2, 1, 2, 2, 1, 3]
def baseStart_3421366 : Nat := 118140960795 + 3421366 * 2 ^ 59
def prefixEnd_3421366 : Nat := 4983230072969 + 3 ^ 40 * 3421366 * 2
def baseEnd_3421366 : Nat := 1756805252950766123490431

theorem tailTrace_3421366 : CollatzResearch.WordTrace tailWord_3421366 prefixEnd_3421366 1756805252950766123490431 := by
  unfold tailWord_3421366
  simp only [CollatzResearch.WordTrace]
  refine ⟨7799216857686423727349747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 83191646481988519758397301 7799216857686423727349747)
  ·
    refine ⟨11698825286529635591024621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7799216857686423727349747 11698825286529635591024621)
    ·
      refine ⟨4387059482448613346634233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11698825286529635591024621 4387059482448613346634233)
      ·
        refine ⟨3290294611836460009975675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4387059482448613346634233 3290294611836460009975675)
        ·
          refine ⟨4935441917754690014963513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3290294611836460009975675 4935441917754690014963513)
          ·
            refine ⟨3701581438316017511222635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4935441917754690014963513 3701581438316017511222635)
            ·
              refine ⟨5552372157474026266833953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3701581438316017511222635 5552372157474026266833953)
              ·
                refine ⟨4164279118105519700125465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5552372157474026266833953 4164279118105519700125465)
                ·
                  refine ⟨3123209338579139775094099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4164279118105519700125465 3123209338579139775094099)
                  ·
                    refine ⟨4684814007868709662641149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3123209338579139775094099 4684814007868709662641149)
                    ·
                      refine ⟨1756805252950766123490431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4684814007868709662641149 1756805252950766123490431)
                      ·
                        rfl

theorem cell23_3421366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_3421366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3421366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3421366 prefixEnd_3421366 := by exact prefixLift 3421366
  have htrace : WordTrace (prefixWord ++ tailWord_3421366) baseStart_3421366 baseEnd_3421366 := by
    simpa [prefixWord, tailWord_3421366, baseEnd_3421366] using wordTrace_append hprefix tailTrace_3421366
  have hstable : (prefixWord ++ tailWord_3421366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3421366).length < 2 ^ (prefixWord ++ tailWord_3421366).sum := by decide
  have hdescent : baseEnd_3421366 < baseStart_3421366 := by decide
  rcases family_descends (prefixWord ++ tailWord_3421366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3421372 : List Nat := [2, 2, 2, 3, 2, 1, 3, 2, 2, 2, 2]
def baseStart_3421372 : Nat := 118140960795 + 3421372 * 2 ^ 59
def prefixEnd_3421372 : Nat := 4983230072969 + 3 ^ 40 * 3421372 * 2
def baseEnd_3421372 : Nat := 1756808333834693100015403

theorem tailTrace_3421372 : CollatzResearch.WordTrace tailWord_3421372 prefixEnd_3421372 1756808333834693100015403 := by
  unfold tailWord_3421372
  simp only [CollatzResearch.WordTrace]
  refine ⟨62393844280480521331157185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83191792373974028441542913 62393844280480521331157185)
  ·
    refine ⟨46795383210360390998367889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62393844280480521331157185 46795383210360390998367889)
    ·
      refine ⟨35096537407770293248775917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46795383210360390998367889 35096537407770293248775917)
      ·
        refine ⟨13161201527913859968290969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35096537407770293248775917 13161201527913859968290969)
        ·
          refine ⟨9870901145935394976218227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13161201527913859968290969 9870901145935394976218227)
          ·
            refine ⟨14806351718903092464327341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9870901145935394976218227 14806351718903092464327341)
            ·
              refine ⟨5552381894588659674122753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14806351718903092464327341 5552381894588659674122753)
              ·
                refine ⟨4164286420941494755592065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5552381894588659674122753 4164286420941494755592065)
                ·
                  refine ⟨3123214815706121066694049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4164286420941494755592065 3123214815706121066694049)
                  ·
                    refine ⟨2342411111779590800020537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3123214815706121066694049 2342411111779590800020537)
                    ·
                      refine ⟨1756808333834693100015403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2342411111779590800020537 1756808333834693100015403)
                      ·
                        rfl

theorem cell23_3421372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 3, 2, 2, 2, 2].length) (baseStart_3421372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3421372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3421372 prefixEnd_3421372 := by exact prefixLift 3421372
  have htrace : WordTrace (prefixWord ++ tailWord_3421372) baseStart_3421372 baseEnd_3421372 := by
    simpa [prefixWord, tailWord_3421372, baseEnd_3421372] using wordTrace_append hprefix tailTrace_3421372
  have hstable : (prefixWord ++ tailWord_3421372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3421372).length < 2 ^ (prefixWord ++ tailWord_3421372).sum := by decide
  have hdescent : baseEnd_3421372 < baseStart_3421372 := by decide
  rcases family_descends (prefixWord ++ tailWord_3421372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3421485 : List Nat := [1, 5, 3, 1, 1, 1, 1, 4, 6]
def baseStart_3421485 : Nat := 118140960795 + 3421485 * 2 ^ 59
def prefixEnd_3421485 : Nat := 4983230072969 + 3 ^ 40 * 3421485 * 2
def baseEnd_3421485 : Nat := 195207373016516795322487

theorem tailTrace_3421485 : CollatzResearch.WordTrace tailWord_3421485 prefixEnd_3421485 195207373016516795322487 := by
  unfold tailWord_3421485
  simp only [CollatzResearch.WordTrace]
  refine ⟨124791810009551662961177909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83194540006367775307451939 124791810009551662961177909)
  ·
    refine ⟨11699232188395468402610429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 124791810009551662961177909 11699232188395468402610429)
    ·
      refine ⟨4387212070648300650978911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11699232188395468402610429 4387212070648300650978911)
      ·
        refine ⟨6580818105972450976468367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4387212070648300650978911 6580818105972450976468367)
        ·
          refine ⟨9871227158958676464702551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6580818105972450976468367 9871227158958676464702551)
          ·
            refine ⟨14806840738438014697053827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9871227158958676464702551 14806840738438014697053827)
            ·
              refine ⟨22210261107657022045580741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14806840738438014697053827 22210261107657022045580741)
              ·
                refine ⟨4164423957685691633546389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22210261107657022045580741 4164423957685691633546389)
                ·
                  refine ⟨195207373016516795322487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4164423957685691633546389 195207373016516795322487)
                  ·
                    rfl

theorem cell23_3421485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 4, 6].length) (baseStart_3421485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3421485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3421485 prefixEnd_3421485 := by exact prefixLift 3421485
  have htrace : WordTrace (prefixWord ++ tailWord_3421485) baseStart_3421485 baseEnd_3421485 := by
    simpa [prefixWord, tailWord_3421485, baseEnd_3421485] using wordTrace_append hprefix tailTrace_3421485
  have hstable : (prefixWord ++ tailWord_3421485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3421485).length < 2 ^ (prefixWord ++ tailWord_3421485).sum := by decide
  have hdescent : baseEnd_3421485 < baseStart_3421485 := by decide
  rcases family_descends (prefixWord ++ tailWord_3421485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3421489 : List Nat := [1, 2, 2, 3, 3, 3, 2, 2, 1, 4]
def baseStart_3421489 : Nat := 118140960795 + 3421489 * 2 ^ 59
def prefixEnd_3421489 : Nat := 4983230072969 + 3 ^ 40 * 3421489 * 2
def baseEnd_3421489 : Nat := 585622803690423047417455

theorem tailTrace_3421489 : CollatzResearch.WordTrace tailWord_3421489 prefixEnd_3421489 585622803690423047417455 := by
  unfold tailWord_3421489
  simp only [CollatzResearch.WordTrace]
  refine ⟨124791955901537171644323521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83194637267691447762882347 124791955901537171644323521)
  ·
    refine ⟨93593966926152878733242641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124791955901537171644323521 93593966926152878733242641)
    ·
      refine ⟨70195475194614659049931981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93593966926152878733242641 70195475194614659049931981)
      ·
        refine ⟨26323303197980497143724493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70195475194614659049931981 26323303197980497143724493)
        ·
          refine ⟨9871238699242686428896685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26323303197980497143724493 9871238699242686428896685)
          ·
            refine ⟨3701714512216007410836257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9871238699242686428896685 3701714512216007410836257)
            ·
              refine ⟨2776285884162005558127193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3701714512216007410836257 2776285884162005558127193)
              ·
                refine ⟨2082214413121504168595395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2776285884162005558127193 2082214413121504168595395)
                ·
                  refine ⟨3123321619682256252893093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2082214413121504168595395 3123321619682256252893093)
                  ·
                    refine ⟨585622803690423047417455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3123321619682256252893093 585622803690423047417455)
                    ·
                      rfl

theorem cell23_3421489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 2, 2, 1, 4].length) (baseStart_3421489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3421489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3421489 prefixEnd_3421489 := by exact prefixLift 3421489
  have htrace : WordTrace (prefixWord ++ tailWord_3421489) baseStart_3421489 baseEnd_3421489 := by
    simpa [prefixWord, tailWord_3421489, baseEnd_3421489] using wordTrace_append hprefix tailTrace_3421489
  have hstable : (prefixWord ++ tailWord_3421489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3421489).length < 2 ^ (prefixWord ++ tailWord_3421489).sum := by decide
  have hdescent : baseEnd_3421489 < baseStart_3421489 := by decide
  rcases family_descends (prefixWord ++ tailWord_3421489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3421518 : List Nat := [4, 1, 1, 1, 1, 1, 3, 3, 3, 1, 4]
def baseStart_3421518 : Nat := 118140960795 + 3421518 * 2 ^ 59
def prefixEnd_3421518 : Nat := 4983230072969 + 3 ^ 40 * 3421518 * 2
def baseEnd_3421518 : Nat := 1756883302010249528789731

theorem tailTrace_3421518 : CollatzResearch.WordTrace tailWord_3421518 prefixEnd_3421518 1756883302010249528789731 := by
  unfold tailWord_3421518
  simp only [CollatzResearch.WordTrace]
  refine ⟨15599126702304013699641151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83195342412288073064752805 15599126702304013699641151)
  ·
    refine ⟨23398690053456020549461727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15599126702304013699641151 23398690053456020549461727)
    ·
      refine ⟨35098035080184030824192591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23398690053456020549461727 35098035080184030824192591)
      ·
        refine ⟨52647052620276046236288887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35098035080184030824192591 52647052620276046236288887)
        ·
          refine ⟨78970578930414069354433331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52647052620276046236288887 78970578930414069354433331)
          ·
            refine ⟨118455868395621104031649997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78970578930414069354433331 118455868395621104031649997)
            ·
              refine ⟨44420950648357914011868749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118455868395621104031649997 44420950648357914011868749)
              ·
                refine ⟨16657856493134217754450781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44420950648357914011868749 16657856493134217754450781)
                ·
                  refine ⟨6246696184925331657919043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16657856493134217754450781 6246696184925331657919043)
                  ·
                    refine ⟨9370044277387997486878565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6246696184925331657919043 9370044277387997486878565)
                    ·
                      refine ⟨1756883302010249528789731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9370044277387997486878565 1756883302010249528789731)
                      ·
                        rfl

theorem cell23_3421518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 3, 3, 1, 4].length) (baseStart_3421518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3421518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3421518 prefixEnd_3421518 := by exact prefixLift 3421518
  have htrace : WordTrace (prefixWord ++ tailWord_3421518) baseStart_3421518 baseEnd_3421518 := by
    simpa [prefixWord, tailWord_3421518, baseEnd_3421518] using wordTrace_append hprefix tailTrace_3421518
  have hstable : (prefixWord ++ tailWord_3421518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3421518).length < 2 ^ (prefixWord ++ tailWord_3421518).sum := by decide
  have hdescent : baseEnd_3421518 < baseStart_3421518 := by decide
  rcases family_descends (prefixWord ++ tailWord_3421518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3421528 : List Nat := [2, 1, 2, 2, 1, 1, 4, 2, 4, 4]
def baseStart_3421528 : Nat := 118140960795 + 3421528 * 2 ^ 59
def prefixEnd_3421528 : Nat := 4983230072969 + 3 ^ 40 * 3421528 * 2
def baseEnd_3421528 : Nat := 585629478938931496554895

theorem tailTrace_3421528 : CollatzResearch.WordTrace tailWord_3421528 prefixEnd_3421528 585629478938931496554895 := by
  unfold tailWord_3421528
  simp only [CollatzResearch.WordTrace]
  refine ⟨62396689174197940652496619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83195585565597254203328825 62396689174197940652496619)
  ·
    refine ⟨93595033761296910978744929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62396689174197940652496619 93595033761296910978744929)
    ·
      refine ⟨70196275320972683234058697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93595033761296910978744929 70196275320972683234058697)
      ·
        refine ⟨52647206490729512425544023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70196275320972683234058697 52647206490729512425544023)
        ·
          refine ⟨78970809736094268638316035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52647206490729512425544023 78970809736094268638316035)
          ·
            refine ⟨118456214604141402957474053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78970809736094268638316035 118456214604141402957474053)
            ·
              refine ⟨22210540238276513054526385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 118456214604141402957474053 22210540238276513054526385)
              ·
                refine ⟨16657905178707384790894789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22210540238276513054526385 16657905178707384790894789)
                ·
                  refine ⟨3123357221007634648292773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16657905178707384790894789 3123357221007634648292773)
                  ·
                    refine ⟨585629478938931496554895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3123357221007634648292773 585629478938931496554895)
                    ·
                      rfl

theorem cell23_3421528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 2, 4, 4].length) (baseStart_3421528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3421528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3421528 prefixEnd_3421528 := by exact prefixLift 3421528
  have htrace : WordTrace (prefixWord ++ tailWord_3421528) baseStart_3421528 baseEnd_3421528 := by
    simpa [prefixWord, tailWord_3421528, baseEnd_3421528] using wordTrace_append hprefix tailTrace_3421528
  have hstable : (prefixWord ++ tailWord_3421528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3421528).length < 2 ^ (prefixWord ++ tailWord_3421528).sum := by decide
  have hdescent : baseEnd_3421528 < baseStart_3421528 := by decide
  rcases family_descends (prefixWord ++ tailWord_3421528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3421535 : List Nat := [1, 1, 2, 3, 1, 2, 1, 1, 7, 2, 2]
def baseStart_3421535 : Nat := 118140960795 + 3421535 * 2 ^ 59
def prefixEnd_3421535 : Nat := 4983230072969 + 3 ^ 40 * 3421535 * 2
def baseEnd_3421535 : Nat := 1756892031181375962277153

theorem tailTrace_3421535 : CollatzResearch.WordTrace tailWord_3421535 prefixEnd_3421535 1756892031181375962277153 := by
  unfold tailWord_3421535
  simp only [CollatzResearch.WordTrace]
  refine ⟨124793633659370521500498059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83195755772913681000332039 124793633659370521500498059)
  ·
    refine ⟨187190450489055782250747089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124793633659370521500498059 187190450489055782250747089)
    ·
      refine ⟨140392837866791836688060317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187190450489055782250747089 140392837866791836688060317)
      ·
        refine ⟨52647314200046938758022619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140392837866791836688060317 52647314200046938758022619)
        ·
          refine ⟨78970971300070408137033929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52647314200046938758022619 78970971300070408137033929)
          ·
            refine ⟨59228228475052806102775447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78970971300070408137033929 59228228475052806102775447)
            ·
              refine ⟨88842342712579209154163171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59228228475052806102775447 88842342712579209154163171)
              ·
                refine ⟨133263514068868813731244757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88842342712579209154163171 133263514068868813731244757)
                ·
                  refine ⟨3123363610989112821826049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 133263514068868813731244757 3123363610989112821826049)
                  ·
                    refine ⟨2342522708241834616369537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3123363610989112821826049 2342522708241834616369537)
                    ·
                      refine ⟨1756892031181375962277153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2342522708241834616369537 1756892031181375962277153)
                      ·
                        rfl

theorem cell23_3421535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 7, 2, 2].length) (baseStart_3421535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3421535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3421535 prefixEnd_3421535 := by exact prefixLift 3421535
  have htrace : WordTrace (prefixWord ++ tailWord_3421535) baseStart_3421535 baseEnd_3421535 := by
    simpa [prefixWord, tailWord_3421535, baseEnd_3421535] using wordTrace_append hprefix tailTrace_3421535
  have hstable : (prefixWord ++ tailWord_3421535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3421535).length < 2 ^ (prefixWord ++ tailWord_3421535).sum := by decide
  have hdescent : baseEnd_3421535 < baseStart_3421535 := by decide
  rcases family_descends (prefixWord ++ tailWord_3421535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3421541 : List Nat := [1, 3, 1, 3, 1, 2, 12]
def baseStart_3421541 : Nat := 118140960795 + 3421541 * 2 ^ 59
def prefixEnd_3421541 : Nat := 4983230072969 + 3 ^ 40 * 3421541 * 2
def baseEnd_3421541 : Nat := 21690063111917320232125

theorem tailTrace_3421541 : CollatzResearch.WordTrace tailWord_3421541 prefixEnd_3421541 21690063111917320232125 := by
  unfold tailWord_3421541
  simp only [CollatzResearch.WordTrace]
  refine ⟨124793852497348784525216477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83195901664899189683477651 124793852497348784525216477)
  ·
    refine ⟨46797694686505794196956179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124793852497348784525216477 46797694686505794196956179)
    ·
      refine ⟨70196542029758691295434269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46797694686505794196956179 70196542029758691295434269)
      ·
        refine ⟨26323703261159509235787851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70196542029758691295434269 26323703261159509235787851)
        ·
          refine ⟨39485554891739263853681777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26323703261159509235787851 39485554891739263853681777)
          ·
            refine ⟨29614166168804447890261333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39485554891739263853681777 29614166168804447890261333)
            ·
              refine ⟨21690063111917320232125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 29614166168804447890261333 21690063111917320232125)
              ·
                rfl

theorem cell23_3421541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 12].length) (baseStart_3421541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3421541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3421541 prefixEnd_3421541 := by exact prefixLift 3421541
  have htrace : WordTrace (prefixWord ++ tailWord_3421541) baseStart_3421541 baseEnd_3421541 := by
    simpa [prefixWord, tailWord_3421541, baseEnd_3421541] using wordTrace_append hprefix tailTrace_3421541
  have hstable : (prefixWord ++ tailWord_3421541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3421541).length < 2 ^ (prefixWord ++ tailWord_3421541).sum := by decide
  have hdescent : baseEnd_3421541 < baseStart_3421541 := by decide
  rcases family_descends (prefixWord ++ tailWord_3421541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3421552 : List Nat := [2, 1, 1, 1, 4, 2, 4, 1, 3, 2, 2]
def baseStart_3421552 : Nat := 118140960795 + 3421552 * 2 ^ 59
def prefixEnd_3421552 : Nat := 4983230072969 + 3 ^ 40 * 3421552 * 2
def baseEnd_3421552 : Nat := 1756900760352502395764575

theorem tailTrace_3421552 : CollatzResearch.WordTrace tailWord_3421552 prefixEnd_3421552 1756900760352502395764575 := by
  unfold tailWord_3421552
  simp only [CollatzResearch.WordTrace]
  refine ⟨62397126850154466701933455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83196169133539288935911273 62397126850154466701933455)
  ·
    refine ⟨93595690275231700052900183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62397126850154466701933455 93595690275231700052900183)
    ·
      refine ⟨140393535412847550079350275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93595690275231700052900183 140393535412847550079350275)
      ·
        refine ⟨210590303119271325119025413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140393535412847550079350275 210590303119271325119025413)
        ·
          refine ⟨39485681834863373459817265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 210590303119271325119025413 39485681834863373459817265)
          ·
            refine ⟨29614261376147530094862949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39485681834863373459817265 29614261376147530094862949)
            ·
              refine ⟨5552674008027661892786803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29614261376147530094862949 5552674008027661892786803)
              ·
                refine ⟨8329011012041492839180205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5552674008027661892786803 8329011012041492839180205)
                ·
                  refine ⟨3123379129515559814692577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8329011012041492839180205 3123379129515559814692577)
                  ·
                    refine ⟨2342534347136669861019433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3123379129515559814692577 2342534347136669861019433)
                    ·
                      refine ⟨1756900760352502395764575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2342534347136669861019433 1756900760352502395764575)
                      ·
                        rfl

theorem cell23_3421552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 4, 1, 3, 2, 2].length) (baseStart_3421552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3421552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3421552 prefixEnd_3421552 := by exact prefixLift 3421552
  have htrace : WordTrace (prefixWord ++ tailWord_3421552) baseStart_3421552 baseEnd_3421552 := by
    simpa [prefixWord, tailWord_3421552, baseEnd_3421552] using wordTrace_append hprefix tailTrace_3421552
  have hstable : (prefixWord ++ tailWord_3421552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3421552).length < 2 ^ (prefixWord ++ tailWord_3421552).sum := by decide
  have hdescent : baseEnd_3421552 < baseStart_3421552 := by decide
  rcases family_descends (prefixWord ++ tailWord_3421552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3421572 : List Nat := [2, 3, 2, 1, 1, 4, 2, 2, 1, 2, 3]
def baseStart_3421572 : Nat := 118140960795 + 3421572 * 2 ^ 59
def prefixEnd_3421572 : Nat := 4983230072969 + 3 ^ 40 * 3421572 * 2
def baseEnd_3421572 : Nat := 1756911029965592317514483

theorem tailTrace_3421572 : CollatzResearch.WordTrace tailWord_3421572 prefixEnd_3421572 1756911029965592317514483 := by
  unfold tailWord_3421572
  simp only [CollatzResearch.WordTrace]
  refine ⟨62397491580118238409797485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83196655440157651213063313 62397491580118238409797485)
  ·
    refine ⟨23399059342544339403674057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62397491580118238409797485 23399059342544339403674057)
    ·
      refine ⟨17549294506908254552755543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23399059342544339403674057 17549294506908254552755543)
      ·
        refine ⟨26323941760362381829133315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17549294506908254552755543 26323941760362381829133315)
        ·
          refine ⟨39485912640543572743699973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26323941760362381829133315 39485912640543572743699973)
          ·
            refine ⟨7403608620101919889443745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39485912640543572743699973 7403608620101919889443745)
            ·
              refine ⟨5552706465076439917082809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7403608620101919889443745 5552706465076439917082809)
              ·
                refine ⟨4164529848807329937812107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5552706465076439917082809 4164529848807329937812107)
                ·
                  refine ⟨6246794773210994906718161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4164529848807329937812107 6246794773210994906718161)
                  ·
                    refine ⟨4685096079908246180038621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6246794773210994906718161 4685096079908246180038621)
                    ·
                      refine ⟨1756911029965592317514483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4685096079908246180038621 1756911029965592317514483)
                      ·
                        rfl

theorem cell23_3421572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 2, 2, 1, 2, 3].length) (baseStart_3421572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3421572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3421572 prefixEnd_3421572 := by exact prefixLift 3421572
  have htrace : WordTrace (prefixWord ++ tailWord_3421572) baseStart_3421572 baseEnd_3421572 := by
    simpa [prefixWord, tailWord_3421572, baseEnd_3421572] using wordTrace_append hprefix tailTrace_3421572
  have hstable : (prefixWord ++ tailWord_3421572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3421572).length < 2 ^ (prefixWord ++ tailWord_3421572).sum := by decide
  have hdescent : baseEnd_3421572 < baseStart_3421572 := by decide
  rcases family_descends (prefixWord ++ tailWord_3421572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3421575 : List Nat := [1, 1, 4, 2, 2, 4, 2, 7]
def baseStart_3421575 : Nat := 118140960795 + 3421575 * 2 ^ 59
def prefixEnd_3421575 : Nat := 4983230072969 + 3 ^ 40 * 3421575 * 2
def baseEnd_3421575 : Nat := 65070835941020585399147

theorem tailTrace_3421575 : CollatzResearch.WordTrace tailWord_3421575 prefixEnd_3421575 65070835941020585399147 := by
  unfold tailWord_3421575
  simp only [CollatzResearch.WordTrace]
  refine ⟨124795092579225608331954179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83196728386150405554636119 124795092579225608331954179)
  ·
    refine ⟨187192638868838412497931269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124795092579225608331954179 187192638868838412497931269)
    ·
      refine ⟨35098619787907202343362113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 187192638868838412497931269 35098619787907202343362113)
      ·
        refine ⟨26323964840930401757521585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35098619787907202343362113 26323964840930401757521585)
        ·
          refine ⟨19742973630697801318141189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26323964840930401757521585 19742973630697801318141189)
          ·
            refine ⟨3701807555755837747151473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19742973630697801318141189 3701807555755837747151473)
            ·
              refine ⟨2776355666816878310363605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3701807555755837747151473 2776355666816878310363605)
              ·
                refine ⟨65070835941020585399147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2776355666816878310363605 65070835941020585399147)
                ·
                  rfl

theorem cell23_3421575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 2, 7].length) (baseStart_3421575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3421575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3421575 prefixEnd_3421575 := by exact prefixLift 3421575
  have htrace : WordTrace (prefixWord ++ tailWord_3421575) baseStart_3421575 baseEnd_3421575 := by
    simpa [prefixWord, tailWord_3421575, baseEnd_3421575] using wordTrace_append hprefix tailTrace_3421575
  have hstable : (prefixWord ++ tailWord_3421575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3421575).length < 2 ^ (prefixWord ++ tailWord_3421575).sum := by decide
  have hdescent : baseEnd_3421575 < baseStart_3421575 := by decide
  rcases family_descends (prefixWord ++ tailWord_3421575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3421602 : List Nat := [3, 3, 1, 2, 1, 2, 2, 1, 4, 1, 3]
def baseStart_3421602 : Nat := 118140960795 + 3421602 * 2 ^ 59
def prefixEnd_3421602 : Nat := 4983230072969 + 3 ^ 40 * 3421602 * 2
def baseEnd_3421602 : Nat := 1756926434385227200139345

theorem tailTrace_3421602 : CollatzResearch.WordTrace tailWord_3421602 prefixEnd_3421602 1756926434385227200139345 := by
  unfold tailWord_3421602
  simp only [CollatzResearch.WordTrace]
  refine ⟨31199019337531947985796765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83197384900085194628791373 31199019337531947985796765)
  ·
    refine ⟨11699632251574480494673787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31199019337531947985796765 11699632251574480494673787)
    ·
      refine ⟨17549448377361720742010681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11699632251574480494673787 17549448377361720742010681)
      ·
        refine ⟨13162086283021290556508011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17549448377361720742010681 13162086283021290556508011)
        ·
          refine ⟨19743129424531935834762017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13162086283021290556508011 19743129424531935834762017)
          ·
            refine ⟨14807347068398951876071513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19743129424531935834762017 14807347068398951876071513)
            ·
              refine ⟨11105510301299213907053635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14807347068398951876071513 11105510301299213907053635)
              ·
                refine ⟨16658265451948820860580453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11105510301299213907053635 16658265451948820860580453)
                ·
                  refine ⟨3123424772240403911358835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16658265451948820860580453 3123424772240403911358835)
                  ·
                    refine ⟨4685137158360605867038253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3123424772240403911358835 4685137158360605867038253)
                    ·
                      refine ⟨1756926434385227200139345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4685137158360605867038253 1756926434385227200139345)
                      ·
                        rfl

theorem cell23_3421602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 1, 4, 1, 3].length) (baseStart_3421602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3421602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3421602 prefixEnd_3421602 := by exact prefixLift 3421602
  have htrace : WordTrace (prefixWord ++ tailWord_3421602) baseStart_3421602 baseEnd_3421602 := by
    simpa [prefixWord, tailWord_3421602, baseEnd_3421602] using wordTrace_append hprefix tailTrace_3421602
  have hstable : (prefixWord ++ tailWord_3421602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3421602).length < 2 ^ (prefixWord ++ tailWord_3421602).sum := by decide
  have hdescent : baseEnd_3421602 < baseStart_3421602 := by decide
  rcases family_descends (prefixWord ++ tailWord_3421602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3421642 : List Nat := [3, 1, 2, 1, 2, 4, 1, 2, 1, 4, 2]
def baseStart_3421642 : Nat := 118140960795 + 3421642 * 2 ^ 59
def prefixEnd_3421642 : Nat := 4983230072969 + 3 ^ 40 * 3421642 * 2
def baseEnd_3421642 : Nat := 1756946973611407043639161

theorem tailTrace_3421642 : CollatzResearch.WordTrace tailWord_3421642 prefixEnd_3421642 1756946973611407043639161 := by
  unfold tailWord_3421642
  simp only [CollatzResearch.WordTrace]
  refine ⟨31199384067495719693660795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83198357513321919183095453 31199384067495719693660795)
  ·
    refine ⟨46799076101243579540491193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31199384067495719693660795 46799076101243579540491193)
    ·
      refine ⟨35099307075932684655368395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46799076101243579540491193 35099307075932684655368395)
      ·
        refine ⟨52648960613899026983052593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35099307075932684655368395 52648960613899026983052593)
        ·
          refine ⟨39486720460424270237289445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52648960613899026983052593 39486720460424270237289445)
          ·
            refine ⟨7403760086329550669491771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39486720460424270237289445 7403760086329550669491771)
            ·
              refine ⟨11105640129494326004237657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7403760086329550669491771 11105640129494326004237657)
              ·
                refine ⟨8329230097120744503178243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11105640129494326004237657 8329230097120744503178243)
                ·
                  refine ⟨12493845145681116754767365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8329230097120744503178243 12493845145681116754767365)
                  ·
                    refine ⟨2342595964815209391518881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12493845145681116754767365 2342595964815209391518881)
                    ·
                      refine ⟨1756946973611407043639161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2342595964815209391518881 1756946973611407043639161)
                      ·
                        rfl

theorem cell23_3421642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 2, 1, 4, 2].length) (baseStart_3421642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3421642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3421642 prefixEnd_3421642 := by exact prefixLift 3421642
  have htrace : WordTrace (prefixWord ++ tailWord_3421642) baseStart_3421642 baseEnd_3421642 := by
    simpa [prefixWord, tailWord_3421642, baseEnd_3421642] using wordTrace_append hprefix tailTrace_3421642
  have hstable : (prefixWord ++ tailWord_3421642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3421642).length < 2 ^ (prefixWord ++ tailWord_3421642).sum := by decide
  have hdescent : baseEnd_3421642 < baseStart_3421642 := by decide
  rcases family_descends (prefixWord ++ tailWord_3421642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3421759 : List Nat := [1, 1, 2, 2, 3, 3, 3, 3, 1, 4]
def baseStart_3421759 : Nat := 118140960795 + 3421759 * 2 ^ 59
def prefixEnd_3421759 : Nat := 4983230072969 + 3 ^ 40 * 3421759 * 2
def baseEnd_3421759 : Nat := 585669016949327695292041

theorem tailTrace_3421759 : CollatzResearch.WordTrace tailWord_3421759 prefixEnd_3421759 585669016949327695292041 := by
  unfold tailWord_3421759
  simp only [CollatzResearch.WordTrace]
  refine ⟨124801803610559007756652331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83201202407039338504434887 124801803610559007756652331)
  ·
    refine ⟨187202705415838511634978497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124801803610559007756652331 187202705415838511634978497)
    ·
      refine ⟨140402029061878883726233873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187202705415838511634978497 140402029061878883726233873)
      ·
        refine ⟨105301521796409162794675405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140402029061878883726233873 105301521796409162794675405)
        ·
          refine ⟨39488070673653436048003277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105301521796409162794675405 39488070673653436048003277)
          ·
            refine ⟨14808026502620038518001229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39488070673653436048003277 14808026502620038518001229)
            ·
              refine ⟨5553009938482514444250461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14808026502620038518001229 5553009938482514444250461)
              ·
                refine ⟨2082378726930942916593923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5553009938482514444250461 2082378726930942916593923)
                ·
                  refine ⟨3123568090396414374890885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2082378726930942916593923 3123568090396414374890885)
                  ·
                    refine ⟨585669016949327695292041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3123568090396414374890885 585669016949327695292041)
                    ·
                      rfl

theorem cell23_3421759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 3, 3, 1, 4].length) (baseStart_3421759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3421759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3421759 prefixEnd_3421759 := by exact prefixLift 3421759
  have htrace : WordTrace (prefixWord ++ tailWord_3421759) baseStart_3421759 baseEnd_3421759 := by
    simpa [prefixWord, tailWord_3421759, baseEnd_3421759] using wordTrace_append hprefix tailTrace_3421759
  have hstable : (prefixWord ++ tailWord_3421759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3421759).length < 2 ^ (prefixWord ++ tailWord_3421759).sum := by decide
  have hdescent : baseEnd_3421759 < baseStart_3421759 := by decide
  rcases family_descends (prefixWord ++ tailWord_3421759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3421766 : List Nat := [6, 1, 1, 1, 3, 1, 1, 2, 2, 1, 4]
def baseStart_3421766 : Nat := 118140960795 + 3421766 * 2 ^ 59
def prefixEnd_3421766 : Nat := 4983230072969 + 3 ^ 40 * 3421766 * 2
def baseEnd_3421766 : Nat := 1757010645212564558488591

theorem tailTrace_3421766 : CollatzResearch.WordTrace tailWord_3421766 prefixEnd_3421766 1757010645212564558488591 := by
  unfold tailWord_3421766
  simp only [CollatzResearch.WordTrace]
  refine ⟨3900064341297926498504911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 83201372614355765301438101 3900064341297926498504911)
  ·
    refine ⟨5850096511946889747757367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3900064341297926498504911 5850096511946889747757367)
    ·
      refine ⟨8775144767920334621636051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5850096511946889747757367 8775144767920334621636051)
      ·
        refine ⟨13162717151880501932454077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8775144767920334621636051 13162717151880501932454077)
        ·
          refine ⟨4936018931955188224670279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13162717151880501932454077 4936018931955188224670279)
          ·
            refine ⟨7404028397932782337005419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4936018931955188224670279 7404028397932782337005419)
            ·
              refine ⟨11106042596899173505508129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7404028397932782337005419 11106042596899173505508129)
              ·
                refine ⟨8329531947674380129131097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11106042596899173505508129 8329531947674380129131097)
                ·
                  refine ⟨6247148960755785096848323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8329531947674380129131097 6247148960755785096848323)
                  ·
                    refine ⟨9370723441133677645272485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6247148960755785096848323 9370723441133677645272485)
                    ·
                      refine ⟨1757010645212564558488591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9370723441133677645272485 1757010645212564558488591)
                      ·
                        rfl

theorem cell23_3421766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 2, 2, 1, 4].length) (baseStart_3421766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3421766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3421766 prefixEnd_3421766 := by exact prefixLift 3421766
  have htrace : WordTrace (prefixWord ++ tailWord_3421766) baseStart_3421766 baseEnd_3421766 := by
    simpa [prefixWord, tailWord_3421766, baseEnd_3421766] using wordTrace_append hprefix tailTrace_3421766
  have hstable : (prefixWord ++ tailWord_3421766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3421766).length < 2 ^ (prefixWord ++ tailWord_3421766).sum := by decide
  have hdescent : baseEnd_3421766 < baseStart_3421766 := by decide
  rcases family_descends (prefixWord ++ tailWord_3421766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3421792 : List Nat := [2, 1, 1, 3, 2, 1, 1, 1, 6, 3, 2]
def baseStart_3421792 : Nat := 118140960795 + 3421792 * 2 ^ 59
def prefixEnd_3421792 : Nat := 4983230072969 + 3 ^ 40 * 3421792 * 2
def baseEnd_3421792 : Nat := 1757023995709581456763471

theorem tailTrace_3421792 : CollatzResearch.WordTrace tailWord_3421792 prefixEnd_3421792 1757023995709581456763471 := by
  unfold tailWord_3421792
  simp only [CollatzResearch.WordTrace]
  refine ⟨62401503609719727196301815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83202004812959636261735753 62401503609719727196301815)
  ·
    refine ⟨93602255414579590794452723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62401503609719727196301815 93602255414579590794452723)
    ·
      refine ⟨140403383121869386191679085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93602255414579590794452723 140403383121869386191679085)
      ·
        refine ⟨52651268670701019821879657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140403383121869386191679085 52651268670701019821879657)
        ·
          refine ⟨39488451503025764866409743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52651268670701019821879657 39488451503025764866409743)
          ·
            refine ⟨59232677254538647299614615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39488451503025764866409743 59232677254538647299614615)
            ·
              refine ⟨88849015881807970949421923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59232677254538647299614615 88849015881807970949421923)
              ·
                refine ⟨133273523822711956424132885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88849015881807970949421923 133273523822711956424132885)
                ·
                  refine ⟨6247196429189622957381229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 133273523822711956424132885 6247196429189622957381229)
                  ·
                    refine ⟨2342698660946108609017961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6247196429189622957381229 2342698660946108609017961)
                    ·
                      refine ⟨1757023995709581456763471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2342698660946108609017961 1757023995709581456763471)
                      ·
                        rfl

theorem cell23_3421792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 6, 3, 2].length) (baseStart_3421792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3421792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3421792 prefixEnd_3421792 := by exact prefixLift 3421792
  have htrace : WordTrace (prefixWord ++ tailWord_3421792) baseStart_3421792 baseEnd_3421792 := by
    simpa [prefixWord, tailWord_3421792, baseEnd_3421792] using wordTrace_append hprefix tailTrace_3421792
  have hstable : (prefixWord ++ tailWord_3421792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3421792).length < 2 ^ (prefixWord ++ tailWord_3421792).sum := by decide
  have hdescent : baseEnd_3421792 < baseStart_3421792 := by decide
  rcases family_descends (prefixWord ++ tailWord_3421792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3421802 : List Nat := [3, 1, 3, 2, 1, 3, 1, 1, 3, 5]
def baseStart_3421802 : Nat := 118140960795 + 3421802 * 2 ^ 59
def prefixEnd_3421802 : Nat := 4983230072969 + 3 ^ 40 * 3421802 * 2
def baseEnd_3421802 : Nat := 585676376838708805879475

theorem tailTrace_3421802 : CollatzResearch.WordTrace tailWord_3421802 prefixEnd_3421802 585676376838708805879475 := by
  unfold tailWord_3421802
  simp only [CollatzResearch.WordTrace]
  refine ⟨31200842987350806525116915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83202247966268817400311773 31200842987350806525116915)
  ·
    refine ⟨46801264481026209787675373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31200842987350806525116915 46801264481026209787675373)
    ·
      refine ⟨17550474180384828670378265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46801264481026209787675373 17550474180384828670378265)
      ·
        refine ⟨13162855635288621502783699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17550474180384828670378265 13162855635288621502783699)
        ·
          refine ⟨19744283452932932254175549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13162855635288621502783699 19744283452932932254175549)
          ·
            refine ⟨7404106294849849595315831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19744283452932932254175549 7404106294849849595315831)
            ·
              refine ⟨11106159442274774392973747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7404106294849849595315831 11106159442274774392973747)
              ·
                refine ⟨16659239163412161589460621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11106159442274774392973747 16659239163412161589460621)
                ·
                  refine ⟨6247214686279560596047733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16659239163412161589460621 6247214686279560596047733)
                  ·
                    refine ⟨585676376838708805879475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6247214686279560596047733 585676376838708805879475)
                    ·
                      rfl

theorem cell23_3421802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 1, 3, 5].length) (baseStart_3421802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3421802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3421802 prefixEnd_3421802 := by exact prefixLift 3421802
  have htrace : WordTrace (prefixWord ++ tailWord_3421802) baseStart_3421802 baseEnd_3421802 := by
    simpa [prefixWord, tailWord_3421802, baseEnd_3421802] using wordTrace_append hprefix tailTrace_3421802
  have hstable : (prefixWord ++ tailWord_3421802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3421802).length < 2 ^ (prefixWord ++ tailWord_3421802).sum := by decide
  have hdescent : baseEnd_3421802 < baseStart_3421802 := by decide
  rcases family_descends (prefixWord ++ tailWord_3421802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3421835 : List Nat := [1, 1, 1, 1, 4, 1, 3, 2, 3, 2, 4]
def baseStart_3421835 : Nat := 118140960795 + 3421835 * 2 ^ 59
def prefixEnd_3421835 : Nat := 4983230072969 + 3 ^ 40 * 3421835 * 2
def baseEnd_3421835 : Nat := 1757046075377724788525773

theorem tailTrace_3421835 : CollatzResearch.WordTrace tailWord_3421835 prefixEnd_3421835 1757046075377724788525773 := by
  unfold tailWord_3421835
  simp only [CollatzResearch.WordTrace]
  refine ⟨124804575558283672736418959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83203050372189115157612639 124804575558283672736418959)
  ·
    refine ⟨187206863337425509104628439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124804575558283672736418959 187206863337425509104628439)
    ·
      refine ⟨280810295006138263656942659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187206863337425509104628439 280810295006138263656942659)
      ·
        refine ⟨421215442509207395485413989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280810295006138263656942659 421215442509207395485413989)
        ·
          refine ⟨78977895470476386653515123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 421215442509207395485413989 78977895470476386653515123)
          ·
            refine ⟨118466843205714579980272685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78977895470476386653515123 118466843205714579980272685)
            ·
              refine ⟨44425066202142967492602257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118466843205714579980272685 44425066202142967492602257)
              ·
                refine ⟨33318799651607225619451693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44425066202142967492602257 33318799651607225619451693)
                ·
                  refine ⟨12494549869352709607294385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33318799651607225619451693 12494549869352709607294385)
                  ·
                    refine ⟨9370912402014532205470789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12494549869352709607294385 9370912402014532205470789)
                    ·
                      refine ⟨1757046075377724788525773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9370912402014532205470789 1757046075377724788525773)
                      ·
                        rfl

theorem cell23_3421835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 2, 3, 2, 4].length) (baseStart_3421835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3421835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3421835 prefixEnd_3421835 := by exact prefixLift 3421835
  have htrace : WordTrace (prefixWord ++ tailWord_3421835) baseStart_3421835 baseEnd_3421835 := by
    simpa [prefixWord, tailWord_3421835, baseEnd_3421835] using wordTrace_append hprefix tailTrace_3421835
  have hstable : (prefixWord ++ tailWord_3421835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3421835).length < 2 ^ (prefixWord ++ tailWord_3421835).sum := by decide
  have hdescent : baseEnd_3421835 < baseStart_3421835 := by decide
  rcases family_descends (prefixWord ++ tailWord_3421835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3421856 : List Nat := [2, 1, 1, 4, 3, 2, 1, 2, 3, 2, 2]
def baseStart_3421856 : Nat := 118140960795 + 3421856 * 2 ^ 59
def prefixEnd_3421856 : Nat := 4983230072969 + 3 ^ 40 * 3421856 * 2
def baseEnd_3421856 : Nat := 1757056858471469206363177

theorem tailTrace_3421856 : CollatzResearch.WordTrace tailWord_3421856 prefixEnd_3421856 1757056858471469206363177 := by
  unfold tailWord_3421856
  simp only [CollatzResearch.WordTrace]
  refine ⟨62402670745603796661466711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83203560994138395548622281 62402670745603796661466711)
  ·
    refine ⟨93604006118405694992200067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62402670745603796661466711 93604006118405694992200067)
    ·
      refine ⟨140406009177608542488300101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93604006118405694992200067 140406009177608542488300101)
      ·
        refine ⟨26326126720801601716556269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 140406009177608542488300101 26326126720801601716556269)
        ·
          refine ⟨9872297520300600643708601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26326126720801601716556269 9872297520300600643708601)
          ·
            refine ⟨7404223140225450482781451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9872297520300600643708601 7404223140225450482781451)
            ·
              refine ⟨11106334710338175724172177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7404223140225450482781451 11106334710338175724172177)
              ·
                refine ⟨8329751032753631793129133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11106334710338175724172177 8329751032753631793129133)
                ·
                  refine ⟨3123656637282611922423425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8329751032753631793129133 3123656637282611922423425)
                  ·
                    refine ⟨2342742477961958941817569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3123656637282611922423425 2342742477961958941817569)
                    ·
                      refine ⟨1757056858471469206363177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2342742477961958941817569 1757056858471469206363177)
                      ·
                        rfl

theorem cell23_3421856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 2, 3, 2, 2].length) (baseStart_3421856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3421856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3421856 prefixEnd_3421856 := by exact prefixLift 3421856
  have htrace : WordTrace (prefixWord ++ tailWord_3421856) baseStart_3421856 baseEnd_3421856 := by
    simpa [prefixWord, tailWord_3421856, baseEnd_3421856] using wordTrace_append hprefix tailTrace_3421856
  have hstable : (prefixWord ++ tailWord_3421856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3421856).length < 2 ^ (prefixWord ++ tailWord_3421856).sum := by decide
  have hdescent : baseEnd_3421856 < baseStart_3421856 := by decide
  rcases family_descends (prefixWord ++ tailWord_3421856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3421870 : List Nat := [4, 1, 4, 1, 3, 1, 2, 1, 1, 5]
def baseStart_3421870 : Nat := 118140960795 + 3421870 * 2 ^ 59
def prefixEnd_3421870 : Nat := 4983230072969 + 3 ^ 40 * 3421870 * 2
def baseEnd_3421870 : Nat := 585688015733544050529371

theorem tailTrace_3421870 : CollatzResearch.WordTrace tailWord_3421870 prefixEnd_3421870 585688015733544050529371 := by
  unfold tailWord_3421870
  simp only [CollatzResearch.WordTrace]
  refine ⟨15600731514144609214242883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83203901408771249142628709 15600731514144609214242883)
  ·
    refine ⟨23401097271216913821364325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15600731514144609214242883 23401097271216913821364325)
    ·
      refine ⟨4387705738353171341505811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23401097271216913821364325 4387705738353171341505811)
      ·
        refine ⟨6581558607529757012258717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4387705738353171341505811 6581558607529757012258717)
        ·
          refine ⟨2468084477823658879597019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6581558607529757012258717 2468084477823658879597019)
          ·
            refine ⟨3702126716735488319395529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2468084477823658879597019 3702126716735488319395529)
            ·
              refine ⟨2776595037551616239546647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3702126716735488319395529 2776595037551616239546647)
              ·
                refine ⟨4164892556327424359319971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2776595037551616239546647 4164892556327424359319971)
                ·
                  refine ⟨6247338834491136538979957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4164892556327424359319971 6247338834491136538979957)
                  ·
                    refine ⟨585688015733544050529371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6247338834491136538979957 585688015733544050529371)
                    ·
                      rfl

theorem cell23_3421870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_3421870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3421870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3421870 prefixEnd_3421870 := by exact prefixLift 3421870
  have htrace : WordTrace (prefixWord ++ tailWord_3421870) baseStart_3421870 baseEnd_3421870 := by
    simpa [prefixWord, tailWord_3421870, baseEnd_3421870] using wordTrace_append hprefix tailTrace_3421870
  have hstable : (prefixWord ++ tailWord_3421870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3421870).length < 2 ^ (prefixWord ++ tailWord_3421870).sum := by decide
  have hdescent : baseEnd_3421870 < baseStart_3421870 := by decide
  rcases family_descends (prefixWord ++ tailWord_3421870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3421872 : List Nat := [2, 1, 1, 1, 2, 1, 6, 2, 1, 3, 3]
def baseStart_3421872 : Nat := 118140960795 + 3421872 * 2 ^ 59
def prefixEnd_3421872 : Nat := 4983230072969 + 3 ^ 40 * 3421872 * 2
def baseEnd_3421872 : Nat := 1757065074161941143763103

theorem tailTrace_3421872 : CollatzResearch.WordTrace tailWord_3421872 prefixEnd_3421872 1757065074161941143763103 := by
  unfold tailWord_3421872
  simp only [CollatzResearch.WordTrace]
  refine ⟨62402962529574814027757935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83203950039433085370343913 62402962529574814027757935)
  ·
    refine ⟨93604443794362221041636903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62402962529574814027757935 93604443794362221041636903)
    ·
      refine ⟨140406665691543331562455355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93604443794362221041636903 140406665691543331562455355)
      ·
        refine ⟨210609998537314997343683033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140406665691543331562455355 210609998537314997343683033)
        ·
          refine ⟨157957498902986248007762275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210609998537314997343683033 157957498902986248007762275)
          ·
            refine ⟨236936248354479372011643413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157957498902986248007762275 236936248354479372011643413)
            ·
              refine ⟨11106386641616220563045785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 236936248354479372011643413 11106386641616220563045785)
              ·
                refine ⟨8329789981212165422284339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11106386641616220563045785 8329789981212165422284339)
                ·
                  refine ⟨12494684971818248133426509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8329789981212165422284339 12494684971818248133426509)
                  ·
                    refine ⟨4685506864431843050034941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12494684971818248133426509 4685506864431843050034941)
                    ·
                      refine ⟨1757065074161941143763103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4685506864431843050034941 1757065074161941143763103)
                      ·
                        rfl

theorem cell23_3421872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 2, 1, 3, 3].length) (baseStart_3421872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3421872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3421872 prefixEnd_3421872 := by exact prefixLift 3421872
  have htrace : WordTrace (prefixWord ++ tailWord_3421872) baseStart_3421872 baseEnd_3421872 := by
    simpa [prefixWord, tailWord_3421872, baseEnd_3421872] using wordTrace_append hprefix tailTrace_3421872
  have hstable : (prefixWord ++ tailWord_3421872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3421872).length < 2 ^ (prefixWord ++ tailWord_3421872).sum := by decide
  have hdescent : baseEnd_3421872 < baseStart_3421872 := by decide
  rcases family_descends (prefixWord ++ tailWord_3421872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3421906 : List Nat := [3, 2, 2, 2, 2, 3, 1, 1, 1, 3, 3]
def baseStart_3421906 : Nat := 118140960795 + 3421906 * 2 ^ 59
def prefixEnd_3421906 : Nat := 4983230072969 + 3 ^ 40 * 3421906 * 2
def baseEnd_3421906 : Nat := 1757082532504194010737947

theorem tailTrace_3421906 : CollatzResearch.WordTrace tailWord_3421906 prefixEnd_3421906 1757082532504194010737947 := by
  unfold tailWord_3421906
  simp only [CollatzResearch.WordTrace]
  refine ⟨31201791285256612965563393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83204776760684301241502381 31201791285256612965563393)
  ·
    refine ⟨23401343463942459724172545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31201791285256612965563393 23401343463942459724172545)
    ·
      refine ⟨17551007597956844793129409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23401343463942459724172545 17551007597956844793129409)
      ·
        refine ⟨13163255698467633594847057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17551007597956844793129409 13163255698467633594847057)
        ·
          refine ⟨9872441773850725196135293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13163255698467633594847057 9872441773850725196135293)
          ·
            refine ⟨3702165665194021948550735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9872441773850725196135293 3702165665194021948550735)
            ·
              refine ⟨5553248497791032922826103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3702165665194021948550735 5553248497791032922826103)
              ·
                refine ⟨8329872746686549384239155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5553248497791032922826103 8329872746686549384239155)
                ·
                  refine ⟨12494809120029824076358733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8329872746686549384239155 12494809120029824076358733)
                  ·
                    refine ⟨4685553420011184028634525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12494809120029824076358733 4685553420011184028634525)
                    ·
                      refine ⟨1757082532504194010737947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4685553420011184028634525 1757082532504194010737947)
                      ·
                        rfl

theorem cell23_3421906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 1, 1, 1, 3, 3].length) (baseStart_3421906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3421906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3421906 prefixEnd_3421906 := by exact prefixLift 3421906
  have htrace : WordTrace (prefixWord ++ tailWord_3421906) baseStart_3421906 baseEnd_3421906 := by
    simpa [prefixWord, tailWord_3421906, baseEnd_3421906] using wordTrace_append hprefix tailTrace_3421906
  have hstable : (prefixWord ++ tailWord_3421906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3421906).length < 2 ^ (prefixWord ++ tailWord_3421906).sum := by decide
  have hdescent : baseEnd_3421906 < baseStart_3421906 := by decide
  rcases family_descends (prefixWord ++ tailWord_3421906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3421910 : List Nat := [5, 2, 1, 3, 1, 1, 2, 2, 1, 2, 3]
def baseStart_3421910 : Nat := 118140960795 + 3421910 * 2 ^ 59
def prefixEnd_3421910 : Nat := 4983230072969 + 3 ^ 40 * 3421910 * 2
def baseEnd_3421910 : Nat := 1757084586426811995087929

theorem tailTrace_3421910 : CollatzResearch.WordTrace tailWord_3421910 prefixEnd_3421910 1757084586426811995087929 := by
  unfold tailWord_3421910
  simp only [CollatzResearch.WordTrace]
  refine ⟨7800456939563247534087449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 83204874022007973696932789 7800456939563247534087449)
  ·
    refine ⟨5850342704672435650565587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7800456939563247534087449 5850342704672435650565587)
    ·
      refine ⟨8775514057008653475848381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5850342704672435650565587 8775514057008653475848381)
      ·
        refine ⟨3290817771378245053443143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8775514057008653475848381 3290817771378245053443143)
        ·
          refine ⟨4936226657067367580164715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3290817771378245053443143 4936226657067367580164715)
          ·
            refine ⟨7404339985601051370247073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4936226657067367580164715 7404339985601051370247073)
            ·
              refine ⟨5553254989200788527685305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7404339985601051370247073 5553254989200788527685305)
              ·
                refine ⟨4164941241900591395763979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5553254989200788527685305 4164941241900591395763979)
                ·
                  refine ⟨6247411862850887093645969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4164941241900591395763979 6247411862850887093645969)
                  ·
                    refine ⟨4685558897138165320234477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6247411862850887093645969 4685558897138165320234477)
                    ·
                      refine ⟨1757084586426811995087929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4685558897138165320234477 1757084586426811995087929)
                      ·
                        rfl

theorem cell23_3421910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_3421910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3421910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3421910 prefixEnd_3421910 := by exact prefixLift 3421910
  have htrace : WordTrace (prefixWord ++ tailWord_3421910) baseStart_3421910 baseEnd_3421910 := by
    simpa [prefixWord, tailWord_3421910, baseEnd_3421910] using wordTrace_append hprefix tailTrace_3421910
  have hstable : (prefixWord ++ tailWord_3421910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3421910).length < 2 ^ (prefixWord ++ tailWord_3421910).sum := by decide
  have hdescent : baseEnd_3421910 < baseStart_3421910 := by decide
  rcases family_descends (prefixWord ++ tailWord_3421910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3421946 : List Nat := [3, 1, 1, 1, 1, 3, 1, 6, 2, 2, 2]
def baseStart_3421946 : Nat := 118140960795 + 3421946 * 2 ^ 59
def prefixEnd_3421946 : Nat := 4983230072969 + 3 ^ 40 * 3421946 * 2
def baseEnd_3421946 : Nat := 1757103071730373854237763

theorem tailTrace_3421946 : CollatzResearch.WordTrace tailWord_3421946 prefixEnd_3421946 1757103071730373854237763 := by
  unfold tailWord_3421946
  simp only [CollatzResearch.WordTrace]
  refine ⟨31202156015220384673427423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83205749373921025795806461 31202156015220384673427423)
  ·
    refine ⟨46803234022830577010141135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31202156015220384673427423 46803234022830577010141135)
    ·
      refine ⟨70204851034245865515211703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46803234022830577010141135 70204851034245865515211703)
      ·
        refine ⟨105307276551368798272817555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70204851034245865515211703 105307276551368798272817555)
        ·
          refine ⟨157960914827053197409226333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105307276551368798272817555 157960914827053197409226333)
          ·
            refine ⟨59235343060144949028459875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 157960914827053197409226333 59235343060144949028459875)
            ·
              refine ⟨88853014590217423542689813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59235343060144949028459875 88853014590217423542689813)
              ·
                refine ⟨4164985058916441728563585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 88853014590217423542689813 4164985058916441728563585)
                ·
                  refine ⟨3123738794187331296422689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4164985058916441728563585 3123738794187331296422689)
                  ·
                    refine ⟨2342804095640498472317017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3123738794187331296422689 2342804095640498472317017)
                    ·
                      refine ⟨1757103071730373854237763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2342804095640498472317017 1757103071730373854237763)
                      ·
                        rfl

theorem cell23_3421946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 6, 2, 2, 2].length) (baseStart_3421946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3421946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3421946 prefixEnd_3421946 := by exact prefixLift 3421946
  have htrace : WordTrace (prefixWord ++ tailWord_3421946) baseStart_3421946 baseEnd_3421946 := by
    simpa [prefixWord, tailWord_3421946, baseEnd_3421946] using wordTrace_append hprefix tailTrace_3421946
  have hstable : (prefixWord ++ tailWord_3421946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3421946).length < 2 ^ (prefixWord ++ tailWord_3421946).sum := by decide
  have hdescent : baseEnd_3421946 < baseStart_3421946 := by decide
  rcases family_descends (prefixWord ++ tailWord_3421946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3421963 : List Nat := [1, 1, 1, 1, 5, 1, 6, 1, 2, 2, 2]
def baseStart_3421963 : Nat := 118140960795 + 3421963 * 2 ^ 59
def prefixEnd_3421963 : Nat := 4983230072969 + 3 ^ 40 * 3421963 * 2
def baseEnd_3421963 : Nat := 1757111800901500287725185

theorem tailTrace_3421963 : CollatzResearch.WordTrace tailWord_3421963 prefixEnd_3421963 1757111800901500287725185 := by
  unfold tailWord_3421963
  simp only [CollatzResearch.WordTrace]
  refine ⟨124809244101819950597078543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83206162734546633731385695 124809244101819950597078543)
  ·
    refine ⟨187213866152729925895617815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124809244101819950597078543 187213866152729925895617815)
    ·
      refine ⟨280820799229094888843426723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187213866152729925895617815 280820799229094888843426723)
      ·
        refine ⟨421231198843642333265140085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280820799229094888843426723 421231198843642333265140085)
        ·
          refine ⟨39490424891591468743606883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 421231198843642333265140085 39490424891591468743606883)
          ·
            refine ⟨59235637337387203115410325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39490424891591468743606883 59235637337387203115410325)
            ·
              refine ⟨2776670500190025146034859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 59235637337387203115410325 2776670500190025146034859)
              ·
                refine ⟨4165005750285037719052289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2776670500190025146034859 4165005750285037719052289)
                ·
                  refine ⟨3123754312713778289289217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4165005750285037719052289 3123754312713778289289217)
                  ·
                    refine ⟨2342815734535333716966913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3123754312713778289289217 2342815734535333716966913)
                    ·
                      refine ⟨1757111800901500287725185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2342815734535333716966913 1757111800901500287725185)
                      ·
                        rfl

theorem cell23_3421963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 6, 1, 2, 2, 2].length) (baseStart_3421963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3421963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3421963 prefixEnd_3421963 := by exact prefixLift 3421963
  have htrace : WordTrace (prefixWord ++ tailWord_3421963) baseStart_3421963 baseEnd_3421963 := by
    simpa [prefixWord, tailWord_3421963, baseEnd_3421963] using wordTrace_append hprefix tailTrace_3421963
  have hstable : (prefixWord ++ tailWord_3421963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3421963).length < 2 ^ (prefixWord ++ tailWord_3421963).sum := by decide
  have hdescent : baseEnd_3421963 < baseStart_3421963 := by decide
  rcases family_descends (prefixWord ++ tailWord_3421963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3422003 : List Nat := [1, 1, 1, 2, 7, 2, 2, 2, 5]
def baseStart_3422003 : Nat := 118140960795 + 3422003 * 2 ^ 59
def prefixEnd_3422003 : Nat := 4983230072969 + 3 ^ 40 * 3422003 * 2
def baseEnd_3422003 : Nat := 195236926680853347913889

theorem tailTrace_3422003 : CollatzResearch.WordTrace tailWord_3422003 prefixEnd_3422003 195236926680853347913889 := by
  unfold tailWord_3422003
  simp only [CollatzResearch.WordTrace]
  refine ⟨124810703021675037428534663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83207135347783358285689775 124810703021675037428534663)
  ·
    refine ⟨187216054532512556142801995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124810703021675037428534663 187216054532512556142801995)
    ·
      refine ⟨280824081798768834214202993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187216054532512556142801995 280824081798768834214202993)
      ·
        refine ⟨210618061349076625660652245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 280824081798768834214202993 210618061349076625660652245)
        ·
          refine ⟨4936360812868983413921537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 210618061349076625660652245 4936360812868983413921537)
          ·
            refine ⟨3702270609651737560441153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4936360812868983413921537 3702270609651737560441153)
            ·
              refine ⟨2776702957238803170330865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3702270609651737560441153 2776702957238803170330865)
              ·
                refine ⟨2082527217929102377748149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2776702957238803170330865 2082527217929102377748149)
                ·
                  refine ⟨195236926680853347913889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2082527217929102377748149 195236926680853347913889)
                  ·
                    rfl

theorem cell23_3422003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 2, 2, 5].length) (baseStart_3422003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3422003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3422003 prefixEnd_3422003 := by exact prefixLift 3422003
  have htrace : WordTrace (prefixWord ++ tailWord_3422003) baseStart_3422003 baseEnd_3422003 := by
    simpa [prefixWord, tailWord_3422003, baseEnd_3422003] using wordTrace_append hprefix tailTrace_3422003
  have hstable : (prefixWord ++ tailWord_3422003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3422003).length < 2 ^ (prefixWord ++ tailWord_3422003).sum := by decide
  have hdescent : baseEnd_3422003 < baseStart_3422003 := by decide
  rcases family_descends (prefixWord ++ tailWord_3422003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3422019 : List Nat := [1, 1, 1, 3, 1, 5, 1, 1, 1, 6, 2]
def baseStart_3422019 : Nat := 118140960795 + 3422019 * 2 ^ 59
def prefixEnd_3422019 : Nat := 4983230072969 + 3 ^ 40 * 3422019 * 2
def baseEnd_3422019 : Nat := 1757140555818152068624927

theorem tailTrace_3422019 : CollatzResearch.WordTrace tailWord_3422019 prefixEnd_3422019 1757140555818152068624927 := by
  unfold tailWord_3422019
  simp only [CollatzResearch.WordTrace]
  refine ⟨124811286589617072161117111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83207524393078048107411407 124811286589617072161117111)
  ·
    refine ⟨187216929884425608241675667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124811286589617072161117111 187216929884425608241675667)
    ·
      refine ⟨280825394826638412362513501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187216929884425608241675667 280825394826638412362513501)
      ·
        refine ⟨105309523059989404635942563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 280825394826638412362513501 105309523059989404635942563)
        ·
          refine ⟨157964284589984106953913845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105309523059989404635942563 157964284589984106953913845)
          ·
            refine ⟨14809151680311010026929423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 157964284589984106953913845 14809151680311010026929423)
            ·
              refine ⟨22213727520466515040394135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14809151680311010026929423 22213727520466515040394135)
              ·
                refine ⟨33320591280699772560591203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22213727520466515040394135 33320591280699772560591203)
                ·
                  refine ⟨49980886921049658840886805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33320591280699772560591203 49980886921049658840886805)
                  ·
                    refine ⟨2342854074424202758166569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 49980886921049658840886805 2342854074424202758166569)
                    ·
                      refine ⟨1757140555818152068624927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2342854074424202758166569 1757140555818152068624927)
                      ·
                        rfl

theorem cell23_3422019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 1, 1, 6, 2].length) (baseStart_3422019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3422019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3422019 prefixEnd_3422019 := by exact prefixLift 3422019
  have htrace : WordTrace (prefixWord ++ tailWord_3422019) baseStart_3422019 baseEnd_3422019 := by
    simpa [prefixWord, tailWord_3422019, baseEnd_3422019] using wordTrace_append hprefix tailTrace_3422019
  have hstable : (prefixWord ++ tailWord_3422019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3422019).length < 2 ^ (prefixWord ++ tailWord_3422019).sum := by decide
  have hdescent : baseEnd_3422019 < baseStart_3422019 := by decide
  rcases family_descends (prefixWord ++ tailWord_3422019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3422036 : List Nat := [2, 4, 1, 1, 3, 1, 3, 1, 2, 1, 4]
def baseStart_3422036 : Nat := 118140960795 + 3422036 * 2 ^ 59
def prefixEnd_3422036 : Nat := 4983230072969 + 3 ^ 40 * 3422036 * 2
def baseEnd_3422036 : Nat := 1757149284989278502112349

theorem tailTrace_3422036 : CollatzResearch.WordTrace tailWord_3422036 prefixEnd_3422036 1757149284989278502112349 := by
  unfold tailWord_3422036
  simp only [CollatzResearch.WordTrace]
  refine ⟨62405953315277742032242981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83207937753703656042990641 62405953315277742032242981)
  ·
    refine ⟨11701116246614576631045559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62405953315277742032242981 11701116246614576631045559)
    ·
      refine ⟨17551674369921864946568339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11701116246614576631045559 17551674369921864946568339)
      ·
        refine ⟨26327511554882797419852509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17551674369921864946568339 26327511554882797419852509)
        ·
          refine ⟨9872816833081049032444691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26327511554882797419852509 9872816833081049032444691)
          ·
            refine ⟨14809225249621573548667037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9872816833081049032444691 14809225249621573548667037)
            ·
              refine ⟨5553459468608090080750139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14809225249621573548667037 5553459468608090080750139)
              ·
                refine ⟨8330189202912135121125209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5553459468608090080750139 8330189202912135121125209)
                ·
                  refine ⟨6247641902184101340843907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8330189202912135121125209 6247641902184101340843907)
                  ·
                    refine ⟨9371462853276152011265861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6247641902184101340843907 9371462853276152011265861)
                    ·
                      refine ⟨1757149284989278502112349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9371462853276152011265861 1757149284989278502112349)
                      ·
                        rfl

theorem cell23_3422036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 3, 1, 2, 1, 4].length) (baseStart_3422036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3422036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3422036 prefixEnd_3422036 := by exact prefixLift 3422036
  have htrace : WordTrace (prefixWord ++ tailWord_3422036) baseStart_3422036 baseEnd_3422036 := by
    simpa [prefixWord, tailWord_3422036, baseEnd_3422036] using wordTrace_append hprefix tailTrace_3422036
  have hstable : (prefixWord ++ tailWord_3422036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3422036).length < 2 ^ (prefixWord ++ tailWord_3422036).sum := by decide
  have hdescent : baseEnd_3422036 < baseStart_3422036 := by decide
  rcases family_descends (prefixWord ++ tailWord_3422036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3422042 : List Nat := [3, 1, 1, 2, 1, 3, 2, 2, 8]
def baseStart_3422042 : Nat := 118140960795 + 3422042 * 2 ^ 59
def prefixEnd_3422042 : Nat := 4983230072969 + 3 ^ 40 * 3422042 * 2
def baseEnd_3422042 : Nat := 195239151763689497626369

theorem tailTrace_3422042 : CollatzResearch.WordTrace tailWord_3422042 prefixEnd_3422042 195239151763689497626369 := by
  unfold tailWord_3422042
  simp only [CollatzResearch.WordTrace]
  refine ⟨31203031367133436772301095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83208083645689164726136253 31203031367133436772301095)
  ·
    refine ⟨46804547050700155158451643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31203031367133436772301095 46804547050700155158451643)
    ·
      refine ⟨70206820576050232737677465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46804547050700155158451643 70206820576050232737677465)
      ·
        refine ⟨52655115432037674553258099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70206820576050232737677465 52655115432037674553258099)
        ·
          refine ⟨78982673148056511829887149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52655115432037674553258099 78982673148056511829887149)
          ·
            refine ⟨29618502430521191936207681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78982673148056511829887149 29618502430521191936207681)
            ·
              refine ⟨22213876822890893952155761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29618502430521191936207681 22213876822890893952155761)
              ·
                refine ⟨16660407617168170464116821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22213876822890893952155761 16660407617168170464116821)
                ·
                  refine ⟨195239151763689497626369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16660407617168170464116821 195239151763689497626369)
                  ·
                    rfl

theorem cell23_3422042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 2, 8].length) (baseStart_3422042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3422042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3422042 prefixEnd_3422042 := by exact prefixLift 3422042
  have htrace : WordTrace (prefixWord ++ tailWord_3422042) baseStart_3422042 baseEnd_3422042 := by
    simpa [prefixWord, tailWord_3422042, baseEnd_3422042] using wordTrace_append hprefix tailTrace_3422042
  have hstable : (prefixWord ++ tailWord_3422042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3422042).length < 2 ^ (prefixWord ++ tailWord_3422042).sum := by decide
  have hdescent : baseEnd_3422042 < baseStart_3422042 := by decide
  rcases family_descends (prefixWord ++ tailWord_3422042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3422106 : List Nat := [3, 1, 1, 4, 2, 1, 2, 3, 1, 5]
def baseStart_3422106 : Nat := 118140960795 + 3422106 * 2 ^ 59
def prefixEnd_3422106 : Nat := 4983230072969 + 3 ^ 40 * 3422106 * 2
def baseEnd_3422106 : Nat := 585728409545031076079009

theorem tailTrace_3422106 : CollatzResearch.WordTrace tailWord_3422106 prefixEnd_3422106 585728409545031076079009 := by
  unfold tailWord_3422106
  simp only [CollatzResearch.WordTrace]
  refine ⟨31203614935075471504883543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83209639826867924013022781 31203614935075471504883543)
  ·
    refine ⟨46805422402613207257325315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31203614935075471504883543 46805422402613207257325315)
    ·
      refine ⟨70208133603919810885987973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46805422402613207257325315 70208133603919810885987973)
      ·
        refine ⟨13164025050734964541122745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70208133603919810885987973 13164025050734964541122745)
        ·
          refine ⟨9873018788051223405842059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13164025050734964541122745 9873018788051223405842059)
          ·
            refine ⟨14809528182076835108763089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9873018788051223405842059 14809528182076835108763089)
            ·
              refine ⟨11107146136557626331572317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14809528182076835108763089 11107146136557626331572317)
              ·
                refine ⟨4165179801209109874339619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11107146136557626331572317 4165179801209109874339619)
                ·
                  refine ⟨6247769701813664811509429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4165179801209109874339619 6247769701813664811509429)
                  ·
                    refine ⟨585728409545031076079009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6247769701813664811509429 585728409545031076079009)
                    ·
                      rfl

theorem cell23_3422106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 3, 1, 5].length) (baseStart_3422106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3422106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3422106 prefixEnd_3422106 := by exact prefixLift 3422106
  have htrace : WordTrace (prefixWord ++ tailWord_3422106) baseStart_3422106 baseEnd_3422106 := by
    simpa [prefixWord, tailWord_3422106, baseEnd_3422106] using wordTrace_append hprefix tailTrace_3422106
  have hstable : (prefixWord ++ tailWord_3422106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3422106).length < 2 ^ (prefixWord ++ tailWord_3422106).sum := by decide
  have hdescent : baseEnd_3422106 < baseStart_3422106 := by decide
  rcases family_descends (prefixWord ++ tailWord_3422106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3422136 : List Nat := [2, 1, 2, 1, 2, 3, 3, 3, 2, 4]
def baseStart_3422136 : Nat := 118140960795 + 3422136 * 2 ^ 59
def prefixEnd_3422136 : Nat := 4983230072969 + 3 ^ 40 * 3422136 * 2
def baseEnd_3422136 : Nat := 585733544351576036953963

theorem tailTrace_3422136 : CollatzResearch.WordTrace tailWord_3422136 prefixEnd_3422136 585733544351576036953963 := by
  unfold tailWord_3422136
  simp only [CollatzResearch.WordTrace]
  refine ⟨62407776965096600571563131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83210369286795467428750841 62407776965096600571563131)
  ·
    refine ⟨93611665447644900857344697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62407776965096600571563131 93611665447644900857344697)
    ·
      refine ⟨70208749085733675643008523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93611665447644900857344697 70208749085733675643008523)
      ·
        refine ⟨105313123628600513464512785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70208749085733675643008523 105313123628600513464512785)
        ·
          refine ⟨78984842721450385098384589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105313123628600513464512785 78984842721450385098384589)
          ·
            refine ⟨29619316020543894411894221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78984842721450385098384589 29619316020543894411894221)
            ·
              refine ⟨11107243507703960404460333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29619316020543894411894221 11107243507703960404460333)
              ·
                refine ⟨4165216315388985151672625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11107243507703960404460333 4165216315388985151672625)
                ·
                  refine ⟨3123912236541738863754469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4165216315388985151672625 3123912236541738863754469)
                  ·
                    refine ⟨585733544351576036953963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3123912236541738863754469 585733544351576036953963)
                    ·
                      rfl

theorem cell23_3422136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 3, 2, 4].length) (baseStart_3422136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3422136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3422136 prefixEnd_3422136 := by exact prefixLift 3422136
  have htrace : WordTrace (prefixWord ++ tailWord_3422136) baseStart_3422136 baseEnd_3422136 := by
    simpa [prefixWord, tailWord_3422136, baseEnd_3422136] using wordTrace_append hprefix tailTrace_3422136
  have hstable : (prefixWord ++ tailWord_3422136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3422136).length < 2 ^ (prefixWord ++ tailWord_3422136).sum := by decide
  have hdescent : baseEnd_3422136 < baseStart_3422136 := by decide
  rcases family_descends (prefixWord ++ tailWord_3422136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3422140 : List Nat := [2, 2, 2, 5, 1, 2, 1, 2, 1, 5]
def baseStart_3422140 : Nat := 118140960795 + 3422140 * 2 ^ 59
def prefixEnd_3422140 : Nat := 4983230072969 + 3 ^ 40 * 3422140 * 2
def baseEnd_3422140 : Nat := 585734228992448698403957

theorem tailTrace_3422140 : CollatzResearch.WordTrace tailWord_3422140 prefixEnd_3422140 585734228992448698403957 := by
  unfold tailWord_3422140
  simp only [CollatzResearch.WordTrace]
  refine ⟨62407849911089354913135937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83210466548119139884181249 62407849911089354913135937)
  ·
    refine ⟨46805887433317016184851953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62407849911089354913135937 46805887433317016184851953)
    ·
      refine ⟨35104415574987762138638965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46805887433317016184851953 35104415574987762138638965)
      ·
        refine ⟨3291038960155102700497403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35104415574987762138638965 3291038960155102700497403)
        ·
          refine ⟨4936558440232654050746105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3291038960155102700497403 4936558440232654050746105)
          ·
            refine ⟨3702418830174490538059579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4936558440232654050746105 3702418830174490538059579)
            ·
              refine ⟨5553628245261735807089369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3702418830174490538059579 5553628245261735807089369)
              ·
                refine ⟨4165221183946301855317027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5553628245261735807089369 4165221183946301855317027)
                ·
                  refine ⟨6247831775919452782975541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4165221183946301855317027 6247831775919452782975541)
                  ·
                    refine ⟨585734228992448698403957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6247831775919452782975541 585734228992448698403957)
                    ·
                      rfl

theorem cell23_3422140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 1, 2, 1, 5].length) (baseStart_3422140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3422140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3422140 prefixEnd_3422140 := by exact prefixLift 3422140
  have htrace : WordTrace (prefixWord ++ tailWord_3422140) baseStart_3422140 baseEnd_3422140 := by
    simpa [prefixWord, tailWord_3422140, baseEnd_3422140] using wordTrace_append hprefix tailTrace_3422140
  have hstable : (prefixWord ++ tailWord_3422140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3422140).length < 2 ^ (prefixWord ++ tailWord_3422140).sum := by decide
  have hdescent : baseEnd_3422140 < baseStart_3422140 := by decide
  rcases family_descends (prefixWord ++ tailWord_3422140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3422156 : List Nat := [2, 2, 1, 4, 1, 3, 1, 2, 1, 2, 4]
def baseStart_3422156 : Nat := 118140960795 + 3422156 * 2 ^ 59
def prefixEnd_3422156 : Nat := 4983230072969 + 3 ^ 40 * 3422156 * 2
def baseEnd_3422156 : Nat := 1757210902667818032611797

theorem tailTrace_3422156 : CollatzResearch.WordTrace tailWord_3422156 prefixEnd_3422156 1757210902667818032611797 := by
  unfold tailWord_3422156
  simp only [CollatzResearch.WordTrace]
  refine ⟨62408141695060372279427161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83210855593413829705902881 62408141695060372279427161)
  ·
    refine ⟨46806106271295279209570371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62408141695060372279427161 46806106271295279209570371)
    ·
      refine ⟨70209159406942918814355557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46806106271295279209570371 70209159406942918814355557)
      ·
        refine ⟨13164217388801797277691667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70209159406942918814355557 13164217388801797277691667)
        ·
          refine ⟨19746326083202695916537501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13164217388801797277691667 19746326083202695916537501)
          ·
            refine ⟨7404872281201010968701563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19746326083202695916537501 7404872281201010968701563)
            ·
              refine ⟨11107308421801516453052345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7404872281201010968701563 11107308421801516453052345)
              ·
                refine ⟨8330481316351137339789259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11107308421801516453052345 8330481316351137339789259)
                ·
                  refine ⟨12495721974526706009683889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8330481316351137339789259 12495721974526706009683889)
                  ·
                    refine ⟨9371791480895029507262917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12495721974526706009683889 9371791480895029507262917)
                    ·
                      refine ⟨1757210902667818032611797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9371791480895029507262917 1757210902667818032611797)
                      ·
                        rfl

theorem cell23_3422156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_3422156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3422156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3422156 prefixEnd_3422156 := by exact prefixLift 3422156
  have htrace : WordTrace (prefixWord ++ tailWord_3422156) baseStart_3422156 baseEnd_3422156 := by
    simpa [prefixWord, tailWord_3422156, baseEnd_3422156] using wordTrace_append hprefix tailTrace_3422156
  have hstable : (prefixWord ++ tailWord_3422156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3422156).length < 2 ^ (prefixWord ++ tailWord_3422156).sum := by decide
  have hdescent : baseEnd_3422156 < baseStart_3422156 := by decide
  rcases family_descends (prefixWord ++ tailWord_3422156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3422166 : List Nat := [5, 2, 1, 1, 3, 11]
def baseStart_3422166 : Nat := 118140960795 + 3422166 * 2 ^ 59
def prefixEnd_3422166 : Nat := 4983230072969 + 3 ^ 40 * 3422166 * 2
def baseEnd_3422166 : Nat := 7231341718001493800357

theorem tailTrace_3422166 : CollatzResearch.WordTrace tailWord_3422166 prefixEnd_3422166 7231341718001493800357 := by
  unfold tailWord_3422166
  simp only [CollatzResearch.WordTrace]
  refine ⟨7801040507505282266669897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 83211098746723010844478901 7801040507505282266669897)
  ·
    refine ⟨5850780380628961700002423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7801040507505282266669897 5850780380628961700002423)
    ·
      refine ⟨8776170570943442550003635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5850780380628961700002423 8776170570943442550003635)
      ·
        refine ⟨13164255856415163825005453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8776170570943442550003635 13164255856415163825005453)
        ·
          refine ⟨4936595946155686434377045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13164255856415163825005453 4936595946155686434377045)
          ·
            refine ⟨7231341718001493800357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 4936595946155686434377045 7231341718001493800357)
            ·
              rfl

theorem cell23_3422166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 11].length) (baseStart_3422166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3422166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3422166 prefixEnd_3422166 := by exact prefixLift 3422166
  have htrace : WordTrace (prefixWord ++ tailWord_3422166) baseStart_3422166 baseEnd_3422166 := by
    simpa [prefixWord, tailWord_3422166, baseEnd_3422166] using wordTrace_append hprefix tailTrace_3422166
  have hstable : (prefixWord ++ tailWord_3422166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3422166).length < 2 ^ (prefixWord ++ tailWord_3422166).sum := by decide
  have hdescent : baseEnd_3422166 < baseStart_3422166 := by decide
  rcases family_descends (prefixWord ++ tailWord_3422166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3422176 : List Nat := [2, 1, 1, 3, 1, 1, 1, 5, 4, 1, 3]
def baseStart_3422176 : Nat := 118140960795 + 3422176 * 2 ^ 59
def prefixEnd_3422176 : Nat := 4983230072969 + 3 ^ 40 * 3422176 * 2
def baseEnd_3422176 : Nat := 1757221172280907954361705

theorem tailTrace_3422176 : CollatzResearch.WordTrace tailWord_3422176 prefixEnd_3422176 1757221172280907954361705 := by
  unfold tailWord_3422176
  simp only [CollatzResearch.WordTrace]
  refine ⟨62408506425024143987291191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83211341900032191983054921 62408506425024143987291191)
  ·
    refine ⟨93612759637536215980936787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62408506425024143987291191 93612759637536215980936787)
    ·
      refine ⟨140419139456304323971405181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93612759637536215980936787 140419139456304323971405181)
      ·
        refine ⟨52657177296114121489276943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140419139456304323971405181 52657177296114121489276943)
        ·
          refine ⟨78985765944171182233915415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52657177296114121489276943 78985765944171182233915415)
          ·
            refine ⟨118478648916256773350873123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78985765944171182233915415 118478648916256773350873123)
            ·
              refine ⟨177717973374385160026309685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118478648916256773350873123 177717973374385160026309685)
              ·
                refine ⟨16661060003848608752466533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 177717973374385160026309685 16661060003848608752466533)
                ·
                  refine ⟨3123948750721614141087475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16661060003848608752466533 3123948750721614141087475)
                  ·
                    refine ⟨4685923126082421211631213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3123948750721614141087475 4685923126082421211631213)
                    ·
                      refine ⟨1757221172280907954361705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4685923126082421211631213 1757221172280907954361705)
                      ·
                        rfl

theorem cell23_3422176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 5, 4, 1, 3].length) (baseStart_3422176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3422176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3422176 prefixEnd_3422176 := by exact prefixLift 3422176
  have htrace : WordTrace (prefixWord ++ tailWord_3422176) baseStart_3422176 baseEnd_3422176 := by
    simpa [prefixWord, tailWord_3422176, baseEnd_3422176] using wordTrace_append hprefix tailTrace_3422176
  have hstable : (prefixWord ++ tailWord_3422176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3422176).length < 2 ^ (prefixWord ++ tailWord_3422176).sum := by decide
  have hdescent : baseEnd_3422176 < baseStart_3422176 := by decide
  rcases family_descends (prefixWord ++ tailWord_3422176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3422177 : List Nat := [1, 2, 3, 1, 2, 1, 6, 2, 1, 2, 2]
def baseStart_3422177 : Nat := 118140960795 + 3422177 * 2 ^ 59
def prefixEnd_3422177 : Nat := 4983230072969 + 3 ^ 40 * 3422177 * 2
def baseEnd_3422177 : Nat := 1757221685761562450449201

theorem tailTrace_3422177 : CollatzResearch.WordTrace tailWord_3422177 prefixEnd_3422177 1757221685761562450449201 := by
  unfold tailWord_3422177
  simp only [CollatzResearch.WordTrace]
  refine ⟨124817049323044665145368785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83211366215363110096912523 124817049323044665145368785)
  ·
    refine ⟨93612786992283498859026589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124817049323044665145368785 93612786992283498859026589)
    ·
      refine ⟨35104795122106312072134971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93612786992283498859026589 35104795122106312072134971)
      ·
        refine ⟨52657192683159468108202457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35104795122106312072134971 52657192683159468108202457)
        ·
          refine ⟨39492894512369601081151843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52657192683159468108202457 39492894512369601081151843)
          ·
            refine ⟨59239341768554401621727765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39492894512369601081151843 59239341768554401621727765)
            ·
              refine ⟨2776844145400987576018489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 59239341768554401621727765 2776844145400987576018489)
              ·
                refine ⟨2082633109050740682013867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2776844145400987576018489 2082633109050740682013867)
                ·
                  refine ⟨3123949663576111023020801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2082633109050740682013867 3123949663576111023020801)
                  ·
                    refine ⟨2342962247682083267265601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3123949663576111023020801 2342962247682083267265601)
                    ·
                      refine ⟨1757221685761562450449201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2342962247682083267265601 1757221685761562450449201)
                      ·
                        rfl

theorem cell23_3422177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 6, 2, 1, 2, 2].length) (baseStart_3422177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3422177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3422177 prefixEnd_3422177 := by exact prefixLift 3422177
  have htrace : WordTrace (prefixWord ++ tailWord_3422177) baseStart_3422177 baseEnd_3422177 := by
    simpa [prefixWord, tailWord_3422177, baseEnd_3422177] using wordTrace_append hprefix tailTrace_3422177
  have hstable : (prefixWord ++ tailWord_3422177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3422177).length < 2 ^ (prefixWord ++ tailWord_3422177).sum := by decide
  have hdescent : baseEnd_3422177 < baseStart_3422177 := by decide
  rcases family_descends (prefixWord ++ tailWord_3422177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3422179 : List Nat := [1, 1, 1, 6, 1, 2, 1, 1, 2, 7]
def baseStart_3422179 : Nat := 118140960795 + 3422179 * 2 ^ 59
def prefixEnd_3422179 : Nat := 4983230072969 + 3 ^ 40 * 3422179 * 2
def baseEnd_3422179 : Nat := 585740904240957147541397

theorem tailTrace_3422179 : CollatzResearch.WordTrace tailWord_3422179 prefixEnd_3422179 585740904240957147541397 := by
  unfold tailWord_3422179
  simp only [CollatzResearch.WordTrace]
  refine ⟨124817122269037419486941591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83211414846024946324627727 124817122269037419486941591)
  ·
    refine ⟨187225683403556129230412387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124817122269037419486941591 187225683403556129230412387)
    ·
      refine ⟨280838525105334193845618581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187225683403556129230412387 280838525105334193845618581)
      ·
        refine ⟨13164305864312540336513371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 280838525105334193845618581 13164305864312540336513371)
        ·
          refine ⟨19746458796468810504770057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13164305864312540336513371 19746458796468810504770057)
          ·
            refine ⟨14809844097351607878577543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19746458796468810504770057 14809844097351607878577543)
            ·
              refine ⟨22214766146027411817866315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14809844097351607878577543 22214766146027411817866315)
              ·
                refine ⟨33322149219041117726799473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22214766146027411817866315 33322149219041117726799473)
                ·
                  refine ⟨24991611914280838295099605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33322149219041117726799473 24991611914280838295099605)
                  ·
                    refine ⟨585740904240957147541397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24991611914280838295099605 585740904240957147541397)
                    ·
                      rfl

theorem cell23_3422179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 1, 2, 7].length) (baseStart_3422179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3422179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3422179 prefixEnd_3422179 := by exact prefixLift 3422179
  have htrace : WordTrace (prefixWord ++ tailWord_3422179) baseStart_3422179 baseEnd_3422179 := by
    simpa [prefixWord, tailWord_3422179, baseEnd_3422179] using wordTrace_append hprefix tailTrace_3422179
  have hstable : (prefixWord ++ tailWord_3422179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3422179).length < 2 ^ (prefixWord ++ tailWord_3422179).sum := by decide
  have hdescent : baseEnd_3422179 < baseStart_3422179 := by decide
  rcases family_descends (prefixWord ++ tailWord_3422179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3422183 : List Nat := [1, 1, 5, 2, 4, 1, 1, 8]
def baseStart_3422183 : Nat := 118140960795 + 3422183 * 2 ^ 59
def prefixEnd_3422183 : Nat := 4983230072969 + 3 ^ 40 * 3422183 * 2
def baseEnd_3422183 : Nat := 65082398764647756554599

theorem tailTrace_3422183 : CollatzResearch.WordTrace tailWord_3422183 prefixEnd_3422183 65082398764647756554599 := by
  unfold tailWord_3422183
  simp only [CollatzResearch.WordTrace]
  refine ⟨124817268161022928170087203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83211512107348618780058135 124817268161022928170087203)
  ·
    refine ⟨187225902241534392255130805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124817268161022928170087203 187225902241534392255130805)
    ·
      refine ⟨17552428335143849273918513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 187225902241534392255130805 17552428335143849273918513)
      ·
        refine ⟨13164321251357886955438885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17552428335143849273918513 13164321251357886955438885)
        ·
          refine ⟨2468310234629603804144791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13164321251357886955438885 2468310234629603804144791)
          ·
            refine ⟨3702465351944405706217187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2468310234629603804144791 3702465351944405706217187)
            ·
              refine ⟨5553698027916608559325781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3702465351944405706217187 5553698027916608559325781)
              ·
                refine ⟨65082398764647756554599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5553698027916608559325781 65082398764647756554599)
                ·
                  rfl

theorem cell23_3422183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 1, 8].length) (baseStart_3422183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3422183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3422183 prefixEnd_3422183 := by exact prefixLift 3422183
  have htrace : WordTrace (prefixWord ++ tailWord_3422183) baseStart_3422183 baseEnd_3422183 := by
    simpa [prefixWord, tailWord_3422183, baseEnd_3422183] using wordTrace_append hprefix tailTrace_3422183
  have hstable : (prefixWord ++ tailWord_3422183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3422183).length < 2 ^ (prefixWord ++ tailWord_3422183).sum := by decide
  have hdescent : baseEnd_3422183 < baseStart_3422183 := by decide
  rcases family_descends (prefixWord ++ tailWord_3422183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3422193 : List Nat := [1, 2, 2, 2, 5, 1, 2, 1, 1, 3, 3]
def baseStart_3422193 : Nat := 118140960795 + 3422193 * 2 ^ 59
def prefixEnd_3422193 : Nat := 4983230072969 + 3 ^ 40 * 3422193 * 2
def baseEnd_3422193 : Nat := 1757229901452034387849127

theorem tailTrace_3422193 : CollatzResearch.WordTrace tailWord_3422193 prefixEnd_3422193 1757229901452034387849127 := by
  unfold tailWord_3422193
  simp only [CollatzResearch.WordTrace]
  refine ⟨124817632890986699877951233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83211755260657799918634155 124817632890986699877951233)
  ·
    refine ⟨93613224668240024908463425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124817632890986699877951233 93613224668240024908463425)
    ·
      refine ⟨70209918501180018681347569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93613224668240024908463425 70209918501180018681347569)
      ·
        refine ⟨52657438875885014011010677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70209918501180018681347569 52657438875885014011010677)
        ·
          refine ⟨4936634894614220063532251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52657438875885014011010677 4936634894614220063532251)
          ·
            refine ⟨7404952341921330095298377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4936634894614220063532251 7404952341921330095298377)
            ·
              refine ⟨5553714256440997571473783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7404952341921330095298377 5553714256440997571473783)
              ·
                refine ⟨8330571384661496357210675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5553714256440997571473783 8330571384661496357210675)
                ·
                  refine ⟨12495857076992244535816013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8330571384661496357210675 12495857076992244535816013)
                  ·
                    refine ⟨4685946403872091700931005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12495857076992244535816013 4685946403872091700931005)
                    ·
                      refine ⟨1757229901452034387849127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4685946403872091700931005 1757229901452034387849127)
                      ·
                        rfl

theorem cell23_3422193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 2, 1, 1, 3, 3].length) (baseStart_3422193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3422193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3422193 prefixEnd_3422193 := by exact prefixLift 3422193
  have htrace : WordTrace (prefixWord ++ tailWord_3422193) baseStart_3422193 baseEnd_3422193 := by
    simpa [prefixWord, tailWord_3422193, baseEnd_3422193] using wordTrace_append hprefix tailTrace_3422193
  have hstable : (prefixWord ++ tailWord_3422193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3422193).length < 2 ^ (prefixWord ++ tailWord_3422193).sum := by decide
  have hdescent : baseEnd_3422193 < baseStart_3422193 := by decide
  rcases family_descends (prefixWord ++ tailWord_3422193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3422209 : List Nat := [1, 2, 4, 1, 2, 1, 1, 2, 1, 8]
def baseStart_3422209 : Nat := 118140960795 + 3422209 * 2 ^ 59
def prefixEnd_3422209 : Nat := 4983230072969 + 3 ^ 40 * 3422209 * 2
def baseEnd_3422209 : Nat := 585746039047502108416351

theorem tailTrace_3422209 : CollatzResearch.WordTrace tailWord_3422209 prefixEnd_3422209 585746039047502108416351 := by
  unfold tailWord_3422209
  simp only [CollatzResearch.WordTrace]
  refine ⟨124818216458928734610533681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83212144305952489740355787 124818216458928734610533681)
  ·
    refine ⟨93613662344196550957900261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124818216458928734610533681 93613662344196550957900261)
    ·
      refine ⟨17552561689536853304606299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93613662344196550957900261 17552561689536853304606299)
      ·
        refine ⟨26328842534305279956909449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17552561689536853304606299 26328842534305279956909449)
        ·
          refine ⟨19746631900728959967682087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26328842534305279956909449 19746631900728959967682087)
          ·
            refine ⟨29619947851093439951523131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19746631900728959967682087 29619947851093439951523131)
            ·
              refine ⟨44429921776640159927284697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29619947851093439951523131 44429921776640159927284697)
              ·
                refine ⟨33322441332480119945463523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44429921776640159927284697 33322441332480119945463523)
                ·
                  refine ⟨49983661998720179918195285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33322441332480119945463523 49983661998720179918195285)
                  ·
                    refine ⟨585746039047502108416351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 49983661998720179918195285 585746039047502108416351)
                    ·
                      rfl

theorem cell23_3422209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 2, 1, 8].length) (baseStart_3422209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3422209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3422209 prefixEnd_3422209 := by exact prefixLift 3422209
  have htrace : WordTrace (prefixWord ++ tailWord_3422209) baseStart_3422209 baseEnd_3422209 := by
    simpa [prefixWord, tailWord_3422209, baseEnd_3422209] using wordTrace_append hprefix tailTrace_3422209
  have hstable : (prefixWord ++ tailWord_3422209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3422209).length < 2 ^ (prefixWord ++ tailWord_3422209).sum := by decide
  have hdescent : baseEnd_3422209 < baseStart_3422209 := by decide
  rcases family_descends (prefixWord ++ tailWord_3422209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3422219 : List Nat := [1, 1, 1, 1, 6, 1, 2, 1, 1, 3, 5]
def baseStart_3422219 : Nat := 118140960795 + 3422219 * 2 ^ 59
def prefixEnd_3422219 : Nat := 4983230072969 + 3 ^ 40 * 3422219 * 2
def baseEnd_3422219 : Nat := 1757243251949051286124007

theorem tailTrace_3422219 : CollatzResearch.WordTrace tailWord_3422219 prefixEnd_3422219 1757243251949051286124007 := by
  unfold tailWord_3422219
  simp only [CollatzResearch.WordTrace]
  refine ⟨124818581188892506318397711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83212387459261670878931807 124818581188892506318397711)
  ·
    refine ⟨187227871783338759477596567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124818581188892506318397711 187227871783338759477596567)
    ·
      refine ⟨280841807675008139216394851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187227871783338759477596567 280841807675008139216394851)
      ·
        refine ⟨421262711512512208824592277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280841807675008139216394851 421262711512512208824592277)
        ·
          refine ⟨19746689602149009788652763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 421262711512512208824592277 19746689602149009788652763)
          ·
            refine ⟨29620034403223514682979145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19746689602149009788652763 29620034403223514682979145)
            ·
              refine ⟨22215025802417636012234359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29620034403223514682979145 22215025802417636012234359)
              ·
                refine ⟨33322538703626454018351539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22215025802417636012234359 33322538703626454018351539)
                ·
                  refine ⟨49983808055439681027527309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33322538703626454018351539 49983808055439681027527309)
                  ·
                    refine ⟨18743928020789880385322741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49983808055439681027527309 18743928020789880385322741)
                    ·
                      refine ⟨1757243251949051286124007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18743928020789880385322741 1757243251949051286124007)
                      ·
                        rfl

theorem cell23_3422219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 1, 1, 3, 5].length) (baseStart_3422219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3422219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3422219 prefixEnd_3422219 := by exact prefixLift 3422219
  have htrace : WordTrace (prefixWord ++ tailWord_3422219) baseStart_3422219 baseEnd_3422219 := by
    simpa [prefixWord, tailWord_3422219, baseEnd_3422219] using wordTrace_append hprefix tailTrace_3422219
  have hstable : (prefixWord ++ tailWord_3422219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3422219).length < 2 ^ (prefixWord ++ tailWord_3422219).sum := by decide
  have hdescent : baseEnd_3422219 < baseStart_3422219 := by decide
  rcases family_descends (prefixWord ++ tailWord_3422219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3422221 : List Nat := [1, 7, 1, 2, 2, 1, 1, 2, 2, 4]
def baseStart_3422221 : Nat := 118140960795 + 3422221 * 2 ^ 59
def prefixEnd_3422221 : Nat := 4983230072969 + 3 ^ 40 * 3422221 * 2
def baseEnd_3422221 : Nat := 585748092970120092766333

theorem tailTrace_3422221 : CollatzResearch.WordTrace tailWord_3422221 prefixEnd_3422221 585748092970120092766333 := by
  unfold tailWord_3422221
  simp only [CollatzResearch.WordTrace]
  refine ⟨124818654134885260659970517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83212436089923507106647011 124818654134885260659970517)
  ·
    refine ⟨2925437206286373296718059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 124818654134885260659970517 2925437206286373296718059)
    ·
      refine ⟨4388155809429559945077089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2925437206286373296718059 4388155809429559945077089)
      ·
        refine ⟨3291116857072169958807817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4388155809429559945077089 3291116857072169958807817)
        ·
          refine ⟨2468337642804127469105863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3291116857072169958807817 2468337642804127469105863)
          ·
            refine ⟨3702506464206191203658795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2468337642804127469105863 3702506464206191203658795)
            ·
              refine ⟨5553759696309286805488193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3702506464206191203658795 5553759696309286805488193)
              ·
                refine ⟨4165319772231965104116145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5553759696309286805488193 4165319772231965104116145)
                ·
                  refine ⟨3123989829173973828087109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4165319772231965104116145 3123989829173973828087109)
                  ·
                    refine ⟨585748092970120092766333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3123989829173973828087109 585748092970120092766333)
                    ·
                      rfl

theorem cell23_3422221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_3422221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3422221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3422221 prefixEnd_3422221 := by exact prefixLift 3422221
  have htrace : WordTrace (prefixWord ++ tailWord_3422221) baseStart_3422221 baseEnd_3422221 := by
    simpa [prefixWord, tailWord_3422221, baseEnd_3422221] using wordTrace_append hprefix tailTrace_3422221
  have hstable : (prefixWord ++ tailWord_3422221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3422221).length < 2 ^ (prefixWord ++ tailWord_3422221).sum := by decide
  have hdescent : baseEnd_3422221 < baseStart_3422221 := by decide
  rcases family_descends (prefixWord ++ tailWord_3422221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3422250 : List Nat := [3, 1, 4, 1, 2, 1, 3, 1, 1, 4, 2]
def baseStart_3422250 : Nat := 118140960795 + 3422250 * 2 ^ 59
def prefixEnd_3422250 : Nat := 4983230072969 + 3 ^ 40 * 3422250 * 2
def baseEnd_3422250 : Nat := 1757259169849340664836365

theorem tailTrace_3422250 : CollatzResearch.WordTrace tailWord_3422250 prefixEnd_3422250 1757259169849340664836365 := by
  unfold tailWord_3422250
  simp only [CollatzResearch.WordTrace]
  refine ⟨31204927962945049653194051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83213141234520132408517469 31204927962945049653194051)
  ·
    refine ⟨46807391944417574479791077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31204927962945049653194051 46807391944417574479791077)
    ·
      refine ⟨8776385989578295214960827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46807391944417574479791077 8776385989578295214960827)
      ·
        refine ⟨13164578984367442822441241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8776385989578295214960827 13164578984367442822441241)
        ·
          refine ⟨9873434238275582116830931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13164578984367442822441241 9873434238275582116830931)
          ·
            refine ⟨14810151357413373175246397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9873434238275582116830931 14810151357413373175246397)
            ·
              refine ⟨5553806759030014940717399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14810151357413373175246397 5553806759030014940717399)
              ·
                refine ⟨8330710138545022411076099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5553806759030014940717399 8330710138545022411076099)
                ·
                  refine ⟨12496065207817533616614149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8330710138545022411076099 12496065207817533616614149)
                  ·
                    refine ⟨2343012226465787553115153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12496065207817533616614149 2343012226465787553115153)
                    ·
                      refine ⟨1757259169849340664836365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2343012226465787553115153 1757259169849340664836365)
                      ·
                        rfl

theorem cell23_3422250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 3, 1, 1, 4, 2].length) (baseStart_3422250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3422250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3422250 prefixEnd_3422250 := by exact prefixLift 3422250
  have htrace : WordTrace (prefixWord ++ tailWord_3422250) baseStart_3422250 baseEnd_3422250 := by
    simpa [prefixWord, tailWord_3422250, baseEnd_3422250] using wordTrace_append hprefix tailTrace_3422250
  have hstable : (prefixWord ++ tailWord_3422250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3422250).length < 2 ^ (prefixWord ++ tailWord_3422250).sum := by decide
  have hdescent : baseEnd_3422250 < baseStart_3422250 := by decide
  rcases family_descends (prefixWord ++ tailWord_3422250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3422286 : List Nat := [4, 1, 1, 1, 1, 4, 1, 1, 4, 5]
def baseStart_3422286 : Nat := 118140960795 + 3422286 * 2 ^ 59
def prefixEnd_3422286 : Nat := 4983230072969 + 3 ^ 40 * 3422286 * 2
def baseEnd_3422286 : Nat := 585759218384300841328733

theorem tailTrace_3422286 : CollatzResearch.WordTrace tailWord_3422286 prefixEnd_3422286 585759218384300841328733 := by
  unfold tailWord_3422286
  simp only [CollatzResearch.WordTrace]
  refine ⟨15602628109956222095135839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83214016586433184507391141 15602628109956222095135839)
  ·
    refine ⟨23403942164934333142703759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15602628109956222095135839 23403942164934333142703759)
    ·
      refine ⟨35105913247401499714055639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23403942164934333142703759 35105913247401499714055639)
      ·
        refine ⟨52658869871102249571083459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35105913247401499714055639 52658869871102249571083459)
        ·
          refine ⟨78988304806653374356625189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52658869871102249571083459 78988304806653374356625189)
          ·
            refine ⟨14810307151247507691867223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78988304806653374356625189 14810307151247507691867223)
            ·
              refine ⟨22215460726871261537800835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14810307151247507691867223 22215460726871261537800835)
              ·
                refine ⟨33323191090306892306701253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22215460726871261537800835 33323191090306892306701253)
                ·
                  refine ⟨6248098329432542307506485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33323191090306892306701253 6248098329432542307506485)
                  ·
                    refine ⟨585759218384300841328733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6248098329432542307506485 585759218384300841328733)
                    ·
                      rfl

theorem cell23_3422286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 1, 4, 5].length) (baseStart_3422286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3422286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3422286 prefixEnd_3422286 := by exact prefixLift 3422286
  have htrace : WordTrace (prefixWord ++ tailWord_3422286) baseStart_3422286 baseEnd_3422286 := by
    simpa [prefixWord, tailWord_3422286, baseEnd_3422286] using wordTrace_append hprefix tailTrace_3422286
  have hstable : (prefixWord ++ tailWord_3422286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3422286).length < 2 ^ (prefixWord ++ tailWord_3422286).sum := by decide
  have hdescent : baseEnd_3422286 < baseStart_3422286 := by decide
  rcases family_descends (prefixWord ++ tailWord_3422286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3422290 : List Nat := [3, 2, 2, 1, 5, 1, 1, 1, 7]
def baseStart_3422290 : Nat := 118140960795 + 3422290 * 2 ^ 59
def prefixEnd_3422290 : Nat := 4983230072969 + 3 ^ 40 * 3422290 * 2
def baseEnd_3422290 : Nat := 195253301008391167592909

theorem tailTrace_3422290 : CollatzResearch.WordTrace tailWord_3422290 prefixEnd_3422290 195253301008391167592909 := by
  unfold tailWord_3422290
  simp only [CollatzResearch.WordTrace]
  refine ⟨31205292692908821361058081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83214113847756856962821549 31205292692908821361058081)
  ·
    refine ⟨23403969519681616020793561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31205292692908821361058081 23403969519681616020793561)
    ·
      refine ⟨17552977139761212015595171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23403969519681616020793561 17552977139761212015595171)
      ·
        refine ⟨26329465709641818023392757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17552977139761212015595171 26329465709641818023392757)
        ·
          refine ⟨2468387410278920439693071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26329465709641818023392757 2468387410278920439693071)
          ·
            refine ⟨3702581115418380659539607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2468387410278920439693071 3702581115418380659539607)
            ·
              refine ⟨5553871673127570989309411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3702581115418380659539607 5553871673127570989309411)
              ·
                refine ⟨8330807509691356483964117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5553871673127570989309411 8330807509691356483964117)
                ·
                  refine ⟨195253301008391167592909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8330807509691356483964117 195253301008391167592909)
                  ·
                    rfl

theorem cell23_3422290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 1, 1, 7].length) (baseStart_3422290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3422290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3422290 prefixEnd_3422290 := by exact prefixLift 3422290
  have htrace : WordTrace (prefixWord ++ tailWord_3422290) baseStart_3422290 baseEnd_3422290 := by
    simpa [prefixWord, tailWord_3422290, baseEnd_3422290] using wordTrace_append hprefix tailTrace_3422290
  have hstable : (prefixWord ++ tailWord_3422290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3422290).length < 2 ^ (prefixWord ++ tailWord_3422290).sum := by decide
  have hdescent : baseEnd_3422290 < baseStart_3422290 := by decide
  rcases family_descends (prefixWord ++ tailWord_3422290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3422296 : List Nat := [2, 1, 2, 2, 1, 5, 1, 1, 1, 2, 5]
def baseStart_3422296 : Nat := 118140960795 + 3422296 * 2 ^ 59
def prefixEnd_3422296 : Nat := 4983230072969 + 3 ^ 40 * 3422296 * 2
def baseEnd_3422296 : Nat := 1757282789959447484861153

theorem tailTrace_3422296 : CollatzResearch.WordTrace tailWord_3422296 prefixEnd_3422296 1757282789959447484861153 := by
  unfold tailWord_3422296
  simp only [CollatzResearch.WordTrace]
  refine ⟨62410694804806774234475371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83214259739742365645967161 62410694804806774234475371)
  ·
    refine ⟨93616042207210161351713057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62410694804806774234475371 93616042207210161351713057)
    ·
      refine ⟨70212031655407621013784793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93616042207210161351713057 70212031655407621013784793)
      ·
        refine ⟨52659023741555715760338595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70212031655407621013784793 52659023741555715760338595)
        ·
          refine ⟨78988535612333573640507893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52659023741555715760338595 78988535612333573640507893)
          ·
            refine ⟨7405175213656272528797615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 78988535612333573640507893 7405175213656272528797615)
            ·
              refine ⟨11107762820484408793196423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7405175213656272528797615 11107762820484408793196423)
              ·
                refine ⟨16661644230726613189794635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11107762820484408793196423 16661644230726613189794635)
                ·
                  refine ⟨24992466346089919784691953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16661644230726613189794635 24992466346089919784691953)
                  ·
                    refine ⟨18744349759567439838518965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24992466346089919784691953 18744349759567439838518965)
                    ·
                      refine ⟨1757282789959447484861153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18744349759567439838518965 1757282789959447484861153)
                      ·
                        rfl

theorem cell23_3422296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 1, 1, 2, 5].length) (baseStart_3422296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3422296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3422296 prefixEnd_3422296 := by exact prefixLift 3422296
  have htrace : WordTrace (prefixWord ++ tailWord_3422296) baseStart_3422296 baseEnd_3422296 := by
    simpa [prefixWord, tailWord_3422296, baseEnd_3422296] using wordTrace_append hprefix tailTrace_3422296
  have hstable : (prefixWord ++ tailWord_3422296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3422296).length < 2 ^ (prefixWord ++ tailWord_3422296).sum := by decide
  have hdescent : baseEnd_3422296 < baseStart_3422296 := by decide
  rcases family_descends (prefixWord ++ tailWord_3422296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3422301 : List Nat := [1, 4, 4, 1, 1, 3, 2, 1, 2, 2, 2]
def baseStart_3422301 : Nat := 118140960795 + 3422301 * 2 ^ 59
def prefixEnd_3422301 : Nat := 4983230072969 + 3 ^ 40 * 3422301 * 2
def baseEnd_3422301 : Nat := 1757285357362719965298631

theorem tailTrace_3422301 : CollatzResearch.WordTrace tailWord_3422301 prefixEnd_3422301 1757285357362719965298631 := by
  unfold tailWord_3422301
  simp only [CollatzResearch.WordTrace]
  refine ⟨124821571974595434322882757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83214381316396956215255171 124821571974595434322882757)
  ·
    refine ⟨23404044745236643935540517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124821571974595434322882757 23404044745236643935540517)
    ·
      refine ⟨4388258389731870737913847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23404044745236643935540517 4388258389731870737913847)
      ·
        refine ⟨6582387584597806106870771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4388258389731870737913847 6582387584597806106870771)
        ·
          refine ⟨9873581376896709160306157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6582387584597806106870771 9873581376896709160306157)
          ·
            refine ⟨3702593016336265935114809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9873581376896709160306157 3702593016336265935114809)
            ·
              refine ⟨2776944762252199451336107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3702593016336265935114809 2776944762252199451336107)
              ·
                refine ⟨4165417143378299177004161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2776944762252199451336107 4165417143378299177004161)
                ·
                  refine ⟨3124062857533724382753121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4165417143378299177004161 3124062857533724382753121)
                  ·
                    refine ⟨2343047143150293287064841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3124062857533724382753121 2343047143150293287064841)
                    ·
                      refine ⟨1757285357362719965298631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2343047143150293287064841 1757285357362719965298631)
                      ·
                        rfl

theorem cell23_3422301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 2, 1, 2, 2, 2].length) (baseStart_3422301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3422301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3422301 prefixEnd_3422301 := by exact prefixLift 3422301
  have htrace : WordTrace (prefixWord ++ tailWord_3422301) baseStart_3422301 baseEnd_3422301 := by
    simpa [prefixWord, tailWord_3422301, baseEnd_3422301] using wordTrace_append hprefix tailTrace_3422301
  have hstable : (prefixWord ++ tailWord_3422301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3422301).length < 2 ^ (prefixWord ++ tailWord_3422301).sum := by decide
  have hdescent : baseEnd_3422301 < baseStart_3422301 := by decide
  rcases family_descends (prefixWord ++ tailWord_3422301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3422343 : List Nat := [1, 1, 4, 2, 1, 1, 4, 2, 2, 2, 3]
def baseStart_3422343 : Nat := 118140960795 + 3422343 * 2 ^ 59
def prefixEnd_3422343 : Nat := 4983230072969 + 3 ^ 40 * 3422343 * 2
def baseEnd_3422343 : Nat := 1757306923550208800973437

theorem tailTrace_3422343 : CollatzResearch.WordTrace tailWord_3422343 prefixEnd_3422343 1757306923550208800973437 := by
  unfold tailWord_3422343
  simp only [CollatzResearch.WordTrace]
  refine ⟨124823103840443275495911683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83215402560295516997274455 124823103840443275495911683)
  ·
    refine ⟨187234655760664913243867525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124823103840443275495911683 187234655760664913243867525)
    ·
      refine ⟨35106497955124671233225161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 187234655760664913243867525 35106497955124671233225161)
      ·
        refine ⟨26329873466343503424918871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35106497955124671233225161 26329873466343503424918871)
        ·
          refine ⟨39494810199515255137378307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26329873466343503424918871 39494810199515255137378307)
          ·
            refine ⟨59242215299272882706067461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39494810199515255137378307 59242215299272882706067461)
            ·
              refine ⟨11107915368613665507387649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59242215299272882706067461 11107915368613665507387649)
              ·
                refine ⟨8330936526460249130540737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11107915368613665507387649 8330936526460249130540737)
                ·
                  refine ⟨6248202394845186847905553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8330936526460249130540737 6248202394845186847905553)
                  ·
                    refine ⟨4686151796133890135929165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6248202394845186847905553 4686151796133890135929165)
                    ·
                      refine ⟨1757306923550208800973437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4686151796133890135929165 1757306923550208800973437)
                      ·
                        rfl

theorem cell23_3422343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 2, 2, 2, 3].length) (baseStart_3422343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3422343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3422343 prefixEnd_3422343 := by exact prefixLift 3422343
  have htrace : WordTrace (prefixWord ++ tailWord_3422343) baseStart_3422343 baseEnd_3422343 := by
    simpa [prefixWord, tailWord_3422343, baseEnd_3422343] using wordTrace_append hprefix tailTrace_3422343
  have hstable : (prefixWord ++ tailWord_3422343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3422343).length < 2 ^ (prefixWord ++ tailWord_3422343).sum := by decide
  have hdescent : baseEnd_3422343 < baseStart_3422343 := by decide
  rcases family_descends (prefixWord ++ tailWord_3422343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3422393 : List Nat := [1, 2, 1, 4, 1, 2, 3, 3, 1, 5]
def baseStart_3422393 : Nat := 118140960795 + 3422393 * 2 ^ 59
def prefixEnd_3422393 : Nat := 4983230072969 + 3 ^ 40 * 3422393 * 2
def baseEnd_3422393 : Nat := 585777532527644535116069

theorem tailTrace_3422393 : CollatzResearch.WordTrace tailWord_3422393 prefixEnd_3422393 585777532527644535116069 := by
  unfold tailWord_3422393
  simp only [CollatzResearch.WordTrace]
  refine ⟨124824927490262134035231833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83216618326841422690154555 124824927490262134035231833)
  ·
    refine ⟨93618695617696600526423875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124824927490262134035231833 93618695617696600526423875)
    ·
      refine ⟨140428043426544900789635813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93618695617696600526423875 140428043426544900789635813)
      ·
        refine ⟨26330258142477168898056715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 140428043426544900789635813 26330258142477168898056715)
        ·
          refine ⟨39495387213715753347085073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26330258142477168898056715 39495387213715753347085073)
          ·
            refine ⟨29621540410286815010313805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39495387213715753347085073 29621540410286815010313805)
            ·
              refine ⟨11108077653857555628867677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29621540410286815010313805 11108077653857555628867677)
              ·
                refine ⟨4165529120196583360825379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11108077653857555628867677 4165529120196583360825379)
                ·
                  refine ⟨6248293680294875041238069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4165529120196583360825379 6248293680294875041238069)
                  ·
                    refine ⟨585777532527644535116069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6248293680294875041238069 585777532527644535116069)
                    ·
                      rfl

theorem cell23_3422393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 3, 1, 5].length) (baseStart_3422393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3422393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3422393 prefixEnd_3422393 := by exact prefixLift 3422393
  have htrace : WordTrace (prefixWord ++ tailWord_3422393) baseStart_3422393 baseEnd_3422393 := by
    simpa [prefixWord, tailWord_3422393, baseEnd_3422393] using wordTrace_append hprefix tailTrace_3422393
  have hstable : (prefixWord ++ tailWord_3422393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3422393).length < 2 ^ (prefixWord ++ tailWord_3422393).sum := by decide
  have hdescent : baseEnd_3422393 < baseStart_3422393 := by decide
  rcases family_descends (prefixWord ++ tailWord_3422393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3422450 : List Nat := [3, 2, 1, 3, 2, 2, 2, 1, 1, 1, 5]
def baseStart_3422450 : Nat := 118140960795 + 3422450 * 2 ^ 59
def prefixEnd_3422450 : Nat := 4983230072969 + 3 ^ 40 * 3422450 * 2
def baseEnd_3422450 : Nat := 1757361865980239882335445

theorem tailTrace_3422450 : CollatzResearch.WordTrace tailWord_3422450 prefixEnd_3422450 1757361865980239882335445 := by
  unfold tailWord_3422450
  simp only [CollatzResearch.WordTrace]
  refine ⟨31206751612763908192514201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83218004300703755180037869 31206751612763908192514201)
  ·
    refine ⟨23405063709572931144385651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31206751612763908192514201 23405063709572931144385651)
    ·
      refine ⟨35107595564359396716578477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23405063709572931144385651 35107595564359396716578477)
      ·
        refine ⟨13165348336634773768716929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35107595564359396716578477 13165348336634773768716929)
        ·
          refine ⟨9874011252476080326537697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13165348336634773768716929 9874011252476080326537697)
          ·
            refine ⟨7405508439357060244903273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9874011252476080326537697 7405508439357060244903273)
            ·
              refine ⟨5554131329517795183677455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7405508439357060244903273 5554131329517795183677455)
              ·
                refine ⟨8331196994276692775516183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5554131329517795183677455 8331196994276692775516183)
                ·
                  refine ⟨12496795491415039163274275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8331196994276692775516183 12496795491415039163274275)
                  ·
                    refine ⟨18745193237122558744911413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12496795491415039163274275 18745193237122558744911413)
                    ·
                      refine ⟨1757361865980239882335445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18745193237122558744911413 1757361865980239882335445)
                      ·
                        rfl

theorem cell23_3422450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 2, 1, 1, 1, 5].length) (baseStart_3422450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3422450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3422450 prefixEnd_3422450 := by exact prefixLift 3422450
  have htrace : WordTrace (prefixWord ++ tailWord_3422450) baseStart_3422450 baseEnd_3422450 := by
    simpa [prefixWord, tailWord_3422450, baseEnd_3422450] using wordTrace_append hprefix tailTrace_3422450
  have hstable : (prefixWord ++ tailWord_3422450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3422450).length < 2 ^ (prefixWord ++ tailWord_3422450).sum := by decide
  have hdescent : baseEnd_3422450 < baseStart_3422450 := by decide
  rcases family_descends (prefixWord ++ tailWord_3422450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3422514 : List Nat := [3, 2, 1, 1, 5, 1, 2, 2, 2, 1, 3]
def baseStart_3422514 : Nat := 118140960795 + 3422514 * 2 ^ 59
def prefixEnd_3422514 : Nat := 4983230072969 + 3 ^ 40 * 3422514 * 2
def baseEnd_3422514 : Nat := 1757394728742127631935151

theorem tailTrace_3422514 : CollatzResearch.WordTrace tailWord_3422514 prefixEnd_3422514 1757394728742127631935151 := by
  unfold tailWord_3422514
  simp only [CollatzResearch.WordTrace]
  refine ⟨31207335180705942925096649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83219560481882514466924397 31207335180705942925096649)
  ·
    refine ⟨23405501385529457193822487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31207335180705942925096649 23405501385529457193822487)
    ·
      refine ⟨35108252078294185790733731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23405501385529457193822487 35108252078294185790733731)
      ·
        refine ⟨52662378117441278686100597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35108252078294185790733731 52662378117441278686100597)
        ·
          refine ⟨4937097948510119876821931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52662378117441278686100597 4937097948510119876821931)
          ·
            refine ⟨7405646922765179815232897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4937097948510119876821931 7405646922765179815232897)
            ·
              refine ⟨5554235192073884861424673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7405646922765179815232897 5554235192073884861424673)
              ·
                refine ⟨4165676394055413646068505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5554235192073884861424673 4165676394055413646068505)
                ·
                  refine ⟨3124257295541560234551379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4165676394055413646068505 3124257295541560234551379)
                  ·
                    refine ⟨4686385943312340351827069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3124257295541560234551379 4686385943312340351827069)
                    ·
                      refine ⟨1757394728742127631935151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4686385943312340351827069 1757394728742127631935151)
                      ·
                        rfl

theorem cell23_3422514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 2, 2, 2, 1, 3].length) (baseStart_3422514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3422514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3422514 prefixEnd_3422514 := by exact prefixLift 3422514
  have htrace : WordTrace (prefixWord ++ tailWord_3422514) baseStart_3422514 baseEnd_3422514 := by
    simpa [prefixWord, tailWord_3422514, baseEnd_3422514] using wordTrace_append hprefix tailTrace_3422514
  have hstable : (prefixWord ++ tailWord_3422514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3422514).length < 2 ^ (prefixWord ++ tailWord_3422514).sum := by decide
  have hdescent : baseEnd_3422514 < baseStart_3422514 := by decide
  rcases family_descends (prefixWord ++ tailWord_3422514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3422553 : List Nat := [1, 2, 1, 2, 2, 2, 1, 1, 3, 5, 3]
def baseStart_3422553 : Nat := 118140960795 + 3422553 * 2 ^ 59
def prefixEnd_3422553 : Nat := 4983230072969 + 3 ^ 40 * 3422553 * 2
def baseEnd_3422553 : Nat := 1757414754487652979347471

theorem tailTrace_3422553 : CollatzResearch.WordTrace tailWord_3422553 prefixEnd_3422553 1757414754487652979347471 := by
  unfold tailWord_3422553
  simp only [CollatzResearch.WordTrace]
  refine ⟨124830763169682481361056313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83220508779788320907370875 124830763169682481361056313)
  ·
    refine ⟨93623072377261861020792235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124830763169682481361056313 93623072377261861020792235)
    ·
      refine ⟨140434608565892791531188353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93623072377261861020792235 140434608565892791531188353)
      ·
        refine ⟨105325956424419593648391265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140434608565892791531188353 105325956424419593648391265)
        ·
          refine ⟨78994467318314695236293449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105325956424419593648391265 78994467318314695236293449)
          ·
            refine ⟨59245850488736021427220087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78994467318314695236293449 59245850488736021427220087)
            ·
              refine ⟨88868775733104032140830131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59245850488736021427220087 88868775733104032140830131)
              ·
                refine ⟨133303163599656048211245197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88868775733104032140830131 133303163599656048211245197)
                ·
                  refine ⟨49988686349871018079216949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 133303163599656048211245197 49988686349871018079216949)
                  ·
                    refine ⟨4686439345300407944926589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49988686349871018079216949 4686439345300407944926589)
                    ·
                      refine ⟨1757414754487652979347471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4686439345300407944926589 1757414754487652979347471)
                      ·
                        rfl

theorem cell23_3422553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 3, 5, 3].length) (baseStart_3422553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3422553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3422553 prefixEnd_3422553 := by exact prefixLift 3422553
  have htrace : WordTrace (prefixWord ++ tailWord_3422553) baseStart_3422553 baseEnd_3422553 := by
    simpa [prefixWord, tailWord_3422553, baseEnd_3422553] using wordTrace_append hprefix tailTrace_3422553
  have hstable : (prefixWord ++ tailWord_3422553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3422553).length < 2 ^ (prefixWord ++ tailWord_3422553).sum := by decide
  have hdescent : baseEnd_3422553 < baseStart_3422553 := by decide
  rcases family_descends (prefixWord ++ tailWord_3422553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3422613 : List Nat := [1, 3, 2, 1, 1, 2, 1, 2, 2, 3, 5]
def baseStart_3422613 : Nat := 118140960795 + 3422613 * 2 ^ 59
def prefixEnd_3422613 : Nat := 4983230072969 + 3 ^ 40 * 3422613 * 2
def baseEnd_3422613 : Nat := 1757445563326922744597195

theorem tailTrace_3422613 : CollatzResearch.WordTrace tailWord_3422613 prefixEnd_3422613 1757445563326922744597195 := by
  unfold tailWord_3422613
  simp only [CollatzResearch.WordTrace]
  refine ⟨124832951549465111608240493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83221967699643407738826995 124832951549465111608240493)
  ·
    refine ⟨46812356831049416853090185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124832951549465111608240493 46812356831049416853090185)
    ·
      refine ⟨35109267623287062639817639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46812356831049416853090185 35109267623287062639817639)
      ·
        refine ⟨52663901434930593959726459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35109267623287062639817639 52663901434930593959726459)
        ·
          refine ⟨78995852152395890939589689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52663901434930593959726459 78995852152395890939589689)
          ·
            refine ⟨59246889114296918204692267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78995852152395890939589689 59246889114296918204692267)
            ·
              refine ⟨88870333671445377307038401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59246889114296918204692267 88870333671445377307038401)
              ·
                refine ⟨66652750253584032980278801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88870333671445377307038401 66652750253584032980278801)
                ·
                  refine ⟨49989562690188024735209101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66652750253584032980278801 49989562690188024735209101)
                  ·
                    refine ⟨18746086008820509275703413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49989562690188024735209101 18746086008820509275703413)
                    ·
                      refine ⟨1757445563326922744597195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18746086008820509275703413 1757445563326922744597195)
                      ·
                        rfl

theorem cell23_3422613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 2, 3, 5].length) (baseStart_3422613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3422613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3422613 prefixEnd_3422613 := by exact prefixLift 3422613
  have htrace : WordTrace (prefixWord ++ tailWord_3422613) baseStart_3422613 baseEnd_3422613 := by
    simpa [prefixWord, tailWord_3422613, baseEnd_3422613] using wordTrace_append hprefix tailTrace_3422613
  have hstable : (prefixWord ++ tailWord_3422613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3422613).length < 2 ^ (prefixWord ++ tailWord_3422613).sum := by decide
  have hdescent : baseEnd_3422613 < baseStart_3422613 := by decide
  rcases family_descends (prefixWord ++ tailWord_3422613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3422673 : List Nat := [1, 2, 2, 1, 2, 1, 1, 2, 1, 3, 7]
def baseStart_3422673 : Nat := 118140960795 + 3422673 * 2 ^ 59
def prefixEnd_3422673 : Nat := 4983230072969 + 3 ^ 40 * 3422673 * 2
def baseEnd_3422673 : Nat := 1757476372166192509846919

theorem tailTrace_3422673 : CollatzResearch.WordTrace tailWord_3422673 prefixEnd_3422673 1757476372166192509846919 := by
  unfold tailWord_3422673
  simp only [CollatzResearch.WordTrace]
  refine ⟨124835139929247741855424673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83223426619498494570283115 124835139929247741855424673)
  ·
    refine ⟨93626354946935806391568505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124835139929247741855424673 93626354946935806391568505)
    ·
      refine ⟨70219766210201854793676379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93626354946935806391568505 70219766210201854793676379)
      ·
        refine ⟨105329649315302782190514569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70219766210201854793676379 105329649315302782190514569)
        ·
          refine ⟨78997236986477086642885927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105329649315302782190514569 78997236986477086642885927)
          ·
            refine ⟨118495855479715629964328891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78997236986477086642885927 118495855479715629964328891)
            ·
              refine ⟨177743783219573444946493337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118495855479715629964328891 177743783219573444946493337)
              ·
                refine ⟨133307837414680083709870003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 177743783219573444946493337 133307837414680083709870003)
                ·
                  refine ⟨199961756122020125564805005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 133307837414680083709870003 199961756122020125564805005)
                  ·
                    refine ⟨74985658545757547086801877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 199961756122020125564805005 74985658545757547086801877)
                    ·
                      refine ⟨1757476372166192509846919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 74985658545757547086801877 1757476372166192509846919)
                      ·
                        rfl

theorem cell23_3422673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 3, 7].length) (baseStart_3422673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3422673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3422673 prefixEnd_3422673 := by exact prefixLift 3422673
  have htrace : WordTrace (prefixWord ++ tailWord_3422673) baseStart_3422673 baseEnd_3422673 := by
    simpa [prefixWord, tailWord_3422673, baseEnd_3422673] using wordTrace_append hprefix tailTrace_3422673
  have hstable : (prefixWord ++ tailWord_3422673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3422673).length < 2 ^ (prefixWord ++ tailWord_3422673).sum := by decide
  have hdescent : baseEnd_3422673 < baseStart_3422673 := by decide
  rcases family_descends (prefixWord ++ tailWord_3422673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3422700 : List Nat := [2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 4]
def baseStart_3422700 : Nat := 118140960795 + 3422700 * 2 ^ 59
def prefixEnd_3422700 : Nat := 4983230072969 + 3 ^ 40 * 3422700 * 2
def baseEnd_3422700 : Nat := 1757490236143863904209295

theorem tailTrace_3422700 : CollatzResearch.WordTrace tailWord_3422700 prefixEnd_3422700 1757490236143863904209295 := by
  unfold tailWord_3422700
  simp only [CollatzResearch.WordTrace]
  refine ⟨62418062350074962733328777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83224083133433283644438369 62418062350074962733328777)
  ·
    refine ⟨46813546762556222049996583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62418062350074962733328777 46813546762556222049996583)
    ·
      refine ⟨70220320143834333074994875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46813546762556222049996583 70220320143834333074994875)
      ·
        refine ⟨105330480215751499612492313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70220320143834333074994875 105330480215751499612492313)
        ·
          refine ⟨78997860161813624709369235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105330480215751499612492313 78997860161813624709369235)
          ·
            refine ⟨118496790242720437064053853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78997860161813624709369235 118496790242720437064053853)
            ·
              refine ⟨44436296341020163899020195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118496790242720437064053853 44436296341020163899020195)
              ·
                refine ⟨66654444511530245848530293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44436296341020163899020195 66654444511530245848530293)
                ·
                  refine ⟨6248854172955960548299715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 66654444511530245848530293 6248854172955960548299715)
                  ·
                    refine ⟨9373281259433940822449573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6248854172955960548299715 9373281259433940822449573)
                    ·
                      refine ⟨1757490236143863904209295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9373281259433940822449573 1757490236143863904209295)
                      ·
                        rfl

theorem cell23_3422700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 4].length) (baseStart_3422700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3422700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3422700 prefixEnd_3422700 := by exact prefixLift 3422700
  have htrace : WordTrace (prefixWord ++ tailWord_3422700) baseStart_3422700 baseEnd_3422700 := by
    simpa [prefixWord, tailWord_3422700, baseEnd_3422700] using wordTrace_append hprefix tailTrace_3422700
  have hstable : (prefixWord ++ tailWord_3422700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3422700).length < 2 ^ (prefixWord ++ tailWord_3422700).sum := by decide
  have hdescent : baseEnd_3422700 < baseStart_3422700 := by decide
  rcases family_descends (prefixWord ++ tailWord_3422700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3422717 : List Nat := [1, 4, 1, 1, 1, 3, 2, 4, 1, 1, 4]
def baseStart_3422717 : Nat := 118140960795 + 3422717 * 2 ^ 59
def prefixEnd_3422717 : Nat := 4983230072969 + 3 ^ 40 * 3422717 * 2
def baseEnd_3422717 : Nat := 1757498965314990337696717

theorem tailTrace_3422717 : CollatzResearch.WordTrace tailWord_3422717 prefixEnd_3422717 1757498965314990337696717 := by
  unfold tailWord_3422717
  simp only [CollatzResearch.WordTrace]
  refine ⟨124836744741088337370026405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83224496494058891580017603 124836744741088337370026405)
  ·
    refine ⟨23406889638954063256879951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124836744741088337370026405 23406889638954063256879951)
    ·
      refine ⟨35110334458431094885319927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23406889638954063256879951 35110334458431094885319927)
      ·
        refine ⟨52665501687646642327979891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35110334458431094885319927 52665501687646642327979891)
        ·
          refine ⟨78998252531469963491969837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52665501687646642327979891 78998252531469963491969837)
          ·
            refine ⟨29624344699301236309488689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78998252531469963491969837 29624344699301236309488689)
            ·
              refine ⟨22218258524475927232116517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29624344699301236309488689 22218258524475927232116517)
              ·
                refine ⟨4165923473339236356021847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22218258524475927232116517 4165923473339236356021847)
                ·
                  refine ⟨6248885210008854534032771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4165923473339236356021847 6248885210008854534032771)
                  ·
                    refine ⟨9373327815013281801049157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6248885210008854534032771 9373327815013281801049157)
                    ·
                      refine ⟨1757498965314990337696717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9373327815013281801049157 1757498965314990337696717)
                      ·
                        rfl

theorem cell23_3422717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 4, 1, 1, 4].length) (baseStart_3422717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3422717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3422717 prefixEnd_3422717 := by exact prefixLift 3422717
  have htrace : WordTrace (prefixWord ++ tailWord_3422717) baseStart_3422717 baseEnd_3422717 := by
    simpa [prefixWord, tailWord_3422717, baseEnd_3422717] using wordTrace_append hprefix tailTrace_3422717
  have hstable : (prefixWord ++ tailWord_3422717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3422717).length < 2 ^ (prefixWord ++ tailWord_3422717).sum := by decide
  have hdescent : baseEnd_3422717 < baseStart_3422717 := by decide
  rcases family_descends (prefixWord ++ tailWord_3422717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3422721 : List Nat := [1, 2, 4, 1, 3, 3, 1, 1, 2, 3, 2]
def baseStart_3422721 : Nat := 118140960795 + 3422721 * 2 ^ 59
def prefixEnd_3422721 : Nat := 4983230072969 + 3 ^ 40 * 3422721 * 2
def baseEnd_3422721 : Nat := 1757501019237608322046699

theorem tailTrace_3422721 : CollatzResearch.WordTrace tailWord_3422721 prefixEnd_3422721 1757501019237608322046699 := by
  unfold tailWord_3422721
  simp only [CollatzResearch.WordTrace]
  refine ⟨124836890633073846053172017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83224593755382564035448011 124836890633073846053172017)
  ·
    refine ⟨93627667974805384539879013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124836890633073846053172017 93627667974805384539879013)
    ·
      refine ⟨17555187745276009601227315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93627667974805384539879013 17555187745276009601227315)
      ·
        refine ⟨26332781617914014401840973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17555187745276009601227315 26332781617914014401840973)
        ·
          refine ⟨9874793106717755400690365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26332781617914014401840973 9874793106717755400690365)
          ·
            refine ⟨3703047415019158275258887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9874793106717755400690365 3703047415019158275258887)
            ·
              refine ⟨5554571122528737412888331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3703047415019158275258887 5554571122528737412888331)
              ·
                refine ⟨8331856683793106119332497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5554571122528737412888331 8331856683793106119332497)
                ·
                  refine ⟨6248892512844829589499373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8331856683793106119332497 6248892512844829589499373)
                  ·
                    refine ⟨2343334692316811096062265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6248892512844829589499373 2343334692316811096062265)
                    ·
                      refine ⟨1757501019237608322046699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2343334692316811096062265 1757501019237608322046699)
                      ·
                        rfl

theorem cell23_3422721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 1, 1, 2, 3, 2].length) (baseStart_3422721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3422721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3422721 prefixEnd_3422721 := by exact prefixLift 3422721
  have htrace : WordTrace (prefixWord ++ tailWord_3422721) baseStart_3422721 baseEnd_3422721 := by
    simpa [prefixWord, tailWord_3422721, baseEnd_3422721] using wordTrace_append hprefix tailTrace_3422721
  have hstable : (prefixWord ++ tailWord_3422721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3422721).length < 2 ^ (prefixWord ++ tailWord_3422721).sum := by decide
  have hdescent : baseEnd_3422721 < baseStart_3422721 := by decide
  rcases family_descends (prefixWord ++ tailWord_3422721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3422734 : List Nat := [4, 1, 1, 2, 3, 2, 1, 3, 1, 1, 4]
def baseStart_3422734 : Nat := 118140960795 + 3422734 * 2 ^ 59
def prefixEnd_3422734 : Nat := 4983230072969 + 3 ^ 40 * 3422734 * 2
def baseEnd_3422734 : Nat := 1757507694486116771184139

theorem tailTrace_3422734 : CollatzResearch.WordTrace tailWord_3422734 prefixEnd_3422734 1757507694486116771184139 := by
  unfold tailWord_3422734
  simp only [CollatzResearch.WordTrace]
  refine ⟨15604670597753343659174407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83224909854684499515596837 15604670597753343659174407)
  ·
    refine ⟨23407005896630015488761611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15604670597753343659174407 23407005896630015488761611)
    ·
      refine ⟨35110508844945023233142417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23407005896630015488761611 35110508844945023233142417)
      ·
        refine ⟨26332881633708767424856813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35110508844945023233142417 26332881633708767424856813)
        ·
          refine ⟨9874830612640787784321305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26332881633708767424856813 9874830612640787784321305)
          ·
            refine ⟨7406122959480590838240979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9874830612640787784321305 7406122959480590838240979)
            ·
              refine ⟨11109184439220886257361469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7406122959480590838240979 11109184439220886257361469)
              ·
                refine ⟨4165944164707832346510551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11109184439220886257361469 4165944164707832346510551)
                ·
                  refine ⟨6248916247061748519765827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4165944164707832346510551 6248916247061748519765827)
                  ·
                    refine ⟨9373374370592622779648741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6248916247061748519765827 9373374370592622779648741)
                    ·
                      refine ⟨1757507694486116771184139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9373374370592622779648741 1757507694486116771184139)
                      ·
                        rfl

theorem cell23_3422734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 3, 1, 1, 4].length) (baseStart_3422734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3422734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3422734 prefixEnd_3422734 := by exact prefixLift 3422734
  have htrace : WordTrace (prefixWord ++ tailWord_3422734) baseStart_3422734 baseEnd_3422734 := by
    simpa [prefixWord, tailWord_3422734, baseEnd_3422734] using wordTrace_append hprefix tailTrace_3422734
  have hstable : (prefixWord ++ tailWord_3422734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3422734).length < 2 ^ (prefixWord ++ tailWord_3422734).sum := by decide
  have hdescent : baseEnd_3422734 < baseStart_3422734 := by decide
  rcases family_descends (prefixWord ++ tailWord_3422734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3422744 : List Nat := [2, 1, 2, 3, 3, 1, 3, 2, 2, 4]
def baseStart_3422744 : Nat := 118140960795 + 3422744 * 2 ^ 59
def prefixEnd_3422744 : Nat := 4983230072969 + 3 ^ 40 * 3422744 * 2
def baseEnd_3422744 : Nat := 585837609764220577353031

theorem tailTrace_3422744 : CollatzResearch.WordTrace tailWord_3422744 prefixEnd_3422744 585837609764220577353031 := by
  unfold tailWord_3422744
  simp only [CollatzResearch.WordTrace]
  refine ⟨62418864755995260490629643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83225153007993680654172857 62418864755995260490629643)
  ·
    refine ⟨93628297133992890735944465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62418864755995260490629643 93628297133992890735944465)
    ·
      refine ⟨70221222850494668051958349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93628297133992890735944465 70221222850494668051958349)
      ·
        refine ⟨26332958568935500519484381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70221222850494668051958349 26332958568935500519484381)
        ·
          refine ⟨9874859463350812694806643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26332958568935500519484381 9874859463350812694806643)
          ·
            refine ⟨14812289195026219042209965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9874859463350812694806643 14812289195026219042209965)
            ·
              refine ⟨5554608448134832140828737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14812289195026219042209965 5554608448134832140828737)
              ·
                refine ⟨4165956336101124105621553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5554608448134832140828737 4165956336101124105621553)
                ·
                  refine ⟨3124467252075843079216165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4165956336101124105621553 3124467252075843079216165)
                  ·
                    refine ⟨585837609764220577353031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3124467252075843079216165 585837609764220577353031)
                    ·
                      rfl

theorem cell23_3422744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 3, 2, 2, 4].length) (baseStart_3422744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3422744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3422744 prefixEnd_3422744 := by exact prefixLift 3422744
  have htrace : WordTrace (prefixWord ++ tailWord_3422744) baseStart_3422744 baseEnd_3422744 := by
    simpa [prefixWord, tailWord_3422744, baseEnd_3422744] using wordTrace_append hprefix tailTrace_3422744
  have hstable : (prefixWord ++ tailWord_3422744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3422744).length < 2 ^ (prefixWord ++ tailWord_3422744).sum := by decide
  have hdescent : baseEnd_3422744 < baseStart_3422744 := by decide
  rcases family_descends (prefixWord ++ tailWord_3422744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3422770 : List Nat := [3, 2, 1, 1, 2, 1, 2, 2, 2, 7]
def baseStart_3422770 : Nat := 118140960795 + 3422770 * 2 ^ 59
def prefixEnd_3422770 : Nat := 4983230072969 + 3 ^ 40 * 3422770 * 2
def baseEnd_3422770 : Nat := 585842059929892876777991

theorem tailTrace_3422770 : CollatzResearch.WordTrace tailWord_3422770 prefixEnd_3422770 585842059929892876777991 := by
  unfold tailWord_3422770
  simp only [CollatzResearch.WordTrace]
  refine ⟨31209669452474081855426441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83225785206597551614470509 31209669452474081855426441)
  ·
    refine ⟨23407252089355561391569831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31209669452474081855426441 23407252089355561391569831)
    ·
      refine ⟨35110878134033342087354747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23407252089355561391569831 35110878134033342087354747)
      ·
        refine ⟨52666317201050013131032121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35110878134033342087354747 52666317201050013131032121)
        ·
          refine ⟨39499737900787509848274091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52666317201050013131032121 39499737900787509848274091)
          ·
            refine ⟨59249606851181264772411137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39499737900787509848274091 59249606851181264772411137)
            ·
              refine ⟨44437205138385948579308353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59249606851181264772411137 44437205138385948579308353)
              ·
                refine ⟨33327903853789461434481265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44437205138385948579308353 33327903853789461434481265)
                ·
                  refine ⟨24995927890342096075860949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33327903853789461434481265 24995927890342096075860949)
                  ·
                    refine ⟨585842059929892876777991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24995927890342096075860949 585842059929892876777991)
                    ·
                      rfl

theorem cell23_3422770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 2, 2, 7].length) (baseStart_3422770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3422770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3422770 prefixEnd_3422770 := by exact prefixLift 3422770
  have htrace : WordTrace (prefixWord ++ tailWord_3422770) baseStart_3422770 baseEnd_3422770 := by
    simpa [prefixWord, tailWord_3422770, baseEnd_3422770] using wordTrace_append hprefix tailTrace_3422770
  have hstable : (prefixWord ++ tailWord_3422770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3422770).length < 2 ^ (prefixWord ++ tailWord_3422770).sum := by decide
  have hdescent : baseEnd_3422770 < baseStart_3422770 := by decide
  rcases family_descends (prefixWord ++ tailWord_3422770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3422774 : List Nat := [5, 1, 2, 1, 2, 1, 4, 7]
def baseStart_3422774 : Nat := 118140960795 + 3422774 * 2 ^ 59
def prefixEnd_3422774 : Nat := 4983230072969 + 3 ^ 40 * 3422774 * 2
def baseEnd_3422774 : Nat := 65093638285640615358665

theorem tailTrace_3422774 : CollatzResearch.WordTrace tailWord_3422774 prefixEnd_3422774 65093638285640615358665 := by
  unfold tailWord_3422774
  simp only [CollatzResearch.WordTrace]
  refine ⟨7802426481367614756553211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 83225882467921224069900917 7802426481367614756553211)
  ·
    refine ⟨11703639722051422134829817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7802426481367614756553211 11703639722051422134829817)
    ·
      refine ⟨8777729791538566601122363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11703639722051422134829817 8777729791538566601122363)
      ·
        refine ⟨13166594687307849901683545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8777729791538566601122363 13166594687307849901683545)
        ·
          refine ⟨9874946015480887426262659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13166594687307849901683545 9874946015480887426262659)
          ·
            refine ⟨14812419023221331139393989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9874946015480887426262659 14812419023221331139393989)
            ·
              refine ⟨2777328566853999588636373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14812419023221331139393989 2777328566853999588636373)
              ·
                refine ⟨65093638285640615358665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2777328566853999588636373 65093638285640615358665)
                ·
                  rfl

theorem cell23_3422774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 4, 7].length) (baseStart_3422774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3422774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3422774 prefixEnd_3422774 := by exact prefixLift 3422774
  have htrace : WordTrace (prefixWord ++ tailWord_3422774) baseStart_3422774 baseEnd_3422774 := by
    simpa [prefixWord, tailWord_3422774, baseEnd_3422774] using wordTrace_append hprefix tailTrace_3422774
  have hstable : (prefixWord ++ tailWord_3422774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3422774).length < 2 ^ (prefixWord ++ tailWord_3422774).sum := by decide
  have hdescent : baseEnd_3422774 < baseStart_3422774 := by decide
  rcases family_descends (prefixWord ++ tailWord_3422774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3422785 : List Nat := [1, 2, 5, 1, 1, 4, 1, 3, 1, 2, 2]
def baseStart_3422785 : Nat := 118140960795 + 3422785 * 2 ^ 59
def prefixEnd_3422785 : Nat := 4983230072969 + 3 ^ 40 * 3422785 * 2
def baseEnd_3422785 : Nat := 1757533881999496071646405

theorem tailTrace_3422785 : CollatzResearch.WordTrace tailWord_3422785 prefixEnd_3422785 1757533881999496071646405 := by
  unfold tailWord_3422785
  simp only [CollatzResearch.WordTrace]
  refine ⟨124839224904841984983501809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83226149936561323322334539 124839224904841984983501809)
  ·
    refine ⟨93629418678631488737626357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124839224904841984983501809 93629418678631488737626357)
    ·
      refine ⟨8777758001121702069152471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 93629418678631488737626357 8777758001121702069152471)
      ·
        refine ⟨13166637001682553103728707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8777758001121702069152471 13166637001682553103728707)
        ·
          refine ⟨19749955502523829655593061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13166637001682553103728707 19749955502523829655593061)
          ·
            refine ⟨3703116656723218060423699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19749955502523829655593061 3703116656723218060423699)
            ·
              refine ⟨5554674985084827090635549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3703116656723218060423699 5554674985084827090635549)
              ·
                refine ⟨2083003119406810158988331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5554674985084827090635549 2083003119406810158988331)
                ·
                  refine ⟨3124504679110215238482497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2083003119406810158988331 3124504679110215238482497)
                  ·
                    refine ⟨2343378509332661428861873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3124504679110215238482497 2343378509332661428861873)
                    ·
                      refine ⟨1757533881999496071646405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2343378509332661428861873 1757533881999496071646405)
                      ·
                        rfl

theorem cell23_3422785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 1, 3, 1, 2, 2].length) (baseStart_3422785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3422785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3422785 prefixEnd_3422785 := by exact prefixLift 3422785
  have htrace : WordTrace (prefixWord ++ tailWord_3422785) baseStart_3422785 baseEnd_3422785 := by
    simpa [prefixWord, tailWord_3422785, baseEnd_3422785] using wordTrace_append hprefix tailTrace_3422785
  have hstable : (prefixWord ++ tailWord_3422785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3422785).length < 2 ^ (prefixWord ++ tailWord_3422785).sum := by decide
  have hdescent : baseEnd_3422785 < baseStart_3422785 := by decide
  rcases family_descends (prefixWord ++ tailWord_3422785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3422788 : List Nat := [2, 3, 5, 1, 1, 1, 2, 1, 1, 1, 5]
def baseStart_3422788 : Nat := 118140960795 + 3422788 * 2 ^ 59
def prefixEnd_3422788 : Nat := 4983230072969 + 3 ^ 40 * 3422788 * 2
def baseEnd_3422788 : Nat := 1757535422441459559908891

theorem tailTrace_3422788 : CollatzResearch.WordTrace tailWord_3422788 prefixEnd_3422788 1757535422441459559908891 := by
  unfold tailWord_3422788
  simp only [CollatzResearch.WordTrace]
  refine ⟨62419667161915558247930509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83226222882554077663907345 62419667161915558247930509)
  ·
    refine ⟨23407375185718334342973941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62419667161915558247930509 23407375185718334342973941)
    ·
      refine ⟨2194441423661093844653807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23407375185718334342973941 2194441423661093844653807)
      ·
        refine ⟨3291662135491640766980711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2194441423661093844653807 3291662135491640766980711)
        ·
          refine ⟨4937493203237461150471067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3291662135491640766980711 4937493203237461150471067)
          ·
            refine ⟨7406239804856191725706601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4937493203237461150471067 7406239804856191725706601)
            ·
              refine ⟨5554679853642143794279951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7406239804856191725706601 5554679853642143794279951)
              ·
                refine ⟨8332019780463215691419927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5554679853642143794279951 8332019780463215691419927)
                ·
                  refine ⟨12498029670694823537129891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8332019780463215691419927 12498029670694823537129891)
                  ·
                    refine ⟨18747044506042235305694837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12498029670694823537129891 18747044506042235305694837)
                    ·
                      refine ⟨1757535422441459559908891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18747044506042235305694837 1757535422441459559908891)
                      ·
                        rfl

theorem cell23_3422788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_3422788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3422788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3422788 prefixEnd_3422788 := by exact prefixLift 3422788
  have htrace : WordTrace (prefixWord ++ tailWord_3422788) baseStart_3422788 baseEnd_3422788 := by
    simpa [prefixWord, tailWord_3422788, baseEnd_3422788] using wordTrace_append hprefix tailTrace_3422788
  have hstable : (prefixWord ++ tailWord_3422788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3422788).length < 2 ^ (prefixWord ++ tailWord_3422788).sum := by decide
  have hdescent : baseEnd_3422788 < baseStart_3422788 := by decide
  rcases family_descends (prefixWord ++ tailWord_3422788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3422800 : List Nat := [2, 1, 1, 1, 1, 3, 2, 4, 2, 6]
def baseStart_3422800 : Nat := 118140960795 + 3422800 * 2 ^ 59
def prefixEnd_3422800 : Nat := 4983230072969 + 3 ^ 40 * 3422800 * 2
def baseEnd_3422800 : Nat := 585847194736437837652945

theorem tailTrace_3422800 : CollatzResearch.WordTrace tailWord_3422800 prefixEnd_3422800 585847194736437837652945 := by
  unfold tailWord_3422800
  simp only [CollatzResearch.WordTrace]
  refine ⟨62419885999893821272648927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83226514666525095030198569 62419885999893821272648927)
  ·
    refine ⟨93629828999840731908973391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62419885999893821272648927 93629828999840731908973391)
    ·
      refine ⟨140444743499761097863460087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93629828999840731908973391 140444743499761097863460087)
      ·
        refine ⟨210667115249641646795190131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140444743499761097863460087 210667115249641646795190131)
        ·
          refine ⟨316000672874462470192785197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210667115249641646795190131 316000672874462470192785197)
          ·
            refine ⟨118500252327923426322294449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 316000672874462470192785197 118500252327923426322294449)
            ·
              refine ⟨88875189245942569741720837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118500252327923426322294449 88875189245942569741720837)
              ·
                refine ⟨16664097983614231826572657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88875189245942569741720837 16664097983614231826572657)
                ·
                  refine ⟨12498073487710673869929493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16664097983614231826572657 12498073487710673869929493)
                  ·
                    refine ⟨585847194736437837652945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12498073487710673869929493 585847194736437837652945)
                    ·
                      rfl

theorem cell23_3422800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 4, 2, 6].length) (baseStart_3422800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3422800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3422800 prefixEnd_3422800 := by exact prefixLift 3422800
  have htrace : WordTrace (prefixWord ++ tailWord_3422800) baseStart_3422800 baseEnd_3422800 := by
    simpa [prefixWord, tailWord_3422800, baseEnd_3422800] using wordTrace_append hprefix tailTrace_3422800
  have hstable : (prefixWord ++ tailWord_3422800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3422800).length < 2 ^ (prefixWord ++ tailWord_3422800).sum := by decide
  have hdescent : baseEnd_3422800 < baseStart_3422800 := by decide
  rcases family_descends (prefixWord ++ tailWord_3422800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3422857 : List Nat := [1, 2, 1, 1, 4, 1, 1, 4, 2, 3, 3]
def baseStart_3422857 : Nat := 118140960795 + 3422857 * 2 ^ 59
def prefixEnd_3422857 : Nat := 4983230072969 + 3 ^ 40 * 3422857 * 2
def baseEnd_3422857 : Nat := 1757570852606619789946073

theorem tailTrace_3422857 : CollatzResearch.WordTrace tailWord_3422857 prefixEnd_3422857 1757570852606619789946073 := by
  unfold tailWord_3422857
  simp only [CollatzResearch.WordTrace]
  refine ⟨124841850960581141280122825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83227900640387427520081883 124841850960581141280122825)
  ·
    refine ⟨93631388220435855960092119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124841850960581141280122825 93631388220435855960092119)
    ·
      refine ⟨140447082330653783940138179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93631388220435855960092119 140447082330653783940138179)
      ·
        refine ⟨210670623495980675910207269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140447082330653783940138179 210670623495980675910207269)
        ·
          refine ⟨39500741905496376733163863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 210670623495980675910207269 39500741905496376733163863)
          ·
            refine ⟨59251112858244565099745795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39500741905496376733163863 59251112858244565099745795)
            ·
              refine ⟨88876669287366847649618693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59251112858244565099745795 88876669287366847649618693)
              ·
                refine ⟨16664375491381283934303505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88876669287366847649618693 16664375491381283934303505)
                ·
                  refine ⟨12498281618535962950727629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16664375491381283934303505 12498281618535962950727629)
                  ·
                    refine ⟨4686855606950986106522861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12498281618535962950727629 4686855606950986106522861)
                    ·
                      refine ⟨1757570852606619789946073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4686855606950986106522861 1757570852606619789946073)
                      ·
                        rfl

theorem cell23_3422857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 4, 2, 3, 3].length) (baseStart_3422857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3422857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3422857 prefixEnd_3422857 := by exact prefixLift 3422857
  have htrace : WordTrace (prefixWord ++ tailWord_3422857) baseStart_3422857 baseEnd_3422857 := by
    simpa [prefixWord, tailWord_3422857, baseEnd_3422857] using wordTrace_append hprefix tailTrace_3422857
  have hstable : (prefixWord ++ tailWord_3422857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3422857).length < 2 ^ (prefixWord ++ tailWord_3422857).sum := by decide
  have hdescent : baseEnd_3422857 < baseStart_3422857 := by decide
  rcases family_descends (prefixWord ++ tailWord_3422857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3422877 : List Nat := [1, 4, 2, 1, 1, 1, 2, 2, 4, 5]
def baseStart_3422877 : Nat := 118140960795 + 3422877 * 2 ^ 59
def prefixEnd_3422877 : Nat := 4983230072969 + 3 ^ 40 * 3422877 * 2
def baseEnd_3422877 : Nat := 585860374073236570565327

theorem tailTrace_3422877 : CollatzResearch.WordTrace tailWord_3422877 prefixEnd_3422877 585860374073236570565327 := by
  unfold tailWord_3422877
  simp only [CollatzResearch.WordTrace]
  refine ⟨124842580420508684695850885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83228386947005789797233923 124842580420508684695850885)
  ·
    refine ⟨23407983828845378380472041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124842580420508684695850885 23407983828845378380472041)
    ·
      refine ⟨17555987871634033785354031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23407983828845378380472041 17555987871634033785354031)
      ·
        refine ⟨26333981807451050678031047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17555987871634033785354031 26333981807451050678031047)
        ·
          refine ⟨39500972711176576017046571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26333981807451050678031047 39500972711176576017046571)
          ·
            refine ⟨59251459066764864025569857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39500972711176576017046571 59251459066764864025569857)
            ·
              refine ⟨44438594300073648019177393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59251459066764864025569857 44438594300073648019177393)
              ·
                refine ⟨33328945725055236014383045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44438594300073648019177393 33328945725055236014383045)
                ·
                  refine ⟨6249177323447856752696821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33328945725055236014383045 6249177323447856752696821)
                  ·
                    refine ⟨585860374073236570565327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6249177323447856752696821 585860374073236570565327)
                    ·
                      rfl

theorem cell23_3422877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 2, 4, 5].length) (baseStart_3422877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3422877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3422877 prefixEnd_3422877 := by exact prefixLift 3422877
  have htrace : WordTrace (prefixWord ++ tailWord_3422877) baseStart_3422877 baseEnd_3422877 := by
    simpa [prefixWord, tailWord_3422877, baseEnd_3422877] using wordTrace_append hprefix tailTrace_3422877
  have hstable : (prefixWord ++ tailWord_3422877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3422877).length < 2 ^ (prefixWord ++ tailWord_3422877).sum := by decide
  have hdescent : baseEnd_3422877 < baseStart_3422877 := by decide
  rcases family_descends (prefixWord ++ tailWord_3422877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3422884 : List Nat := [2, 3, 1, 2, 2, 1, 1, 2, 2, 5, 2]
def baseStart_3422884 : Nat := 118140960795 + 3422884 * 2 ^ 59
def prefixEnd_3422884 : Nat := 4983230072969 + 3 ^ 40 * 3422884 * 2
def baseEnd_3422884 : Nat := 1757584716584291184308449

theorem tailTrace_3422884 : CollatzResearch.WordTrace tailWord_3422884 prefixEnd_3422884 1757584716584291184308449 := by
  unfold tailWord_3422884
  simp only [CollatzResearch.WordTrace]
  refine ⟨62421417865741662445677853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83228557154322216594237137 62421417865741662445677853)
  ·
    refine ⟨23408031699653123417129195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62421417865741662445677853 23408031699653123417129195)
    ·
      refine ⟨35112047549479685125693793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23408031699653123417129195 35112047549479685125693793)
      ·
        refine ⟨26334035662109763844270345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35112047549479685125693793 26334035662109763844270345)
        ·
          refine ⟨19750526746582322883202759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26334035662109763844270345 19750526746582322883202759)
          ·
            refine ⟨29625790119873484324804139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19750526746582322883202759 29625790119873484324804139)
            ·
              refine ⟨44438685179810226487206209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29625790119873484324804139 44438685179810226487206209)
              ·
                refine ⟨33329013884857669865404657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44438685179810226487206209 33329013884857669865404657)
                ·
                  refine ⟨24996760413643252399053493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33329013884857669865404657 24996760413643252399053493)
                  ·
                    refine ⟨2343446288779054912411265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24996760413643252399053493 2343446288779054912411265)
                    ·
                      refine ⟨1757584716584291184308449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2343446288779054912411265 1757584716584291184308449)
                      ·
                        rfl

theorem cell23_3422884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 2, 2, 5, 2].length) (baseStart_3422884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3422884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3422884 prefixEnd_3422884 := by exact prefixLift 3422884
  have htrace : WordTrace (prefixWord ++ tailWord_3422884) baseStart_3422884 baseEnd_3422884 := by
    simpa [prefixWord, tailWord_3422884, baseEnd_3422884] using wordTrace_append hprefix tailTrace_3422884
  have hstable : (prefixWord ++ tailWord_3422884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3422884).length < 2 ^ (prefixWord ++ tailWord_3422884).sum := by decide
  have hdescent : baseEnd_3422884 < baseStart_3422884 := by decide
  rcases family_descends (prefixWord ++ tailWord_3422884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3422917 : List Nat := [1, 3, 1, 1, 1, 1, 2, 1, 5, 4, 3]
def baseStart_3422917 : Nat := 118140960795 + 3422917 * 2 ^ 59
def prefixEnd_3422917 : Nat := 4983230072969 + 3 ^ 40 * 3422917 * 2
def baseEnd_3422917 : Nat := 1757601661445889555195797

theorem tailTrace_3422917 : CollatzResearch.WordTrace tailWord_3422917 prefixEnd_3422917 1757601661445889555195797 := by
  unfold tailWord_3422917
  simp only [CollatzResearch.WordTrace]
  refine ⟨124844039340363771527307005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83229359560242514351538003 124844039340363771527307005)
  ·
    refine ⟨46816514752636414322740127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124844039340363771527307005 46816514752636414322740127)
    ·
      refine ⟨70224772128954621484110191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46816514752636414322740127 70224772128954621484110191)
      ·
        refine ⟨105337158193431932226165287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70224772128954621484110191 105337158193431932226165287)
        ·
          refine ⟨158005737290147898339247931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105337158193431932226165287 158005737290147898339247931)
          ·
            refine ⟨237008605935221847508871897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158005737290147898339247931 237008605935221847508871897)
            ·
              refine ⟨177756454451416385631653923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 237008605935221847508871897 177756454451416385631653923)
              ·
                refine ⟨266634681677124578447480885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 177756454451416385631653923 266634681677124578447480885)
                ·
                  refine ⟨24997001407230429229451333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 266634681677124578447480885 24997001407230429229451333)
                  ·
                    refine ⟨4686937763855705480522125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24997001407230429229451333 4686937763855705480522125)
                    ·
                      refine ⟨1757601661445889555195797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4686937763855705480522125 1757601661445889555195797)
                      ·
                        rfl

theorem cell23_3422917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 5, 4, 3].length) (baseStart_3422917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3422917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3422917 prefixEnd_3422917 := by exact prefixLift 3422917
  have htrace : WordTrace (prefixWord ++ tailWord_3422917) baseStart_3422917 baseEnd_3422917 := by
    simpa [prefixWord, tailWord_3422917, baseEnd_3422917] using wordTrace_append hprefix tailTrace_3422917
  have hstable : (prefixWord ++ tailWord_3422917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3422917).length < 2 ^ (prefixWord ++ tailWord_3422917).sum := by decide
  have hdescent : baseEnd_3422917 < baseStart_3422917 := by decide
  rcases family_descends (prefixWord ++ tailWord_3422917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3422958 : List Nat := [4, 1, 2, 1, 1, 3, 3, 3, 1, 4]
def baseStart_3422958 : Nat := 118140960795 + 3422958 * 2 ^ 59
def prefixEnd_3422958 : Nat := 4983230072969 + 3 ^ 40 * 3422958 * 2
def baseEnd_3422958 : Nat := 585874238050907964927703

theorem tailTrace_3422958 : CollatzResearch.WordTrace tailWord_3422958 prefixEnd_3422958 585874238050907964927703 := by
  unfold tailWord_3422958
  simp only [CollatzResearch.WordTrace]
  refine ⟨15605691841651904441193691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83230356488810157019699685 15605691841651904441193691)
  ·
    refine ⟨23408537762477856661790537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15605691841651904441193691 23408537762477856661790537)
    ·
      refine ⟨17556403321858392496342903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23408537762477856661790537 17556403321858392496342903)
      ·
        refine ⟨26334604982787588744514355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17556403321858392496342903 26334604982787588744514355)
        ·
          refine ⟨39501907474181383116771533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26334604982787588744514355 39501907474181383116771533)
          ·
            refine ⟨14813215302818018668789325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39501907474181383116771533 14813215302818018668789325)
            ·
              refine ⟨5554955738556757000795997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14813215302818018668789325 5554955738556757000795997)
              ·
                refine ⟨2083108401958783875298499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5554955738556757000795997 2083108401958783875298499)
                ·
                  refine ⟨3124662602938175812947749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2083108401958783875298499 3124662602938175812947749)
                  ·
                    refine ⟨585874238050907964927703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3124662602938175812947749 585874238050907964927703)
                    ·
                      rfl

theorem cell23_3422958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 3, 3, 1, 4].length) (baseStart_3422958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3422958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3422958 prefixEnd_3422958 := by exact prefixLift 3422958
  have htrace : WordTrace (prefixWord ++ tailWord_3422958) baseStart_3422958 baseEnd_3422958 := by
    simpa [prefixWord, tailWord_3422958, baseEnd_3422958] using wordTrace_append hprefix tailTrace_3422958
  have hstable : (prefixWord ++ tailWord_3422958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3422958).length < 2 ^ (prefixWord ++ tailWord_3422958).sum := by decide
  have hdescent : baseEnd_3422958 < baseStart_3422958 := by decide
  rcases family_descends (prefixWord ++ tailWord_3422958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3422965 : List Nat := [1, 3, 6, 1, 1, 1, 1, 2, 2, 1, 4]
def baseStart_3422965 : Nat := 118140960795 + 3422965 * 2 ^ 59
def prefixEnd_3422965 : Nat := 4983230072969 + 3 ^ 40 * 3422965 * 2
def baseEnd_3422965 : Nat := 1757626308517305367395577

theorem tailTrace_3422965 : CollatzResearch.WordTrace tailWord_3422965 prefixEnd_3422965 1757626308517305367395577 := by
  unfold tailWord_3422965
  simp only [CollatzResearch.WordTrace]
  refine ⟨124845790044189875725054349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83230526696126583816702899 124845790044189875725054349)
  ·
    refine ⟨46817171266571203396895381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124845790044189875725054349 46817171266571203396895381)
    ·
      refine ⟨2194554903120525159229471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 46817171266571203396895381 2194554903120525159229471)
      ·
        refine ⟨3291832354680787738844207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2194554903120525159229471 3291832354680787738844207)
        ·
          refine ⟨4937748532021181608266311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3291832354680787738844207 4937748532021181608266311)
          ·
            refine ⟨7406622798031772412399467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4937748532021181608266311 7406622798031772412399467)
            ·
              refine ⟨11109934197047658618599201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7406622798031772412399467 11109934197047658618599201)
              ·
                refine ⟨8332450647785743963949401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11109934197047658618599201 8332450647785743963949401)
                ·
                  refine ⟨6249337985839307972962051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8332450647785743963949401 6249337985839307972962051)
                  ·
                    refine ⟨9374006978758961959443077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6249337985839307972962051 9374006978758961959443077)
                    ·
                      refine ⟨1757626308517305367395577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9374006978758961959443077 1757626308517305367395577)
                      ·
                        rfl

theorem cell23_3422965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_3422965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3422965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3422965 prefixEnd_3422965 := by exact prefixLift 3422965
  have htrace : WordTrace (prefixWord ++ tailWord_3422965) baseStart_3422965 baseEnd_3422965 := by
    simpa [prefixWord, tailWord_3422965, baseEnd_3422965] using wordTrace_append hprefix tailTrace_3422965
  have hstable : (prefixWord ++ tailWord_3422965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3422965).length < 2 ^ (prefixWord ++ tailWord_3422965).sum := by decide
  have hdescent : baseEnd_3422965 < baseStart_3422965 := by decide
  rcases family_descends (prefixWord ++ tailWord_3422965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3422967 : List Nat := [1, 1, 3, 1, 1, 1, 3, 2, 5, 5]
def baseStart_3422967 : Nat := 118140960795 + 3422967 * 2 ^ 59
def prefixEnd_3422967 : Nat := 4983230072969 + 3 ^ 40 * 3422967 * 2
def baseEnd_3422967 : Nat := 585875778492871453190189

theorem tailTrace_3422967 : CollatzResearch.WordTrace tailWord_3422967 prefixEnd_3422967 585875778492871453190189 := by
  unfold tailWord_3422967
  simp only [CollatzResearch.WordTrace]
  refine ⟨124845862990182630066627155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83230575326788420044418103 124845862990182630066627155)
  ·
    refine ⟨187268794485273945099940733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124845862990182630066627155 187268794485273945099940733)
    ·
      refine ⟨70225797931977729412477775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187268794485273945099940733 70225797931977729412477775)
      ·
        refine ⟨105338696897966594118716663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70225797931977729412477775 105338696897966594118716663)
        ·
          refine ⟨158008045346949891178074995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105338696897966594118716663 158008045346949891178074995)
          ·
            refine ⟨237012068020424836767112493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158008045346949891178074995 237012068020424836767112493)
            ·
              refine ⟨88879525507659313787667185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 237012068020424836767112493 88879525507659313787667185)
              ·
                refine ⟨66659644130744485340750389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88879525507659313787667185 66659644130744485340750389)
                ·
                  refine ⟨6249341637257295500695349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 66659644130744485340750389 6249341637257295500695349)
                  ·
                    refine ⟨585875778492871453190189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6249341637257295500695349 585875778492871453190189)
                    ·
                      rfl

theorem cell23_3422967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 5, 5].length) (baseStart_3422967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3422967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3422967 prefixEnd_3422967 := by exact prefixLift 3422967
  have htrace : WordTrace (prefixWord ++ tailWord_3422967) baseStart_3422967 baseEnd_3422967 := by
    simpa [prefixWord, tailWord_3422967, baseEnd_3422967] using wordTrace_append hprefix tailTrace_3422967
  have hstable : (prefixWord ++ tailWord_3422967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3422967).length < 2 ^ (prefixWord ++ tailWord_3422967).sum := by decide
  have hdescent : baseEnd_3422967 < baseStart_3422967 := by decide
  rcases family_descends (prefixWord ++ tailWord_3422967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3422977 : List Nat := [1, 2, 4, 1, 1, 1, 1, 2, 2, 1, 7]
def baseStart_3422977 : Nat := 118140960795 + 3422977 * 2 ^ 59
def prefixEnd_3422977 : Nat := 4983230072969 + 3 ^ 40 * 3422977 * 2
def baseEnd_3422977 : Nat := 1757632470285159320445521

theorem tailTrace_3422977 : CollatzResearch.WordTrace tailWord_3422977 prefixEnd_3422977 1757632470285159320445521 := by
  unfold tailWord_3422977
  simp only [CollatzResearch.WordTrace]
  refine ⟨124846227720146401774491185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83230818480097601182994123 124846227720146401774491185)
  ·
    refine ⟨93634670790109801330868389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124846227720146401774491185 93634670790109801330868389)
    ·
      refine ⟨17556500773145587749537823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93634670790109801330868389 17556500773145587749537823)
      ·
        refine ⟨26334751159718381624306735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17556500773145587749537823 26334751159718381624306735)
        ·
          refine ⟨39502126739577572436460103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26334751159718381624306735 39502126739577572436460103)
          ·
            refine ⟨59253190109366358654690155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39502126739577572436460103 59253190109366358654690155)
            ·
              refine ⟨88879785164049537982035233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59253190109366358654690155 88879785164049537982035233)
              ·
                refine ⟨66659838873037153486526425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88879785164049537982035233 66659838873037153486526425)
                ·
                  refine ⟨49994879154777865114894819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66659838873037153486526425 49994879154777865114894819)
                  ·
                    refine ⟨74992318732166797672342229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49994879154777865114894819 74992318732166797672342229)
                    ·
                      refine ⟨1757632470285159320445521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 74992318732166797672342229 1757632470285159320445521)
                      ·
                        rfl

theorem cell23_3422977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 2, 1, 7].length) (baseStart_3422977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3422977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3422977 prefixEnd_3422977 := by exact prefixLift 3422977
  have htrace : WordTrace (prefixWord ++ tailWord_3422977) baseStart_3422977 baseEnd_3422977 := by
    simpa [prefixWord, tailWord_3422977, baseEnd_3422977] using wordTrace_append hprefix tailTrace_3422977
  have hstable : (prefixWord ++ tailWord_3422977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3422977).length < 2 ^ (prefixWord ++ tailWord_3422977).sum := by decide
  have hdescent : baseEnd_3422977 < baseStart_3422977 := by decide
  rcases family_descends (prefixWord ++ tailWord_3422977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3422987 : List Nat := [1, 1, 1, 1, 5, 1, 1, 1, 2, 5, 4]
def baseStart_3422987 : Nat := 118140960795 + 3422987 * 2 ^ 59
def prefixEnd_3422987 : Nat := 4983230072969 + 3 ^ 40 * 3422987 * 2
def baseEnd_3422987 : Nat := 1757637605091704281320475

theorem tailTrace_3422987 : CollatzResearch.WordTrace tailWord_3422987 prefixEnd_3422987 1757637605091704281320475 := by
  unfold tailWord_3422987
  simp only [CollatzResearch.WordTrace]
  refine ⟨124846592450110173482355215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83231061633406782321570143 124846592450110173482355215)
  ·
    refine ⟨187269888675165260223532823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124846592450110173482355215 187269888675165260223532823)
    ·
      refine ⟨280904833012747890335299235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187269888675165260223532823 280904833012747890335299235)
      ·
        refine ⟨421357249519121835502948853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280904833012747890335299235 421357249519121835502948853)
        ·
          refine ⟨39502242142417672078401455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 421357249519121835502948853 39502242142417672078401455)
          ·
            refine ⟨59253363213626508117602183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39502242142417672078401455 59253363213626508117602183)
            ·
              refine ⟨88880044820439762176403275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59253363213626508117602183 88880044820439762176403275)
              ·
                refine ⟨133320067230659643264604913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88880044820439762176403275 133320067230659643264604913)
                ·
                  refine ⟨99990050422994732448453685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 133320067230659643264604913 99990050422994732448453685)
                  ·
                    refine ⟨9374067227155756167042533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 99990050422994732448453685 9374067227155756167042533)
                    ·
                      refine ⟨1757637605091704281320475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9374067227155756167042533 1757637605091704281320475)
                      ·
                        rfl

theorem cell23_3422987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 5, 4].length) (baseStart_3422987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3422987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3422987 prefixEnd_3422987 := by exact prefixLift 3422987
  have htrace : WordTrace (prefixWord ++ tailWord_3422987) baseStart_3422987 baseEnd_3422987 := by
    simpa [prefixWord, tailWord_3422987, baseEnd_3422987] using wordTrace_append hprefix tailTrace_3422987
  have hstable : (prefixWord ++ tailWord_3422987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3422987).length < 2 ^ (prefixWord ++ tailWord_3422987).sum := by decide
  have hdescent : baseEnd_3422987 < baseStart_3422987 := by decide
  rcases family_descends (prefixWord ++ tailWord_3422987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3423008 : List Nat := [2, 1, 1, 5, 1, 3, 2, 1, 2, 3, 2]
def baseStart_3423008 : Nat := 118140960795 + 3423008 * 2 ^ 59
def prefixEnd_3423008 : Nat := 4983230072969 + 3 ^ 40 * 3423008 * 2
def baseEnd_3423008 : Nat := 1757648388185448699157879

theorem tailTrace_3423008 : CollatzResearch.WordTrace tailWord_3423008 prefixEnd_3423008 1757648388185448699157879 := by
  unfold tailWord_3423008
  simp only [CollatzResearch.WordTrace]
  refine ⟨62423679191517047034434839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83231572255356062712579785 62423679191517047034434839)
  ·
    refine ⟨93635518787275570551652259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62423679191517047034434839 93635518787275570551652259)
    ·
      refine ⟨140453278180913355827478389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93635518787275570551652259 140453278180913355827478389)
      ·
        refine ⟨13167494829460627108826099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 140453278180913355827478389 13167494829460627108826099)
        ·
          refine ⟨19751242244190940663239149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13167494829460627108826099 19751242244190940663239149)
          ·
            refine ⟨7406715841571602748714681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19751242244190940663239149 7406715841571602748714681)
            ·
              refine ⟨5555036881178702061536011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7406715841571602748714681 5555036881178702061536011)
              ·
                refine ⟨8332555321768053092304017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5555036881178702061536011 8332555321768053092304017)
                ·
                  refine ⟨6249416491326039819228013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8332555321768053092304017 6249416491326039819228013)
                  ·
                    refine ⟨2343531184247264932210505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6249416491326039819228013 2343531184247264932210505)
                    ·
                      refine ⟨1757648388185448699157879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2343531184247264932210505 1757648388185448699157879)
                      ·
                        rfl

theorem cell23_3423008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 2, 1, 2, 3, 2].length) (baseStart_3423008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3423008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3423008 prefixEnd_3423008 := by exact prefixLift 3423008
  have htrace : WordTrace (prefixWord ++ tailWord_3423008) baseStart_3423008 baseEnd_3423008 := by
    simpa [prefixWord, tailWord_3423008, baseEnd_3423008] using wordTrace_append hprefix tailTrace_3423008
  have hstable : (prefixWord ++ tailWord_3423008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3423008).length < 2 ^ (prefixWord ++ tailWord_3423008).sum := by decide
  have hdescent : baseEnd_3423008 < baseStart_3423008 := by decide
  rcases family_descends (prefixWord ++ tailWord_3423008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3423027 : List Nat := [1, 1, 1, 2, 6, 12]
def baseStart_3423027 : Nat := 118140960795 + 3423027 * 2 ^ 59
def prefixEnd_3423027 : Nat := 4983230072969 + 3 ^ 40 * 3423027 * 2
def baseEnd_3423027 : Nat := 7233161087727918209137

theorem tailTrace_3423027 : CollatzResearch.WordTrace tailWord_3423027 prefixEnd_3423027 7233161087727918209137 := by
  unfold tailWord_3423027
  simp only [CollatzResearch.WordTrace]
  refine ⟨124848051369965260313811335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83232034246643506875874223 124848051369965260313811335)
  ·
    refine ⟨187272077054947890470717003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124848051369965260313811335 187272077054947890470717003)
    ·
      refine ⟨280908115582421835706075505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187272077054947890470717003 280908115582421835706075505)
      ·
        refine ⟨210681086686816376779556629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 280908115582421835706075505 210681086686816376779556629)
        ·
          refine ⟨9875675938444517661541717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 210681086686816376779556629 9875675938444517661541717)
          ·
            refine ⟨7233161087727918209137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 9875675938444517661541717 7233161087727918209137)
            ·
              rfl

theorem cell23_3423027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 12].length) (baseStart_3423027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3423027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3423027 prefixEnd_3423027 := by exact prefixLift 3423027
  have htrace : WordTrace (prefixWord ++ tailWord_3423027) baseStart_3423027 baseEnd_3423027 := by
    simpa [prefixWord, tailWord_3423027, baseEnd_3423027] using wordTrace_append hprefix tailTrace_3423027
  have hstable : (prefixWord ++ tailWord_3423027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3423027).length < 2 ^ (prefixWord ++ tailWord_3423027).sum := by decide
  have hdescent : baseEnd_3423027 < baseStart_3423027 := by decide
  rcases family_descends (prefixWord ++ tailWord_3423027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3423031 : List Nat := [1, 1, 3, 1, 2, 1, 6, 2, 2, 4]
def baseStart_3423031 : Nat := 118140960795 + 3423031 * 2 ^ 59
def prefixEnd_3423031 : Nat := 4983230072969 + 3 ^ 40 * 3423031 * 2
def baseEnd_3423031 : Nat := 585886732746834036390091

theorem tailTrace_3423031 : CollatzResearch.WordTrace tailWord_3423031 prefixEnd_3423031 585886732746834036390091 := by
  unfold tailWord_3423031
  simp only [CollatzResearch.WordTrace]
  refine ⟨124848197261950768996956947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83232131507967179331304631 124848197261950768996956947)
  ·
    refine ⟨187272295892926153495435421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124848197261950768996956947 187272295892926153495435421)
    ·
      refine ⟨70227110959847307560788283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187272295892926153495435421 70227110959847307560788283)
      ·
        refine ⟨105340666439770961341182425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70227110959847307560788283 105340666439770961341182425)
        ·
          refine ⟨79005499829828221005886819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105340666439770961341182425 79005499829828221005886819)
          ·
            refine ⟨118508249744742331508830229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79005499829828221005886819 118508249744742331508830229)
            ·
              refine ⟨5555074206784796789476417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 118508249744742331508830229 5555074206784796789476417)
              ·
                refine ⟨4166305655088597592107313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5555074206784796789476417 4166305655088597592107313)
                ·
                  refine ⟨3124729241316448194080485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4166305655088597592107313 3124729241316448194080485)
                  ·
                    refine ⟨585886732746834036390091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3124729241316448194080485 585886732746834036390091)
                    ·
                      rfl

theorem cell23_3423031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 6, 2, 2, 4].length) (baseStart_3423031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3423031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3423031 prefixEnd_3423031 := by exact prefixLift 3423031
  have htrace : WordTrace (prefixWord ++ tailWord_3423031) baseStart_3423031 baseEnd_3423031 := by
    simpa [prefixWord, tailWord_3423031, baseEnd_3423031] using wordTrace_append hprefix tailTrace_3423031
  have hstable : (prefixWord ++ tailWord_3423031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3423031).length < 2 ^ (prefixWord ++ tailWord_3423031).sum := by decide
  have hdescent : baseEnd_3423031 < baseStart_3423031 := by decide
  rcases family_descends (prefixWord ++ tailWord_3423031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3423071 : List Nat := [1, 1, 2, 3, 1, 3, 2, 2, 4, 1, 3]
def baseStart_3423071 : Nat := 118140960795 + 3423071 * 2 ^ 59
def prefixEnd_3423071 : Nat := 4983230072969 + 3 ^ 40 * 3423071 * 2
def baseEnd_3423071 : Nat := 1757680737466681952670089

theorem tailTrace_3423071 : CollatzResearch.WordTrace tailWord_3423071 prefixEnd_3423071 1757680737466681952670089 := by
  unfold tailWord_3423071
  simp only [CollatzResearch.WordTrace]
  refine ⟨124849656181805855828413067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83233104121203903885608711 124849656181805855828413067)
  ·
    refine ⟨187274484272708783742619601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124849656181805855828413067 187274484272708783742619601)
    ·
      refine ⟨140455863204531587806964701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187274484272708783742619601 140455863204531587806964701)
      ·
        refine ⟨52670948701699345427611763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140455863204531587806964701 52670948701699345427611763)
        ·
          refine ⟨79006423052549018141417645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52670948701699345427611763 79006423052549018141417645)
          ·
            refine ⟨29627408644705881803031617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79006423052549018141417645 29627408644705881803031617)
            ·
              refine ⟨22220556483529411352273713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29627408644705881803031617 22220556483529411352273713)
              ·
                refine ⟨16665417362647058514205285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22220556483529411352273713 16665417362647058514205285)
                ·
                  refine ⟨3124765755496323471413491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16665417362647058514205285 3124765755496323471413491)
                  ·
                    refine ⟨4687148633244485207120237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3124765755496323471413491 4687148633244485207120237)
                    ·
                      refine ⟨1757680737466681952670089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4687148633244485207120237 1757680737466681952670089)
                      ·
                        rfl

theorem cell23_3423071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 2, 4, 1, 3].length) (baseStart_3423071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3423071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3423071 prefixEnd_3423071 := by exact prefixLift 3423071
  have htrace : WordTrace (prefixWord ++ tailWord_3423071) baseStart_3423071 baseEnd_3423071 := by
    simpa [prefixWord, tailWord_3423071, baseEnd_3423071] using wordTrace_append hprefix tailTrace_3423071
  have hstable : (prefixWord ++ tailWord_3423071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3423071).length < 2 ^ (prefixWord ++ tailWord_3423071).sum := by decide
  have hdescent : baseEnd_3423071 < baseStart_3423071 := by decide
  rcases family_descends (prefixWord ++ tailWord_3423071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3423075 : List Nat := [1, 1, 1, 5, 3, 3, 2, 1, 1, 2, 3]
def baseStart_3423075 : Nat := 118140960795 + 3423075 * 2 ^ 59
def prefixEnd_3423075 : Nat := 4983230072969 + 3 ^ 40 * 3423075 * 2
def baseEnd_3423075 : Nat := 1757682791389299937020071

theorem tailTrace_3423075 : CollatzResearch.WordTrace tailWord_3423075 prefixEnd_3423075 1757682791389299937020071 := by
  unfold tailWord_3423075
  simp only [CollatzResearch.WordTrace]
  refine ⟨124849802073791364511558679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83233201382527576341039119 124849802073791364511558679)
  ·
    refine ⟨187274703110687046767338019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124849802073791364511558679 187274703110687046767338019)
    ·
      refine ⟨280912054666030570151007029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187274703110687046767338019 280912054666030570151007029)
      ·
        refine ⟨26335505124940365951656909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 280912054666030570151007029 26335505124940365951656909)
        ·
          refine ⟨9875814421852637231871341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26335505124940365951656909 9875814421852637231871341)
          ·
            refine ⟨3703430408194738961951753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9875814421852637231871341 3703430408194738961951753)
            ·
              refine ⟨2777572806146054221463815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3703430408194738961951753 2777572806146054221463815)
              ·
                refine ⟨4166359209219081332195723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2777572806146054221463815 4166359209219081332195723)
                ·
                  refine ⟨6249538813828621998293585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4166359209219081332195723 6249538813828621998293585)
                  ·
                    refine ⟨4687154110371466498720189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6249538813828621998293585 4687154110371466498720189)
                    ·
                      refine ⟨1757682791389299937020071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4687154110371466498720189 1757682791389299937020071)
                      ·
                        rfl

theorem cell23_3423075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 2, 1, 1, 2, 3].length) (baseStart_3423075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3423075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3423075 prefixEnd_3423075 := by exact prefixLift 3423075
  have htrace : WordTrace (prefixWord ++ tailWord_3423075) baseStart_3423075 baseEnd_3423075 := by
    simpa [prefixWord, tailWord_3423075, baseEnd_3423075] using wordTrace_append hprefix tailTrace_3423075
  have hstable : (prefixWord ++ tailWord_3423075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3423075).length < 2 ^ (prefixWord ++ tailWord_3423075).sum := by decide
  have hdescent : baseEnd_3423075 < baseStart_3423075 := by decide
  rcases family_descends (prefixWord ++ tailWord_3423075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3423088 : List Nat := [2, 1, 1, 1, 4, 1, 5, 2, 2, 1, 3]
def baseStart_3423088 : Nat := 118140960795 + 3423088 * 2 ^ 59
def prefixEnd_3423088 : Nat := 4983230072969 + 3 ^ 40 * 3423088 * 2
def baseEnd_3423088 : Nat := 1757689466637808386157511

theorem tailTrace_3423088 : CollatzResearch.WordTrace tailWord_3423088 prefixEnd_3423088 1757689466637808386157511 := by
  unfold tailWord_3423088
  simp only [CollatzResearch.WordTrace]
  refine ⟨62425138111372133865890959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83233517481829511821187945 62425138111372133865890959)
  ·
    refine ⟨93637707167058200798836439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62425138111372133865890959 93637707167058200798836439)
    ·
      refine ⟨140456560750587301198254659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93637707167058200798836439 140456560750587301198254659)
      ·
        refine ⟨210684841125880951797381989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140456560750587301198254659 210684841125880951797381989)
        ·
          refine ⟨39503407711102678462009123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 210684841125880951797381989 39503407711102678462009123)
          ·
            refine ⟨59255111566654017693013685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39503407711102678462009123 59255111566654017693013685)
            ·
              refine ⟨5555166709373814158720033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 59255111566654017693013685 5555166709373814158720033)
              ·
                refine ⟨4166375032030360619040025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5555166709373814158720033 4166375032030360619040025)
                ·
                  refine ⟨3124781274022770464280019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4166375032030360619040025 3124781274022770464280019)
                  ·
                    refine ⟨4687171911034155696420029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3124781274022770464280019 4687171911034155696420029)
                    ·
                      refine ⟨1757689466637808386157511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4687171911034155696420029 1757689466637808386157511)
                      ·
                        rfl

theorem cell23_3423088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 5, 2, 2, 1, 3].length) (baseStart_3423088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3423088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3423088 prefixEnd_3423088 := by exact prefixLift 3423088
  have htrace : WordTrace (prefixWord ++ tailWord_3423088) baseStart_3423088 baseEnd_3423088 := by
    simpa [prefixWord, tailWord_3423088, baseEnd_3423088] using wordTrace_append hprefix tailTrace_3423088
  have hstable : (prefixWord ++ tailWord_3423088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3423088).length < 2 ^ (prefixWord ++ tailWord_3423088).sum := by decide
  have hdescent : baseEnd_3423088 < baseStart_3423088 := by decide
  rcases family_descends (prefixWord ++ tailWord_3423088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3423102 : List Nat := [4, 2, 3, 1, 3, 1, 1, 1, 1, 2, 4]
def baseStart_3423102 : Nat := 118140960795 + 3423102 * 2 ^ 59
def prefixEnd_3423102 : Nat := 4983230072969 + 3 ^ 40 * 3423102 * 2
def baseEnd_3423102 : Nat := 1757696655366971331382447

theorem tailTrace_3423102 : CollatzResearch.WordTrace tailWord_3423102 prefixEnd_3423102 1757696655366971331382447 := by
  unfold tailWord_3423102
  simp only [CollatzResearch.WordTrace]
  refine ⟨15606348355586693515348945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83233857896462365415194373 15606348355586693515348945)
  ·
    refine ⟨11704761266690020136511709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15606348355586693515348945 11704761266690020136511709)
    ·
      refine ⟨4389285475008757551191891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11704761266690020136511709 4389285475008757551191891)
      ·
        refine ⟨6583928212513136326787837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4389285475008757551191891 6583928212513136326787837)
        ·
          refine ⟨2468973079692426122545439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6583928212513136326787837 2468973079692426122545439)
          ·
            refine ⟨3703459619538639183818159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2468973079692426122545439 3703459619538639183818159)
            ·
              refine ⟨5555189429307958775727239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3703459619538639183818159 5555189429307958775727239)
              ·
                refine ⟨8332784143961938163590859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5555189429307958775727239 8332784143961938163590859)
                ·
                  refine ⟨12499176215942907245386289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8332784143961938163590859 12499176215942907245386289)
                  ·
                    refine ⟨9374382161957180434039717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12499176215942907245386289 9374382161957180434039717)
                    ·
                      refine ⟨1757696655366971331382447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9374382161957180434039717 1757696655366971331382447)
                      ·
                        rfl

theorem cell23_3423102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 1, 1, 1, 2, 4].length) (baseStart_3423102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3423102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3423102 prefixEnd_3423102 := by exact prefixLift 3423102
  have htrace : WordTrace (prefixWord ++ tailWord_3423102) baseStart_3423102 baseEnd_3423102 := by
    simpa [prefixWord, tailWord_3423102, baseEnd_3423102] using wordTrace_append hprefix tailTrace_3423102
  have hstable : (prefixWord ++ tailWord_3423102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3423102).length < 2 ^ (prefixWord ++ tailWord_3423102).sum := by decide
  have hdescent : baseEnd_3423102 < baseStart_3423102 := by decide
  rcases family_descends (prefixWord ++ tailWord_3423102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3423171 : List Nat := [1, 1, 1, 3, 1, 1, 2, 4, 2, 5, 2]
def baseStart_3423171 : Nat := 118140960795 + 3423171 * 2 ^ 59
def prefixEnd_3423171 : Nat := 4983230072969 + 3 ^ 40 * 3423171 * 2
def baseEnd_3423171 : Nat := 1757732085532131561419629

theorem tailTrace_3423171 : CollatzResearch.WordTrace tailWord_3423171 prefixEnd_3423171 1757732085532131561419629 := by
  unfold tailWord_3423171
  simp only [CollatzResearch.WordTrace]
  refine ⟨124853303481443572907053367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83235535654295715271368911 124853303481443572907053367)
  ·
    refine ⟨187279955222165359360580051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124853303481443572907053367 187279955222165359360580051)
    ·
      refine ⟨280919932833248039040870077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187279955222165359360580051 280919932833248039040870077)
      ·
        refine ⟨105344974812468014640326279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 280919932833248039040870077 105344974812468014640326279)
        ·
          refine ⟨158017462218702021960489419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105344974812468014640326279 158017462218702021960489419)
          ·
            refine ⟨237026193328053032940734129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158017462218702021960489419 237026193328053032940734129)
            ·
              refine ⟨177769644996039774705550597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 237026193328053032940734129 177769644996039774705550597)
              ·
                refine ⟨33331808436757457757290737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 177769644996039774705550597 33331808436757457757290737)
                ·
                  refine ⟨24998856327568093317968053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33331808436757457757290737 24998856327568093317968053)
                  ·
                    refine ⟨2343642780709508748559505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24998856327568093317968053 2343642780709508748559505)
                    ·
                      refine ⟨1757732085532131561419629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2343642780709508748559505 1757732085532131561419629)
                      ·
                        rfl

theorem cell23_3423171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 2, 5, 2].length) (baseStart_3423171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3423171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3423171 prefixEnd_3423171 := by exact prefixLift 3423171
  have htrace : WordTrace (prefixWord ++ tailWord_3423171) baseStart_3423171 baseEnd_3423171 := by
    simpa [prefixWord, tailWord_3423171, baseEnd_3423171] using wordTrace_append hprefix tailTrace_3423171
  have hstable : (prefixWord ++ tailWord_3423171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3423171).length < 2 ^ (prefixWord ++ tailWord_3423171).sum := by decide
  have hdescent : baseEnd_3423171 < baseStart_3423171 := by decide
  rcases family_descends (prefixWord ++ tailWord_3423171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3423202 : List Nat := [3, 3, 3, 1, 1, 1, 4, 2, 5]
def baseStart_3423202 : Nat := 118140960795 + 3423202 * 2 ^ 59
def prefixEnd_3423202 : Nat := 4983230072969 + 3 ^ 40 * 3423202 * 2
def baseEnd_3423202 : Nat := 195305333714713437792443

theorem tailTrace_3423202 : CollatzResearch.WordTrace tailWord_3423202 prefixEnd_3423202 195305333714713437792443 := by
  unfold tailWord_3423202
  simp only [CollatzResearch.WordTrace]
  refine ⟨31213608536082816300357965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83236289429554176800954573 31213608536082816300357965)
  ·
    refine ⟨11705103201031056112634237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31213608536082816300357965 11705103201031056112634237)
    ·
      refine ⟨4389413700386646042237839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11705103201031056112634237 4389413700386646042237839)
      ·
        refine ⟨6584120550579969063356759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4389413700386646042237839 6584120550579969063356759)
        ·
          refine ⟨9876180825869953595035139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6584120550579969063356759 9876180825869953595035139)
          ·
            refine ⟨14814271238804930392552709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9876180825869953595035139 14814271238804930392552709)
            ·
              refine ⟨2777675857275924448603633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14814271238804930392552709 2777675857275924448603633)
              ·
                refine ⟨2083256892956943336452725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2777675857275924448603633 2083256892956943336452725)
                ·
                  refine ⟨195305333714713437792443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2083256892956943336452725 195305333714713437792443)
                  ·
                    rfl

theorem cell23_3423202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 4, 2, 5].length) (baseStart_3423202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3423202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3423202 prefixEnd_3423202 := by exact prefixLift 3423202
  have htrace : WordTrace (prefixWord ++ tailWord_3423202) baseStart_3423202 baseEnd_3423202 := by
    simpa [prefixWord, tailWord_3423202, baseEnd_3423202] using wordTrace_append hprefix tailTrace_3423202
  have hstable : (prefixWord ++ tailWord_3423202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3423202).length < 2 ^ (prefixWord ++ tailWord_3423202).sum := by decide
  have hdescent : baseEnd_3423202 < baseStart_3423202 := by decide
  rcases family_descends (prefixWord ++ tailWord_3423202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3423224 : List Nat := [2, 1, 2, 1, 1, 3, 1, 2, 10]
def baseStart_3423224 : Nat := 118140960795 + 3423224 * 2 ^ 59
def prefixEnd_3423224 : Nat := 4983230072969 + 3 ^ 40 * 3423224 * 2
def baseEnd_3423224 : Nat := 195306588889646650450765

theorem tailTrace_3423224 : CollatzResearch.WordTrace tailWord_3423224 prefixEnd_3423224 195306588889646650450765 := by
  unfold tailWord_3423224
  simp only [CollatzResearch.WordTrace]
  refine ⟨62427618275125781479366363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83236824366834375305821817 62427618275125781479366363)
  ·
    refine ⟨93641427412688672219049545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62427618275125781479366363 93641427412688672219049545)
    ·
      refine ⟨70231070559516504164287159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93641427412688672219049545 70231070559516504164287159)
      ·
        refine ⟨105346605839274756246430739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70231070559516504164287159 105346605839274756246430739)
        ·
          refine ⟨158019908758912134369646109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105346605839274756246430739 158019908758912134369646109)
          ·
            refine ⟨59257465784592050388617291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 158019908758912134369646109 59257465784592050388617291)
            ·
              refine ⟨88886198676888075582925937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59257465784592050388617291 88886198676888075582925937)
              ·
                refine ⟨66664649007666056687194453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88886198676888075582925937 66664649007666056687194453)
                ·
                  refine ⟨195306588889646650450765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 66664649007666056687194453 195306588889646650450765)
                  ·
                    rfl

theorem cell23_3423224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 10].length) (baseStart_3423224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3423224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3423224 prefixEnd_3423224 := by exact prefixLift 3423224
  have htrace : WordTrace (prefixWord ++ tailWord_3423224) baseStart_3423224 baseEnd_3423224 := by
    simpa [prefixWord, tailWord_3423224, baseEnd_3423224] using wordTrace_append hprefix tailTrace_3423224
  have hstable : (prefixWord ++ tailWord_3423224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3423224).length < 2 ^ (prefixWord ++ tailWord_3423224).sum := by decide
  have hdescent : baseEnd_3423224 < baseStart_3423224 := by decide
  rcases family_descends (prefixWord ++ tailWord_3423224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3423228 : List Nat := [2, 2, 2, 1, 2, 4, 1, 2, 3, 4]
def baseStart_3423228 : Nat := 118140960795 + 3423228 * 2 ^ 59
def prefixEnd_3423228 : Nat := 4983230072969 + 3 ^ 40 * 3423228 * 2
def baseEnd_3423228 : Nat := 585920451309812612802289

theorem tailTrace_3423228 : CollatzResearch.WordTrace tailWord_3423228 prefixEnd_3423228 585920451309812612802289 := by
  unfold tailWord_3423228
  simp only [CollatzResearch.WordTrace]
  refine ⟨62427691221118535820939169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83236921628158047761252225 62427691221118535820939169)
  ·
    refine ⟨46820768415838901865704377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62427691221118535820939169 46820768415838901865704377)
    ·
      refine ⟨35115576311879176399278283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46820768415838901865704377 35115576311879176399278283)
      ·
        refine ⟨52673364467818764598917425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35115576311879176399278283 52673364467818764598917425)
        ·
          refine ⟨39505023350864073449188069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52673364467818764598917425 39505023350864073449188069)
          ·
            refine ⟨7407191878287013771722763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39505023350864073449188069 7407191878287013771722763)
            ·
              refine ⟨11110787817430520657584145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7407191878287013771722763 11110787817430520657584145)
              ·
                refine ⟨8333090863072890493188109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11110787817430520657584145 8333090863072890493188109)
                ·
                  refine ⟨3124909073652333934945541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8333090863072890493188109 3124909073652333934945541)
                  ·
                    refine ⟨585920451309812612802289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3124909073652333934945541 585920451309812612802289)
                    ·
                      rfl

theorem cell23_3423228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 2, 3, 4].length) (baseStart_3423228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3423228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3423228 prefixEnd_3423228 := by exact prefixLift 3423228
  have htrace : WordTrace (prefixWord ++ tailWord_3423228) baseStart_3423228 baseEnd_3423228 := by
    simpa [prefixWord, tailWord_3423228, baseEnd_3423228] using wordTrace_append hprefix tailTrace_3423228
  have hstable : (prefixWord ++ tailWord_3423228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3423228).length < 2 ^ (prefixWord ++ tailWord_3423228).sum := by decide
  have hdescent : baseEnd_3423228 < baseStart_3423228 := by decide
  rcases family_descends (prefixWord ++ tailWord_3423228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3423288 : List Nat := [2, 1, 2, 1, 5, 1, 1, 4, 1, 5]
def baseStart_3423288 : Nat := 118140960795 + 3423288 * 2 ^ 59
def prefixEnd_3423288 : Nat := 4983230072969 + 3 ^ 40 * 3423288 * 2
def baseEnd_3423288 : Nat := 585930720922902534552197

theorem tailTrace_3423288 : CollatzResearch.WordTrace tailWord_3423288 prefixEnd_3423288 585930720922902534552197 := by
  unfold tailWord_3423288
  simp only [CollatzResearch.WordTrace]
  refine ⟨62428785411009850944531259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83238380548013134592708345 62428785411009850944531259)
  ·
    refine ⟨93643178116514776416796889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62428785411009850944531259 93643178116514776416796889)
    ·
      refine ⟨70232383587386082312597667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93643178116514776416796889 70232383587386082312597667)
      ·
        refine ⟨105348575381079123468896501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70232383587386082312597667 105348575381079123468896501)
        ·
          refine ⟨9876428941976167825209047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 105348575381079123468896501 9876428941976167825209047)
          ·
            refine ⟨14814643412964251737813571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9876428941976167825209047 14814643412964251737813571)
            ·
              refine ⟨22221965119446377606720357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14814643412964251737813571 22221965119446377606720357)
              ·
                refine ⟨4166618459896195801260067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22221965119446377606720357 4166618459896195801260067)
                ·
                  refine ⟨6249927689844293701890101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4166618459896195801260067 6249927689844293701890101)
                  ·
                    refine ⟨585930720922902534552197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6249927689844293701890101 585930720922902534552197)
                    ·
                      rfl

theorem cell23_3423288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 4, 1, 5].length) (baseStart_3423288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3423288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3423288 prefixEnd_3423288 := by exact prefixLift 3423288
  have htrace : WordTrace (prefixWord ++ tailWord_3423288) baseStart_3423288 baseEnd_3423288 := by
    simpa [prefixWord, tailWord_3423288, baseEnd_3423288] using wordTrace_append hprefix tailTrace_3423288
  have hstable : (prefixWord ++ tailWord_3423288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3423288).length < 2 ^ (prefixWord ++ tailWord_3423288).sum := by decide
  have hdescent : baseEnd_3423288 < baseStart_3423288 := by decide
  rcases family_descends (prefixWord ++ tailWord_3423288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3423301 : List Nat := [1, 3, 1, 1, 1, 3, 2, 4, 1, 6]
def baseStart_3423301 : Nat := 118140960795 + 3423301 * 2 ^ 59
def prefixEnd_3423301 : Nat := 4983230072969 + 3 ^ 40 * 3423301 * 2
def baseEnd_3423301 : Nat := 585932946005738684264677

theorem tailTrace_3423301 : CollatzResearch.WordTrace tailWord_3423301 prefixEnd_3423301 585932946005738684264677 := by
  unfold tailWord_3423301
  simp only [CollatzResearch.WordTrace]
  refine ⟨124858044970972605109285757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83238696647315070072857171 124858044970972605109285757)
  ·
    refine ⟨46821766864114726915982159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124858044970972605109285757 46821766864114726915982159)
    ·
      refine ⟨70232650296172090373973239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46821766864114726915982159 70232650296172090373973239)
      ·
        refine ⟨105348975444258135560959859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70232650296172090373973239 105348975444258135560959859)
        ·
          refine ⟨158023463166387203341439789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105348975444258135560959859 158023463166387203341439789)
          ·
            refine ⟨59258798687395201253039921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 158023463166387203341439789 59258798687395201253039921)
            ·
              refine ⟨44444099015546400939779941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59258798687395201253039921 44444099015546400939779941)
              ·
                refine ⟨8333268565414950176208739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44444099015546400939779941 8333268565414950176208739)
                ·
                  refine ⟨12499902848122425264313109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8333268565414950176208739 12499902848122425264313109)
                  ·
                    refine ⟨585932946005738684264677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12499902848122425264313109 585932946005738684264677)
                    ·
                      rfl

theorem cell23_3423301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 4, 1, 6].length) (baseStart_3423301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3423301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3423301 prefixEnd_3423301 := by exact prefixLift 3423301
  have htrace : WordTrace (prefixWord ++ tailWord_3423301) baseStart_3423301 baseEnd_3423301 := by
    simpa [prefixWord, tailWord_3423301, baseEnd_3423301] using wordTrace_append hprefix tailTrace_3423301
  have hstable : (prefixWord ++ tailWord_3423301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3423301).length < 2 ^ (prefixWord ++ tailWord_3423301).sum := by decide
  have hdescent : baseEnd_3423301 < baseStart_3423301 := by decide
  rcases family_descends (prefixWord ++ tailWord_3423301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3423321 : List Nat := [1, 2, 1, 2, 2, 1, 2, 1, 5, 2, 4]
def baseStart_3423321 : Nat := 118140960795 + 3423321 * 2 ^ 59
def prefixEnd_3423321 : Nat := 4983230072969 + 3 ^ 40 * 3423321 * 2
def baseEnd_3423321 : Nat := 1757809107630305974543939

theorem tailTrace_3423321 : CollatzResearch.WordTrace tailWord_3423321 prefixEnd_3423321 1757809107630305974543939 := by
  unfold tailWord_3423321
  simp only [CollatzResearch.WordTrace]
  refine ⟨124858774430900148525013817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83239182953933432350009211 124858774430900148525013817)
  ·
    refine ⟨93644080823175111393760363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124858774430900148525013817 93644080823175111393760363)
    ·
      refine ⟨140466121234762667090640545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93644080823175111393760363 140466121234762667090640545)
      ·
        refine ⟨105349590926072000317980409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140466121234762667090640545 105349590926072000317980409)
        ·
          refine ⟨79012193194554000238485307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105349590926072000317980409 79012193194554000238485307)
          ·
            refine ⟨118518289791831000357727961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79012193194554000238485307 118518289791831000357727961)
            ·
              refine ⟨88888717343873250268295971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118518289791831000357727961 88888717343873250268295971)
              ·
                refine ⟨133333076015809875402443957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88888717343873250268295971 133333076015809875402443957)
                ·
                  refine ⟨12499975876482175818979121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 133333076015809875402443957 12499975876482175818979121)
                  ·
                    refine ⟨9374981907361631864234341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12499975876482175818979121 9374981907361631864234341)
                    ·
                      refine ⟨1757809107630305974543939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9374981907361631864234341 1757809107630305974543939)
                      ·
                        rfl

theorem cell23_3423321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 5, 2, 4].length) (baseStart_3423321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3423321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3423321 prefixEnd_3423321 := by exact prefixLift 3423321
  have htrace : WordTrace (prefixWord ++ tailWord_3423321) baseStart_3423321 baseEnd_3423321 := by
    simpa [prefixWord, tailWord_3423321, baseEnd_3423321] using wordTrace_append hprefix tailTrace_3423321
  have hstable : (prefixWord ++ tailWord_3423321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3423321).length < 2 ^ (prefixWord ++ tailWord_3423321).sum := by decide
  have hdescent : baseEnd_3423321 < baseStart_3423321 := by decide
  rcases family_descends (prefixWord ++ tailWord_3423321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3423328 : List Nat := [2, 1, 1, 3, 2, 2, 2, 2, 3, 2, 3]
def baseStart_3423328 : Nat := 118140960795 + 3423328 * 2 ^ 59
def prefixEnd_3423328 : Nat := 4983230072969 + 3 ^ 40 * 3423328 * 2
def baseEnd_3423328 : Nat := 1757812701994887447156407

theorem tailTrace_3423328 : CollatzResearch.WordTrace tailWord_3423328 prefixEnd_3423328 1757812701994887447156407 := by
  unfold tailWord_3423328
  simp only [CollatzResearch.WordTrace]
  refine ⟨62429514870937394360259319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83239353161249859147012425 62429514870937394360259319)
  ·
    refine ⟨93644272306406091540388979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62429514870937394360259319 93644272306406091540388979)
    ·
      refine ⟨140466408459609137310583469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93644272306406091540388979 140466408459609137310583469)
      ·
        refine ⟨52674903172353426491468801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140466408459609137310583469 52674903172353426491468801)
        ·
          refine ⟨39506177379265069868601601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52674903172353426491468801 39506177379265069868601601)
          ·
            refine ⟨29629633034448802401451201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39506177379265069868601601 29629633034448802401451201)
            ·
              refine ⟨22222224775836601801088401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29629633034448802401451201 22222224775836601801088401)
              ·
                refine ⟨16666668581877451350816301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22222224775836601801088401 16666668581877451350816301)
                ·
                  refine ⟨6250000718204044256556113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16666668581877451350816301 6250000718204044256556113)
                  ·
                    refine ⟨4687500538653033192417085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6250000718204044256556113 4687500538653033192417085)
                    ·
                      refine ⟨1757812701994887447156407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4687500538653033192417085 1757812701994887447156407)
                      ·
                        rfl

theorem cell23_3423328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 2, 3, 2, 3].length) (baseStart_3423328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3423328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3423328 prefixEnd_3423328 := by exact prefixLift 3423328
  have htrace : WordTrace (prefixWord ++ tailWord_3423328) baseStart_3423328 baseEnd_3423328 := by
    simpa [prefixWord, tailWord_3423328, baseEnd_3423328] using wordTrace_append hprefix tailTrace_3423328
  have hstable : (prefixWord ++ tailWord_3423328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3423328).length < 2 ^ (prefixWord ++ tailWord_3423328).sum := by decide
  have hdescent : baseEnd_3423328 < baseStart_3423328 := by decide
  rcases family_descends (prefixWord ++ tailWord_3423328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3423335 : List Nat := [1, 1, 5, 1, 1, 4, 1, 3, 2, 4]
def baseStart_3423335 : Nat := 118140960795 + 3423335 * 2 ^ 59
def prefixEnd_3423335 : Nat := 4983230072969 + 3 ^ 40 * 3423335 * 2
def baseEnd_3423335 : Nat := 585938765453156306589625

theorem tailTrace_3423335 : CollatzResearch.WordTrace tailWord_3423335 prefixEnd_3423335 585938765453156306589625 := by
  unfold tailWord_3423335
  simp only [CollatzResearch.WordTrace]
  refine ⟨124859285052849428916023459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83239523368566285944015639 124859285052849428916023459)
  ·
    refine ⟨187288927579274143374035189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124859285052849428916023459 187288927579274143374035189)
    ·
      refine ⟨17558336960556950941315799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 187288927579274143374035189 17558336960556950941315799)
      ·
        refine ⟨26337505440835426411973699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17558336960556950941315799 26337505440835426411973699)
        ·
          refine ⟨39506258161253139617960549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26337505440835426411973699 39506258161253139617960549)
          ·
            refine ⟨7407423405234963678367603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39506258161253139617960549 7407423405234963678367603)
            ·
              refine ⟨11111135107852445517551405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7407423405234963678367603 11111135107852445517551405)
              ·
                refine ⟨4166675665444667069081777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11111135107852445517551405 4166675665444667069081777)
                ·
                  refine ⟨3125006749083500301811333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4166675665444667069081777 3125006749083500301811333)
                  ·
                    refine ⟨585938765453156306589625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3125006749083500301811333 585938765453156306589625)
                    ·
                      rfl

theorem cell23_3423335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 3, 2, 4].length) (baseStart_3423335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3423335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3423335 prefixEnd_3423335 := by exact prefixLift 3423335
  have htrace : WordTrace (prefixWord ++ tailWord_3423335) baseStart_3423335 baseEnd_3423335 := by
    simpa [prefixWord, tailWord_3423335, baseEnd_3423335] using wordTrace_append hprefix tailTrace_3423335
  have hstable : (prefixWord ++ tailWord_3423335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3423335).length < 2 ^ (prefixWord ++ tailWord_3423335).sum := by decide
  have hdescent : baseEnd_3423335 < baseStart_3423335 := by decide
  rcases family_descends (prefixWord ++ tailWord_3423335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3423338 : List Nat := [3, 1, 3, 2, 2, 1, 2, 1, 1, 1, 6]
def baseStart_3423338 : Nat := 118140960795 + 3423338 * 2 ^ 59
def prefixEnd_3423338 : Nat := 4983230072969 + 3 ^ 40 * 3423338 * 2
def baseEnd_3423338 : Nat := 1757817836801432408031361

theorem tailTrace_3423338 : CollatzResearch.WordTrace tailWord_3423338 prefixEnd_3423338 1757817836801432408031361 := by
  unfold tailWord_3423338
  simp only [CollatzResearch.WordTrace]
  refine ⟨31214848617959640107095667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83239596314559040285588445 31214848617959640107095667)
  ·
    refine ⟨46822272926939460160643501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31214848617959640107095667 46822272926939460160643501)
    ·
      refine ⟨17558352347602297560241313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46822272926939460160643501 17558352347602297560241313)
      ·
        refine ⟨13168764260701723170180985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17558352347602297560241313 13168764260701723170180985)
        ·
          refine ⟨9876573195526292377635739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13168764260701723170180985 9876573195526292377635739)
          ·
            refine ⟨14814859793289438566453609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9876573195526292377635739 14814859793289438566453609)
            ·
              refine ⟨11111144844967078924840207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14814859793289438566453609 11111144844967078924840207)
              ·
                refine ⟨16666717267450618387260311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11111144844967078924840207 16666717267450618387260311)
                ·
                  refine ⟨25000075901175927580890467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16666717267450618387260311 25000075901175927580890467)
                  ·
                    refine ⟨37500113851763891371335701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25000075901175927580890467 37500113851763891371335701)
                    ·
                      refine ⟨1757817836801432408031361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37500113851763891371335701 1757817836801432408031361)
                      ·
                        rfl

theorem cell23_3423338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_3423338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3423338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3423338 prefixEnd_3423338 := by exact prefixLift 3423338
  have htrace : WordTrace (prefixWord ++ tailWord_3423338) baseStart_3423338 baseEnd_3423338 := by
    simpa [prefixWord, tailWord_3423338, baseEnd_3423338] using wordTrace_append hprefix tailTrace_3423338
  have hstable : (prefixWord ++ tailWord_3423338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3423338).length < 2 ^ (prefixWord ++ tailWord_3423338).sum := by decide
  have hdescent : baseEnd_3423338 < baseStart_3423338 := by decide
  rcases family_descends (prefixWord ++ tailWord_3423338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3423342 : List Nat := [4, 1, 2, 2, 1, 4, 1, 2, 1, 1, 4]
def baseStart_3423342 : Nat := 118140960795 + 3423342 * 2 ^ 59
def prefixEnd_3423342 : Nat := 4983230072969 + 3 ^ 40 * 3423342 * 2
def baseEnd_3423342 : Nat := 1757819890724050392381343

theorem tailTrace_3423342 : CollatzResearch.WordTrace tailWord_3423342 prefixEnd_3423342 1757819890724050392381343 := by
  unfold tailWord_3423342
  simp only [CollatzResearch.WordTrace]
  refine ⟨15607442545478008638941035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83239693575882712741018853 15607442545478008638941035)
  ·
    refine ⟨23411163818217012958411553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15607442545478008638941035 23411163818217012958411553)
    ·
      refine ⟨17558372863662759718808665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23411163818217012958411553 17558372863662759718808665)
      ·
        refine ⟨13168779647747069789106499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17558372863662759718808665 13168779647747069789106499)
        ·
          refine ⟨19753169471620604683659749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13168779647747069789106499 19753169471620604683659749)
          ·
            refine ⟨3703719275928863378186203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19753169471620604683659749 3703719275928863378186203)
            ·
              refine ⟨5555578913893295067279305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3703719275928863378186203 5555578913893295067279305)
              ·
                refine ⟨4166684185419971300459479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5555578913893295067279305 4166684185419971300459479)
                ·
                  refine ⟨6250026278129956950689219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4166684185419971300459479 6250026278129956950689219)
                  ·
                    refine ⟨9375039417194935426033829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6250026278129956950689219 9375039417194935426033829)
                    ·
                      refine ⟨1757819890724050392381343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9375039417194935426033829 1757819890724050392381343)
                      ·
                        rfl

theorem cell23_3423342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 1, 2, 1, 1, 4].length) (baseStart_3423342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3423342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3423342 prefixEnd_3423342 := by exact prefixLift 3423342
  have htrace : WordTrace (prefixWord ++ tailWord_3423342) baseStart_3423342 baseEnd_3423342 := by
    simpa [prefixWord, tailWord_3423342, baseEnd_3423342] using wordTrace_append hprefix tailTrace_3423342
  have hstable : (prefixWord ++ tailWord_3423342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3423342).length < 2 ^ (prefixWord ++ tailWord_3423342).sum := by decide
  have hdescent : baseEnd_3423342 < baseStart_3423342 := by decide
  rcases family_descends (prefixWord ++ tailWord_3423342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3423371 : List Nat := [1, 1, 1, 1, 4, 1, 1, 4, 2, 2, 5]
def baseStart_3423371 : Nat := 118140960795 + 3423371 * 2 ^ 59
def prefixEnd_3423371 : Nat := 4983230072969 + 3 ^ 40 * 3423371 * 2
def baseEnd_3423371 : Nat := 1757834781663030778918709

theorem tailTrace_3423371 : CollatzResearch.WordTrace tailWord_3423371 prefixEnd_3423371 1757834781663030778918709 := by
  unfold tailWord_3423371
  simp only [CollatzResearch.WordTrace]
  refine ⟨124860598080719007064333967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83240398720479338042889311 124860598080719007064333967)
  ·
    refine ⟨187290897121078510596500951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124860598080719007064333967 187290897121078510596500951)
    ·
      refine ⟨280936345681617765894751427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187290897121078510596500951 280936345681617765894751427)
      ·
        refine ⟨421404518522426648842127141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280936345681617765894751427 421404518522426648842127141)
        ·
          refine ⟨79013347222954996657898839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 421404518522426648842127141 79013347222954996657898839)
          ·
            refine ⟨118520020834432494986848259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79013347222954996657898839 118520020834432494986848259)
            ·
              refine ⟨177780031251648742480272389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118520020834432494986848259 177780031251648742480272389)
              ·
                refine ⟨33333755859684139215051073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 177780031251648742480272389 33333755859684139215051073)
                ·
                  refine ⟨25000316894763104411288305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33333755859684139215051073 25000316894763104411288305)
                  ·
                    refine ⟨18750237671072328308466229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25000316894763104411288305 18750237671072328308466229)
                    ·
                      refine ⟨1757834781663030778918709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18750237671072328308466229 1757834781663030778918709)
                      ·
                        rfl

theorem cell23_3423371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 4, 2, 2, 5].length) (baseStart_3423371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3423371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3423371 prefixEnd_3423371 := by exact prefixLift 3423371
  have htrace : WordTrace (prefixWord ++ tailWord_3423371) baseStart_3423371 baseEnd_3423371 := by
    simpa [prefixWord, tailWord_3423371, baseEnd_3423371] using wordTrace_append hprefix tailTrace_3423371
  have hstable : (prefixWord ++ tailWord_3423371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3423371).length < 2 ^ (prefixWord ++ tailWord_3423371).sum := by decide
  have hdescent : baseEnd_3423371 < baseStart_3423371 := by decide
  rcases family_descends (prefixWord ++ tailWord_3423371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3423378 : List Nat := [3, 2, 3, 1, 1, 2, 1, 1, 2, 7]
def baseStart_3423378 : Nat := 118140960795 + 3423378 * 2 ^ 59
def prefixEnd_3423378 : Nat := 4983230072969 + 3 ^ 40 * 3423378 * 2
def baseEnd_3423378 : Nat := 585946125342537417177059

theorem tailTrace_3423378 : CollatzResearch.WordTrace tailWord_3423378 prefixEnd_3423378 585946125342537417177059 := by
  unfold tailWord_3423378
  simp only [CollatzResearch.WordTrace]
  refine ⟨31215213347923411814959697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83240568927795764839892525 31215213347923411814959697)
  ·
    refine ⟨23411410010942558861219773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31215213347923411814959697 23411410010942558861219773)
    ·
      refine ⟨8779278754103459572957415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23411410010942558861219773 8779278754103459572957415)
      ·
        refine ⟨13168918131155189359436123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8779278754103459572957415 13168918131155189359436123)
        ·
          refine ⟨19753377196732784039154185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13168918131155189359436123 19753377196732784039154185)
          ·
            refine ⟨14815032897549588029365639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19753377196732784039154185 14815032897549588029365639)
            ·
              refine ⟨22222549346324382044048459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14815032897549588029365639 22222549346324382044048459)
              ·
                refine ⟨33333824019486573066072689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22222549346324382044048459 33333824019486573066072689)
                ·
                  refine ⟨25000368014614929799554517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33333824019486573066072689 25000368014614929799554517)
                  ·
                    refine ⟨585946125342537417177059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25000368014614929799554517 585946125342537417177059)
                    ·
                      rfl

theorem cell23_3423378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 1, 2, 7].length) (baseStart_3423378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3423378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3423378 prefixEnd_3423378 := by exact prefixLift 3423378
  have htrace : WordTrace (prefixWord ++ tailWord_3423378) baseStart_3423378 baseEnd_3423378 := by
    simpa [prefixWord, tailWord_3423378, baseEnd_3423378] using wordTrace_append hprefix tailTrace_3423378
  have hstable : (prefixWord ++ tailWord_3423378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3423378).length < 2 ^ (prefixWord ++ tailWord_3423378).sum := by decide
  have hdescent : baseEnd_3423378 < baseStart_3423378 := by decide
  rcases family_descends (prefixWord ++ tailWord_3423378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3423401 : List Nat := [1, 2, 1, 1, 1, 1, 2, 1, 5, 3, 5]
def baseStart_3423401 : Nat := 118140960795 + 3423401 * 2 ^ 59
def prefixEnd_3423401 : Nat := 4983230072969 + 3 ^ 40 * 3423401 * 2
def baseEnd_3423401 : Nat := 1757850186082665661543571

theorem tailTrace_3423401 : CollatzResearch.WordTrace tailWord_3423401 prefixEnd_3423401 1757850186082665661543571 := by
  unfold tailWord_3423401
  simp only [CollatzResearch.WordTrace]
  refine ⟨124861692270610322187926057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83241128180406881458617371 124861692270610322187926057)
  ·
    refine ⟨93646269202957741640944543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124861692270610322187926057 93646269202957741640944543)
    ·
      refine ⟨140469403804436612461416815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93646269202957741640944543 140469403804436612461416815)
      ·
        refine ⟨210704105706654918692125223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140469403804436612461416815 210704105706654918692125223)
        ·
          refine ⟨316056158559982378038187835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210704105706654918692125223 316056158559982378038187835)
          ·
            refine ⟨474084237839973567057281753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 316056158559982378038187835 474084237839973567057281753)
            ·
              refine ⟨355563178379980175292961315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 474084237839973567057281753 355563178379980175292961315)
              ·
                refine ⟨533344767569970262939441973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 355563178379980175292961315 533344767569970262939441973)
                ·
                  refine ⟨50001071959684712150572685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 533344767569970262939441973 50001071959684712150572685)
                  ·
                    refine ⟨18750401984881767056464757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50001071959684712150572685 18750401984881767056464757)
                    ·
                      refine ⟨1757850186082665661543571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18750401984881767056464757 1757850186082665661543571)
                      ·
                        rfl

theorem cell23_3423401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 5, 3, 5].length) (baseStart_3423401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3423401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3423401 prefixEnd_3423401 := by exact prefixLift 3423401
  have htrace : WordTrace (prefixWord ++ tailWord_3423401) baseStart_3423401 baseEnd_3423401 := by
    simpa [prefixWord, tailWord_3423401, baseEnd_3423401] using wordTrace_append hprefix tailTrace_3423401
  have hstable : (prefixWord ++ tailWord_3423401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3423401).length < 2 ^ (prefixWord ++ tailWord_3423401).sum := by decide
  have hdescent : baseEnd_3423401 < baseStart_3423401 := by decide
  rcases family_descends (prefixWord ++ tailWord_3423401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3423415 : List Nat := [1, 1, 3, 1, 4, 1, 1, 4, 1, 4, 2]
def baseStart_3423415 : Nat := 118140960795 + 3423415 * 2 ^ 59
def prefixEnd_3423415 : Nat := 4983230072969 + 3 ^ 40 * 3423415 * 2
def baseEnd_3423415 : Nat := 1757857374811828606768507

theorem tailTrace_3423415 : CollatzResearch.WordTrace tailWord_3423415 prefixEnd_3423415 1757857374811828606768507 := by
  unfold tailWord_3423415
  simp only [CollatzResearch.WordTrace]
  refine ⟨124862202892559602578935699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83241468595039735052623799 124862202892559602578935699)
  ·
    refine ⟨187293304338839403868403549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124862202892559602578935699 187293304338839403868403549)
    ·
      refine ⟨70234989127064776450651331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187293304338839403868403549 70234989127064776450651331)
      ·
        refine ⟨105352483690597164675976997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70234989127064776450651331 105352483690597164675976997)
        ·
          refine ⟨19753590691986968376745687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 105352483690597164675976997 19753590691986968376745687)
          ·
            refine ⟨29630386037980452565118531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19753590691986968376745687 29630386037980452565118531)
            ·
              refine ⟨44445579056970678847677797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29630386037980452565118531 44445579056970678847677797)
              ·
                refine ⟨8333546073182002283939587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44445579056970678847677797 8333546073182002283939587)
                ·
                  refine ⟨12500319109773003425909381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8333546073182002283939587 12500319109773003425909381)
                  ·
                    refine ⟨2343809833082438142358009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12500319109773003425909381 2343809833082438142358009)
                    ·
                      refine ⟨1757857374811828606768507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2343809833082438142358009 1757857374811828606768507)
                      ·
                        rfl

theorem cell23_3423415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 4, 1, 4, 2].length) (baseStart_3423415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3423415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3423415 prefixEnd_3423415 := by exact prefixLift 3423415
  have htrace : WordTrace (prefixWord ++ tailWord_3423415) baseStart_3423415 baseEnd_3423415 := by
    simpa [prefixWord, tailWord_3423415, baseEnd_3423415] using wordTrace_append hprefix tailTrace_3423415
  have hstable : (prefixWord ++ tailWord_3423415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3423415).length < 2 ^ (prefixWord ++ tailWord_3423415).sum := by decide
  have hdescent : baseEnd_3423415 < baseStart_3423415 := by decide
  rcases family_descends (prefixWord ++ tailWord_3423415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3423425 : List Nat := [1, 2, 6, 1, 1, 1, 1, 2, 2, 6]
def baseStart_3423425 : Nat := 118140960795 + 3423425 * 2 ^ 59
def prefixEnd_3423425 : Nat := 4983230072969 + 3 ^ 40 * 3423425 * 2
def baseEnd_3423425 : Nat := 585954169872791189214487

theorem tailTrace_3423425 : CollatzResearch.WordTrace tailWord_3423425 prefixEnd_3423425 585954169872791189214487 := by
  unfold tailWord_3423425
  simp only [CollatzResearch.WordTrace]
  refine ⟨124862567622523374286799729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83241711748348916191199819 124862567622523374286799729)
  ·
    refine ⟨93646925716892530715099797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124862567622523374286799729 93646925716892530715099797)
    ·
      refine ⟨4389699642979337377270303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 93646925716892530715099797 4389699642979337377270303)
      ·
        refine ⟨6584549464469006065905455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4389699642979337377270303 6584549464469006065905455)
        ·
          refine ⟨9876824196703509098858183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6584549464469006065905455 9876824196703509098858183)
          ·
            refine ⟨14815236295055263648287275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9876824196703509098858183 14815236295055263648287275)
            ·
              refine ⟨22222854442582895472430913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14815236295055263648287275 22222854442582895472430913)
              ·
                refine ⟨16667140831937171604323185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22222854442582895472430913 16667140831937171604323185)
                ·
                  refine ⟨12500355623952878703242389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16667140831937171604323185 12500355623952878703242389)
                  ·
                    refine ⟨585954169872791189214487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12500355623952878703242389 585954169872791189214487)
                    ·
                      rfl

theorem cell23_3423425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_3423425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3423425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3423425 prefixEnd_3423425 := by exact prefixLift 3423425
  have htrace : WordTrace (prefixWord ++ tailWord_3423425) baseStart_3423425 baseEnd_3423425 := by
    simpa [prefixWord, tailWord_3423425, baseEnd_3423425] using wordTrace_append hprefix tailTrace_3423425
  have hstable : (prefixWord ++ tailWord_3423425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3423425).length < 2 ^ (prefixWord ++ tailWord_3423425).sum := by decide
  have hdescent : baseEnd_3423425 < baseStart_3423425 := by decide
  rcases family_descends (prefixWord ++ tailWord_3423425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3423426 : List Nat := [3, 5, 1, 1, 2, 1, 1, 1, 4, 1, 3]
def baseStart_3423426 : Nat := 118140960795 + 3423426 * 2 ^ 59
def prefixEnd_3423426 : Nat := 4983230072969 + 3 ^ 40 * 3423426 * 2
def baseEnd_3423426 : Nat := 1757863023099028063730957

theorem tailTrace_3423426 : CollatzResearch.WordTrace tailWord_3423426 prefixEnd_3423426 1757863023099028063730957 := by
  unfold tailWord_3423426
  simp only [CollatzResearch.WordTrace]
  refine ⟨31215651023879937864396533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83241736063679834305057421 31215651023879937864396533)
  ·
    refine ⟨2926467283488744174787175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31215651023879937864396533 2926467283488744174787175)
    ·
      refine ⟨4389700925233116262180763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2926467283488744174787175 4389700925233116262180763)
      ·
        refine ⟨6584551387849674393271145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4389700925233116262180763 6584551387849674393271145)
        ·
          refine ⟨4938413540887255794953359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6584551387849674393271145 4938413540887255794953359)
          ·
            refine ⟨7407620311330883692430039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4938413540887255794953359 7407620311330883692430039)
            ·
              refine ⟨11111430466996325538645059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7407620311330883692430039 11111430466996325538645059)
              ·
                refine ⟨16667145700494488307967589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11111430466996325538645059 16667145700494488307967589)
                ·
                  refine ⟨3125089818842716557743923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16667145700494488307967589 3125089818842716557743923)
                  ·
                    refine ⟨4687634728264074836615885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3125089818842716557743923 4687634728264074836615885)
                    ·
                      refine ⟨1757863023099028063730957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4687634728264074836615885 1757863023099028063730957)
                      ·
                        rfl

theorem cell23_3423426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_3423426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3423426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3423426 prefixEnd_3423426 := by exact prefixLift 3423426
  have htrace : WordTrace (prefixWord ++ tailWord_3423426) baseStart_3423426 baseEnd_3423426 := by
    simpa [prefixWord, tailWord_3423426, baseEnd_3423426] using wordTrace_append hprefix tailTrace_3423426
  have hstable : (prefixWord ++ tailWord_3423426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3423426).length < 2 ^ (prefixWord ++ tailWord_3423426).sum := by decide
  have hdescent : baseEnd_3423426 < baseStart_3423426 := by decide
  rcases family_descends (prefixWord ++ tailWord_3423426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3423445 : List Nat := [1, 3, 2, 4, 1, 1, 2, 1, 2, 2, 4]
def baseStart_3423445 : Nat := 118140960795 + 3423445 * 2 ^ 59
def prefixEnd_3423445 : Nat := 4983230072969 + 3 ^ 40 * 3423445 * 2
def baseEnd_3423445 : Nat := 1757872779231463489393369

theorem tailTrace_3423445 : CollatzResearch.WordTrace tailWord_3423445 prefixEnd_3423445 1757872779231463489393369 := by
  unfold tailWord_3423445
  simp only [CollatzResearch.WordTrace]
  refine ⟨124863297082450917702527789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83242198054967278468351859 124863297082450917702527789)
  ·
    refine ⟨46823736405919094138447921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124863297082450917702527789 46823736405919094138447921)
    ·
      refine ⟨35117802304439320603835941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46823736405919094138447921 35117802304439320603835941)
      ·
        refine ⟨6584587932082372613219239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35117802304439320603835941 6584587932082372613219239)
        ·
          refine ⟨9876881898123558919828859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6584587932082372613219239 9876881898123558919828859)
          ·
            refine ⟨14815322847185338379743289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9876881898123558919828859 14815322847185338379743289)
            ·
              refine ⟨11111492135389003784807467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14815322847185338379743289 11111492135389003784807467)
              ·
                refine ⟨16667238203083505677211201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11111492135389003784807467 16667238203083505677211201)
                ·
                  refine ⟨12500428652312629257908401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16667238203083505677211201 12500428652312629257908401)
                  ·
                    refine ⟨9375321489234471943431301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12500428652312629257908401 9375321489234471943431301)
                    ·
                      refine ⟨1757872779231463489393369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9375321489234471943431301 1757872779231463489393369)
                      ·
                        rfl

theorem cell23_3423445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_3423445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3423445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3423445 prefixEnd_3423445 := by exact prefixLift 3423445
  have htrace : WordTrace (prefixWord ++ tailWord_3423445) baseStart_3423445 baseEnd_3423445 := by
    simpa [prefixWord, tailWord_3423445, baseEnd_3423445] using wordTrace_append hprefix tailTrace_3423445
  have hstable : (prefixWord ++ tailWord_3423445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3423445).length < 2 ^ (prefixWord ++ tailWord_3423445).sum := by decide
  have hdescent : baseEnd_3423445 < baseStart_3423445 := by decide
  rcases family_descends (prefixWord ++ tailWord_3423445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3423468 : List Nat := [2, 2, 1, 1, 2, 4, 2, 1, 1, 7]
def baseStart_3423468 : Nat := 118140960795 + 3423468 * 2 ^ 59
def prefixEnd_3423468 : Nat := 4983230072969 + 3 ^ 40 * 3423468 * 2
def baseEnd_3423468 : Nat := 585961529762172299801921

theorem tailTrace_3423468 : CollatzResearch.WordTrace tailWord_3423468 prefixEnd_3423468 585961529762172299801921 := by
  unfold tailWord_3423468
  simp only [CollatzResearch.WordTrace]
  refine ⟨62432067980683796315307529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83242757307578395087076705 62432067980683796315307529)
  ·
    refine ⟨46824050985512847236480647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62432067980683796315307529 46824050985512847236480647)
    ·
      refine ⟨70236076478269270854720971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46824050985512847236480647 70236076478269270854720971)
      ·
        refine ⟨105354114717403906282081457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70236076478269270854720971 105354114717403906282081457)
        ·
          refine ⟨79015586038052929711561093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105354114717403906282081457 79015586038052929711561093)
          ·
            refine ⟨14815422382134924320917705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79015586038052929711561093 14815422382134924320917705)
            ·
              refine ⟨11111566786601193240688279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14815422382134924320917705 11111566786601193240688279)
              ·
                refine ⟨16667350179901789861032419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11111566786601193240688279 16667350179901789861032419)
                ·
                  refine ⟨25001025269852684791548629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16667350179901789861032419 25001025269852684791548629)
                  ·
                    refine ⟨585961529762172299801921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25001025269852684791548629 585961529762172299801921)
                    ·
                      rfl

theorem cell23_3423468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 7].length) (baseStart_3423468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3423468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3423468 prefixEnd_3423468 := by exact prefixLift 3423468
  have htrace : WordTrace (prefixWord ++ tailWord_3423468) baseStart_3423468 baseEnd_3423468 := by
    simpa [prefixWord, tailWord_3423468, baseEnd_3423468] using wordTrace_append hprefix tailTrace_3423468
  have hstable : (prefixWord ++ tailWord_3423468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3423468).length < 2 ^ (prefixWord ++ tailWord_3423468).sum := by decide
  have hdescent : baseEnd_3423468 < baseStart_3423468 := by decide
  rcases family_descends (prefixWord ++ tailWord_3423468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3423505 : List Nat := [1, 2, 2, 1, 1, 4, 2, 1, 1, 6, 2]
def baseStart_3423505 : Nat := 118140960795 + 3423505 * 2 ^ 59
def prefixEnd_3423505 : Nat := 4983230072969 + 3 ^ 40 * 3423505 * 2
def baseEnd_3423505 : Nat := 1757903588070733254643093

theorem tailTrace_3423505 : CollatzResearch.WordTrace tailWord_3423505 prefixEnd_3423505 1757903588070733254643093 := by
  unfold tailWord_3423505
  simp only [CollatzResearch.WordTrace]
  refine ⟨124865485462233547949711969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83243656974822365299807979 124865485462233547949711969)
  ·
    refine ⟨93649114096675160962283977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124865485462233547949711969 93649114096675160962283977)
    ·
      refine ⟨70236835572506370721712983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93649114096675160962283977 70236835572506370721712983)
      ·
        refine ⟨105355253358759556082569475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70236835572506370721712983 105355253358759556082569475)
        ·
          refine ⟨158032880038139334123854213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105355253358759556082569475 158032880038139334123854213)
          ·
            refine ⟨29631165007151125148222665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 158032880038139334123854213 29631165007151125148222665)
            ·
              refine ⟨22223373755363343861166999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29631165007151125148222665 22223373755363343861166999)
              ·
                refine ⟨33335060633045015791750499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22223373755363343861166999 33335060633045015791750499)
                ·
                  refine ⟨50002590949567523687625749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33335060633045015791750499 50002590949567523687625749)
                  ·
                    refine ⟨2343871450760977672857457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 50002590949567523687625749 2343871450760977672857457)
                    ·
                      refine ⟨1757903588070733254643093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2343871450760977672857457 1757903588070733254643093)
                      ·
                        rfl

theorem cell23_3423505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 6, 2].length) (baseStart_3423505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3423505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3423505 prefixEnd_3423505 := by exact prefixLift 3423505
  have htrace : WordTrace (prefixWord ++ tailWord_3423505) baseStart_3423505 baseEnd_3423505 := by
    simpa [prefixWord, tailWord_3423505, baseEnd_3423505] using wordTrace_append hprefix tailTrace_3423505
  have hstable : (prefixWord ++ tailWord_3423505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3423505).length < 2 ^ (prefixWord ++ tailWord_3423505).sum := by decide
  have hdescent : baseEnd_3423505 < baseStart_3423505 := by decide
  rcases family_descends (prefixWord ++ tailWord_3423505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3423532 : List Nat := [2, 2, 1, 1, 1, 3, 1, 7, 1, 4]
def baseStart_3423532 : Nat := 118140960795 + 3423532 * 2 ^ 59
def prefixEnd_3423532 : Nat := 4983230072969 + 3 ^ 40 * 3423532 * 2
def baseEnd_3423532 : Nat := 585972484016134883001823

theorem tailTrace_3423532 : CollatzResearch.WordTrace tailWord_3423532 prefixEnd_3423532 585972484016134883001823 := by
  unfold tailWord_3423532
  simp only [CollatzResearch.WordTrace]
  refine ⟨62433235116567865780472425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83244313488757154373963233 62433235116567865780472425)
  ·
    refine ⟨46824926337425899335354319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62433235116567865780472425 46824926337425899335354319)
    ·
      refine ⟨70237389506138849003031479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46824926337425899335354319 70237389506138849003031479)
      ·
        refine ⟨105356084259208273504547219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70237389506138849003031479 105356084259208273504547219)
        ·
          refine ⟨158034126388812410256820829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105356084259208273504547219 158034126388812410256820829)
          ·
            refine ⟨59262797395804653846307811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 158034126388812410256820829 59262797395804653846307811)
            ·
              refine ⟨88894196093706980769461717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59262797395804653846307811 88894196093706980769461717)
              ·
                refine ⟨2083457720946257361784259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 88894196093706980769461717 2083457720946257361784259)
                ·
                  refine ⟨3125186581419386042676389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2083457720946257361784259 3125186581419386042676389)
                  ·
                    refine ⟨585972484016134883001823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3125186581419386042676389 585972484016134883001823)
                    ·
                      rfl

theorem cell23_3423532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 7, 1, 4].length) (baseStart_3423532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3423532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3423532 prefixEnd_3423532 := by exact prefixLift 3423532
  have htrace : WordTrace (prefixWord ++ tailWord_3423532) baseStart_3423532 baseEnd_3423532 := by
    simpa [prefixWord, tailWord_3423532, baseEnd_3423532] using wordTrace_append hprefix tailTrace_3423532
  have hstable : (prefixWord ++ tailWord_3423532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3423532).length < 2 ^ (prefixWord ++ tailWord_3423532).sum := by decide
  have hdescent : baseEnd_3423532 < baseStart_3423532 := by decide
  rcases family_descends (prefixWord ++ tailWord_3423532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3423568 : List Nat := [2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 7]
def baseStart_3423568 : Nat := 118140960795 + 3423568 * 2 ^ 59
def prefixEnd_3423568 : Nat := 4983230072969 + 3 ^ 40 * 3423568 * 2
def baseEnd_3423568 : Nat := 1757935937351966508155303

theorem tailTrace_3423568 : CollatzResearch.WordTrace tailWord_3423568 prefixEnd_3423568 1757935937351966508155303 := by
  unfold tailWord_3423568
  simp only [CollatzResearch.WordTrace]
  refine ⟨62433891630502654854627679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83245188840670206472836905 62433891630502654854627679)
  ·
    refine ⟨93650837445753982281941519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62433891630502654854627679 93650837445753982281941519)
    ·
      refine ⟨140476256168630973422912279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93650837445753982281941519 140476256168630973422912279)
      ·
        refine ⟨210714384252946460134368419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140476256168630973422912279 210714384252946460134368419)
        ·
          refine ⟨316071576379419690201552629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210714384252946460134368419 316071576379419690201552629)
          ·
            refine ⟨29631710285570595956395559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 316071576379419690201552629 29631710285570595956395559)
            ·
              refine ⟨44447565428355893934593339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29631710285570595956395559 44447565428355893934593339)
              ·
                refine ⟨66671348142533840901890009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44447565428355893934593339 66671348142533840901890009)
                ·
                  refine ⟨50003511106900380676417507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66671348142533840901890009 50003511106900380676417507)
                  ·
                    refine ⟨75005266660350571014626261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50003511106900380676417507 75005266660350571014626261)
                    ·
                      refine ⟨1757935937351966508155303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 75005266660350571014626261 1757935937351966508155303)
                      ·
                        rfl

theorem cell23_3423568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 7].length) (baseStart_3423568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3423568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3423568 prefixEnd_3423568 := by exact prefixLift 3423568
  have htrace : WordTrace (prefixWord ++ tailWord_3423568) baseStart_3423568 baseEnd_3423568 := by
    simpa [prefixWord, tailWord_3423568, baseEnd_3423568] using wordTrace_append hprefix tailTrace_3423568
  have hstable : (prefixWord ++ tailWord_3423568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3423568).length < 2 ^ (prefixWord ++ tailWord_3423568).sum := by decide
  have hdescent : baseEnd_3423568 < baseStart_3423568 := by decide
  rcases family_descends (prefixWord ++ tailWord_3423568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3423575 : List Nat := [1, 1, 3, 2, 3, 2, 2, 1, 3, 5]
def baseStart_3423575 : Nat := 118140960795 + 3423575 * 2 ^ 59
def prefixEnd_3423575 : Nat := 4983230072969 + 3 ^ 40 * 3423575 * 2
def baseEnd_3423575 : Nat := 585979843905515993589257

theorem tailTrace_3423575 : CollatzResearch.WordTrace tailWord_3423575 prefixEnd_3423575 585979843905515993589257 := by
  unfold tailWord_3423575
  simp only [CollatzResearch.WordTrace]
  refine ⟨124868038571979949904760179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83245359047986633269840119 124868038571979949904760179)
  ·
    refine ⟨187302057857969924857140269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124868038571979949904760179 187302057857969924857140269)
    ·
      refine ⟨70238271696738721821427601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187302057857969924857140269 70238271696738721821427601)
      ·
        refine ⟨52678703772554041366070701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70238271696738721821427601 52678703772554041366070701)
        ·
          refine ⟨19754513914707765512276513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52678703772554041366070701 19754513914707765512276513)
          ·
            refine ⟨14815885436030824134207385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19754513914707765512276513 14815885436030824134207385)
            ·
              refine ⟨11111914077023118100655539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14815885436030824134207385 11111914077023118100655539)
              ·
                refine ⟨16667871115534677150983309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11111914077023118100655539 16667871115534677150983309)
                ·
                  refine ⟨6250451668325503931618741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16667871115534677150983309 6250451668325503931618741)
                  ·
                    refine ⟨585979843905515993589257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6250451668325503931618741 585979843905515993589257)
                    ·
                      rfl

theorem cell23_3423575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 1, 3, 5].length) (baseStart_3423575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3423575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3423575 prefixEnd_3423575 := by exact prefixLift 3423575
  have htrace : WordTrace (prefixWord ++ tailWord_3423575) baseStart_3423575 baseEnd_3423575 := by
    simpa [prefixWord, tailWord_3423575, baseEnd_3423575] using wordTrace_append hprefix tailTrace_3423575
  have hstable : (prefixWord ++ tailWord_3423575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3423575).length < 2 ^ (prefixWord ++ tailWord_3423575).sum := by decide
  have hdescent : baseEnd_3423575 < baseStart_3423575 := by decide
  rcases family_descends (prefixWord ++ tailWord_3423575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3423640 : List Nat := [2, 1, 2, 5, 3, 1, 1, 3, 1, 1, 3]
def baseStart_3423640 : Nat := 118140960795 + 3423640 * 2 ^ 59
def prefixEnd_3423640 : Nat := 4983230072969 + 3 ^ 40 * 3423640 * 2
def baseEnd_3423640 : Nat := 1757972907959090226454973

theorem tailTrace_3423640 : CollatzResearch.WordTrace tailWord_3423640 prefixEnd_3423640 1757972907959090226454973 := by
  unfold tailWord_3423640
  simp only [CollatzResearch.WordTrace]
  refine ⟨62435204658372233002938187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83246939544496310670584249 62435204658372233002938187)
  ·
    refine ⟨93652806987558349504407281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62435204658372233002938187 93652806987558349504407281)
    ·
      refine ⟨70239605240668762128305461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93652806987558349504407281 70239605240668762128305461)
      ·
        refine ⟨6584962991312696449528637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 70239605240668762128305461 6584962991312696449528637)
        ·
          refine ⟨2469361121742261168573239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6584962991312696449528637 2469361121742261168573239)
          ·
            refine ⟨3704041682613391752859859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2469361121742261168573239 3704041682613391752859859)
            ·
              refine ⟨5556062523920087629289789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3704041682613391752859859 5556062523920087629289789)
              ·
                refine ⟨2083523446470032860983671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5556062523920087629289789 2083523446470032860983671)
                ·
                  refine ⟨3125285169705049291475507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2083523446470032860983671 3125285169705049291475507)
                  ·
                    refine ⟨4687927754557573937213261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3125285169705049291475507 4687927754557573937213261)
                    ·
                      refine ⟨1757972907959090226454973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4687927754557573937213261 1757972907959090226454973)
                      ·
                        rfl

theorem cell23_3423640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 1, 3, 1, 1, 3].length) (baseStart_3423640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3423640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3423640 prefixEnd_3423640 := by exact prefixLift 3423640
  have htrace : WordTrace (prefixWord ++ tailWord_3423640) baseStart_3423640 baseEnd_3423640 := by
    simpa [prefixWord, tailWord_3423640, baseEnd_3423640] using wordTrace_append hprefix tailTrace_3423640
  have hstable : (prefixWord ++ tailWord_3423640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3423640).length < 2 ^ (prefixWord ++ tailWord_3423640).sum := by decide
  have hdescent : baseEnd_3423640 < baseStart_3423640 := by decide
  rcases family_descends (prefixWord ++ tailWord_3423640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3423665 : List Nat := [1, 2, 2, 4, 1, 1, 2, 1, 2, 7]
def baseStart_3423665 : Nat := 118140960795 + 3423665 * 2 ^ 59
def prefixEnd_3423665 : Nat := 4983230072969 + 3 ^ 40 * 3423665 * 2
def baseEnd_3423665 : Nat := 585995248325150876214119

theorem tailTrace_3423665 : CollatzResearch.WordTrace tailWord_3423665 prefixEnd_3423665 585995248325150876214119 := by
  unfold tailWord_3423665
  simp only [CollatzResearch.WordTrace]
  refine ⟨124871321141653895275536449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83247547427769263517024299 124871321141653895275536449)
  ·
    refine ⟨93653490856240421456652337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124871321141653895275536449 93653490856240421456652337)
    ·
      refine ⟨70240118142180316092489253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93653490856240421456652337 70240118142180316092489253)
      ·
        refine ⟨13170022151658809267341735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70240118142180316092489253 13170022151658809267341735)
        ·
          refine ⟨19755033227488213901012603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13170022151658809267341735 19755033227488213901012603)
          ·
            refine ⟨29632549841232320851518905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19755033227488213901012603 29632549841232320851518905)
            ·
              refine ⟨22224412380924240638639179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29632549841232320851518905 22224412380924240638639179)
              ·
                refine ⟨33336618571386360957958769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22224412380924240638639179 33336618571386360957958769)
                ·
                  refine ⟨25002463928539770718469077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33336618571386360957958769 25002463928539770718469077)
                  ·
                    refine ⟨585995248325150876214119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25002463928539770718469077 585995248325150876214119)
                    ·
                      rfl

theorem cell23_3423665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 1, 2, 7].length) (baseStart_3423665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3423665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3423665 prefixEnd_3423665 := by exact prefixLift 3423665
  have htrace : WordTrace (prefixWord ++ tailWord_3423665) baseStart_3423665 baseEnd_3423665 := by
    simpa [prefixWord, tailWord_3423665, baseEnd_3423665] using wordTrace_append hprefix tailTrace_3423665
  have hstable : (prefixWord ++ tailWord_3423665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3423665).length < 2 ^ (prefixWord ++ tailWord_3423665).sum := by decide
  have hdescent : baseEnd_3423665 < baseStart_3423665 := by decide
  rcases family_descends (prefixWord ++ tailWord_3423665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3423673 : List Nat := [1, 2, 1, 4, 5, 1, 2, 1, 2, 4]
def baseStart_3423673 : Nat := 118140960795 + 3423673 * 2 ^ 59
def prefixEnd_3423673 : Nat := 4983230072969 + 3 ^ 40 * 3423673 * 2
def baseEnd_3423673 : Nat := 585996617606896199114107

theorem tailTrace_3423673 : CollatzResearch.WordTrace tailWord_3423673 prefixEnd_3423673 585996617606896199114107 := by
  unfold tailWord_3423673
  simp only [CollatzResearch.WordTrace]
  refine ⟨124871612925624912641827673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83247741950416608427885115 124871612925624912641827673)
  ·
    refine ⟨93653709694218684481370755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124871612925624912641827673 93653709694218684481370755)
    ·
      refine ⟨140480564541328026722056133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93653709694218684481370755 140480564541328026722056133)
      ·
        refine ⟨26340105851499005010385525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 140480564541328026722056133 26340105851499005010385525)
        ·
          refine ⟨2469384923578031719723643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26340105851499005010385525 2469384923578031719723643)
          ·
            refine ⟨3704077385367047579585465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2469384923578031719723643 3704077385367047579585465)
            ·
              refine ⟨2778058039025285684689099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3704077385367047579585465 2778058039025285684689099)
              ·
                refine ⟨4167087058537928527033649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2778058039025285684689099 4167087058537928527033649)
                ·
                  refine ⟨3125315293903446395275237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4167087058537928527033649 3125315293903446395275237)
                  ·
                    refine ⟨585996617606896199114107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3125315293903446395275237 585996617606896199114107)
                    ·
                      rfl

theorem cell23_3423673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 2, 1, 2, 4].length) (baseStart_3423673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3423673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3423673 prefixEnd_3423673 := by exact prefixLift 3423673
  have htrace : WordTrace (prefixWord ++ tailWord_3423673) baseStart_3423673 baseEnd_3423673 := by
    simpa [prefixWord, tailWord_3423673, baseEnd_3423673] using wordTrace_append hprefix tailTrace_3423673
  have hstable : (prefixWord ++ tailWord_3423673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3423673).length < 2 ^ (prefixWord ++ tailWord_3423673).sum := by decide
  have hdescent : baseEnd_3423673 < baseStart_3423673 := by decide
  rcases family_descends (prefixWord ++ tailWord_3423673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3423736 : List Nat := [2, 1, 2, 1, 1, 5, 2, 3, 2, 2, 2]
def baseStart_3423736 : Nat := 118140960795 + 3423736 * 2 ^ 59
def prefixEnd_3423736 : Nat := 4983230072969 + 3 ^ 40 * 3423736 * 2
def baseEnd_3423736 : Nat := 1758022202101921850854531

theorem tailTrace_3423736 : CollatzResearch.WordTrace tailWord_3423736 prefixEnd_3423736 1758022202101921850854531 := by
  unfold tailWord_3423736
  simp only [CollatzResearch.WordTrace]
  refine ⟨62436955362198337200685531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83249273816264449600914041 62436955362198337200685531)
  ·
    refine ⟨93655433043297505801028297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62436955362198337200685531 93655433043297505801028297)
    ·
      refine ⟨70241574782473129350771223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93655433043297505801028297 70241574782473129350771223)
      ·
        refine ⟨105362362173709694026156835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70241574782473129350771223 105362362173709694026156835)
        ·
          refine ⟨158043543260564541039235253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105362362173709694026156835 158043543260564541039235253)
          ·
            refine ⟨14816582180677925722428305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 158043543260564541039235253 14816582180677925722428305)
            ·
              refine ⟨11112436635508444291821229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14816582180677925722428305 11112436635508444291821229)
              ·
                refine ⟨4167163738315666609432961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11112436635508444291821229 4167163738315666609432961)
                ·
                  refine ⟨3125372803736749957074721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4167163738315666609432961 3125372803736749957074721)
                  ·
                    refine ⟨2344029602802562467806041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3125372803736749957074721 2344029602802562467806041)
                    ·
                      refine ⟨1758022202101921850854531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2344029602802562467806041 1758022202101921850854531)
                      ·
                        rfl

theorem cell23_3423736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 3, 2, 2, 2].length) (baseStart_3423736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3423736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3423736 prefixEnd_3423736 := by exact prefixLift 3423736
  have htrace : WordTrace (prefixWord ++ tailWord_3423736) baseStart_3423736 baseEnd_3423736 := by
    simpa [prefixWord, tailWord_3423736, baseEnd_3423736] using wordTrace_append hprefix tailTrace_3423736
  have hstable : (prefixWord ++ tailWord_3423736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3423736).length < 2 ^ (prefixWord ++ tailWord_3423736).sum := by decide
  have hdescent : baseEnd_3423736 < baseStart_3423736 := by decide
  rcases family_descends (prefixWord ++ tailWord_3423736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3423772 : List Nat := [2, 2, 3, 1, 2, 1, 2, 1, 4, 5]
def baseStart_3423772 : Nat := 118140960795 + 3423772 * 2 ^ 59
def prefixEnd_3423772 : Nat := 4983230072969 + 3 ^ 40 * 3423772 * 2
def baseEnd_3423772 : Nat := 586013562468494570001455

theorem tailTrace_3423772 : CollatzResearch.WordTrace tailWord_3423772 prefixEnd_3423772 586013562468494570001455 := by
  unfold tailWord_3423772
  simp only [CollatzResearch.WordTrace]
  refine ⟨62437611876133126274840785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83250149168177501699787713 62437611876133126274840785)
  ·
    refine ⟨46828208907099844706130589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62437611876133126274840785 46828208907099844706130589)
    ·
      refine ⟨17560578340162441764798971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46828208907099844706130589 17560578340162441764798971)
      ·
        refine ⟨26340867510243662647198457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17560578340162441764798971 26340867510243662647198457)
        ·
          refine ⟨19755650632682746985398843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26340867510243662647198457 19755650632682746985398843)
          ·
            refine ⟨29633475949024120478098265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19755650632682746985398843 29633475949024120478098265)
            ·
              refine ⟨22225106961768090358573699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29633475949024120478098265 22225106961768090358573699)
              ·
                refine ⟨33337660442652135537860549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22225106961768090358573699 33337660442652135537860549)
                ·
                  refine ⟨6250811332997275413348853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33337660442652135537860549 6250811332997275413348853)
                  ·
                    refine ⟨586013562468494570001455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6250811332997275413348853 586013562468494570001455)
                    ·
                      rfl

theorem cell23_3423772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 1, 4, 5].length) (baseStart_3423772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3423772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3423772 prefixEnd_3423772 := by exact prefixLift 3423772
  have htrace : WordTrace (prefixWord ++ tailWord_3423772) baseStart_3423772 baseEnd_3423772 := by
    simpa [prefixWord, tailWord_3423772, baseEnd_3423772] using wordTrace_append hprefix tailTrace_3423772
  have hstable : (prefixWord ++ tailWord_3423772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3423772).length < 2 ^ (prefixWord ++ tailWord_3423772).sum := by decide
  have hdescent : baseEnd_3423772 < baseStart_3423772 := by decide
  rcases family_descends (prefixWord ++ tailWord_3423772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3423809 : List Nat := [1, 2, 5, 1, 1, 1, 2, 3, 2, 1, 4]
def baseStart_3423809 : Nat := 118140960795 + 3423809 * 2 ^ 59
def prefixEnd_3423809 : Nat := 4983230072969 + 3 ^ 40 * 3423809 * 2
def baseEnd_3423809 : Nat := 1758059686189700065241695

theorem tailTrace_3423809 : CollatzResearch.WordTrace tailWord_3423809 prefixEnd_3423809 1758059686189700065241695 := by
  unfold tailWord_3423809
  simp only [CollatzResearch.WordTrace]
  refine ⟨124876573253132207868778481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83251048835421471912518987 124876573253132207868778481)
  ·
    refine ⟨93657429939849155901583861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124876573253132207868778481 93657429939849155901583861)
    ·
      refine ⟨8780384056860858365773487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 93657429939849155901583861 8780384056860858365773487)
      ·
        refine ⟨13170576085291287548660231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8780384056860858365773487 13170576085291287548660231)
        ·
          refine ⟨19755864127936931322990347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13170576085291287548660231 19755864127936931322990347)
          ·
            refine ⟨29633796191905396984485521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19755864127936931322990347 29633796191905396984485521)
            ·
              refine ⟨22225347143929047738364141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29633796191905396984485521 22225347143929047738364141)
              ·
                refine ⟨8334505178973392901886553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22225347143929047738364141 8334505178973392901886553)
                ·
                  refine ⟨6250878884230044676414915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8334505178973392901886553 6250878884230044676414915)
                  ·
                    refine ⟨9376318326345067014622373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6250878884230044676414915 9376318326345067014622373)
                    ·
                      refine ⟨1758059686189700065241695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9376318326345067014622373 1758059686189700065241695)
                      ·
                        rfl

theorem cell23_3423809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_3423809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3423809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3423809 prefixEnd_3423809 := by exact prefixLift 3423809
  have htrace : WordTrace (prefixWord ++ tailWord_3423809) baseStart_3423809 baseEnd_3423809 := by
    simpa [prefixWord, tailWord_3423809, baseEnd_3423809] using wordTrace_append hprefix tailTrace_3423809
  have hstable : (prefixWord ++ tailWord_3423809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3423809).length < 2 ^ (prefixWord ++ tailWord_3423809).sum := by decide
  have hdescent : baseEnd_3423809 < baseStart_3423809 := by decide
  rcases family_descends (prefixWord ++ tailWord_3423809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3423832 : List Nat := [2, 1, 2, 2, 1, 2, 1, 6, 6]
def baseStart_3423832 : Nat := 118140960795 + 3423832 * 2 ^ 59
def prefixEnd_3423832 : Nat := 4983230072969 + 3 ^ 40 * 3423832 * 2
def baseEnd_3423832 : Nat := 195341277360528163917121

theorem tailTrace_3423832 : CollatzResearch.WordTrace tailWord_3423832 prefixEnd_3423832 195341277360528163917121 := by
  unfold tailWord_3423832
  simp only [CollatzResearch.WordTrace]
  refine ⟨62438706066024441398432875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83251608088032588531243833 62438706066024441398432875)
  ·
    refine ⟨93658059099036662097649313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62438706066024441398432875 93658059099036662097649313)
    ·
      refine ⟨70243544324277496573236985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93658059099036662097649313 70243544324277496573236985)
      ·
        refine ⟨52682658243208122429927739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70243544324277496573236985 52682658243208122429927739)
        ·
          refine ⟨79023987364812183644891609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52682658243208122429927739 79023987364812183644891609)
          ·
            refine ⟨59267990523609137733668707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79023987364812183644891609 59267990523609137733668707)
            ·
              refine ⟨88901985785413706600503061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59267990523609137733668707 88901985785413706600503061)
              ·
                refine ⟨4167280583691267496898581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 88901985785413706600503061 4167280583691267496898581)
                ·
                  refine ⟨195341277360528163917121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4167280583691267496898581 195341277360528163917121)
                  ·
                    rfl

theorem cell23_3423832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 6, 6].length) (baseStart_3423832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3423832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3423832 prefixEnd_3423832 := by exact prefixLift 3423832
  have htrace : WordTrace (prefixWord ++ tailWord_3423832) baseStart_3423832 baseEnd_3423832 := by
    simpa [prefixWord, tailWord_3423832, baseEnd_3423832] using wordTrace_append hprefix tailTrace_3423832
  have hstable : (prefixWord ++ tailWord_3423832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3423832).length < 2 ^ (prefixWord ++ tailWord_3423832).sum := by decide
  have hdescent : baseEnd_3423832 < baseStart_3423832 := by decide
  rcases family_descends (prefixWord ++ tailWord_3423832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3423836 : List Nat := [2, 2, 4, 1, 2, 1, 3, 1, 3, 4]
def baseStart_3423836 : Nat := 118140960795 + 3423836 * 2 ^ 59
def prefixEnd_3423836 : Nat := 4983230072969 + 3 ^ 40 * 3423836 * 2
def baseEnd_3423836 : Nat := 586024516722457153201357

theorem tailTrace_3423836 : CollatzResearch.WordTrace tailWord_3423836 prefixEnd_3423836 586024516722457153201357 := by
  unfold tailWord_3423836
  simp only [CollatzResearch.WordTrace]
  refine ⟨62438779012017195740005681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83251705349356260986674241 62438779012017195740005681)
  ·
    refine ⟨46829084259012896805004261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62438779012017195740005681 46829084259012896805004261)
    ·
      refine ⟨8780453298564918150938299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46829084259012896805004261 8780453298564918150938299)
      ·
        refine ⟨13170679947847377226407449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8780453298564918150938299 13170679947847377226407449)
        ·
          refine ⟨9878009960885532919805587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13170679947847377226407449 9878009960885532919805587)
          ·
            refine ⟨14817014941328299379708381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9878009960885532919805587 14817014941328299379708381)
            ·
              refine ⟨5556380602998112267390643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14817014941328299379708381 5556380602998112267390643)
              ·
                refine ⟨8334570904497168401085965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5556380602998112267390643 8334570904497168401085965)
                ·
                  refine ⟨3125464089186438150407237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8334570904497168401085965 3125464089186438150407237)
                  ·
                    refine ⟨586024516722457153201357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3125464089186438150407237 586024516722457153201357)
                    ·
                      rfl

theorem cell23_3423836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 3, 1, 3, 4].length) (baseStart_3423836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3423836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3423836 prefixEnd_3423836 := by exact prefixLift 3423836
  have htrace : WordTrace (prefixWord ++ tailWord_3423836) baseStart_3423836 baseEnd_3423836 := by
    simpa [prefixWord, tailWord_3423836, baseEnd_3423836] using wordTrace_append hprefix tailTrace_3423836
  have hstable : (prefixWord ++ tailWord_3423836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3423836).length < 2 ^ (prefixWord ++ tailWord_3423836).sum := by decide
  have hdescent : baseEnd_3423836 < baseStart_3423836 := by decide
  rcases family_descends (prefixWord ++ tailWord_3423836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3423849 : List Nat := [1, 2, 1, 1, 1, 4, 6, 1, 6]
def baseStart_3423849 : Nat := 118140960795 + 3423849 * 2 ^ 59
def prefixEnd_3423849 : Nat := 4983230072969 + 3 ^ 40 * 3423849 * 2
def baseEnd_3423849 : Nat := 195342247268431100971279

theorem tailTrace_3423849 : CollatzResearch.WordTrace tailWord_3423849 prefixEnd_3423849 195342247268431100971279 := by
  unfold tailWord_3423849
  simp only [CollatzResearch.WordTrace]
  refine ⟨124878032172987294700234601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83252021448658196466823067 124878032172987294700234601)
  ·
    refine ⟨93658524129740471025175951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124878032172987294700234601 93658524129740471025175951)
    ·
      refine ⟨140487786194610706537763927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93658524129740471025175951 140487786194610706537763927)
      ·
        refine ⟨210731679291916059806645891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140487786194610706537763927 210731679291916059806645891)
        ·
          refine ⟨316097518937874089709968837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210731679291916059806645891 316097518937874089709968837)
          ·
            refine ⟨59268284800851391820619157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 316097518937874089709968837 59268284800851391820619157)
            ·
              refine ⟨2778200850039908991591523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 59268284800851391820619157 2778200850039908991591523)
              ·
                refine ⟨4167301275059863487387285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2778200850039908991591523 4167301275059863487387285)
                ·
                  refine ⟨195342247268431100971279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4167301275059863487387285 195342247268431100971279)
                  ·
                    rfl

theorem cell23_3423849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 6, 1, 6].length) (baseStart_3423849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3423849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3423849 prefixEnd_3423849 := by exact prefixLift 3423849
  have htrace : WordTrace (prefixWord ++ tailWord_3423849) baseStart_3423849 baseEnd_3423849 := by
    simpa [prefixWord, tailWord_3423849, baseEnd_3423849] using wordTrace_append hprefix tailTrace_3423849
  have hstable : (prefixWord ++ tailWord_3423849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3423849).length < 2 ^ (prefixWord ++ tailWord_3423849).sum := by decide
  have hdescent : baseEnd_3423849 < baseStart_3423849 := by decide
  rcases family_descends (prefixWord ++ tailWord_3423849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3423919 : List Nat := [1, 1, 2, 1, 2, 4, 1, 3, 3, 2, 3]
def baseStart_3423919 : Nat := 118140960795 + 3423919 * 2 ^ 59
def prefixEnd_3423919 : Nat := 4983230072969 + 3 ^ 40 * 3423919 * 2
def baseEnd_3423919 : Nat := 1758116169061694634866189

theorem tailTrace_3423919 : CollatzResearch.WordTrace tailWord_3423919 prefixEnd_3423919 1758116169061694634866189 := by
  unfold tailWord_3423919
  simp only [CollatzResearch.WordTrace]
  refine ⟨124880585282733696655282811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83253723521822464436855207 124880585282733696655282811)
  ·
    refine ⟨187320877924100544982924217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124880585282733696655282811 187320877924100544982924217)
    ·
      refine ⟨140490658443075408737193163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187320877924100544982924217 140490658443075408737193163)
      ·
        refine ⟨210735987664613113105789745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140490658443075408737193163 210735987664613113105789745)
        ·
          refine ⟨158051990748459834829342309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210735987664613113105789745 158051990748459834829342309)
          ·
            refine ⟨29634748265336219030501683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 158051990748459834829342309 29634748265336219030501683)
            ·
              refine ⟨44452122398004328545752525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29634748265336219030501683 44452122398004328545752525)
              ·
                refine ⟨16669545899251623204657197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44452122398004328545752525 16669545899251623204657197)
                ·
                  refine ⟨6251079712219358701746449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16669545899251623204657197 6251079712219358701746449)
                  ·
                    refine ⟨4688309784164519026309837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6251079712219358701746449 4688309784164519026309837)
                    ·
                      refine ⟨1758116169061694634866189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4688309784164519026309837 1758116169061694634866189)
                      ·
                        rfl

theorem cell23_3423919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 3, 3, 2, 3].length) (baseStart_3423919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3423919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3423919 prefixEnd_3423919 := by exact prefixLift 3423919
  have htrace : WordTrace (prefixWord ++ tailWord_3423919) baseStart_3423919 baseEnd_3423919 := by
    simpa [prefixWord, tailWord_3423919, baseEnd_3423919] using wordTrace_append hprefix tailTrace_3423919
  have hstable : (prefixWord ++ tailWord_3423919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3423919).length < 2 ^ (prefixWord ++ tailWord_3423919).sum := by decide
  have hdescent : baseEnd_3423919 < baseStart_3423919 := by decide
  rcases family_descends (prefixWord ++ tailWord_3423919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3423922 : List Nat := [3, 2, 1, 1, 1, 2, 2, 11]
def baseStart_3423922 : Nat := 118140960795 + 3423922 * 2 ^ 59
def prefixEnd_3423922 : Nat := 4983230072969 + 3 ^ 40 * 3423922 * 2
def baseEnd_3423922 : Nat := 65115470722357708264025

theorem tailTrace_3423922 : CollatzResearch.WordTrace tailWord_3423922 prefixEnd_3423922 65115470722357708264025 := by
  unfold tailWord_3423922
  simp only [CollatzResearch.WordTrace]
  refine ⟨31220173675430707041910505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83253796467815218778428013 31220173675430707041910505)
  ·
    refine ⟨23415130256573030281432879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31220173675430707041910505 23415130256573030281432879)
    ·
      refine ⟨35122695384859545422149319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23415130256573030281432879 35122695384859545422149319)
      ·
        refine ⟨52684043077289318133223979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35122695384859545422149319 52684043077289318133223979)
        ·
          refine ⟨79026064615933977199835969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52684043077289318133223979 79026064615933977199835969)
          ·
            refine ⟨59269548461950482899876977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79026064615933977199835969 59269548461950482899876977)
            ·
              refine ⟨44452161346462862174907733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59269548461950482899876977 44452161346462862174907733)
              ·
                refine ⟨65115470722357708264025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 44452161346462862174907733 65115470722357708264025)
                ·
                  rfl

theorem cell23_3423922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 11].length) (baseStart_3423922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3423922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3423922 prefixEnd_3423922 := by exact prefixLift 3423922
  have htrace : WordTrace (prefixWord ++ tailWord_3423922) baseStart_3423922 baseEnd_3423922 := by
    simpa [prefixWord, tailWord_3423922, baseEnd_3423922] using wordTrace_append hprefix tailTrace_3423922
  have hstable : (prefixWord ++ tailWord_3423922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3423922).length < 2 ^ (prefixWord ++ tailWord_3423922).sum := by decide
  have hdescent : baseEnd_3423922 < baseStart_3423922 := by decide
  rcases family_descends (prefixWord ++ tailWord_3423922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
