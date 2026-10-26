import V185TrunkScan23Chunk0277

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1644142 : List Nat := [4, 1, 2, 2, 3, 1, 1, 1, 4, 2, 2]
def baseStart_1644142 : Nat := 118140960795 + 1644142 * 2 ^ 59
def prefixEnd_1644142 : Nat := 4983230072969 + 3 ^ 40 * 1644142 * 2
def baseEnd_1644142 : Nat := 844235110244611520563735

theorem tailTrace_1644142 : CollatzResearch.WordTrace tailWord_1644142 prefixEnd_1644142 844235110244611520563735 := by
  unfold tailWord_1644142
  simp only [CollatzResearch.WordTrace]
  refine ⟨7495848151195225742913835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39977856806374537295540453 7495848151195225742913835)
  ·
    refine ⟨11243772226792838614370753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7495848151195225742913835 11243772226792838614370753)
    ·
      refine ⟨8432829170094628960778065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11243772226792838614370753 8432829170094628960778065)
      ·
        refine ⟨6324621877570971720583549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8432829170094628960778065 6324621877570971720583549)
        ·
          refine ⟨2371733204089114395218831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6324621877570971720583549 2371733204089114395218831)
          ·
            refine ⟨3557599806133671592828247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2371733204089114395218831 3557599806133671592828247)
            ·
              refine ⟨5336399709200507389242371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3557599806133671592828247 5336399709200507389242371)
              ·
                refine ⟨8004599563800761083863557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5336399709200507389242371 8004599563800761083863557)
                ·
                  refine ⟨1500862418212642703224417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8004599563800761083863557 1500862418212642703224417)
                  ·
                    refine ⟨1125646813659482027418313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1500862418212642703224417 1125646813659482027418313)
                    ·
                      refine ⟨844235110244611520563735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1125646813659482027418313 844235110244611520563735)
                      ·
                        rfl

theorem cell23_1644142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 1, 4, 2, 2].length) (baseStart_1644142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1644142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1644142 prefixEnd_1644142 := by exact prefixLift 1644142
  have htrace : WordTrace (prefixWord ++ tailWord_1644142) baseStart_1644142 baseEnd_1644142 := by
    simpa [prefixWord, tailWord_1644142, baseEnd_1644142] using wordTrace_append hprefix tailTrace_1644142
  have hstable : (prefixWord ++ tailWord_1644142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644142).length < 2 ^ (prefixWord ++ tailWord_1644142).sum := by decide
  have hdescent : baseEnd_1644142 < baseStart_1644142 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644161 : List Nat := [1, 2, 4, 2, 1, 2, 1, 2, 1, 7]
def baseStart_1644161 : Nat := 118140960795 + 1644161 * 2 ^ 59
def prefixEnd_1644161 : Nat := 4983230072969 + 3 ^ 40 * 1644161 * 2
def baseEnd_1644161 : Nat := 281414955459015648742049

theorem tailTrace_1644161 : CollatzResearch.WordTrace tailWord_1644161 prefixEnd_1644161 281414955459015648742049 := by
  unfold tailWord_1644161
  simp only [CollatzResearch.WordTrace]
  refine ⟨59967478196492972188252337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39978318797661981458834891 59967478196492972188252337)
  ·
    refine ⟨44975608647369729141189253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59967478196492972188252337 44975608647369729141189253)
    ·
      refine ⟨8432926621381824213972985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44975608647369729141189253 8432926621381824213972985)
      ·
        refine ⟨6324694966036368160479739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8432926621381824213972985 6324694966036368160479739)
        ·
          refine ⟨9487042449054552240719609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6324694966036368160479739 9487042449054552240719609)
          ·
            refine ⟨7115281836790914180539707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9487042449054552240719609 7115281836790914180539707)
            ·
              refine ⟨10672922755186371270809561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7115281836790914180539707 10672922755186371270809561)
              ·
                refine ⟨8004692066389778453107171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10672922755186371270809561 8004692066389778453107171)
                ·
                  refine ⟨12007038099584667679660757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8004692066389778453107171 12007038099584667679660757)
                  ·
                    refine ⟨281414955459015648742049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12007038099584667679660757 281414955459015648742049)
                    ·
                      rfl

theorem cell23_1644161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 2, 1, 7].length) (baseStart_1644161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1644161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1644161 prefixEnd_1644161 := by exact prefixLift 1644161
  have htrace : WordTrace (prefixWord ++ tailWord_1644161) baseStart_1644161 baseEnd_1644161 := by
    simpa [prefixWord, tailWord_1644161, baseEnd_1644161] using wordTrace_append hprefix tailTrace_1644161
  have hstable : (prefixWord ++ tailWord_1644161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644161).length < 2 ^ (prefixWord ++ tailWord_1644161).sum := by decide
  have hdescent : baseEnd_1644161 < baseStart_1644161 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644181 : List Nat := [1, 3, 2, 1, 1, 1, 1, 2, 6, 1, 4]
def baseStart_1644181 : Nat := 118140960795 + 1644181 * 2 ^ 59
def prefixEnd_1644181 : Nat := 4983230072969 + 3 ^ 40 * 1644181 * 2
def baseEnd_1644181 : Nat := 844255135990136867976055

theorem tailTrace_1644181 : CollatzResearch.WordTrace tailWord_1644181 prefixEnd_1644181 844255135990136867976055 := by
  unfold tailWord_1644181
  simp only [CollatzResearch.WordTrace]
  refine ⟨59968207656420515603980397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39978805104280343735986931 59968207656420515603980397)
  ·
    refine ⟨22488077871157693351492649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59968207656420515603980397 22488077871157693351492649)
    ·
      refine ⟨16866058403368270013619487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22488077871157693351492649 16866058403368270013619487)
      ·
        refine ⟨25299087605052405020429231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16866058403368270013619487 25299087605052405020429231)
        ·
          refine ⟨37948631407578607530643847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25299087605052405020429231 37948631407578607530643847)
          ·
            refine ⟨56922947111367911295965771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37948631407578607530643847 56922947111367911295965771)
            ·
              refine ⟨85384420667051866943948657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56922947111367911295965771 85384420667051866943948657)
              ·
                refine ⟨64038315500288900207961493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85384420667051866943948657 64038315500288900207961493)
                ·
                  refine ⟨3001796039076042197248195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 64038315500288900207961493 3001796039076042197248195)
                  ·
                    refine ⟨4502694058614063295872293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3001796039076042197248195 4502694058614063295872293)
                    ·
                      refine ⟨844255135990136867976055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4502694058614063295872293 844255135990136867976055)
                      ·
                        rfl

theorem cell23_1644181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 6, 1, 4].length) (baseStart_1644181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1644181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1644181 prefixEnd_1644181 := by exact prefixLift 1644181
  have htrace : WordTrace (prefixWord ++ tailWord_1644181) baseStart_1644181 baseEnd_1644181 := by
    simpa [prefixWord, tailWord_1644181, baseEnd_1644181] using wordTrace_append hprefix tailTrace_1644181
  have hstable : (prefixWord ++ tailWord_1644181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644181).length < 2 ^ (prefixWord ++ tailWord_1644181).sum := by decide
  have hdescent : baseEnd_1644181 < baseStart_1644181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644208 : List Nat := [2, 1, 1, 1, 2, 1, 7, 1, 3, 4]
def baseStart_1644208 : Nat := 118140960795 + 1644208 * 2 ^ 59
def prefixEnd_1644208 : Nat := 4983230072969 + 3 ^ 40 * 1644208 * 2
def baseEnd_1644208 : Nat := 281422999989269420779477

theorem tailTrace_1644208 : CollatzResearch.WordTrace tailWord_1644208 prefixEnd_1644208 281422999989269420779477 := by
  unfold tailWord_1644208
  simp only [CollatzResearch.WordTrace]
  refine ⟨29984596213661349607606639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39979461618215132810142185 29984596213661349607606639)
  ·
    refine ⟨44976894320492024411409959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29984596213661349607606639 44976894320492024411409959)
    ·
      refine ⟨67465341480738036617114939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44976894320492024411409959 67465341480738036617114939)
      ·
        refine ⟨101198012221107054925672409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67465341480738036617114939 101198012221107054925672409)
        ·
          refine ⟨75898509165830291194254307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101198012221107054925672409 75898509165830291194254307)
          ·
            refine ⟨113847763748745436791381461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75898509165830291194254307 113847763748745436791381461)
            ·
              refine ⟨2668306962861221174798003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 113847763748745436791381461 2668306962861221174798003)
              ·
                refine ⟨4002460444291831762197005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2668306962861221174798003 4002460444291831762197005)
                ·
                  refine ⟨1500922666609436910823877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4002460444291831762197005 1500922666609436910823877)
                  ·
                    refine ⟨281422999989269420779477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1500922666609436910823877 281422999989269420779477)
                    ·
                      rfl

theorem cell23_1644208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 7, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 7, 1, 3, 4].length) (baseStart_1644208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1644208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1644208 prefixEnd_1644208 := by exact prefixLift 1644208
  have htrace : WordTrace (prefixWord ++ tailWord_1644208) baseStart_1644208 baseEnd_1644208 := by
    simpa [prefixWord, tailWord_1644208, baseEnd_1644208] using wordTrace_append hprefix tailTrace_1644208
  have hstable : (prefixWord ++ tailWord_1644208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644208).length < 2 ^ (prefixWord ++ tailWord_1644208).sum := by decide
  have hdescent : baseEnd_1644208 < baseStart_1644208 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644288 : List Nat := [2, 1, 1, 2, 1, 1, 2, 3, 2, 6, 2]
def baseStart_1644288 : Nat := 118140960795 + 1644288 * 2 ^ 59
def prefixEnd_1644288 : Nat := 4983230072969 + 3 ^ 40 * 1644288 * 2
def baseEnd_1644288 : Nat := 844310078420167949338063

theorem tailTrace_1644288 : CollatzResearch.WordTrace tailWord_1644288 prefixEnd_1644288 844310078420167949338063 := by
  unfold tailWord_1644288
  simp only [CollatzResearch.WordTrace]
  refine ⟨29986055133516436439062759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39981406844688581918750345 29986055133516436439062759)
  ·
    refine ⟨44979082700274654658594139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29986055133516436439062759 44979082700274654658594139)
    ·
      refine ⟨67468624050411981987891209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44979082700274654658594139 67468624050411981987891209)
      ·
        refine ⟨50601468037808986490918407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67468624050411981987891209 50601468037808986490918407)
        ·
          refine ⟨75902202056713479736377611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50601468037808986490918407 75902202056713479736377611)
          ·
            refine ⟨113853303085070219604566417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75902202056713479736377611 113853303085070219604566417)
            ·
              refine ⟨85389977313802664703424813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113853303085070219604566417 85389977313802664703424813)
              ·
                refine ⟨32021241492675999263784305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85389977313802664703424813 32021241492675999263784305)
                ·
                  refine ⟨24015931119506999447838229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32021241492675999263784305 24015931119506999447838229)
                  ·
                    refine ⟨1125746771226890599117417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24015931119506999447838229 1125746771226890599117417)
                    ·
                      refine ⟨844310078420167949338063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1125746771226890599117417 844310078420167949338063)
                      ·
                        rfl

theorem cell23_1644288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 2, 6, 2].length) (baseStart_1644288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1644288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1644288 prefixEnd_1644288 := by exact prefixLift 1644288
  have htrace : WordTrace (prefixWord ++ tailWord_1644288) baseStart_1644288 baseEnd_1644288 := by
    simpa [prefixWord, tailWord_1644288, baseEnd_1644288] using wordTrace_append hprefix tailTrace_1644288
  have hstable : (prefixWord ++ tailWord_1644288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644288).length < 2 ^ (prefixWord ++ tailWord_1644288).sum := by decide
  have hdescent : baseEnd_1644288 < baseStart_1644288 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644292 : List Nat := [2, 3, 2, 2, 1, 2, 3, 1, 2, 3, 2]
def baseStart_1644292 : Nat := 118140960795 + 1644292 * 2 ^ 59
def prefixEnd_1644292 : Nat := 4983230072969 + 3 ^ 40 * 1644292 * 2
def baseEnd_1644292 : Nat := 844312132342785933688045

theorem tailTrace_1644292 : CollatzResearch.WordTrace tailWord_1644292 prefixEnd_1644292 844312132342785933688045 := by
  unfold tailWord_1644292
  simp only [CollatzResearch.WordTrace]
  refine ⟨29986128079509190780635565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39981504106012254374180753 29986128079509190780635565)
  ·
    refine ⟨11244798029815946542738337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29986128079509190780635565 11244798029815946542738337)
    ·
      refine ⟨8433598522361959907053753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11244798029815946542738337 8433598522361959907053753)
      ·
        refine ⟨6325198891771469930290315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8433598522361959907053753 6325198891771469930290315)
        ·
          refine ⟨9487798337657204895435473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6325198891771469930290315 9487798337657204895435473)
          ·
            refine ⟨7115848753242903671576605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9487798337657204895435473 7115848753242903671576605)
            ·
              refine ⟨2668443282466088876841227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7115848753242903671576605 2668443282466088876841227)
              ·
                refine ⟨4002664923699133315261841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2668443282466088876841227 4002664923699133315261841)
                ·
                  refine ⟨3001998692774349986446381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4002664923699133315261841 3001998692774349986446381)
                  ·
                    refine ⟨1125749509790381244917393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3001998692774349986446381 1125749509790381244917393)
                    ·
                      refine ⟨844312132342785933688045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1125749509790381244917393 844312132342785933688045)
                      ·
                        rfl

theorem cell23_1644292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 3, 1, 2, 3, 2].length) (baseStart_1644292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1644292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1644292 prefixEnd_1644292 := by exact prefixLift 1644292
  have htrace : WordTrace (prefixWord ++ tailWord_1644292) baseStart_1644292 baseEnd_1644292 := by
    simpa [prefixWord, tailWord_1644292, baseEnd_1644292] using wordTrace_append hprefix tailTrace_1644292
  have hstable : (prefixWord ++ tailWord_1644292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644292).length < 2 ^ (prefixWord ++ tailWord_1644292).sum := by decide
  have hdescent : baseEnd_1644292 < baseStart_1644292 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644298 : List Nat := [3, 1, 2, 2, 1, 3, 2, 2, 1, 6]
def baseStart_1644298 : Nat := 118140960795 + 1644298 * 2 ^ 59
def prefixEnd_1644298 : Nat := 4983230072969 + 3 ^ 40 * 1644298 * 2
def baseEnd_1644298 : Nat := 281438404408904303404339

theorem tailTrace_1644298 : CollatzResearch.WordTrace tailWord_1644298 prefixEnd_1644298 281438404408904303404339 := by
  unfold tailWord_1644298
  simp only [CollatzResearch.WordTrace]
  refine ⟨14993118749249161146497387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39981649997997763057326365 14993118749249161146497387)
  ·
    refine ⟨22489678123873741719746081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14993118749249161146497387 22489678123873741719746081)
    ·
      refine ⟨16867258592905306289809561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22489678123873741719746081 16867258592905306289809561)
      ·
        refine ⟨12650443944678979717357171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16867258592905306289809561 12650443944678979717357171)
        ·
          refine ⟨18975665917018469576035757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12650443944678979717357171 18975665917018469576035757)
          ·
            refine ⟨7115874718881926091013409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18975665917018469576035757 7115874718881926091013409)
            ·
              refine ⟨5336906039161444568260057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7115874718881926091013409 5336906039161444568260057)
              ·
                refine ⟨4002679529371083426195043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5336906039161444568260057 4002679529371083426195043)
                ·
                  refine ⟨6004019294056625139292565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4002679529371083426195043 6004019294056625139292565)
                  ·
                    refine ⟨281438404408904303404339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6004019294056625139292565 281438404408904303404339)
                    ·
                      rfl

theorem cell23_1644298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 2, 1, 6].length) (baseStart_1644298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1644298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1644298 prefixEnd_1644298 := by exact prefixLift 1644298
  have htrace : WordTrace (prefixWord ++ tailWord_1644298) baseStart_1644298 baseEnd_1644298 := by
    simpa [prefixWord, tailWord_1644298, baseEnd_1644298] using wordTrace_append hprefix tailTrace_1644298
  have hstable : (prefixWord ++ tailWord_1644298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644298).length < 2 ^ (prefixWord ++ tailWord_1644298).sum := by decide
  have hdescent : baseEnd_1644298 < baseStart_1644298 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644305 : List Nat := [1, 2, 2, 1, 1, 3, 1, 1, 7, 2, 2]
def baseStart_1644305 : Nat := 118140960795 + 1644305 * 2 ^ 59
def prefixEnd_1644305 : Nat := 4983230072969 + 3 ^ 40 * 1644305 * 2
def baseEnd_1644305 : Nat := 844318807591294382825485

theorem tailTrace_1644305 : CollatzResearch.WordTrace tailWord_1644305 prefixEnd_1644305 844318807591294382825485 := by
  unfold tailWord_1644305
  simp only [CollatzResearch.WordTrace]
  refine ⟨59972730307971284781494369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39981820205314189854329579 59972730307971284781494369)
  ·
    refine ⟨44979547730978463586120777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59972730307971284781494369 44979547730978463586120777)
    ·
      refine ⟨33734660798233847689590583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44979547730978463586120777 33734660798233847689590583)
      ·
        refine ⟨50601991197350771534385875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33734660798233847689590583 50601991197350771534385875)
        ·
          refine ⟨75902986796026157301578813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50601991197350771534385875 75902986796026157301578813)
          ·
            refine ⟨28463620048509808988092055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75902986796026157301578813 28463620048509808988092055)
            ·
              refine ⟨42695430072764713482138083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28463620048509808988092055 42695430072764713482138083)
              ·
                refine ⟨64043145109147070223207125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42695430072764713482138083 64043145109147070223207125)
                ·
                  refine ⟨1501011213495634458356417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 64043145109147070223207125 1501011213495634458356417)
                  ·
                    refine ⟨1125758410121725843767313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1501011213495634458356417 1125758410121725843767313)
                    ·
                      refine ⟨844318807591294382825485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1125758410121725843767313 844318807591294382825485)
                      ·
                        rfl

theorem cell23_1644305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 7, 2, 2].length) (baseStart_1644305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1644305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1644305 prefixEnd_1644305 := by exact prefixLift 1644305
  have htrace : WordTrace (prefixWord ++ tailWord_1644305) baseStart_1644305 baseEnd_1644305 := by
    simpa [prefixWord, tailWord_1644305, baseEnd_1644305] using wordTrace_append hprefix tailTrace_1644305
  have hstable : (prefixWord ++ tailWord_1644305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644305).length < 2 ^ (prefixWord ++ tailWord_1644305).sum := by decide
  have hdescent : baseEnd_1644305 < baseStart_1644305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644332 : List Nat := [2, 2, 1, 1, 1, 6, 3, 1, 2, 4]
def baseStart_1644332 : Nat := 118140960795 + 1644332 * 2 ^ 59
def prefixEnd_1644332 : Nat := 4983230072969 + 3 ^ 40 * 1644332 * 2
def baseEnd_1644332 : Nat := 281444223856321925729287

theorem tailTrace_1644332 : CollatzResearch.WordTrace tailWord_1644332 prefixEnd_1644332 281444223856321925729287 := by
  unfold tailWord_1644332
  simp only [CollatzResearch.WordTrace]
  refine ⟨29986857539436734196363625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39982476719248978928484833 29986857539436734196363625)
  ·
    refine ⟨22490143154577550647272719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29986857539436734196363625 22490143154577550647272719)
    ·
      refine ⟨33735214731866325970909079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22490143154577550647272719 33735214731866325970909079)
      ·
        refine ⟨50602822097799488956363619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33735214731866325970909079 50602822097799488956363619)
        ·
          refine ⟨75904233146699233434545429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50602822097799488956363619 75904233146699233434545429)
          ·
            refine ⟨3558010928751526567244317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 75904233146699233434545429 3558010928751526567244317)
            ·
              refine ⟨1334254098281822462716619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3558010928751526567244317 1334254098281822462716619)
              ·
                refine ⟨2001381147422733694074929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1334254098281822462716619 2001381147422733694074929)
                ·
                  refine ⟨1501035860567050270556197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2001381147422733694074929 1501035860567050270556197)
                  ·
                    refine ⟨281444223856321925729287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1501035860567050270556197 281444223856321925729287)
                    ·
                      rfl

theorem cell23_1644332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 4].length) (baseStart_1644332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1644332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1644332 prefixEnd_1644332 := by exact prefixLift 1644332
  have htrace : WordTrace (prefixWord ++ tailWord_1644332) baseStart_1644332 baseEnd_1644332 := by
    simpa [prefixWord, tailWord_1644332, baseEnd_1644332] using wordTrace_append hprefix tailTrace_1644332
  have hstable : (prefixWord ++ tailWord_1644332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644332).length < 2 ^ (prefixWord ++ tailWord_1644332).sum := by decide
  have hdescent : baseEnd_1644332 < baseStart_1644332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644345 : List Nat := [1, 2, 1, 7, 1, 1, 1, 9]
def baseStart_1644345 : Nat := 118140960795 + 1644345 * 2 ^ 59
def prefixEnd_1644345 : Nat := 4983230072969 + 3 ^ 40 * 1644345 * 2
def baseEnd_1644345 : Nat := 31271827659906452826863

theorem tailTrace_1644345 : CollatzResearch.WordTrace tailWord_1644345 prefixEnd_1644345 31271827659906452826863 := by
  unfold tailWord_1644345
  simp only [CollatzResearch.WordTrace]
  refine ⟨59974189227826371612950489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39982792818550914408633659 59974189227826371612950489)
  ·
    refine ⟨44980641920869778709712867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59974189227826371612950489 44980641920869778709712867)
    ·
      refine ⟨67470962881304668064569301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44980641920869778709712867 67470962881304668064569301)
      ·
        refine ⟨1581350692530578157763343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 67470962881304668064569301 1581350692530578157763343)
        ·
          refine ⟨2372026038795867236645015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1581350692530578157763343 2372026038795867236645015)
          ·
            refine ⟨3558039058193800854967523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2372026038795867236645015 3558039058193800854967523)
            ·
              refine ⟨5337058587290701282451285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3558039058193800854967523 5337058587290701282451285)
              ·
                refine ⟨31271827659906452826863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5337058587290701282451285 31271827659906452826863)
                ·
                  rfl

theorem cell23_1644345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 9].length) (baseStart_1644345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1644345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1644345 prefixEnd_1644345 := by exact prefixLift 1644345
  have htrace : WordTrace (prefixWord ++ tailWord_1644345) baseStart_1644345 baseEnd_1644345 := by
    simpa [prefixWord, tailWord_1644345, baseEnd_1644345] using wordTrace_append hprefix tailTrace_1644345
  have hstable : (prefixWord ++ tailWord_1644345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644345).length < 2 ^ (prefixWord ++ tailWord_1644345).sum := by decide
  have hdescent : baseEnd_1644345 < baseStart_1644345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644355 : List Nat := [1, 1, 1, 3, 1, 5, 1, 2, 4, 1, 3]
def baseStart_1644355 : Nat := 118140960795 + 1644355 * 2 ^ 59
def prefixEnd_1644355 : Nat := 4983230072969 + 3 ^ 40 * 1644355 * 2
def baseEnd_1644355 : Nat := 844344481624019187200255

theorem tailTrace_1644355 : CollatzResearch.WordTrace tailWord_1644355 prefixEnd_1644355 844344481624019187200255 := by
  unfold tailWord_1644355
  simp only [CollatzResearch.WordTrace]
  refine ⟨59974553957790143320814519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39983035971860095547209679 59974553957790143320814519)
  ·
    refine ⟨89961830936685214981221779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59974553957790143320814519 89961830936685214981221779)
    ·
      refine ⟨134942746405027822471832669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89961830936685214981221779 134942746405027822471832669)
      ·
        refine ⟨50603529901885433426937251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134942746405027822471832669 50603529901885433426937251)
        ·
          refine ⟨75905294852828150140405877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50603529901885433426937251 75905294852828150140405877)
          ·
            refine ⟨7116121392452639075663051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 75905294852828150140405877 7116121392452639075663051)
            ·
              refine ⟨10674182088678958613494577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7116121392452639075663051 10674182088678958613494577)
              ·
                refine ⟨8005636566509218960120933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10674182088678958613494577 8005636566509218960120933)
                ·
                  refine ⟨1501056856220478555022675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8005636566509218960120933 1501056856220478555022675)
                  ·
                    refine ⟨2251585284330717832534013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1501056856220478555022675 2251585284330717832534013)
                    ·
                      refine ⟨844344481624019187200255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2251585284330717832534013 844344481624019187200255)
                      ·
                        rfl

theorem cell23_1644355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 2, 4, 1, 3].length) (baseStart_1644355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1644355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1644355 prefixEnd_1644355 := by exact prefixLift 1644355
  have htrace : WordTrace (prefixWord ++ tailWord_1644355) baseStart_1644355 baseEnd_1644355 := by
    simpa [prefixWord, tailWord_1644355, baseEnd_1644355] using wordTrace_append hprefix tailTrace_1644355
  have hstable : (prefixWord ++ tailWord_1644355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644355).length < 2 ^ (prefixWord ++ tailWord_1644355).sum := by decide
  have hdescent : baseEnd_1644355 < baseStart_1644355 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644372 : List Nat := [2, 4, 1, 1, 3, 1, 2, 1, 4, 1, 3]
def baseStart_1644372 : Nat := 118140960795 + 1644372 * 2 ^ 59
def prefixEnd_1644372 : Nat := 4983230072969 + 3 ^ 40 * 1644372 * 2
def baseEnd_1644372 : Nat := 844353210795145620687677

theorem tailTrace_1644372 : CollatzResearch.WordTrace tailWord_1644372 prefixEnd_1644372 844353210795145620687677 := by
  unfold tailWord_1644372
  simp only [CollatzResearch.WordTrace]
  refine ⟨29987586999364277612091685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39983449332485703482788913 29987586999364277612091685)
  ·
    refine ⟨5622672562380802052267191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29987586999364277612091685 5622672562380802052267191)
    ·
      refine ⟨8434008843571203078400787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5622672562380802052267191 8434008843571203078400787)
      ·
        refine ⟨12651013265356804617601181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8434008843571203078400787 12651013265356804617601181)
        ·
          refine ⟨4744129974508801731600443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12651013265356804617601181 4744129974508801731600443)
          ·
            refine ⟨7116194961763202597400665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4744129974508801731600443 7116194961763202597400665)
            ·
              refine ⟨5337146221322401948050499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7116194961763202597400665 5337146221322401948050499)
              ·
                refine ⟨8005719331983602922075749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5337146221322401948050499 8005719331983602922075749)
                ·
                  refine ⟨1501072374746925547889203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8005719331983602922075749 1501072374746925547889203)
                  ·
                    refine ⟨2251608562120388321833805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1501072374746925547889203 2251608562120388321833805)
                    ·
                      refine ⟨844353210795145620687677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2251608562120388321833805 844353210795145620687677)
                      ·
                        rfl

theorem cell23_1644372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 1, 4, 1, 3].length) (baseStart_1644372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1644372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1644372 prefixEnd_1644372 := by exact prefixLift 1644372
  have htrace : WordTrace (prefixWord ++ tailWord_1644372) baseStart_1644372 baseEnd_1644372 := by
    simpa [prefixWord, tailWord_1644372, baseEnd_1644372] using wordTrace_append hprefix tailTrace_1644372
  have hstable : (prefixWord ++ tailWord_1644372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644372).length < 2 ^ (prefixWord ++ tailWord_1644372).sum := by decide
  have hdescent : baseEnd_1644372 < baseStart_1644372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644378 : List Nat := [3, 1, 1, 2, 1, 3, 2, 1, 2, 3, 4]
def baseStart_1644378 : Nat := 118140960795 + 1644378 * 2 ^ 59
def prefixEnd_1644378 : Nat := 4983230072969 + 3 ^ 40 * 1644378 * 2
def baseEnd_1644378 : Nat := 844356291679072597212649

theorem tailTrace_1644378 : CollatzResearch.WordTrace tailWord_1644378 prefixEnd_1644378 844356291679072597212649 := by
  unfold tailWord_1644378
  simp only [CollatzResearch.WordTrace]
  refine ⟨14993848209176704562225447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39983595224471212165934525 14993848209176704562225447)
  ·
    refine ⟨22490772313765056843338171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14993848209176704562225447 22490772313765056843338171)
    ·
      refine ⟨33736158470647585265007257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22490772313765056843338171 33736158470647585265007257)
      ·
        refine ⟨25302118852985688948755443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33736158470647585265007257 25302118852985688948755443)
        ·
          refine ⟨37953178279478533423133165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25302118852985688948755443 37953178279478533423133165)
          ·
            refine ⟨14232441854804450033674937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37953178279478533423133165 14232441854804450033674937)
            ·
              refine ⟨10674331391103337525256203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14232441854804450033674937 10674331391103337525256203)
              ·
                refine ⟨16011497086655006287884305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10674331391103337525256203 16011497086655006287884305)
                ·
                  refine ⟨12008622814991254715913229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16011497086655006287884305 12008622814991254715913229)
                  ·
                    refine ⟨4503233555621720518467461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12008622814991254715913229 4503233555621720518467461)
                    ·
                      refine ⟨844356291679072597212649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4503233555621720518467461 844356291679072597212649)
                      ·
                        rfl

theorem cell23_1644378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 1, 2, 3, 4].length) (baseStart_1644378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1644378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1644378 prefixEnd_1644378 := by exact prefixLift 1644378
  have htrace : WordTrace (prefixWord ++ tailWord_1644378) baseStart_1644378 baseEnd_1644378 := by
    simpa [prefixWord, tailWord_1644378, baseEnd_1644378] using wordTrace_append hprefix tailTrace_1644378
  have hstable : (prefixWord ++ tailWord_1644378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644378).length < 2 ^ (prefixWord ++ tailWord_1644378).sum := by decide
  have hdescent : baseEnd_1644378 < baseStart_1644378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644395 : List Nat := [1, 1, 1, 1, 2, 2, 3, 5, 1, 4, 2]
def baseStart_1644395 : Nat := 118140960795 + 1644395 * 2 ^ 59
def prefixEnd_1644395 : Nat := 4983230072969 + 3 ^ 40 * 1644395 * 2
def baseEnd_1644395 : Nat := 844365020850199030700071

theorem tailTrace_1644395 : CollatzResearch.WordTrace tailWord_1644395 prefixEnd_1644395 844365020850199030700071 := by
  unfold tailWord_1644395
  simp only [CollatzResearch.WordTrace]
  refine ⟨59976012877645230152270639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39984008585096820101513759 59976012877645230152270639)
  ·
    refine ⟨89964019316467845228405959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59976012877645230152270639 89964019316467845228405959)
    ·
      refine ⟨134946028974701767842608939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89964019316467845228405959 134946028974701767842608939)
      ·
        refine ⟨202419043462052651763913409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134946028974701767842608939 202419043462052651763913409)
        ·
          refine ⟨151814282596539488822935057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 202419043462052651763913409 151814282596539488822935057)
          ·
            refine ⟨113860711947404616617201293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151814282596539488822935057 113860711947404616617201293)
            ·
              refine ⟨42697766980276731231450485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113860711947404616617201293 42697766980276731231450485)
              ·
                refine ⟨4002915654400943552948483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42697766980276731231450485 4002915654400943552948483)
                ·
                  refine ⟨6004373481601415329422725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4002915654400943552948483 6004373481601415329422725)
                  ·
                    refine ⟨1125820027800265374266761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6004373481601415329422725 1125820027800265374266761)
                    ·
                      refine ⟨844365020850199030700071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1125820027800265374266761 844365020850199030700071)
                      ·
                        rfl

theorem cell23_1644395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5, 1, 4, 2].length) (baseStart_1644395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1644395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1644395 prefixEnd_1644395 := by exact prefixLift 1644395
  have htrace : WordTrace (prefixWord ++ tailWord_1644395) baseStart_1644395 baseEnd_1644395 := by
    simpa [prefixWord, tailWord_1644395, baseEnd_1644395] using wordTrace_append hprefix tailTrace_1644395
  have hstable : (prefixWord ++ tailWord_1644395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644395).length < 2 ^ (prefixWord ++ tailWord_1644395).sum := by decide
  have hdescent : baseEnd_1644395 < baseStart_1644395 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644445 : List Nat := [1, 4, 2, 1, 2, 2, 1, 1, 1, 5, 3]
def baseStart_1644445 : Nat := 118140960795 + 1644445 * 2 ^ 59
def prefixEnd_1644445 : Nat := 4983230072969 + 3 ^ 40 * 1644445 * 2
def baseEnd_1644445 : Nat := 844390694882923835074841

theorem tailTrace_1644445 : CollatzResearch.WordTrace tailWord_1644445 prefixEnd_1644445 844390694882923835074841 := by
  unfold tailWord_1644445
  simp only [CollatzResearch.WordTrace]
  refine ⟨59977836527464088691590789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39985224351642725794393859 59977836527464088691590789)
  ·
    refine ⟨11245844348899516629673273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59977836527464088691590789 11245844348899516629673273)
    ·
      refine ⟨8434383261674637472254955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11245844348899516629673273 8434383261674637472254955)
      ·
        refine ⟨12651574892511956208382433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8434383261674637472254955 12651574892511956208382433)
        ·
          refine ⟨9488681169383967156286825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12651574892511956208382433 9488681169383967156286825)
          ·
            refine ⟨7116510877037975367215119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9488681169383967156286825 7116510877037975367215119)
            ·
              refine ⟨10674766315556963050822679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7116510877037975367215119 10674766315556963050822679)
              ·
                refine ⟨16012149473335444576234019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10674766315556963050822679 16012149473335444576234019)
                ·
                  refine ⟨24018224210003166864351029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16012149473335444576234019 24018224210003166864351029)
                  ·
                    refine ⟨2251708519687796893532909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24018224210003166864351029 2251708519687796893532909)
                    ·
                      refine ⟨844390694882923835074841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2251708519687796893532909 844390694882923835074841)
                      ·
                        rfl

theorem cell23_1644445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 1, 1, 5, 3].length) (baseStart_1644445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1644445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1644445 prefixEnd_1644445 := by exact prefixLift 1644445
  have htrace : WordTrace (prefixWord ++ tailWord_1644445) baseStart_1644445 baseEnd_1644445 := by
    simpa [prefixWord, tailWord_1644445, baseEnd_1644445] using wordTrace_append hprefix tailTrace_1644445
  have hstable : (prefixWord ++ tailWord_1644445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644445).length < 2 ^ (prefixWord ++ tailWord_1644445).sum := by decide
  have hdescent : baseEnd_1644445 < baseStart_1644445 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644448 : List Nat := [2, 1, 1, 4, 1, 1, 1, 4, 1, 7]
def baseStart_1644448 : Nat := 118140960795 + 1644448 * 2 ^ 59
def prefixEnd_1644448 : Nat := 4983230072969 + 3 ^ 40 * 1644448 * 2
def baseEnd_1644448 : Nat := 281464078441629107779109

theorem tailTrace_1644448 : CollatzResearch.WordTrace tailWord_1644448 prefixEnd_1644448 281464078441629107779109 := by
  unfold tailWord_1644448
  simp only [CollatzResearch.WordTrace]
  refine ⟨29988972973226610101974999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39985297297635480135966665 29988972973226610101974999)
  ·
    refine ⟨44983459459839915152962499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29988972973226610101974999 44983459459839915152962499)
    ·
      refine ⟨67475189189759872729443749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44983459459839915152962499 67475189189759872729443749)
      ·
        refine ⟨12651597973079976136770703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67475189189759872729443749 12651597973079976136770703)
        ·
          refine ⟨18977396959619964205156055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12651597973079976136770703 18977396959619964205156055)
          ·
            refine ⟨28466095439429946307734083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18977396959619964205156055 28466095439429946307734083)
            ·
              refine ⟨42699143159144919461601125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28466095439429946307734083 42699143159144919461601125)
              ·
                refine ⟨8006089342339672399050211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42699143159144919461601125 8006089342339672399050211)
                ·
                  refine ⟨12009134013509508598575317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8006089342339672399050211 12009134013509508598575317)
                  ·
                    refine ⟨281464078441629107779109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12009134013509508598575317 281464078441629107779109)
                    ·
                      rfl

theorem cell23_1644448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 4, 1, 7].length) (baseStart_1644448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1644448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1644448 prefixEnd_1644448 := by exact prefixLift 1644448
  have htrace : WordTrace (prefixWord ++ tailWord_1644448) baseStart_1644448 baseEnd_1644448 := by
    simpa [prefixWord, tailWord_1644448, baseEnd_1644448] using wordTrace_append hprefix tailTrace_1644448
  have hstable : (prefixWord ++ tailWord_1644448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644448).length < 2 ^ (prefixWord ++ tailWord_1644448).sum := by decide
  have hdescent : baseEnd_1644448 < baseStart_1644448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644465 : List Nat := [1, 2, 2, 4, 2, 2, 1, 1, 1, 7]
def baseStart_1644465 : Nat := 118140960795 + 1644465 * 2 ^ 59
def prefixEnd_1644465 : Nat := 4983230072969 + 3 ^ 40 * 1644465 * 2
def baseEnd_1644465 : Nat := 281466988165337918941583

theorem tailTrace_1644465 : CollatzResearch.WordTrace tailWord_1644465 prefixEnd_1644465 281466988165337918941583 := by
  unfold tailWord_1644465
  simp only [CollatzResearch.WordTrace]
  refine ⟨59978565987391632107318849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39985710658261088071545899 59978565987391632107318849)
  ·
    refine ⟨44983924490543724080489137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59978565987391632107318849 44983924490543724080489137)
    ·
      refine ⟨33737943367907793060366853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44983924490543724080489137 33737943367907793060366853)
      ·
        refine ⟨6325864381482711198818785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33737943367907793060366853 6325864381482711198818785)
        ·
          refine ⟨4744398286112033399114089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6325864381482711198818785 4744398286112033399114089)
          ·
            refine ⟨3558298714584025049335567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4744398286112033399114089 3558298714584025049335567)
            ·
              refine ⟨5337448071876037574003351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3558298714584025049335567 5337448071876037574003351)
              ·
                refine ⟨8006172107814056361005027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5337448071876037574003351 8006172107814056361005027)
                ·
                  refine ⟨12009258161721084541507541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8006172107814056361005027 12009258161721084541507541)
                  ·
                    refine ⟨281466988165337918941583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12009258161721084541507541 281466988165337918941583)
                    ·
                      rfl

theorem cell23_1644465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 1, 1, 7].length) (baseStart_1644465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1644465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1644465 prefixEnd_1644465 := by exact prefixLift 1644465
  have htrace : WordTrace (prefixWord ++ tailWord_1644465) baseStart_1644465 baseEnd_1644465 := by
    simpa [prefixWord, tailWord_1644465, baseEnd_1644465] using wordTrace_append hprefix tailTrace_1644465
  have hstable : (prefixWord ++ tailWord_1644465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644465).length < 2 ^ (prefixWord ++ tailWord_1644465).sum := by decide
  have hdescent : baseEnd_1644465 < baseStart_1644465 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644522 : List Nat := [3, 1, 3, 1, 2, 1, 2, 3, 2, 2, 3]
def baseStart_1644522 : Nat := 118140960795 + 1644522 * 2 ^ 59
def prefixEnd_1644522 : Nat := 4983230072969 + 3 ^ 40 * 1644522 * 2
def baseEnd_1644522 : Nat := 844430232893320033811987

theorem tailTrace_1644522 : CollatzResearch.WordTrace tailWord_1644522 prefixEnd_1644522 844430232893320033811987 := by
  unfold tailWord_1644522
  simp only [CollatzResearch.WordTrace]
  refine ⟨14995161237046282710535955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39987096632123420561429213 14995161237046282710535955)
  ·
    refine ⟨22492741855569424065803933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14995161237046282710535955 22492741855569424065803933)
    ·
      refine ⟨8434778195838534024676475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22492741855569424065803933 8434778195838534024676475)
      ·
        refine ⟨12652167293757801037014713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8434778195838534024676475 12652167293757801037014713)
        ·
          refine ⟨9489125470318350777761035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12652167293757801037014713 9489125470318350777761035)
          ·
            refine ⟨14233688205477526166641553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9489125470318350777761035 14233688205477526166641553)
            ·
              refine ⟨10675266154108144624981165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14233688205477526166641553 10675266154108144624981165)
              ·
                refine ⟨4003224807790554234367937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10675266154108144624981165 4003224807790554234367937)
                ·
                  refine ⟨3002418605842915675775953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4003224807790554234367937 3002418605842915675775953)
                  ·
                    refine ⟨2251813954382186756831965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3002418605842915675775953 2251813954382186756831965)
                    ·
                      refine ⟨844430232893320033811987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2251813954382186756831965 844430232893320033811987)
                      ·
                        rfl

theorem cell23_1644522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 3, 2, 2, 3].length) (baseStart_1644522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1644522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1644522 prefixEnd_1644522 := by exact prefixLift 1644522
  have htrace : WordTrace (prefixWord ++ tailWord_1644522) baseStart_1644522 baseEnd_1644522 := by
    simpa [prefixWord, tailWord_1644522, baseEnd_1644522] using wordTrace_append hprefix tailTrace_1644522
  have hstable : (prefixWord ++ tailWord_1644522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644522).length < 2 ^ (prefixWord ++ tailWord_1644522).sum := by decide
  have hdescent : baseEnd_1644522 < baseStart_1644522 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644542 : List Nat := [4, 2, 2, 2, 1, 1, 2, 1, 8]
def baseStart_1644542 : Nat := 118140960795 + 1644542 * 2 ^ 59
def prefixEnd_1644542 : Nat := 4983230072969 + 3 ^ 40 * 1644542 * 2
def baseEnd_1644542 : Nat := 93826722500712217284655

theorem tailTrace_1644542 : CollatzResearch.WordTrace tailWord_1644542 prefixEnd_1644542 93826722500712217284655 := by
  unfold tailWord_1644542
  simp only [CollatzResearch.WordTrace]
  refine ⟨7497671801014084282233985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39987582938741782838581253 7497671801014084282233985)
  ·
    refine ⟨5623253850760563211675489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7497671801014084282233985 5623253850760563211675489)
    ·
      refine ⟨4217440388070422408756617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5623253850760563211675489 4217440388070422408756617)
      ·
        refine ⟨3163080291052816806567463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4217440388070422408756617 3163080291052816806567463)
        ·
          refine ⟨4744620436579225209851195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3163080291052816806567463 4744620436579225209851195)
          ·
            refine ⟨7116930654868837814776793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4744620436579225209851195 7116930654868837814776793)
            ·
              refine ⟨5337697991151628361082595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7116930654868837814776793 5337697991151628361082595)
              ·
                refine ⟨8006546986727442541623893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5337697991151628361082595 8006546986727442541623893)
                ·
                  refine ⟨93826722500712217284655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8006546986727442541623893 93826722500712217284655)
                  ·
                    rfl

theorem cell23_1644542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 1, 8].length) (baseStart_1644542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1644542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1644542 prefixEnd_1644542 := by exact prefixLift 1644542
  have htrace : WordTrace (prefixWord ++ tailWord_1644542) baseStart_1644542 baseEnd_1644542 := by
    simpa [prefixWord, tailWord_1644542, baseEnd_1644542] using wordTrace_append hprefix tailTrace_1644542
  have hstable : (prefixWord ++ tailWord_1644542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644542).length < 2 ^ (prefixWord ++ tailWord_1644542).sum := by decide
  have hdescent : baseEnd_1644542 < baseStart_1644542 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644555 : List Nat := [1, 1, 1, 1, 6, 1, 2, 2, 3, 5]
def baseStart_1644555 : Nat := 118140960795 + 1644555 * 2 ^ 59
def prefixEnd_1644555 : Nat := 4983230072969 + 3 ^ 40 * 1644555 * 2
def baseEnd_1644555 : Nat := 281482392584972801566445

theorem tailTrace_1644555 : CollatzResearch.WordTrace tailWord_1644555 prefixEnd_1644555 281482392584972801566445 := by
  unfold tailWord_1644555
  simp only [CollatzResearch.WordTrace]
  refine ⟨59981848557065577478095119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39987899038043718318730079 59981848557065577478095119)
  ·
    refine ⟨89972772835598366217142679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59981848557065577478095119 89972772835598366217142679)
    ·
      refine ⟨134959159253397549325714019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89972772835598366217142679 134959159253397549325714019)
      ·
        refine ⟨202438738880096323988571029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134959159253397549325714019 202438738880096323988571029)
        ·
          refine ⟨9489315885004515186964267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 202438738880096323988571029 9489315885004515186964267)
          ·
            refine ⟨14233973827506772780446401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9489315885004515186964267 14233973827506772780446401)
            ·
              refine ⟨10675480370630079585334801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14233973827506772780446401 10675480370630079585334801)
              ·
                refine ⟨8006610277972559689001101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10675480370630079585334801 8006610277972559689001101)
                ·
                  refine ⟨3002478854239709883375413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8006610277972559689001101 3002478854239709883375413)
                  ·
                    refine ⟨281482392584972801566445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3002478854239709883375413 281482392584972801566445)
                    ·
                      rfl

theorem cell23_1644555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 2, 3, 5].length) (baseStart_1644555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1644555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1644555 prefixEnd_1644555 := by exact prefixLift 1644555
  have htrace : WordTrace (prefixWord ++ tailWord_1644555) baseStart_1644555 baseEnd_1644555 := by
    simpa [prefixWord, tailWord_1644555, baseEnd_1644555] using wordTrace_append hprefix tailTrace_1644555
  have hstable : (prefixWord ++ tailWord_1644555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644555).length < 2 ^ (prefixWord ++ tailWord_1644555).sum := by decide
  have hdescent : baseEnd_1644555 < baseStart_1644555 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644572 : List Nat := [2, 2, 3, 1, 3, 2, 1, 1, 3, 5]
def baseStart_1644572 : Nat := 118140960795 + 1644572 * 2 ^ 59
def prefixEnd_1644572 : Nat := 4983230072969 + 3 ^ 40 * 1644572 * 2
def baseEnd_1644572 : Nat := 281485302308681612728919

theorem tailTrace_1644572 : CollatzResearch.WordTrace tailWord_1644572 prefixEnd_1644572 281485302308681612728919 := by
  unfold tailWord_1644572
  simp only [CollatzResearch.WordTrace]
  refine ⟨29991234299001994690731985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39988312398669326254309313 29991234299001994690731985)
  ·
    refine ⟨22493425724251496018048989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29991234299001994690731985 22493425724251496018048989)
    ·
      refine ⟨8435034646594311006768371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22493425724251496018048989 8435034646594311006768371)
      ·
        refine ⟨12652551969891466510152557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8435034646594311006768371 12652551969891466510152557)
        ·
          refine ⟨4744706988709299941307209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12652551969891466510152557 4744706988709299941307209)
          ·
            refine ⟨3558530241531974955980407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4744706988709299941307209 3558530241531974955980407)
            ·
              refine ⟨5337795362297962433970611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3558530241531974955980407 5337795362297962433970611)
              ·
                refine ⟨8006693043446943650955917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5337795362297962433970611 8006693043446943650955917)
                ·
                  refine ⟨3002509891292603869108469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8006693043446943650955917 3002509891292603869108469)
                  ·
                    refine ⟨281485302308681612728919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3002509891292603869108469 281485302308681612728919)
                    ·
                      rfl

theorem cell23_1644572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 1, 3, 5].length) (baseStart_1644572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1644572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1644572 prefixEnd_1644572 := by exact prefixLift 1644572
  have htrace : WordTrace (prefixWord ++ tailWord_1644572) baseStart_1644572 baseEnd_1644572 := by
    simpa [prefixWord, tailWord_1644572, baseEnd_1644572] using wordTrace_append hprefix tailTrace_1644572
  have hstable : (prefixWord ++ tailWord_1644572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644572).length < 2 ^ (prefixWord ++ tailWord_1644572).sum := by decide
  have hdescent : baseEnd_1644572 < baseStart_1644572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644579 : List Nat := [1, 1, 1, 4, 3, 1, 4, 1, 2, 3, 2]
def baseStart_1644579 : Nat := 118140960795 + 1644579 * 2 ^ 59
def prefixEnd_1644579 : Nat := 4983230072969 + 3 ^ 40 * 1644579 * 2
def baseEnd_1644579 : Nat := 844459501290626310799225

theorem tailTrace_1644579 : CollatzResearch.WordTrace tailWord_1644579 prefixEnd_1644579 844459501290626310799225 := by
  unfold tailWord_1644579
  simp only [CollatzResearch.WordTrace]
  refine ⟨59982723908978629576968791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39988482605985753051312527 59982723908978629576968791)
  ·
    refine ⟨89974085863467944365453187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59982723908978629576968791 89974085863467944365453187)
    ·
      refine ⟨134961128795201916548179781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89974085863467944365453187 134961128795201916548179781)
      ·
        refine ⟨25305211649100359352783709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 134961128795201916548179781 25305211649100359352783709)
        ·
          refine ⟨9489454368412634757293891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25305211649100359352783709 9489454368412634757293891)
          ·
            refine ⟨14234181552618952135940837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9489454368412634757293891 14234181552618952135940837)
            ·
              refine ⟨2668909041116053525488907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14234181552618952135940837 2668909041116053525488907)
              ·
                refine ⟨4003363561674080288233361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2668909041116053525488907 4003363561674080288233361)
                ·
                  refine ⟨3002522671255560216175021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4003363561674080288233361 3002522671255560216175021)
                  ·
                    refine ⟨1125946001720835081065633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3002522671255560216175021 1125946001720835081065633)
                    ·
                      refine ⟨844459501290626310799225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1125946001720835081065633 844459501290626310799225)
                      ·
                        rfl

theorem cell23_1644579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 4, 1, 2, 3, 2].length) (baseStart_1644579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1644579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1644579 prefixEnd_1644579 := by exact prefixLift 1644579
  have htrace : WordTrace (prefixWord ++ tailWord_1644579) baseStart_1644579 baseEnd_1644579 := by
    simpa [prefixWord, tailWord_1644579, baseEnd_1644579] using wordTrace_append hprefix tailTrace_1644579
  have hstable : (prefixWord ++ tailWord_1644579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644579).length < 2 ^ (prefixWord ++ tailWord_1644579).sum := by decide
  have hdescent : baseEnd_1644579 < baseStart_1644579 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644622 : List Nat := [4, 1, 1, 1, 1, 4, 1, 3, 1, 2, 4]
def baseStart_1644622 : Nat := 118140960795 + 1644622 * 2 ^ 59
def prefixEnd_1644622 : Nat := 4983230072969 + 3 ^ 40 * 1644622 * 2
def baseEnd_1644622 : Nat := 844481580958769642561527

theorem tailTrace_1644622 : CollatzResearch.WordTrace tailWord_1644622 prefixEnd_1644622 844481580958769642561527 := by
  unfold tailWord_1644622
  simp only [CollatzResearch.WordTrace]
  refine ⟨7498036530977855990098015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39989528165215231947189413 7498036530977855990098015)
  ·
    refine ⟨11247054796466783985147023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7498036530977855990098015 11247054796466783985147023)
    ·
      refine ⟨16870582194700175977720535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11247054796466783985147023 16870582194700175977720535)
      ·
        refine ⟨25305873292050263966580803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16870582194700175977720535 25305873292050263966580803)
        ·
          refine ⟨37958809938075395949871205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25305873292050263966580803 37958809938075395949871205)
          ·
            refine ⟨7117276863389136740600851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37958809938075395949871205 7117276863389136740600851)
            ·
              refine ⟨10675915295083705110901277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7117276863389136740600851 10675915295083705110901277)
              ·
                refine ⟨4003468235656389416587979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10675915295083705110901277 4003468235656389416587979)
                ·
                  refine ⟨6005202353484584124881969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4003468235656389416587979 6005202353484584124881969)
                  ·
                    refine ⟨4503901765113438093661477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6005202353484584124881969 4503901765113438093661477)
                    ·
                      refine ⟨844481580958769642561527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4503901765113438093661477 844481580958769642561527)
                      ·
                        rfl

theorem cell23_1644622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 3, 1, 2, 4].length) (baseStart_1644622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1644622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1644622 prefixEnd_1644622 := by exact prefixLift 1644622
  have htrace : WordTrace (prefixWord ++ tailWord_1644622) baseStart_1644622 baseEnd_1644622 := by
    simpa [prefixWord, tailWord_1644622, baseEnd_1644622] using wordTrace_append hprefix tailTrace_1644622
  have hstable : (prefixWord ++ tailWord_1644622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644622).length < 2 ^ (prefixWord ++ tailWord_1644622).sum := by decide
  have hdescent : baseEnd_1644622 < baseStart_1644622 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644630 : List Nat := [5, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2]
def baseStart_1644630 : Nat := 118140960795 + 1644630 * 2 ^ 59
def prefixEnd_1644630 : Nat := 4983230072969 + 3 ^ 40 * 1644630 * 2
def baseEnd_1644630 : Nat := 844485688804005611261491

theorem tailTrace_1644630 : CollatzResearch.WordTrace tailWord_1644630 prefixEnd_1644630 844485688804005611261491 := by
  unfold tailWord_1644630
  simp only [CollatzResearch.WordTrace]
  refine ⟨3749036501987116580442209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39989722687862576858050229 3749036501987116580442209)
  ·
    refine ⟨2811777376490337435331657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3749036501987116580442209 2811777376490337435331657)
    ·
      refine ⟨2108833032367753076498743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2811777376490337435331657 2108833032367753076498743)
      ·
        refine ⟨3163249548551629614748115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2108833032367753076498743 3163249548551629614748115)
        ·
          refine ⟨4744874322827444422122173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3163249548551629614748115 4744874322827444422122173)
          ·
            refine ⟨1779327871060291658295815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4744874322827444422122173 1779327871060291658295815)
            ·
              refine ⟨2668991806590437487443723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1779327871060291658295815 2668991806590437487443723)
              ·
                refine ⟨4003487709885656231165585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2668991806590437487443723 4003487709885656231165585)
                ·
                  refine ⟨3002615782414242173374189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4003487709885656231165585 3002615782414242173374189)
                  ·
                    refine ⟨1125980918405340815015321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3002615782414242173374189 1125980918405340815015321)
                    ·
                      refine ⟨844485688804005611261491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1125980918405340815015321 844485688804005611261491)
                      ·
                        rfl

theorem cell23_1644630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2].length) (baseStart_1644630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1644630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1644630 prefixEnd_1644630 := by exact prefixLift 1644630
  have htrace : WordTrace (prefixWord ++ tailWord_1644630) baseStart_1644630 baseEnd_1644630 := by
    simpa [prefixWord, tailWord_1644630, baseEnd_1644630] using wordTrace_append hprefix tailTrace_1644630
  have hstable : (prefixWord ++ tailWord_1644630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644630).length < 2 ^ (prefixWord ++ tailWord_1644630).sum := by decide
  have hdescent : baseEnd_1644630 < baseStart_1644630 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644632 : List Nat := [2, 1, 2, 2, 1, 5, 3, 7]
def baseStart_1644632 : Nat := 118140960795 + 1644632 * 2 ^ 59
def prefixEnd_1644632 : Nat := 4983230072969 + 3 ^ 40 * 1644632 * 2
def baseEnd_1644632 : Nat := 31277285769085726053203

theorem tailTrace_1644632 : CollatzResearch.WordTrace tailWord_1644632 prefixEnd_1644632 31277285769085726053203 := by
  unfold tailWord_1644632
  simp only [CollatzResearch.WordTrace]
  refine ⟨29992328488893309814324075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39989771318524413085765433 29992328488893309814324075)
  ·
    refine ⟨44988492733339964721486113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29992328488893309814324075 44988492733339964721486113)
    ·
      refine ⟨33741369550004973541114585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44988492733339964721486113 33741369550004973541114585)
      ·
        refine ⟨25306027162503730155835939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33741369550004973541114585 25306027162503730155835939)
        ·
          refine ⟨37959040743755595233753909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25306027162503730155835939 37959040743755595233753909)
          ·
            refine ⟨3558660069727087053164429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37959040743755595233753909 3558660069727087053164429)
            ·
              refine ⟨1334497526147657644936661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3558660069727087053164429 1334497526147657644936661)
              ·
                refine ⟨31277285769085726053203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1334497526147657644936661 31277285769085726053203)
                ·
                  rfl

theorem cell23_1644632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 3, 7].length) (baseStart_1644632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1644632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1644632 prefixEnd_1644632 := by exact prefixLift 1644632
  have htrace : WordTrace (prefixWord ++ tailWord_1644632) baseStart_1644632 baseEnd_1644632 := by
    simpa [prefixWord, tailWord_1644632, baseEnd_1644632] using wordTrace_append hprefix tailTrace_1644632
  have hstable : (prefixWord ++ tailWord_1644632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644632).length < 2 ^ (prefixWord ++ tailWord_1644632).sum := by decide
  have hdescent : baseEnd_1644632 < baseStart_1644632 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644699 : List Nat := [1, 1, 1, 1, 1, 1, 2, 5, 6, 2, 2]
def baseStart_1644699 : Nat := 118140960795 + 1644699 * 2 ^ 59
def prefixEnd_1644699 : Nat := 4983230072969 + 3 ^ 40 * 1644699 * 2
def baseEnd_1644699 : Nat := 844521118969165841298673

theorem tailTrace_1644699 : CollatzResearch.WordTrace tailWord_1644699 prefixEnd_1644699 844521118969165841298673 := by
  unfold tailWord_1644699
  simp only [CollatzResearch.WordTrace]
  refine ⟨59987100668543890071337151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39991400445695926714224767 59987100668543890071337151)
  ·
    refine ⟨89980651002815835107005727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59987100668543890071337151 89980651002815835107005727)
    ·
      refine ⟨134970976504223752660508591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89980651002815835107005727 134970976504223752660508591)
      ·
        refine ⟨202456464756335628990762887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134970976504223752660508591 202456464756335628990762887)
        ·
          refine ⟨303684697134503443486144331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202456464756335628990762887 303684697134503443486144331)
          ·
            refine ⟨455527045701755165229216497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 303684697134503443486144331 455527045701755165229216497)
            ·
              refine ⟨341645284276316373921912373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 455527045701755165229216497 341645284276316373921912373)
              ·
                refine ⟨32029245400904660055179285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 341645284276316373921912373 32029245400904660055179285)
                ·
                  refine ⟨1501370878167405940086529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 32029245400904660055179285 1501370878167405940086529)
                  ·
                    refine ⟨1126028158625554455064897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1501370878167405940086529 1126028158625554455064897)
                    ·
                      refine ⟨844521118969165841298673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1126028158625554455064897 844521118969165841298673)
                      ·
                        rfl

theorem cell23_1644699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 6, 2, 2].length) (baseStart_1644699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1644699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1644699 prefixEnd_1644699 := by exact prefixLift 1644699
  have htrace : WordTrace (prefixWord ++ tailWord_1644699) baseStart_1644699 baseEnd_1644699 := by
    simpa [prefixWord, tailWord_1644699, baseEnd_1644699] using wordTrace_append hprefix tailTrace_1644699
  have hstable : (prefixWord ++ tailWord_1644699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644699).length < 2 ^ (prefixWord ++ tailWord_1644699).sum := by decide
  have hdescent : baseEnd_1644699 < baseStart_1644699 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644737 : List Nat := [1, 2, 6, 1, 3, 1, 1, 2, 1, 3, 2]
def baseStart_1644737 : Nat := 118140960795 + 1644737 * 2 ^ 59
def prefixEnd_1644737 : Nat := 4983230072969 + 3 ^ 40 * 1644737 * 2
def baseEnd_1644737 : Nat := 844540631234036692623499

theorem tailTrace_1644737 : CollatzResearch.WordTrace tailWord_1644737 prefixEnd_1644737 844540631234036692623499 := by
  unfold tailWord_1644737
  simp only [CollatzResearch.WordTrace]
  refine ⟨59988486642406222561220465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39992324428270815040813643 59988486642406222561220465)
  ·
    refine ⟨44991364981804666920915349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59988486642406222561220465 44991364981804666920915349)
    ·
      refine ⟨2108970233522093761917907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 44991364981804666920915349 2108970233522093761917907)
      ·
        refine ⟨3163455350283140642876861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2108970233522093761917907 3163455350283140642876861)
        ·
          refine ⟨1186295756356177741078823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3163455350283140642876861 1186295756356177741078823)
          ·
            refine ⟨1779443634534266611618235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1186295756356177741078823 1779443634534266611618235)
            ·
              refine ⟨2669165451801399917427353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1779443634534266611618235 2669165451801399917427353)
              ·
                refine ⟨2001874088851049938070515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2669165451801399917427353 2001874088851049938070515)
                ·
                  refine ⟨3002811133276574907105773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2001874088851049938070515 3002811133276574907105773)
                  ·
                    refine ⟨1126054174978715590164665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3002811133276574907105773 1126054174978715590164665)
                    ·
                      refine ⟨844540631234036692623499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1126054174978715590164665 844540631234036692623499)
                      ·
                        rfl

theorem cell23_1644737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 1, 2, 1, 3, 2].length) (baseStart_1644737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1644737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1644737 prefixEnd_1644737 := by exact prefixLift 1644737
  have htrace : WordTrace (prefixWord ++ tailWord_1644737) baseStart_1644737 baseEnd_1644737 := by
    simpa [prefixWord, tailWord_1644737, baseEnd_1644737] using wordTrace_append hprefix tailTrace_1644737
  have hstable : (prefixWord ++ tailWord_1644737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644737).length < 2 ^ (prefixWord ++ tailWord_1644737).sum := by decide
  have hdescent : baseEnd_1644737 < baseStart_1644737 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644762 : List Nat := [3, 1, 1, 2, 2, 1, 3, 2, 1, 2, 5]
def baseStart_1644762 : Nat := 118140960795 + 1644762 * 2 ^ 59
def prefixEnd_1644762 : Nat := 4983230072969 + 3 ^ 40 * 1644762 * 2
def baseEnd_1644762 : Nat := 844553468250399094810883

theorem tailTrace_1644762 : CollatzResearch.WordTrace tailWord_1644762 prefixEnd_1644762 844553468250399094810883 := by
  unfold tailWord_1644762
  simp only [CollatzResearch.WordTrace]
  refine ⟨14997349616828912957720135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39992932311543767887253693 14997349616828912957720135)
  ·
    refine ⟨22496024425243369436580203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14997349616828912957720135 22496024425243369436580203)
    ·
      refine ⟨33744036637865054154870305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22496024425243369436580203 33744036637865054154870305)
      ·
        refine ⟨25308027478398790616152729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33744036637865054154870305 25308027478398790616152729)
        ·
          refine ⟨18981020608799092962114547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25308027478398790616152729 18981020608799092962114547)
          ·
            refine ⟨28471530913198639443171821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18981020608799092962114547 28471530913198639443171821)
            ·
              refine ⟨10676824092449489791189433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28471530913198639443171821 10676824092449489791189433)
              ·
                refine ⟨8007618069337117343392075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10676824092449489791189433 8007618069337117343392075)
                ·
                  refine ⟨12011427104005676015088113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8007618069337117343392075 12011427104005676015088113)
                  ·
                    refine ⟨9008570328004257011316085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12011427104005676015088113 9008570328004257011316085)
                    ·
                      refine ⟨844553468250399094810883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9008570328004257011316085 844553468250399094810883)
                      ·
                        rfl

theorem cell23_1644762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 2, 1, 2, 5].length) (baseStart_1644762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1644762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1644762 prefixEnd_1644762 := by exact prefixLift 1644762
  have htrace : WordTrace (prefixWord ++ tailWord_1644762) baseStart_1644762 baseEnd_1644762 := by
    simpa [prefixWord, tailWord_1644762, baseEnd_1644762] using wordTrace_append hprefix tailTrace_1644762
  have hstable : (prefixWord ++ tailWord_1644762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644762).length < 2 ^ (prefixWord ++ tailWord_1644762).sum := by decide
  have hdescent : baseEnd_1644762 < baseStart_1644762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644772 : List Nat := [2, 3, 1, 1, 1, 2, 1, 2, 3, 3, 4]
def baseStart_1644772 : Nat := 118140960795 + 1644772 * 2 ^ 59
def prefixEnd_1644772 : Nat := 4983230072969 + 3 ^ 40 * 1644772 * 2
def baseEnd_1644772 : Nat := 844558603056944055685837

theorem tailTrace_1644772 : CollatzResearch.WordTrace tailWord_1644772 prefixEnd_1644772 844558603056944055685837 := by
  unfold tailWord_1644772
  simp only [CollatzResearch.WordTrace]
  refine ⟨29994881598639711769372285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39993175464852949025829713 29994881598639711769372285)
  ·
    refine ⟨11248080599489891913514607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29994881598639711769372285 11248080599489891913514607)
    ·
      refine ⟨16872120899234837870271911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11248080599489891913514607 16872120899234837870271911)
      ·
        refine ⟨25308181348852256805407867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16872120899234837870271911 25308181348852256805407867)
        ·
          refine ⟨37962272023278385208111801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25308181348852256805407867 37962272023278385208111801)
          ·
            refine ⟨28471704017458788906083851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37962272023278385208111801 28471704017458788906083851)
            ·
              refine ⟨42707556026188183359125777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28471704017458788906083851 42707556026188183359125777)
              ·
                refine ⟨32030667019641137519344333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42707556026188183359125777 32030667019641137519344333)
                ·
                  refine ⟨12011500132365426569754125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32030667019641137519344333 12011500132365426569754125)
                  ·
                    refine ⟨4504312549637034963657797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12011500132365426569754125 4504312549637034963657797)
                    ·
                      refine ⟨844558603056944055685837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4504312549637034963657797 844558603056944055685837)
                      ·
                        rfl

theorem cell23_1644772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 3, 3, 4].length) (baseStart_1644772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1644772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1644772 prefixEnd_1644772 := by exact prefixLift 1644772
  have htrace : WordTrace (prefixWord ++ tailWord_1644772) baseStart_1644772 baseEnd_1644772 := by
    simpa [prefixWord, tailWord_1644772, baseEnd_1644772] using wordTrace_append hprefix tailTrace_1644772
  have hstable : (prefixWord ++ tailWord_1644772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644772).length < 2 ^ (prefixWord ++ tailWord_1644772).sum := by decide
  have hdescent : baseEnd_1644772 < baseStart_1644772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644773 : List Nat := [1, 3, 1, 4, 2, 3, 2, 2, 5]
def baseStart_1644773 : Nat := 118140960795 + 1644773 * 2 ^ 59
def prefixEnd_1644773 : Nat := 4983230072969 + 3 ^ 40 * 1644773 * 2
def baseEnd_1644773 : Nat := 93839901837510950197037

theorem tailTrace_1644773 : CollatzResearch.WordTrace tailWord_1644773 prefixEnd_1644773 93839901837510950197037 := by
  unfold tailWord_1644773
  simp only [CollatzResearch.WordTrace]
  refine ⟨59989799670275800709530973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39993199780183867139687315 59989799670275800709530973)
  ·
    refine ⟨22496174876353425266074115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59989799670275800709530973 22496174876353425266074115)
    ·
      refine ⟨33744262314530137899111173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22496174876353425266074115 33744262314530137899111173)
      ·
        refine ⟨6327049183974400856083345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33744262314530137899111173 6327049183974400856083345)
        ·
          refine ⟨4745286887980800642062509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6327049183974400856083345 4745286887980800642062509)
          ·
            refine ⟨1779482582992800240773441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4745286887980800642062509 1779482582992800240773441)
            ·
              refine ⟨1334611937244600180580081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1779482582992800240773441 1334611937244600180580081)
              ·
                refine ⟨1000958952933450135435061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1334611937244600180580081 1000958952933450135435061)
                ·
                  refine ⟨93839901837510950197037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1000958952933450135435061 93839901837510950197037)
                  ·
                    rfl

theorem cell23_1644773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 2, 2, 5].length) (baseStart_1644773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1644773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1644773 prefixEnd_1644773 := by exact prefixLift 1644773
  have htrace : WordTrace (prefixWord ++ tailWord_1644773) baseStart_1644773 baseEnd_1644773 := by
    simpa [prefixWord, tailWord_1644773, baseEnd_1644773] using wordTrace_append hprefix tailTrace_1644773
  have hstable : (prefixWord ++ tailWord_1644773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644773).length < 2 ^ (prefixWord ++ tailWord_1644773).sum := by decide
  have hdescent : baseEnd_1644773 < baseStart_1644773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644782 : List Nat := [4, 1, 2, 1, 1, 1, 1, 2, 2, 8]
def baseStart_1644782 : Nat := 118140960795 + 1644782 * 2 ^ 59
def prefixEnd_1644782 : Nat := 4983230072969 + 3 ^ 40 * 1644782 * 2
def baseEnd_1644782 : Nat := 281521245954496338853597

theorem tailTrace_1644782 : CollatzResearch.WordTrace tailWord_1644782 prefixEnd_1644782 281521245954496338853597 := by
  unfold tailWord_1644782
  simp only [CollatzResearch.WordTrace]
  refine ⟨7498765990905399405826075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39993418618162130164405733 7498765990905399405826075)
  ·
    refine ⟨11248148986358099108739113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7498765990905399405826075 11248148986358099108739113)
    ·
      refine ⟨8436111739768574331554335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11248148986358099108739113 8436111739768574331554335)
      ·
        refine ⟨12654167609652861497331503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8436111739768574331554335 12654167609652861497331503)
        ·
          refine ⟨18981251414479292245997255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12654167609652861497331503 18981251414479292245997255)
          ·
            refine ⟨28471877121718938368995883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18981251414479292245997255 28471877121718938368995883)
            ·
              refine ⟨42707815682578407553493825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28471877121718938368995883 42707815682578407553493825)
              ·
                refine ⟨32030861761933805665120369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42707815682578407553493825 32030861761933805665120369)
                ·
                  refine ⟨24023146321450354248840277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32030861761933805665120369 24023146321450354248840277)
                  ·
                    refine ⟨281521245954496338853597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 24023146321450354248840277 281521245954496338853597)
                    ·
                      rfl

theorem cell23_1644782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 2, 8].length) (baseStart_1644782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1644782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1644782 prefixEnd_1644782 := by exact prefixLift 1644782
  have htrace : WordTrace (prefixWord ++ tailWord_1644782) baseStart_1644782 baseEnd_1644782 := by
    simpa [prefixWord, tailWord_1644782, baseEnd_1644782] using wordTrace_append hprefix tailTrace_1644782
  have hstable : (prefixWord ++ tailWord_1644782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644782).length < 2 ^ (prefixWord ++ tailWord_1644782).sum := by decide
  have hdescent : baseEnd_1644782 < baseStart_1644782 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644799 : List Nat := [1, 1, 2, 2, 1, 4, 3, 2, 3, 4]
def baseStart_1644799 : Nat := 118140960795 + 1644799 * 2 ^ 59
def prefixEnd_1644799 : Nat := 4983230072969 + 3 ^ 40 * 1644799 * 2
def baseEnd_1644799 : Nat := 281524155678205150016071

theorem tailTrace_1644799 : CollatzResearch.WordTrace tailWord_1644799 prefixEnd_1644799 281524155678205150016071 := by
  unfold tailWord_1644799
  simp only [CollatzResearch.WordTrace]
  refine ⟨59990747968181607149977451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39993831978787738099984967 59990747968181607149977451)
  ·
    refine ⟨89986121952272410724966177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59990747968181607149977451 89986121952272410724966177)
    ·
      refine ⟨67489591464204308043724633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89986121952272410724966177 67489591464204308043724633)
      ·
        refine ⟨50617193598153231032793475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67489591464204308043724633 50617193598153231032793475)
        ·
          refine ⟨75925790397229846549190213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50617193598153231032793475 75925790397229846549190213)
          ·
            refine ⟨14236085699480596227973165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75925790397229846549190213 14236085699480596227973165)
            ·
              refine ⟨5338532137305223585489937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14236085699480596227973165 5338532137305223585489937)
              ·
                refine ⟨4003899102978917689117453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5338532137305223585489937 4003899102978917689117453)
                ·
                  refine ⟨1501462163617094133419045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4003899102978917689117453 1501462163617094133419045)
                  ·
                    refine ⟨281524155678205150016071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1501462163617094133419045 281524155678205150016071)
                    ·
                      rfl

theorem cell23_1644799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 2, 3, 4].length) (baseStart_1644799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1644799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1644799 prefixEnd_1644799 := by exact prefixLift 1644799
  have htrace : WordTrace (prefixWord ++ tailWord_1644799) baseStart_1644799 baseEnd_1644799 := by
    simpa [prefixWord, tailWord_1644799, baseEnd_1644799] using wordTrace_append hprefix tailTrace_1644799
  have hstable : (prefixWord ++ tailWord_1644799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644799).length < 2 ^ (prefixWord ++ tailWord_1644799).sum := by decide
  have hdescent : baseEnd_1644799 < baseStart_1644799 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644809 : List Nat := [1, 2, 1, 1, 3, 5, 1, 1, 1, 4, 3]
def baseStart_1644809 : Nat := 118140960795 + 1644809 * 2 ^ 59
def prefixEnd_1644809 : Nat := 4983230072969 + 3 ^ 40 * 1644809 * 2
def baseEnd_1644809 : Nat := 844577601841160410923167

theorem tailTrace_1644809 : CollatzResearch.WordTrace tailWord_1644809 prefixEnd_1644809 844577601841160410923167 := by
  unfold tailWord_1644809
  simp only [CollatzResearch.WordTrace]
  refine ⟨59991112698145378857841481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39994075132096919238560987 59991112698145378857841481)
  ·
    refine ⟨44993334523609034143381111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59991112698145378857841481 44993334523609034143381111)
    ·
      refine ⟨67490001785413551215071667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44993334523609034143381111 67490001785413551215071667)
      ·
        refine ⟨101235002678120326822607501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67490001785413551215071667 101235002678120326822607501)
        ·
          refine ⟨37963126004295122558477813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101235002678120326822607501 37963126004295122558477813)
          ·
            refine ⟨3559043062902667739857295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37963126004295122558477813 3559043062902667739857295)
            ·
              refine ⟨5338564594354001609785943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3559043062902667739857295 5338564594354001609785943)
              ·
                refine ⟨8007846891531002414678915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5338564594354001609785943 8007846891531002414678915)
                ·
                  refine ⟨12011770337296503622018373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8007846891531002414678915 12011770337296503622018373)
                  ·
                    refine ⟨2252206938243094429128445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12011770337296503622018373 2252206938243094429128445)
                    ·
                      refine ⟨844577601841160410923167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2252206938243094429128445 844577601841160410923167)
                      ·
                        rfl

theorem cell23_1644809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 1, 1, 4, 3].length) (baseStart_1644809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1644809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1644809 prefixEnd_1644809 := by exact prefixLift 1644809
  have htrace : WordTrace (prefixWord ++ tailWord_1644809) baseStart_1644809 baseEnd_1644809 := by
    simpa [prefixWord, tailWord_1644809, baseEnd_1644809] using wordTrace_append hprefix tailTrace_1644809
  have hstable : (prefixWord ++ tailWord_1644809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644809).length < 2 ^ (prefixWord ++ tailWord_1644809).sum := by decide
  have hdescent : baseEnd_1644809 < baseStart_1644809 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644812 : List Nat := [2, 2, 1, 2, 2, 2, 2, 2, 8]
def baseStart_1644812 : Nat := 118140960795 + 1644812 * 2 ^ 59
def prefixEnd_1644812 : Nat := 4983230072969 + 3 ^ 40 * 1644812 * 2
def baseEnd_1644812 : Nat := 93842126920347099909517

theorem tailTrace_1644812 : CollatzResearch.WordTrace tailWord_1644812 prefixEnd_1644812 93842126920347099909517 := by
  unfold tailWord_1644812
  simp only [CollatzResearch.WordTrace]
  refine ⟨29995611058567255185100345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39994148078089673580133793 29995611058567255185100345)
  ·
    refine ⟨22496708293925441388825259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29995611058567255185100345 22496708293925441388825259)
    ·
      refine ⟨33745062440888162083237889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22496708293925441388825259 33745062440888162083237889)
      ·
        refine ⟨25308796830666121562428417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33745062440888162083237889 25308796830666121562428417)
        ·
          refine ⟨18981597622999591171821313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25308796830666121562428417 18981597622999591171821313)
          ·
            refine ⟨14236198217249693378865985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18981597622999591171821313 14236198217249693378865985)
            ·
              refine ⟨10677148662937270034149489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14236198217249693378865985 10677148662937270034149489)
              ·
                refine ⟨8007861497202952525612117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10677148662937270034149489 8007861497202952525612117)
                ·
                  refine ⟨93842126920347099909517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8007861497202952525612117 93842126920347099909517)
                  ·
                    rfl

theorem cell23_1644812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 2, 8].length) (baseStart_1644812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1644812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1644812 prefixEnd_1644812 := by exact prefixLift 1644812
  have htrace : WordTrace (prefixWord ++ tailWord_1644812) baseStart_1644812 baseEnd_1644812 := by
    simpa [prefixWord, tailWord_1644812, baseEnd_1644812] using wordTrace_append hprefix tailTrace_1644812
  have hstable : (prefixWord ++ tailWord_1644812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644812).length < 2 ^ (prefixWord ++ tailWord_1644812).sum := by decide
  have hdescent : baseEnd_1644812 < baseStart_1644812 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644856 : List Nat := [2, 1, 2, 1, 3, 1, 4, 2, 3, 1, 3]
def baseStart_1644856 : Nat := 118140960795 + 1644856 * 2 ^ 59
def prefixEnd_1644856 : Nat := 4983230072969 + 3 ^ 40 * 1644856 * 2
def baseEnd_1644856 : Nat := 844601735431921727035451

theorem tailTrace_1644856 : CollatzResearch.WordTrace tailWord_1644856 prefixEnd_1644856 844601735431921727035451 := by
  unfold tailWord_1644856
  simp only [CollatzResearch.WordTrace]
  refine ⟨29996413464487552942401211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39995217952650070589868281 29996413464487552942401211)
  ·
    refine ⟨44994620196731329413601817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29996413464487552942401211 44994620196731329413601817)
    ·
      refine ⟨33745965147548497060201363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44994620196731329413601817 33745965147548497060201363)
      ·
        refine ⟨50618947721322745590302045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33745965147548497060201363 50618947721322745590302045)
        ·
          refine ⟨18982105395496029596363267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50618947721322745590302045 18982105395496029596363267)
          ·
            refine ⟨28473158093244044394544901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18982105395496029596363267 28473158093244044394544901)
            ·
              refine ⟨5338717142483258323977169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28473158093244044394544901 5338717142483258323977169)
              ·
                refine ⟨4004037856862443742982877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5338717142483258323977169 4004037856862443742982877)
                ·
                  refine ⟨1501514196323416403618579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4004037856862443742982877 1501514196323416403618579)
                  ·
                    refine ⟨2252271294485124605427869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1501514196323416403618579 2252271294485124605427869)
                    ·
                      refine ⟨844601735431921727035451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2252271294485124605427869 844601735431921727035451)
                      ·
                        rfl

theorem cell23_1644856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 2, 3, 1, 3].length) (baseStart_1644856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1644856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1644856 prefixEnd_1644856 := by exact prefixLift 1644856
  have htrace : WordTrace (prefixWord ++ tailWord_1644856) baseStart_1644856 baseEnd_1644856 := by
    simpa [prefixWord, tailWord_1644856, baseEnd_1644856] using wordTrace_append hprefix tailTrace_1644856
  have hstable : (prefixWord ++ tailWord_1644856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644856).length < 2 ^ (prefixWord ++ tailWord_1644856).sum := by decide
  have hdescent : baseEnd_1644856 < baseStart_1644856 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644899 : List Nat := [1, 1, 1, 5, 2, 1, 1, 4, 1, 1, 5]
def baseStart_1644899 : Nat := 118140960795 + 1644899 * 2 ^ 59
def prefixEnd_1644899 : Nat := 4983230072969 + 3 ^ 40 * 1644899 * 2
def baseEnd_1644899 : Nat := 844623815100065058797753

theorem tailTrace_1644899 : CollatzResearch.WordTrace tailWord_1644899 prefixEnd_1644899 844623815100065058797753 := by
  unfold tailWord_1644899
  simp only [CollatzResearch.WordTrace]
  refine ⟨59994395267819324228617751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39996263511879549485745167 59994395267819324228617751)
  ·
    refine ⟨89991592901728986342926627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59994395267819324228617751 89991592901728986342926627)
    ·
      refine ⟨134987389352593479514389941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89991592901728986342926627 134987389352593479514389941)
      ·
        refine ⟨12655067751805638704474057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 134987389352593479514389941 12655067751805638704474057)
        ·
          refine ⟨9491300813854229028355543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12655067751805638704474057 9491300813854229028355543)
          ·
            refine ⟨14236951220781343542533315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9491300813854229028355543 14236951220781343542533315)
            ·
              refine ⟨21355426831172015313799973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14236951220781343542533315 21355426831172015313799973)
              ·
                refine ⟨4004142530844752871337495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21355426831172015313799973 4004142530844752871337495)
                ·
                  refine ⟨6006213796267129307006243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4004142530844752871337495 6006213796267129307006243)
                  ·
                    refine ⟨9009320694400693960509365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6006213796267129307006243 9009320694400693960509365)
                    ·
                      refine ⟨844623815100065058797753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9009320694400693960509365 844623815100065058797753)
                      ·
                        rfl

theorem cell23_1644899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 4, 1, 1, 5].length) (baseStart_1644899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1644899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1644899 prefixEnd_1644899 := by exact prefixLift 1644899
  have htrace : WordTrace (prefixWord ++ tailWord_1644899) baseStart_1644899 baseEnd_1644899 := by
    simpa [prefixWord, tailWord_1644899, baseEnd_1644899] using wordTrace_append hprefix tailTrace_1644899
  have hstable : (prefixWord ++ tailWord_1644899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644899).length < 2 ^ (prefixWord ++ tailWord_1644899).sum := by decide
  have hdescent : baseEnd_1644899 < baseStart_1644899 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644909 : List Nat := [1, 5, 1, 1, 1, 2, 1, 3, 1, 1, 6]
def baseStart_1644909 : Nat := 118140960795 + 1644909 * 2 ^ 59
def prefixEnd_1644909 : Nat := 4983230072969 + 3 ^ 40 * 1644909 * 2
def baseEnd_1644909 : Nat := 844628949906610019672707

theorem tailTrace_1644909 : CollatzResearch.WordTrace tailWord_1644909 prefixEnd_1644909 844628949906610019672707 := by
  unfold tailWord_1644909
  simp only [CollatzResearch.WordTrace]
  refine ⟨59994759997783095936481781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39996506665188730624321187 59994759997783095936481781)
  ·
    refine ⟨5624508749792165244045167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 59994759997783095936481781 5624508749792165244045167)
    ·
      refine ⟨8436763124688247866067751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5624508749792165244045167 8436763124688247866067751)
      ·
        refine ⟨12655144687032371799101627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8436763124688247866067751 12655144687032371799101627)
        ·
          refine ⟨18982717030548557698652441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12655144687032371799101627 18982717030548557698652441)
          ·
            refine ⟨14237037772911418273989331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18982717030548557698652441 14237037772911418273989331)
            ·
              refine ⟨21355556659367127410983997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14237037772911418273989331 21355556659367127410983997)
              ·
                refine ⟨8008333747262672779118999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21355556659367127410983997 8008333747262672779118999)
                ·
                  refine ⟨12012500620894009168678499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8008333747262672779118999 12012500620894009168678499)
                  ·
                    refine ⟨18018750931341013753017749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12012500620894009168678499 18018750931341013753017749)
                    ·
                      refine ⟨844628949906610019672707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18018750931341013753017749 844628949906610019672707)
                      ·
                        rfl

theorem cell23_1644909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 3, 1, 1, 6].length) (baseStart_1644909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1644909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1644909 prefixEnd_1644909 := by exact prefixLift 1644909
  have htrace : WordTrace (prefixWord ++ tailWord_1644909) baseStart_1644909 baseEnd_1644909 := by
    simpa [prefixWord, tailWord_1644909, baseEnd_1644909] using wordTrace_append hprefix tailTrace_1644909
  have hstable : (prefixWord ++ tailWord_1644909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644909).length < 2 ^ (prefixWord ++ tailWord_1644909).sum := by decide
  have hdescent : baseEnd_1644909 < baseStart_1644909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644963 : List Nat := [1, 1, 1, 4, 1, 4, 2, 3, 2, 1, 3]
def baseStart_1644963 : Nat := 118140960795 + 1644963 * 2 ^ 59
def prefixEnd_1644963 : Nat := 4983230072969 + 3 ^ 40 * 1644963 * 2
def baseEnd_1644963 : Nat := 844656677861952808397459

theorem tailTrace_1644963 : CollatzResearch.WordTrace tailWord_1644963 prefixEnd_1644963 844656677861952808397459 := by
  unfold tailWord_1644963
  simp only [CollatzResearch.WordTrace]
  refine ⟨59996729539587463158947543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39997819693058308772631695 59996729539587463158947543)
  ·
    refine ⟨89995094309381194738421315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59996729539587463158947543 89995094309381194738421315)
    ·
      refine ⟨134992641464071792107631973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89995094309381194738421315 134992641464071792107631973)
      ·
        refine ⟨25311120274513461020180995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 134992641464071792107631973 25311120274513461020180995)
        ·
          refine ⟨37966680411770191530271493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25311120274513461020180995 37966680411770191530271493)
          ·
            refine ⟨7118752577206910911925905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37966680411770191530271493 7118752577206910911925905)
            ·
              refine ⟨5339064432905183183944429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7118752577206910911925905 5339064432905183183944429)
              ·
                refine ⟨2002149162339443693979161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5339064432905183183944429 2002149162339443693979161)
                ·
                  refine ⟨1501611871754582770484371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2002149162339443693979161 1501611871754582770484371)
                  ·
                    refine ⟨2252417807631874155726557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1501611871754582770484371 2252417807631874155726557)
                    ·
                      refine ⟨844656677861952808397459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2252417807631874155726557 844656677861952808397459)
                      ·
                        rfl

theorem cell23_1644963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 3, 2, 1, 3].length) (baseStart_1644963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1644963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1644963 prefixEnd_1644963 := by exact prefixLift 1644963
  have htrace : WordTrace (prefixWord ++ tailWord_1644963) baseStart_1644963 baseEnd_1644963 := by
    simpa [prefixWord, tailWord_1644963, baseEnd_1644963] using wordTrace_append hprefix tailTrace_1644963
  have hstable : (prefixWord ++ tailWord_1644963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644963).length < 2 ^ (prefixWord ++ tailWord_1644963).sum := by decide
  have hdescent : baseEnd_1644963 < baseStart_1644963 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1645066 : List Nat := [3, 1, 2, 2, 2, 1, 3, 1, 1, 2, 5]
def baseStart_1645066 : Nat := 118140960795 + 1645066 * 2 ^ 59
def prefixEnd_1645066 : Nat := 4983230072969 + 3 ^ 40 * 1645066 * 2
def baseEnd_1645066 : Nat := 844709566369365905409485

theorem tailTrace_1645066 : CollatzResearch.WordTrace tailWord_1645066 prefixEnd_1645066 844709566369365905409485 := by
  unfold tailWord_1645066
  simp only [CollatzResearch.WordTrace]
  refine ⟨15000121564553577937486763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40000324172142874499964701 15000121564553577937486763)
  ·
    refine ⟨22500182346830366906230145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15000121564553577937486763 22500182346830366906230145)
    ·
      refine ⟨16875136760122775179672609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22500182346830366906230145 16875136760122775179672609)
      ·
        refine ⟨12656352570092081384754457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16875136760122775179672609 12656352570092081384754457)
        ·
          refine ⟨9492264427569061038565843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12656352570092081384754457 9492264427569061038565843)
          ·
            refine ⟨14238396641353591557848765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9492264427569061038565843 14238396641353591557848765)
            ·
              refine ⟨5339398740507596834193287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14238396641353591557848765 5339398740507596834193287)
              ·
                refine ⟨8009098110761395251289931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5339398740507596834193287 8009098110761395251289931)
                ·
                  refine ⟨12013647166142092876934897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8009098110761395251289931 12013647166142092876934897)
                  ·
                    refine ⟨9010235374606569657701173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12013647166142092876934897 9010235374606569657701173)
                    ·
                      refine ⟨844709566369365905409485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9010235374606569657701173 844709566369365905409485)
                      ·
                        rfl

theorem cell23_1645066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 1, 1, 2, 5].length) (baseStart_1645066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1645066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1645066 prefixEnd_1645066 := by exact prefixLift 1645066
  have htrace : WordTrace (prefixWord ++ tailWord_1645066) baseStart_1645066 baseEnd_1645066 := by
    simpa [prefixWord, tailWord_1645066, baseEnd_1645066] using wordTrace_append hprefix tailTrace_1645066
  have hstable : (prefixWord ++ tailWord_1645066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1645066).length < 2 ^ (prefixWord ++ tailWord_1645066).sum := by decide
  have hdescent : baseEnd_1645066 < baseStart_1645066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1645066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1645099 : List Nat := [1, 1, 1, 1, 2, 1, 3, 3, 10]
def baseStart_1645099 : Nat := 118140960795 + 1645099 * 2 ^ 59
def prefixEnd_1645099 : Nat := 4983230072969 + 3 ^ 40 * 1645099 * 2
def baseEnd_1645099 : Nat := 93858501247884919588537

theorem tailTrace_1645099 : CollatzResearch.WordTrace tailWord_1645099 prefixEnd_1645099 93858501247884919588537 := by
  unfold tailWord_1645099
  simp only [CollatzResearch.WordTrace]
  refine ⟨60001689867094758385898351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40001126578063172257265567 60001689867094758385898351)
  ·
    refine ⟨90002534800642137578847527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60001689867094758385898351 90002534800642137578847527)
    ·
      refine ⟨135003802200963206368271291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90002534800642137578847527 135003802200963206368271291)
      ·
        refine ⟨202505703301444809552406937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135003802200963206368271291 202505703301444809552406937)
        ·
          refine ⟨151879277476083607164305203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 202505703301444809552406937 151879277476083607164305203)
          ·
            refine ⟨227818916214125410746457805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151879277476083607164305203 227818916214125410746457805)
            ·
              refine ⟨85432093580297029029921677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 227818916214125410746457805 85432093580297029029921677)
              ·
                refine ⟨32037035092611385886220629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85432093580297029029921677 32037035092611385886220629)
                ·
                  refine ⟨93858501247884919588537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 32037035092611385886220629 93858501247884919588537)
                  ·
                    rfl

theorem cell23_1645099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 10].length) (baseStart_1645099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1645099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1645099 prefixEnd_1645099 := by exact prefixLift 1645099
  have htrace : WordTrace (prefixWord ++ tailWord_1645099) baseStart_1645099 baseEnd_1645099 := by
    simpa [prefixWord, tailWord_1645099, baseEnd_1645099] using wordTrace_append hprefix tailTrace_1645099
  have hstable : (prefixWord ++ tailWord_1645099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1645099).length < 2 ^ (prefixWord ++ tailWord_1645099).sum := by decide
  have hdescent : baseEnd_1645099 < baseStart_1645099 := by decide
  rcases family_descends (prefixWord ++ tailWord_1645099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1645110 : List Nat := [5, 1, 2, 1, 2, 1, 2, 2, 2, 1, 4]
def baseStart_1645110 : Nat := 118140960795 + 1645110 * 2 ^ 59
def prefixEnd_1645110 : Nat := 4983230072969 + 3 ^ 40 * 1645110 * 2
def baseEnd_1645110 : Nat := 844732159518163733259283

theorem tailTrace_1645110 : CollatzResearch.WordTrace tailWord_1645110 prefixEnd_1645110 844732159518163733259283 := by
  unfold tailWord_1645110
  simp only [CollatzResearch.WordTrace]
  refine ⟨3750130691878431704034299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40001394046703271509699189 3750130691878431704034299)
  ·
    refine ⟨5625196037817647556051449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3750130691878431704034299 5625196037817647556051449)
    ·
      refine ⟨4218897028363235667038587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5625196037817647556051449 4218897028363235667038587)
      ·
        refine ⟨6328345542544853500557881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4218897028363235667038587 6328345542544853500557881)
        ·
          refine ⟨4746259156908640125418411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6328345542544853500557881 4746259156908640125418411)
          ·
            refine ⟨7119388735362960188127617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4746259156908640125418411 7119388735362960188127617)
            ·
              refine ⟨5339541551522220141095713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7119388735362960188127617 5339541551522220141095713)
              ·
                refine ⟨4004656163641665105821785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5339541551522220141095713 4004656163641665105821785)
                ·
                  refine ⟨3003492122731248829366339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4004656163641665105821785 3003492122731248829366339)
                  ·
                    refine ⟨4505238184096873244049509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3003492122731248829366339 4505238184096873244049509)
                    ·
                      refine ⟨844732159518163733259283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4505238184096873244049509 844732159518163733259283)
                      ·
                        rfl

theorem cell23_1645110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_1645110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1645110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1645110 prefixEnd_1645110 := by exact prefixLift 1645110
  have htrace : WordTrace (prefixWord ++ tailWord_1645110) baseStart_1645110 baseEnd_1645110 := by
    simpa [prefixWord, tailWord_1645110, baseEnd_1645110] using wordTrace_append hprefix tailTrace_1645110
  have hstable : (prefixWord ++ tailWord_1645110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1645110).length < 2 ^ (prefixWord ++ tailWord_1645110).sum := by decide
  have hdescent : baseEnd_1645110 < baseStart_1645110 := by decide
  rcases family_descends (prefixWord ++ tailWord_1645110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1645113 : List Nat := [1, 2, 1, 5, 1, 1, 1, 4, 2, 2, 3]
def baseStart_1645113 : Nat := 118140960795 + 1645113 * 2 ^ 59
def prefixEnd_1645113 : Nat := 4983230072969 + 3 ^ 40 * 1645113 * 2
def baseEnd_1645113 : Nat := 844733699960127221521769

theorem tailTrace_1645113 : CollatzResearch.WordTrace tailWord_1645113 prefixEnd_1645113 844733699960127221521769 := by
  unfold tailWord_1645113
  simp only [CollatzResearch.WordTrace]
  refine ⟨60002200489044038776907993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40001466992696025851271995 60002200489044038776907993)
  ·
    refine ⟨45001650366783029082680995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60002200489044038776907993 45001650366783029082680995)
    ·
      refine ⟨67502475550174543624021493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45001650366783029082680995 67502475550174543624021493)
      ·
        refine ⟨6328357082828863464752015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 67502475550174543624021493 6328357082828863464752015)
        ·
          refine ⟨9492535624243295197128023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6328357082828863464752015 9492535624243295197128023)
          ·
            refine ⟨14238803436364942795692035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9492535624243295197128023 14238803436364942795692035)
            ·
              refine ⟨21358205154547414193538053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14238803436364942795692035 21358205154547414193538053)
              ·
                refine ⟨4004663466477640161288385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21358205154547414193538053 4004663466477640161288385)
                ·
                  refine ⟨3003497599858230120966289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4004663466477640161288385 3003497599858230120966289)
                  ·
                    refine ⟨2252623199893672590724717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3003497599858230120966289 2252623199893672590724717)
                    ·
                      refine ⟨844733699960127221521769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2252623199893672590724717 844733699960127221521769)
                      ·
                        rfl

theorem cell23_1645113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 4, 2, 2, 3].length) (baseStart_1645113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1645113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1645113 prefixEnd_1645113 := by exact prefixLift 1645113
  have htrace : WordTrace (prefixWord ++ tailWord_1645113) baseStart_1645113 baseEnd_1645113 := by
    simpa [prefixWord, tailWord_1645113, baseEnd_1645113] using wordTrace_append hprefix tailTrace_1645113
  have hstable : (prefixWord ++ tailWord_1645113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1645113).length < 2 ^ (prefixWord ++ tailWord_1645113).sum := by decide
  have hdescent : baseEnd_1645113 < baseStart_1645113 := by decide
  rcases family_descends (prefixWord ++ tailWord_1645113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1645177 : List Nat := [1, 2, 1, 3, 3, 2, 2, 4, 1, 1, 3]
def baseStart_1645177 : Nat := 118140960795 + 1645177 * 2 ^ 59
def prefixEnd_1645177 : Nat := 4983230072969 + 3 ^ 40 * 1645177 * 2
def baseEnd_1645177 : Nat := 844766562722014971121475

theorem tailTrace_1645177 : CollatzResearch.WordTrace tailWord_1645177 prefixEnd_1645177 844766562722014971121475 := by
  unfold tailWord_1645177
  simp only [CollatzResearch.WordTrace]
  refine ⟨60004534760812177707237785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40003023173874785138158523 60004534760812177707237785)
  ·
    refine ⟨45003401070609133280428339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60004534760812177707237785 45003401070609133280428339)
    ·
      refine ⟨67505101605913699920642509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45003401070609133280428339 67505101605913699920642509)
      ·
        refine ⟨25314413102217637470240941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67505101605913699920642509 25314413102217637470240941)
        ·
          refine ⟨9492904913331614051340353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25314413102217637470240941 9492904913331614051340353)
          ·
            refine ⟨7119678684998710538505265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9492904913331614051340353 7119678684998710538505265)
            ·
              refine ⟨5339759013749032903878949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7119678684998710538505265 5339759013749032903878949)
              ·
                refine ⟨1001204815077943669477303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5339759013749032903878949 1001204815077943669477303)
                ·
                  refine ⟨1501807222616915504215955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1001204815077943669477303 1501807222616915504215955)
                  ·
                    refine ⟨2252710833925373256323933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1501807222616915504215955 2252710833925373256323933)
                    ·
                      refine ⟨844766562722014971121475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2252710833925373256323933 844766562722014971121475)
                      ·
                        rfl

theorem cell23_1645177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 4, 1, 1, 3].length) (baseStart_1645177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1645177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1645177 prefixEnd_1645177 := by exact prefixLift 1645177
  have htrace : WordTrace (prefixWord ++ tailWord_1645177) baseStart_1645177 baseEnd_1645177 := by
    simpa [prefixWord, tailWord_1645177, baseEnd_1645177] using wordTrace_append hprefix tailTrace_1645177
  have hstable : (prefixWord ++ tailWord_1645177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1645177).length < 2 ^ (prefixWord ++ tailWord_1645177).sum := by decide
  have hdescent : baseEnd_1645177 < baseStart_1645177 := by decide
  rcases family_descends (prefixWord ++ tailWord_1645177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1645213 : List Nat := [1, 4, 2, 1, 1, 1, 2, 4, 1, 2, 4]
def baseStart_1645213 : Nat := 118140960795 + 1645213 * 2 ^ 59
def prefixEnd_1645213 : Nat := 4983230072969 + 3 ^ 40 * 1645213 * 2
def baseEnd_1645213 : Nat := 844785048025576830271309

theorem tailTrace_1645213 : CollatzResearch.WordTrace tailWord_1645213 prefixEnd_1645213 844785048025576830271309 := by
  unfold tailWord_1645213
  simp only [CollatzResearch.WordTrace]
  refine ⟨60005847788681755855548293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40003898525787837237032195 60005847788681755855548293)
  ·
    refine ⟨11251096460377829222915305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60005847788681755855548293 11251096460377829222915305)
    ·
      refine ⟨8438322345283371917186479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11251096460377829222915305 8438322345283371917186479)
      ·
        refine ⟨12657483517925057875779719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8438322345283371917186479 12657483517925057875779719)
        ·
          refine ⟨18986225276887586813669579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12657483517925057875779719 18986225276887586813669579)
          ·
            refine ⟨28479337915331380220504369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18986225276887586813669579 28479337915331380220504369)
            ·
              refine ⟨21359503436498535165378277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28479337915331380220504369 21359503436498535165378277)
              ·
                refine ⟨4004906894343475343508427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21359503436498535165378277 4004906894343475343508427)
                ·
                  refine ⟨6007360341515213015262641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4004906894343475343508427 6007360341515213015262641)
                  ·
                    refine ⟨4505520256136409761446981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6007360341515213015262641 4505520256136409761446981)
                    ·
                      refine ⟨844785048025576830271309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4505520256136409761446981 844785048025576830271309)
                      ·
                        rfl

theorem cell23_1645213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 4, 1, 2, 4].length) (baseStart_1645213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1645213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1645213 prefixEnd_1645213 := by exact prefixLift 1645213
  have htrace : WordTrace (prefixWord ++ tailWord_1645213) baseStart_1645213 baseEnd_1645213 := by
    simpa [prefixWord, tailWord_1645213, baseEnd_1645213] using wordTrace_append hprefix tailTrace_1645213
  have hstable : (prefixWord ++ tailWord_1645213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1645213).length < 2 ^ (prefixWord ++ tailWord_1645213).sum := by decide
  have hdescent : baseEnd_1645213 < baseStart_1645213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1645213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1645220 : List Nat := [2, 3, 1, 2, 2, 1, 1, 5, 1, 2, 3]
def baseStart_1645220 : Nat := 118140960795 + 1645220 * 2 ^ 59
def prefixEnd_1645220 : Nat := 4983230072969 + 3 ^ 40 * 1645220 * 2
def baseEnd_1645220 : Nat := 844788642390158302883777

theorem tailTrace_1645220 : CollatzResearch.WordTrace tailWord_1645220 prefixEnd_1645220 844788642390158302883777 := by
  unfold tailWord_1645220
  simp only [CollatzResearch.WordTrace]
  refine ⟨30003051549828198025526557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40004068733104264034035409 30003051549828198025526557)
  ·
    refine ⟨11251144331185574259572459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30003051549828198025526557 11251144331185574259572459)
    ·
      refine ⟨16876716496778361389358689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11251144331185574259572459 16876716496778361389358689)
      ·
        refine ⟨12657537372583771042019017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16876716496778361389358689 12657537372583771042019017)
        ·
          refine ⟨9493153029437828281514263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12657537372583771042019017 9493153029437828281514263)
          ·
            refine ⟨14239729544156742422271395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9493153029437828281514263 14239729544156742422271395)
            ·
              refine ⟨21359594316235113633407093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14239729544156742422271395 21359594316235113633407093)
              ·
                refine ⟨2002461967147041903131915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21359594316235113633407093 2002461967147041903131915)
                ·
                  refine ⟨3003692950720562854697873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2002461967147041903131915 3003692950720562854697873)
                  ·
                    refine ⟨2252769713040422141023405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3003692950720562854697873 2252769713040422141023405)
                    ·
                      refine ⟨844788642390158302883777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2252769713040422141023405 844788642390158302883777)
                      ·
                        rfl

theorem cell23_1645220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 5, 1, 2, 3].length) (baseStart_1645220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1645220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1645220 prefixEnd_1645220 := by exact prefixLift 1645220
  have htrace : WordTrace (prefixWord ++ tailWord_1645220) baseStart_1645220 baseEnd_1645220 := by
    simpa [prefixWord, tailWord_1645220, baseEnd_1645220] using wordTrace_append hprefix tailTrace_1645220
  have hstable : (prefixWord ++ tailWord_1645220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1645220).length < 2 ^ (prefixWord ++ tailWord_1645220).sum := by decide
  have hdescent : baseEnd_1645220 < baseStart_1645220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1645220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1645230 : List Nat := [4, 1, 4, 1, 1, 1, 1, 2, 1, 1, 6]
def baseStart_1645230 : Nat := 118140960795 + 1645230 * 2 ^ 59
def prefixEnd_1645230 : Nat := 4983230072969 + 3 ^ 40 * 1645230 * 2
def baseEnd_1645230 : Nat := 844793777196703263758731

theorem tailTrace_1645230 : CollatzResearch.WordTrace tailWord_1645230 prefixEnd_1645230 844793777196703263758731 := by
  unfold tailWord_1645230
  simp only [CollatzResearch.WordTrace]
  refine ⟨7500808478702520969864643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40004311886413445172611429 7500808478702520969864643)
  ·
    refine ⟨11251212718053781454796965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7500808478702520969864643 11251212718053781454796965)
    ·
      refine ⟨2109602384635084022774431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11251212718053781454796965 2109602384635084022774431)
      ·
        refine ⟨3164403576952626034161647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2109602384635084022774431 3164403576952626034161647)
        ·
          refine ⟨4746605365428939051242471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3164403576952626034161647 4746605365428939051242471)
          ·
            refine ⟨7119908048143408576863707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4746605365428939051242471 7119908048143408576863707)
            ·
              refine ⟨10679862072215112865295561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7119908048143408576863707 10679862072215112865295561)
              ·
                refine ⟨8009896554161334648971671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10679862072215112865295561 8009896554161334648971671)
                ·
                  refine ⟨12014844831242001973457507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8009896554161334648971671 12014844831242001973457507)
                  ·
                    refine ⟨18022267246863002960186261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12014844831242001973457507 18022267246863002960186261)
                    ·
                      refine ⟨844793777196703263758731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18022267246863002960186261 844793777196703263758731)
                      ·
                        rfl

theorem cell23_1645230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_1645230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1645230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1645230 prefixEnd_1645230 := by exact prefixLift 1645230
  have htrace : WordTrace (prefixWord ++ tailWord_1645230) baseStart_1645230 baseEnd_1645230 := by
    simpa [prefixWord, tailWord_1645230, baseEnd_1645230] using wordTrace_append hprefix tailTrace_1645230
  have hstable : (prefixWord ++ tailWord_1645230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1645230).length < 2 ^ (prefixWord ++ tailWord_1645230).sum := by decide
  have hdescent : baseEnd_1645230 < baseStart_1645230 := by decide
  rcases family_descends (prefixWord ++ tailWord_1645230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1645243 : List Nat := [1, 1, 1, 1, 1, 2, 3, 1, 1, 9, 2]
def baseStart_1645243 : Nat := 118140960795 + 1645243 * 2 ^ 59
def prefixEnd_1645243 : Nat := 4983230072969 + 3 ^ 40 * 1645243 * 2
def baseEnd_1645243 : Nat := 844800452445211712896171

theorem tailTrace_1645243 : CollatzResearch.WordTrace tailWord_1645243 prefixEnd_1645243 844800452445211712896171 := by
  unfold tailWord_1645243
  simp only [CollatzResearch.WordTrace]
  refine ⟨60006941978573070979140383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40004627985715380652760255 60006941978573070979140383)
  ·
    refine ⟨90010412967859606468710575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60006941978573070979140383 90010412967859606468710575)
    ·
      refine ⟨135015619451789409703065863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90010412967859606468710575 135015619451789409703065863)
      ·
        refine ⟨202523429177684114554598795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135015619451789409703065863 202523429177684114554598795)
        ·
          refine ⟨303785143766526171831898193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202523429177684114554598795 303785143766526171831898193)
          ·
            refine ⟨227838857824894628873923645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 303785143766526171831898193 227838857824894628873923645)
            ·
              refine ⟨85439571684335485827721367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 227838857824894628873923645 85439571684335485827721367)
              ·
                refine ⟨128159357526503228741582051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85439571684335485827721367 128159357526503228741582051)
                ·
                  refine ⟨192239036289754843112373077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 128159357526503228741582051 192239036289754843112373077)
                  ·
                    refine ⟨1126400603260282283861561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 192239036289754843112373077 1126400603260282283861561)
                    ·
                      refine ⟨844800452445211712896171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1126400603260282283861561 844800452445211712896171)
                      ·
                        rfl

theorem cell23_1645243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 9, 2].length) (baseStart_1645243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1645243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1645243 prefixEnd_1645243 := by exact prefixLift 1645243
  have htrace : WordTrace (prefixWord ++ tailWord_1645243) baseStart_1645243 baseEnd_1645243 := by
    simpa [prefixWord, tailWord_1645243, baseEnd_1645243] using wordTrace_append hprefix tailTrace_1645243
  have hstable : (prefixWord ++ tailWord_1645243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1645243).length < 2 ^ (prefixWord ++ tailWord_1645243).sum := by decide
  have hdescent : baseEnd_1645243 < baseStart_1645243 := by decide
  rcases family_descends (prefixWord ++ tailWord_1645243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1645290 : List Nat := [3, 1, 3, 1, 1, 1, 1, 1, 5, 4, 2]
def baseStart_1645290 : Nat := 118140960795 + 1645290 * 2 ^ 59
def prefixEnd_1645290 : Nat := 4983230072969 + 3 ^ 40 * 1645290 * 2
def baseEnd_1645290 : Nat := 844824586035973029008455

theorem tailTrace_1645290 : CollatzResearch.WordTrace tailWord_1645290 prefixEnd_1645290 844824586035973029008455 := by
  unfold tailWord_1645290
  simp only [CollatzResearch.WordTrace]
  refine ⟨15002164052350699501525331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40005770806268532004067549 15002164052350699501525331)
  ·
    refine ⟨22503246078526049252287997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15002164052350699501525331 22503246078526049252287997)
    ·
      refine ⟨8438717279447268469607999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22503246078526049252287997 8438717279447268469607999)
      ·
        refine ⟨12658075919170902704411999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8438717279447268469607999 12658075919170902704411999)
        ·
          refine ⟨18987113878756354056617999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12658075919170902704411999 18987113878756354056617999)
          ·
            refine ⟨28480670818134531084926999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18987113878756354056617999 28480670818134531084926999)
            ·
              refine ⟨42721006227201796627390499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28480670818134531084926999 42721006227201796627390499)
              ·
                refine ⟨64081509340802694941085749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42721006227201796627390499 64081509340802694941085749)
                ·
                  refine ⟨6007641500700252650726789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 64081509340802694941085749 6007641500700252650726789)
                  ·
                    refine ⟨1126432781381297372011273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6007641500700252650726789 1126432781381297372011273)
                    ·
                      refine ⟨844824586035973029008455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1126432781381297372011273 844824586035973029008455)
                      ·
                        rfl

theorem cell23_1645290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 5, 4, 2].length) (baseStart_1645290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1645290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1645290 prefixEnd_1645290 := by exact prefixLift 1645290
  have htrace : WordTrace (prefixWord ++ tailWord_1645290) baseStart_1645290 baseEnd_1645290 := by
    simpa [prefixWord, tailWord_1645290, baseEnd_1645290] using wordTrace_append hprefix tailTrace_1645290
  have hstable : (prefixWord ++ tailWord_1645290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1645290).length < 2 ^ (prefixWord ++ tailWord_1645290).sum := by decide
  have hdescent : baseEnd_1645290 < baseStart_1645290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1645290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1645301 : List Nat := [1, 3, 6, 1, 1, 1, 2, 1, 1, 3, 3]
def baseStart_1645301 : Nat := 118140960795 + 1645301 * 2 ^ 59
def prefixEnd_1645301 : Nat := 4983230072969 + 3 ^ 40 * 1645301 * 2
def baseEnd_1645301 : Nat := 844830234323172485970905

theorem tailTrace_1645301 : CollatzResearch.WordTrace tailWord_1645301 prefixEnd_1645301 844830234323172485970905 := by
  unfold tailWord_1645301
  simp only [CollatzResearch.WordTrace]
  refine ⟨60009057412362946884751757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40006038274908631256501171 60009057412362946884751757)
  ·
    refine ⟨22503396529636105081781909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60009057412362946884751757 22503396529636105081781909)
    ·
      refine ⟨1054846712326692425708527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 22503396529636105081781909 1054846712326692425708527)
      ·
        refine ⟨1582270068490038638562791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1054846712326692425708527 1582270068490038638562791)
        ·
          refine ⟨2373405102735057957844187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1582270068490038638562791 2373405102735057957844187)
          ·
            refine ⟨3560107654102586936766281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2373405102735057957844187 3560107654102586936766281)
            ·
              refine ⟨2670080740576940202574711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3560107654102586936766281 2670080740576940202574711)
              ·
                refine ⟨4005121110865410303862067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2670080740576940202574711 4005121110865410303862067)
                ·
                  refine ⟨6007681666298115455793101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4005121110865410303862067 6007681666298115455793101)
                  ·
                    refine ⟨2252880624861793295922413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6007681666298115455793101 2252880624861793295922413)
                    ·
                      refine ⟨844830234323172485970905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2252880624861793295922413 844830234323172485970905)
                      ·
                        rfl

theorem cell23_1645301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_1645301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1645301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1645301 prefixEnd_1645301 := by exact prefixLift 1645301
  have htrace : WordTrace (prefixWord ++ tailWord_1645301) baseStart_1645301 baseEnd_1645301 := by
    simpa [prefixWord, tailWord_1645301, baseEnd_1645301] using wordTrace_append hprefix tailTrace_1645301
  have hstable : (prefixWord ++ tailWord_1645301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1645301).length < 2 ^ (prefixWord ++ tailWord_1645301).sum := by decide
  have hdescent : baseEnd_1645301 < baseStart_1645301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1645301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1645323 : List Nat := [1, 1, 1, 1, 5, 1, 1, 1, 3, 5, 3]
def baseStart_1645323 : Nat := 118140960795 + 1645323 * 2 ^ 59
def prefixEnd_1645323 : Nat := 4983230072969 + 3 ^ 40 * 1645323 * 2
def baseEnd_1645323 : Nat := 844841530897571399895803

theorem tailTrace_1645323 : CollatzResearch.WordTrace tailWord_1645323 prefixEnd_1645323 844841530897571399895803 := by
  unfold tailWord_1645323
  simp only [CollatzResearch.WordTrace]
  refine ⟨60009859818283244642052623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40006573212188829761368415 60009859818283244642052623)
  ·
    refine ⟨90014789727424866963078935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60009859818283244642052623 90014789727424866963078935)
    ·
      refine ⟨135022184591137300444618403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90014789727424866963078935 135022184591137300444618403)
      ·
        refine ⟨202533276886705950666927605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135022184591137300444618403 202533276886705950666927605)
        ·
          refine ⟨18987494708128682875024463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 202533276886705950666927605 18987494708128682875024463)
          ·
            refine ⟨28481242062193024312536695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18987494708128682875024463 28481242062193024312536695)
            ·
              refine ⟨42721863093289536468805043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28481242062193024312536695 42721863093289536468805043)
              ·
                refine ⟨64082794639934304703207565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42721863093289536468805043 64082794639934304703207565)
                ·
                  refine ⟨24031047989975364263702837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64082794639934304703207565 24031047989975364263702837)
                  ·
                    refine ⟨2252910749060190399722141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24031047989975364263702837 2252910749060190399722141)
                    ·
                      refine ⟨844841530897571399895803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2252910749060190399722141 844841530897571399895803)
                      ·
                        rfl

theorem cell23_1645323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 3, 5, 3].length) (baseStart_1645323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1645323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1645323 prefixEnd_1645323 := by exact prefixLift 1645323
  have htrace : WordTrace (prefixWord ++ tailWord_1645323) baseStart_1645323 baseEnd_1645323 := by
    simpa [prefixWord, tailWord_1645323, baseEnd_1645323] using wordTrace_append hprefix tailTrace_1645323
  have hstable : (prefixWord ++ tailWord_1645323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1645323).length < 2 ^ (prefixWord ++ tailWord_1645323).sum := by decide
  have hdescent : baseEnd_1645323 < baseStart_1645323 := by decide
  rcases family_descends (prefixWord ++ tailWord_1645323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1645340 : List Nat := [2, 2, 3, 1, 1, 3, 1, 2, 2, 3, 3]
def baseStart_1645340 : Nat := 118140960795 + 1645340 * 2 ^ 59
def prefixEnd_1645340 : Nat := 4983230072969 + 3 ^ 40 * 1645340 * 2
def baseEnd_1645340 : Nat := 844850260068697833383225

theorem tailTrace_1645340 : CollatzResearch.WordTrace tailWord_1645340 prefixEnd_1645340 844850260068697833383225 := by
  unfold tailWord_1645340
  simp only [CollatzResearch.WordTrace]
  refine ⟨30005239929610828272710737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40006986572814437696947649 30005239929610828272710737)
  ·
    refine ⟨22503929947208121204533053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30005239929610828272710737 22503929947208121204533053)
    ·
      refine ⟨8438973730203045451699895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22503929947208121204533053 8438973730203045451699895)
      ·
        refine ⟨12658460595304568177549843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8438973730203045451699895 12658460595304568177549843)
        ·
          refine ⟨18987690892956852266324765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12658460595304568177549843 18987690892956852266324765)
          ·
            refine ⟨7120384084858819599871787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18987690892956852266324765 7120384084858819599871787)
            ·
              refine ⟨10680576127288229399807681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7120384084858819599871787 10680576127288229399807681)
              ·
                refine ⟨8010432095466172049855761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10680576127288229399807681 8010432095466172049855761)
                ·
                  refine ⟨6007824071599629037391821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8010432095466172049855761 6007824071599629037391821)
                  ·
                    refine ⟨2252934026849860889021933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6007824071599629037391821 2252934026849860889021933)
                    ·
                      refine ⟨844850260068697833383225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2252934026849860889021933 844850260068697833383225)
                      ·
                        rfl

theorem cell23_1645340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 2, 2, 3, 3].length) (baseStart_1645340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1645340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1645340 prefixEnd_1645340 := by exact prefixLift 1645340
  have htrace : WordTrace (prefixWord ++ tailWord_1645340) baseStart_1645340 baseEnd_1645340 := by
    simpa [prefixWord, tailWord_1645340, baseEnd_1645340] using wordTrace_append hprefix tailTrace_1645340
  have hstable : (prefixWord ++ tailWord_1645340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1645340).length < 2 ^ (prefixWord ++ tailWord_1645340).sum := by decide
  have hdescent : baseEnd_1645340 < baseStart_1645340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1645340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1645341 : List Nat := [1, 4, 2, 4, 1, 1, 1, 1, 4, 2, 2]
def baseStart_1645341 : Nat := 118140960795 + 1645341 * 2 ^ 59
def prefixEnd_1645341 : Nat := 4983230072969 + 3 ^ 40 * 1645341 * 2
def baseEnd_1645341 : Nat := 844850773549352329470721

theorem tailTrace_1645341 : CollatzResearch.WordTrace tailWord_1645341 prefixEnd_1645341 844850773549352329470721 := by
  unfold tailWord_1645341
  simp only [CollatzResearch.WordTrace]
  refine ⟨60010516332218033716207877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40007010888145355810805251 60010516332218033716207877)
  ·
    refine ⟨11251971812290881321788977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60010516332218033716207877 11251971812290881321788977)
    ·
      refine ⟨8438978859218160991341733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11251971812290881321788977 8438978859218160991341733)
      ·
        refine ⟨1582308536103405185876575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8438978859218160991341733 1582308536103405185876575)
        ·
          refine ⟨2373462804155107778814863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1582308536103405185876575 2373462804155107778814863)
          ·
            refine ⟨3560194206232661668222295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2373462804155107778814863 3560194206232661668222295)
            ·
              refine ⟨5340291309348992502333443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3560194206232661668222295 5340291309348992502333443)
              ·
                refine ⟨8010436964023488753500165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5340291309348992502333443 8010436964023488753500165)
                ·
                  refine ⟨1501956930754404141281281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8010436964023488753500165 1501956930754404141281281)
                  ·
                    refine ⟨1126467698065803105960961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1501956930754404141281281 1126467698065803105960961)
                    ·
                      refine ⟨844850773549352329470721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1126467698065803105960961 844850773549352329470721)
                      ·
                        rfl

theorem cell23_1645341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_1645341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1645341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1645341 prefixEnd_1645341 := by exact prefixLift 1645341
  have htrace : WordTrace (prefixWord ++ tailWord_1645341) baseStart_1645341 baseEnd_1645341 := by
    simpa [prefixWord, tailWord_1645341, baseEnd_1645341] using wordTrace_append hprefix tailTrace_1645341
  have hstable : (prefixWord ++ tailWord_1645341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1645341).length < 2 ^ (prefixWord ++ tailWord_1645341).sum := by decide
  have hdescent : baseEnd_1645341 < baseStart_1645341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1645341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1645358 : List Nat := [4, 1, 3, 2, 1, 2, 3, 1, 2, 2, 2]
def baseStart_1645358 : Nat := 118140960795 + 1645358 * 2 ^ 59
def prefixEnd_1645358 : Nat := 4983230072969 + 3 ^ 40 * 1645358 * 2
def baseEnd_1645358 : Nat := 844859502720478762958143

theorem tailTrace_1645358 : CollatzResearch.WordTrace tailWord_1645358 prefixEnd_1645358 844859502720478762958143 := by
  unfold tailWord_1645358
  simp only [CollatzResearch.WordTrace]
  refine ⟨7501392046644555702447091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40007424248770963746384485 7501392046644555702447091)
  ·
    refine ⟨11252088069966833553670637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7501392046644555702447091 11252088069966833553670637)
    ·
      refine ⟨4219533026237562582626489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11252088069966833553670637 4219533026237562582626489)
      ·
        refine ⟨3164649769678171936969867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4219533026237562582626489 3164649769678171936969867)
        ·
          refine ⟨4746974654517257905454801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3164649769678171936969867 4746974654517257905454801)
          ·
            refine ⟨3560230990887943429091101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4746974654517257905454801 3560230990887943429091101)
            ·
              refine ⟨1335086621582978785909163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3560230990887943429091101 1335086621582978785909163)
              ·
                refine ⟨2002629932374468178863745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1335086621582978785909163 2002629932374468178863745)
                ·
                  refine ⟨1501972449280851134147809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2002629932374468178863745 1501972449280851134147809)
                  ·
                    refine ⟨1126479336960638350610857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1501972449280851134147809 1126479336960638350610857)
                    ·
                      refine ⟨844859502720478762958143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1126479336960638350610857 844859502720478762958143)
                      ·
                        rfl

theorem cell23_1645358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 3, 1, 2, 2, 2].length) (baseStart_1645358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1645358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1645358 prefixEnd_1645358 := by exact prefixLift 1645358
  have htrace : WordTrace (prefixWord ++ tailWord_1645358) baseStart_1645358 baseEnd_1645358 := by
    simpa [prefixWord, tailWord_1645358, baseEnd_1645358] using wordTrace_append hprefix tailTrace_1645358
  have hstable : (prefixWord ++ tailWord_1645358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1645358).length < 2 ^ (prefixWord ++ tailWord_1645358).sum := by decide
  have hdescent : baseEnd_1645358 < baseStart_1645358 := by decide
  rcases family_descends (prefixWord ++ tailWord_1645358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1645383 : List Nat := [1, 1, 4, 1, 2, 1, 1, 2, 2, 3, 5]
def baseStart_1645383 : Nat := 118140960795 + 1645383 * 2 ^ 59
def prefixEnd_1645383 : Nat := 4983230072969 + 3 ^ 40 * 1645383 * 2
def baseEnd_1645383 : Nat := 844872339736841165145527

theorem tailTrace_1645383 : CollatzResearch.WordTrace tailWord_1645383 prefixEnd_1645383 844872339736841165145527 := by
  unfold tailWord_1645383
  simp only [CollatzResearch.WordTrace]
  refine ⟨60012048198065874889236803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40008032132043916592824535 60012048198065874889236803)
  ·
    refine ⟨90018072297098812333855205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60012048198065874889236803 90018072297098812333855205)
    ·
      refine ⟨16878388555706027312597851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90018072297098812333855205 16878388555706027312597851)
      ·
        refine ⟨25317582833559040968896777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16878388555706027312597851 25317582833559040968896777)
        ·
          refine ⟨18988187125169280726672583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25317582833559040968896777 18988187125169280726672583)
          ·
            refine ⟨28482280687753921090008875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18988187125169280726672583 28482280687753921090008875)
            ·
              refine ⟨42723421031630881635013313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28482280687753921090008875 42723421031630881635013313)
              ·
                refine ⟨32042565773723161226259985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42723421031630881635013313 32042565773723161226259985)
                ·
                  refine ⟨24031924330292370919694989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32042565773723161226259985 24031924330292370919694989)
                  ·
                    refine ⟨9011971623859639094885621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24031924330292370919694989 9011971623859639094885621)
                    ·
                      refine ⟨844872339736841165145527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9011971623859639094885621 844872339736841165145527)
                      ·
                        rfl

theorem cell23_1645383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 2, 3, 5].length) (baseStart_1645383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1645383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1645383 prefixEnd_1645383 := by exact prefixLift 1645383
  have htrace : WordTrace (prefixWord ++ tailWord_1645383) baseStart_1645383 baseEnd_1645383 := by
    simpa [prefixWord, tailWord_1645383, baseEnd_1645383] using wordTrace_append hprefix tailTrace_1645383
  have hstable : (prefixWord ++ tailWord_1645383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1645383).length < 2 ^ (prefixWord ++ tailWord_1645383).sum := by decide
  have hdescent : baseEnd_1645383 < baseStart_1645383 := by decide
  rcases family_descends (prefixWord ++ tailWord_1645383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1645390 : List Nat := [4, 1, 1, 1, 1, 1, 1, 4, 5, 4]
def baseStart_1645390 : Nat := 118140960795 + 1645390 * 2 ^ 59
def prefixEnd_1645390 : Nat := 4983230072969 + 3 ^ 40 * 1645390 * 2
def baseEnd_1645390 : Nat := 281625311367140879252665

theorem tailTrace_1645390 : CollatzResearch.WordTrace tailWord_1645390 prefixEnd_1645390 281625311367140879252665 := by
  unfold tailWord_1645390
  simp only [CollatzResearch.WordTrace]
  refine ⟨7501537938630064385592703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40008202339360343389827749 7501537938630064385592703)
  ·
    refine ⟨11252306907945096578389055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7501537938630064385592703 11252306907945096578389055)
    ·
      refine ⟨16878460361917644867583583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11252306907945096578389055 16878460361917644867583583)
      ·
        refine ⟨25317690542876467301375375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16878460361917644867583583 25317690542876467301375375)
        ·
          refine ⟨37976535814314700952063063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25317690542876467301375375 37976535814314700952063063)
          ·
            refine ⟨56964803721472051428094595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37976535814314700952063063 56964803721472051428094595)
            ·
              refine ⟨85447205582208077142141893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56964803721472051428094595 85447205582208077142141893)
              ·
                refine ⟨16021351046664014464151605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 85447205582208077142141893 16021351046664014464151605)
                ·
                  refine ⟨1502001660624751356014213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16021351046664014464151605 1502001660624751356014213)
                  ·
                    refine ⟨281625311367140879252665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1502001660624751356014213 281625311367140879252665)
                    ·
                      rfl

theorem cell23_1645390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 4, 5, 4].length) (baseStart_1645390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1645390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1645390 prefixEnd_1645390 := by exact prefixLift 1645390
  have htrace : WordTrace (prefixWord ++ tailWord_1645390) baseStart_1645390 baseEnd_1645390 := by
    simpa [prefixWord, tailWord_1645390, baseEnd_1645390] using wordTrace_append hprefix tailTrace_1645390
  have hstable : (prefixWord ++ tailWord_1645390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1645390).length < 2 ^ (prefixWord ++ tailWord_1645390).sum := by decide
  have hdescent : baseEnd_1645390 < baseStart_1645390 := by decide
  rcases family_descends (prefixWord ++ tailWord_1645390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1645420 : List Nat := [2, 2, 1, 1, 4, 1, 3, 3, 6]
def baseStart_1645420 : Nat := 118140960795 + 1645420 * 2 ^ 59
def prefixEnd_1645420 : Nat := 4983230072969 + 3 ^ 40 * 1645420 * 2
def baseEnd_1645420 : Nat := 93876815391228613375873

theorem tailTrace_1645420 : CollatzResearch.WordTrace tailWord_1645420 prefixEnd_1645420 93876815391228613375873 := by
  unfold tailWord_1645420
  simp only [CollatzResearch.WordTrace]
  refine ⟨30006698849465915104166857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40008931799287886805555809 30006698849465915104166857)
  ·
    refine ⟨22505024137099436328125143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30006698849465915104166857 22505024137099436328125143)
    ·
      refine ⟨33757536205649154492187715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22505024137099436328125143 33757536205649154492187715)
      ·
        refine ⟨50636304308473731738281573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33757536205649154492187715 50636304308473731738281573)
        ·
          refine ⟨9494307057838824700927795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50636304308473731738281573 9494307057838824700927795)
          ·
            refine ⟨14241460586758237051391693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9494307057838824700927795 14241460586758237051391693)
            ·
              refine ⟨5340547720034338894271885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14241460586758237051391693 5340547720034338894271885)
              ·
                refine ⟨2002705395012877085351957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5340547720034338894271885 2002705395012877085351957)
                ·
                  refine ⟨93876815391228613375873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2002705395012877085351957 93876815391228613375873)
                  ·
                    rfl

theorem cell23_1645420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 6].length) (baseStart_1645420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1645420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1645420 prefixEnd_1645420 := by exact prefixLift 1645420
  have htrace : WordTrace (prefixWord ++ tailWord_1645420) baseStart_1645420 baseEnd_1645420 := by
    simpa [prefixWord, tailWord_1645420, baseEnd_1645420] using wordTrace_append hprefix tailTrace_1645420
  have hstable : (prefixWord ++ tailWord_1645420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1645420).length < 2 ^ (prefixWord ++ tailWord_1645420).sum := by decide
  have hdescent : baseEnd_1645420 < baseStart_1645420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1645420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1645423 : List Nat := [1, 1, 2, 1, 3, 1, 1, 4, 1, 2, 6]
def baseStart_1645423 : Nat := 118140960795 + 1645423 * 2 ^ 59
def prefixEnd_1645423 : Nat := 4983230072969 + 3 ^ 40 * 1645423 * 2
def baseEnd_1645423 : Nat := 844892878963021008645343

theorem tailTrace_1645423 : CollatzResearch.WordTrace tailWord_1645423 prefixEnd_1645423 844892878963021008645343 := by
  unfold tailWord_1645423
  simp only [CollatzResearch.WordTrace]
  refine ⟨60013507117920961720692923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40009004745280641147128615 60013507117920961720692923)
  ·
    refine ⟨90020260676881442581039385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60013507117920961720692923 90020260676881442581039385)
    ·
      refine ⟨67515195507661081935779539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90020260676881442581039385 67515195507661081935779539)
      ·
        refine ⟨101272793261491622903669309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67515195507661081935779539 101272793261491622903669309)
        ·
          refine ⟨37977297473059358588875991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101272793261491622903669309 37977297473059358588875991)
          ·
            refine ⟨56965946209589037883313987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37977297473059358588875991 56965946209589037883313987)
            ·
              refine ⟨85448919314383556824970981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56965946209589037883313987 85448919314383556824970981)
              ·
                refine ⟨16021672371446916904682059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 85448919314383556824970981 16021672371446916904682059)
                ·
                  refine ⟨24032508557170375357023089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16021672371446916904682059 24032508557170375357023089)
                  ·
                    refine ⟨18024381417877781517767317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24032508557170375357023089 18024381417877781517767317)
                    ·
                      refine ⟨844892878963021008645343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18024381417877781517767317 844892878963021008645343)
                      ·
                        rfl

theorem cell23_1645423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 4, 1, 2, 6].length) (baseStart_1645423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1645423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1645423 prefixEnd_1645423 := by exact prefixLift 1645423
  have htrace : WordTrace (prefixWord ++ tailWord_1645423) baseStart_1645423 baseEnd_1645423 := by
    simpa [prefixWord, tailWord_1645423, baseEnd_1645423] using wordTrace_append hprefix tailTrace_1645423
  have hstable : (prefixWord ++ tailWord_1645423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1645423).length < 2 ^ (prefixWord ++ tailWord_1645423).sum := by decide
  have hdescent : baseEnd_1645423 < baseStart_1645423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1645423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1645501 : List Nat := [1, 4, 1, 2, 4, 2, 2, 1, 1, 5]
def baseStart_1645501 : Nat := 118140960795 + 1645501 * 2 ^ 59
def prefixEnd_1645501 : Nat := 4983230072969 + 3 ^ 40 * 1645501 * 2
def baseEnd_1645501 : Nat := 281644310151357234489995

theorem tailTrace_1645501 : CollatzResearch.WordTrace tailWord_1645501 prefixEnd_1645501 281644310151357234489995 := by
  unfold tailWord_1645501
  simp only [CollatzResearch.WordTrace]
  refine ⟨60016352011638381042032357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40010901341092254028021571 60016352011638381042032357)
  ·
    refine ⟨11253066002182196445381067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60016352011638381042032357 11253066002182196445381067)
    ·
      refine ⟨16879599003273294668071601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11253066002182196445381067 16879599003273294668071601)
      ·
        refine ⟨12659699252454971001053701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16879599003273294668071601 12659699252454971001053701)
        ·
          refine ⟨2373693609835307062697569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12659699252454971001053701 2373693609835307062697569)
          ·
            refine ⟨1780270207376480297023177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2373693609835307062697569 1780270207376480297023177)
            ·
              refine ⟨1335202655532360222767383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1780270207376480297023177 1335202655532360222767383)
              ·
                refine ⟨2002803983298540334151075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1335202655532360222767383 2002803983298540334151075)
                ·
                  refine ⟨3004205974947810501226613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2002803983298540334151075 3004205974947810501226613)
                  ·
                    refine ⟨281644310151357234489995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3004205974947810501226613 281644310151357234489995)
                    ·
                      rfl

theorem cell23_1645501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 2, 1, 1, 5].length) (baseStart_1645501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1645501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1645501 prefixEnd_1645501 := by exact prefixLift 1645501
  have htrace : WordTrace (prefixWord ++ tailWord_1645501) baseStart_1645501 baseEnd_1645501 := by
    simpa [prefixWord, tailWord_1645501, baseEnd_1645501] using wordTrace_append hprefix tailTrace_1645501
  have hstable : (prefixWord ++ tailWord_1645501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1645501).length < 2 ^ (prefixWord ++ tailWord_1645501).sum := by decide
  have hdescent : baseEnd_1645501 < baseStart_1645501 := by decide
  rcases family_descends (prefixWord ++ tailWord_1645501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1645504 : List Nat := [2, 1, 1, 2, 3, 3, 4, 1, 1, 1, 4]
def baseStart_1645504 : Nat := 118140960795 + 1645504 * 2 ^ 59
def prefixEnd_1645504 : Nat := 4983230072969 + 3 ^ 40 * 1645504 * 2
def baseEnd_1645504 : Nat := 844934470896035191732471

theorem tailTrace_1645504 : CollatzResearch.WordTrace tailWord_1645504 prefixEnd_1645504 844934470896035191732471 := by
  unfold tailWord_1645504
  simp only [CollatzResearch.WordTrace]
  refine ⟨30008230715313756277195783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40010974287085008369594377 30008230715313756277195783)
  ·
    refine ⟨45012346072970634415793675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30008230715313756277195783 45012346072970634415793675)
    ·
      refine ⟨67518519109455951623690513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45012346072970634415793675 67518519109455951623690513)
      ·
        refine ⟨50638889332091963717767885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67518519109455951623690513 50638889332091963717767885)
        ·
          refine ⟨18989583499534486394162957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50638889332091963717767885 18989583499534486394162957)
          ·
            refine ⟨7121093812325432397811109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18989583499534486394162957 7121093812325432397811109)
            ·
              refine ⟨1335205089811018574589583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7121093812325432397811109 1335205089811018574589583)
              ·
                refine ⟨2002807634716527861884375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1335205089811018574589583 2002807634716527861884375)
                ·
                  refine ⟨3004211452074791792826563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2002807634716527861884375 3004211452074791792826563)
                  ·
                    refine ⟨4506317178112187689239845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3004211452074791792826563 4506317178112187689239845)
                    ·
                      refine ⟨844934470896035191732471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4506317178112187689239845 844934470896035191732471)
                      ·
                        rfl

theorem cell23_1645504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 4, 1, 1, 1, 4].length) (baseStart_1645504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1645504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1645504 prefixEnd_1645504 := by exact prefixLift 1645504
  have htrace : WordTrace (prefixWord ++ tailWord_1645504) baseStart_1645504 baseEnd_1645504 := by
    simpa [prefixWord, tailWord_1645504, baseEnd_1645504] using wordTrace_append hprefix tailTrace_1645504
  have hstable : (prefixWord ++ tailWord_1645504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1645504).length < 2 ^ (prefixWord ++ tailWord_1645504).sum := by decide
  have hdescent : baseEnd_1645504 < baseStart_1645504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1645504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1645507 : List Nat := [1, 1, 1, 3, 1, 1, 2, 7, 1, 2, 3]
def baseStart_1645507 : Nat := 118140960795 + 1645507 * 2 ^ 59
def prefixEnd_1645507 : Nat := 4983230072969 + 3 ^ 40 * 1645507 * 2
def baseEnd_1645507 : Nat := 844936011337998679994957

theorem tailTrace_1645507 : CollatzResearch.WordTrace tailWord_1645507 prefixEnd_1645507 844936011337998679994957 := by
  unfold tailWord_1645507
  simp only [CollatzResearch.WordTrace]
  refine ⟨60016570849616644066750775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40011047233077762711167183 60016570849616644066750775)
  ·
    refine ⟨90024856274424966100126163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60016570849616644066750775 90024856274424966100126163)
    ·
      refine ⟨135037284411637449150189245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90024856274424966100126163 135037284411637449150189245)
      ·
        refine ⟨50638981654364043431320967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135037284411637449150189245 50638981654364043431320967)
        ·
          refine ⟨75958472481546065146981451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50638981654364043431320967 75958472481546065146981451)
          ·
            refine ⟨113937708722319097720472177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75958472481546065146981451 113937708722319097720472177)
            ·
              refine ⟨85453281541739323290354133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113937708722319097720472177 85453281541739323290354133)
              ·
                refine ⟨2002811286134515389617675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 85453281541739323290354133 2002811286134515389617675)
                ·
                  refine ⟨3004216929201773084426513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2002811286134515389617675 3004216929201773084426513)
                  ·
                    refine ⟨2253162696901329813319885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3004216929201773084426513 2253162696901329813319885)
                    ·
                      refine ⟨844936011337998679994957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2253162696901329813319885 844936011337998679994957)
                      ·
                        rfl

theorem cell23_1645507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 7, 1, 2, 3].length) (baseStart_1645507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1645507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1645507 prefixEnd_1645507 := by exact prefixLift 1645507
  have htrace : WordTrace (prefixWord ++ tailWord_1645507) baseStart_1645507 baseEnd_1645507 := by
    simpa [prefixWord, tailWord_1645507, baseEnd_1645507] using wordTrace_append hprefix tailTrace_1645507
  have hstable : (prefixWord ++ tailWord_1645507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1645507).length < 2 ^ (prefixWord ++ tailWord_1645507).sum := by decide
  have hdescent : baseEnd_1645507 < baseStart_1645507 := by decide
  rcases family_descends (prefixWord ++ tailWord_1645507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1645521 : List Nat := [1, 2, 2, 1, 2, 1, 3, 6, 1, 2, 2]
def baseStart_1645521 : Nat := 118140960795 + 1645521 * 2 ^ 59
def prefixEnd_1645521 : Nat := 4983230072969 + 3 ^ 40 * 1645521 * 2
def baseEnd_1645521 : Nat := 844943200067161625219893

theorem tailTrace_1645521 : CollatzResearch.WordTrace tailWord_1645521 prefixEnd_1645521 844943200067161625219893 := by
  unfold tailWord_1645521
  simp only [CollatzResearch.WordTrace]
  refine ⟨60017081471565924457760417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40011387647710616305173611 60017081471565924457760417)
  ·
    refine ⟨45012811103674443343320313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60017081471565924457760417 45012811103674443343320313)
    ·
      refine ⟨33759608327755832507490235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45012811103674443343320313 33759608327755832507490235)
      ·
        refine ⟨50639412491633748761235353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33759608327755832507490235 50639412491633748761235353)
        ·
          refine ⟨37979559368725311570926515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50639412491633748761235353 37979559368725311570926515)
          ·
            refine ⟨56969339053087967356389773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37979559368725311570926515 56969339053087967356389773)
            ·
              refine ⟨21363502144907987758646165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56969339053087967356389773 21363502144907987758646165)
              ·
                refine ⟨1001414163042561926186539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 21363502144907987758646165 1001414163042561926186539)
                ·
                  refine ⟨1502121244563842889279809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1001414163042561926186539 1502121244563842889279809)
                  ·
                    refine ⟨1126590933422882166959857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1502121244563842889279809 1126590933422882166959857)
                    ·
                      refine ⟨844943200067161625219893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1126590933422882166959857 844943200067161625219893)
                      ·
                        rfl

theorem cell23_1645521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 6, 1, 2, 2].length) (baseStart_1645521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1645521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1645521 prefixEnd_1645521 := by exact prefixLift 1645521
  have htrace : WordTrace (prefixWord ++ tailWord_1645521) baseStart_1645521 baseEnd_1645521 := by
    simpa [prefixWord, tailWord_1645521, baseEnd_1645521] using wordTrace_append hprefix tailTrace_1645521
  have hstable : (prefixWord ++ tailWord_1645521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1645521).length < 2 ^ (prefixWord ++ tailWord_1645521).sum := by decide
  have hdescent : baseEnd_1645521 < baseStart_1645521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1645521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1645538 : List Nat := [3, 3, 3, 1, 1, 1, 2, 2, 3, 2, 2]
def baseStart_1645538 : Nat := 118140960795 + 1645538 * 2 ^ 59
def prefixEnd_1645538 : Nat := 4983230072969 + 3 ^ 40 * 1645538 * 2
def baseEnd_1645538 : Nat := 844951929238288058707315

theorem tailTrace_1645538 : CollatzResearch.WordTrace tailWord_1645538 prefixEnd_1645538 844951929238288058707315 := by
  unfold tailWord_1645538
  simp only [CollatzResearch.WordTrace]
  refine ⟨15004425378126084090282317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40011801008336224240752845 15004425378126084090282317)
  ·
    refine ⟨5626659516797281533855869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15004425378126084090282317 5626659516797281533855869)
    ·
      refine ⟨2109997318798980575195951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5626659516797281533855869 2109997318798980575195951)
      ·
        refine ⟨3164995978198470862793927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2109997318798980575195951 3164995978198470862793927)
        ·
          refine ⟨4747493967297706294190891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3164995978198470862793927 4747493967297706294190891)
          ·
            refine ⟨7121240950946559441286337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4747493967297706294190891 7121240950946559441286337)
            ·
              refine ⟨5340930713209919580964753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7121240950946559441286337 5340930713209919580964753)
              ·
                refine ⟨4005698034907439685723565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5340930713209919580964753 4005698034907439685723565)
                ·
                  refine ⟨1502136763090289882146337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4005698034907439685723565 1502136763090289882146337)
                  ·
                    refine ⟨1126602572317717411609753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1502136763090289882146337 1126602572317717411609753)
                    ·
                      refine ⟨844951929238288058707315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1126602572317717411609753 844951929238288058707315)
                      ·
                        rfl

theorem cell23_1645538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 2, 3, 2, 2].length) (baseStart_1645538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1645538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1645538 prefixEnd_1645538 := by exact prefixLift 1645538
  have htrace : WordTrace (prefixWord ++ tailWord_1645538) baseStart_1645538 baseEnd_1645538 := by
    simpa [prefixWord, tailWord_1645538, baseEnd_1645538] using wordTrace_append hprefix tailTrace_1645538
  have hstable : (prefixWord ++ tailWord_1645538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1645538).length < 2 ^ (prefixWord ++ tailWord_1645538).sum := by decide
  have hdescent : baseEnd_1645538 < baseStart_1645538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1645538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1645560 : List Nat := [2, 1, 2, 1, 1, 3, 1, 2, 1, 5, 4]
def baseStart_1645560 : Nat := 118140960795 + 1645560 * 2 ^ 59
def prefixEnd_1645560 : Nat := 4983230072969 + 3 ^ 40 * 1645560 * 2
def baseEnd_1645560 : Nat := 844963225812686972632213

theorem tailTrace_1645560 : CollatzResearch.WordTrace tailWord_1645560 prefixEnd_1645560 844963225812686972632213 := by
  unfold tailWord_1645560
  simp only [CollatzResearch.WordTrace]
  refine ⟨30009251959212317059215067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40012335945616422745620089 30009251959212317059215067)
  ·
    refine ⟨45013877938818475588822601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30009251959212317059215067 45013877938818475588822601)
    ·
      refine ⟨33760408454113856691616951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45013877938818475588822601 33760408454113856691616951)
      ·
        refine ⟨50640612681170785037425427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33760408454113856691616951 50640612681170785037425427)
        ·
          refine ⟨75960919021756177556138141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50640612681170785037425427 75960919021756177556138141)
          ·
            refine ⟨28485344633158566583551803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75960919021756177556138141 28485344633158566583551803)
            ·
              refine ⟨42728016949737849875327705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28485344633158566583551803 42728016949737849875327705)
              ·
                refine ⟨32046012712303387406495779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42728016949737849875327705 32046012712303387406495779)
                ·
                  refine ⟨48069019068455081109743669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32046012712303387406495779 48069019068455081109743669)
                  ·
                    refine ⟨4506470537667663854038469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48069019068455081109743669 4506470537667663854038469)
                    ·
                      refine ⟨844963225812686972632213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4506470537667663854038469 844963225812686972632213)
                      ·
                        rfl

theorem cell23_1645560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 1, 5, 4].length) (baseStart_1645560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1645560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1645560 prefixEnd_1645560 := by exact prefixLift 1645560
  have htrace : WordTrace (prefixWord ++ tailWord_1645560) baseStart_1645560 baseEnd_1645560 := by
    simpa [prefixWord, tailWord_1645560, baseEnd_1645560] using wordTrace_append hprefix tailTrace_1645560
  have hstable : (prefixWord ++ tailWord_1645560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1645560).length < 2 ^ (prefixWord ++ tailWord_1645560).sum := by decide
  have hdescent : baseEnd_1645560 < baseStart_1645560 := by decide
  rcases family_descends (prefixWord ++ tailWord_1645560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1645594 : List Nat := [3, 1, 1, 3, 1, 2, 2, 3, 1, 4, 2]
def baseStart_1645594 : Nat := 118140960795 + 1645594 * 2 ^ 59
def prefixEnd_1645594 : Nat := 4983230072969 + 3 ^ 40 * 1645594 * 2
def baseEnd_1645594 : Nat := 844980684154939839607057

theorem tailTrace_1645594 : CollatzResearch.WordTrace tailWord_1645594 prefixEnd_1645594 844980684154939839607057 := by
  unfold tailWord_1645594
  simp only [CollatzResearch.WordTrace]
  refine ⟨15004936000075364481291959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40013162666867638616778557 15004936000075364481291959)
  ·
    refine ⟨22507404000113046721937939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15004936000075364481291959 22507404000113046721937939)
    ·
      refine ⟨33761106000169570082906909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22507404000113046721937939 33761106000169570082906909)
      ·
        refine ⟨12660414750063588781090091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33761106000169570082906909 12660414750063588781090091)
        ·
          refine ⟨18990622125095383171635137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12660414750063588781090091 18990622125095383171635137)
          ·
            refine ⟨14242966593821537378726353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18990622125095383171635137 14242966593821537378726353)
            ·
              refine ⟨10682224945366153034044765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14242966593821537378726353 10682224945366153034044765)
              ·
                refine ⟨4005834354512307387766787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10682224945366153034044765 4005834354512307387766787)
                ·
                  refine ⟨6008751531768461081650181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4005834354512307387766787 6008751531768461081650181)
                  ·
                    refine ⟨1126640912206586452809409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6008751531768461081650181 1126640912206586452809409)
                    ·
                      refine ⟨844980684154939839607057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1126640912206586452809409 844980684154939839607057)
                      ·
                        rfl

theorem cell23_1645594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 3, 1, 4, 2].length) (baseStart_1645594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1645594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1645594 prefixEnd_1645594 := by exact prefixLift 1645594
  have htrace : WordTrace (prefixWord ++ tailWord_1645594) baseStart_1645594 baseEnd_1645594 := by
    simpa [prefixWord, tailWord_1645594, baseEnd_1645594] using wordTrace_append hprefix tailTrace_1645594
  have hstable : (prefixWord ++ tailWord_1645594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1645594).length < 2 ^ (prefixWord ++ tailWord_1645594).sum := by decide
  have hdescent : baseEnd_1645594 < baseStart_1645594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1645594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1645628 : List Nat := [2, 2, 2, 2, 2, 3, 2, 2, 2, 2, 2]
def baseStart_1645628 : Nat := 118140960795 + 1645628 * 2 ^ 59
def prefixEnd_1645628 : Nat := 4983230072969 + 3 ^ 40 * 1645628 * 2
def baseEnd_1645628 : Nat := 844998142497192706581901

theorem tailTrace_1645628 : CollatzResearch.WordTrace tailWord_1645628 prefixEnd_1645628 844998142497192706581901 := by
  unfold tailWord_1645628
  simp only [CollatzResearch.WordTrace]
  refine ⟨30010492041089140865952769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40013989388118854487937025 30010492041089140865952769)
  ·
    refine ⟨22507869030816855649464577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30010492041089140865952769 22507869030816855649464577)
    ·
      refine ⟨16880901773112641737098433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22507869030816855649464577 16880901773112641737098433)
      ·
        refine ⟨12660676329834481302823825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16880901773112641737098433 12660676329834481302823825)
        ·
          refine ⟨9495507247375860977117869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12660676329834481302823825 9495507247375860977117869)
          ·
            refine ⟨3560815217765947866419201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9495507247375860977117869 3560815217765947866419201)
            ·
              refine ⟨2670611413324460899814401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3560815217765947866419201 2670611413324460899814401)
              ·
                refine ⟨2002958559993345674860801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2670611413324460899814401 2002958559993345674860801)
                ·
                  refine ⟨1502218919995009256145601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2002958559993345674860801 1502218919995009256145601)
                  ·
                    refine ⟨1126664189996256942109201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1502218919995009256145601 1126664189996256942109201)
                    ·
                      refine ⟨844998142497192706581901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1126664189996256942109201 844998142497192706581901)
                      ·
                        rfl

theorem cell23_1645628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 2, 2, 2, 2, 2].length) (baseStart_1645628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1645628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1645628 prefixEnd_1645628 := by exact prefixLift 1645628
  have htrace : WordTrace (prefixWord ++ tailWord_1645628) baseStart_1645628 baseEnd_1645628 := by
    simpa [prefixWord, tailWord_1645628, baseEnd_1645628] using wordTrace_append hprefix tailTrace_1645628
  have hstable : (prefixWord ++ tailWord_1645628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1645628).length < 2 ^ (prefixWord ++ tailWord_1645628).sum := by decide
  have hdescent : baseEnd_1645628 < baseStart_1645628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1645628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1645707 : List Nat := [1, 1, 1, 1, 4, 1, 1, 7, 6]
def baseStart_1645707 : Nat := 118140960795 + 1645707 * 2 ^ 59
def prefixEnd_1645707 : Nat := 4983230072969 + 3 ^ 40 * 1645707 * 2
def baseEnd_1645707 : Nat := 93893189718766433054893

theorem tailTrace_1645707 : CollatzResearch.WordTrace tailWord_1645707 prefixEnd_1645707 93893189718766433054893 := by
  unfold tailWord_1645707
  simp only [CollatzResearch.WordTrace]
  refine ⟨60023865448892078224031375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40015910299261385482687583 60023865448892078224031375)
  ·
    refine ⟨90035798173338117336047063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60023865448892078224031375 90035798173338117336047063)
    ·
      refine ⟨135053697260007176004070595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90035798173338117336047063 135053697260007176004070595)
      ·
        refine ⟨202580545890010764006105893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135053697260007176004070595 202580545890010764006105893)
        ·
          refine ⟨37983852354377018251144855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 202580545890010764006105893 37983852354377018251144855)
          ·
            refine ⟨56975778531565527376717283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37983852354377018251144855 56975778531565527376717283)
            ·
              refine ⟨85463667797348291065075925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56975778531565527376717283 85463667797348291065075925)
              ·
                refine ⟨2003054714000350571837717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 85463667797348291065075925 2003054714000350571837717)
                ·
                  refine ⟨93893189718766433054893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2003054714000350571837717 93893189718766433054893)
                  ·
                    rfl

theorem cell23_1645707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 7, 6].length) (baseStart_1645707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1645707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1645707 prefixEnd_1645707 := by exact prefixLift 1645707
  have htrace : WordTrace (prefixWord ++ tailWord_1645707) baseStart_1645707 baseEnd_1645707 := by
    simpa [prefixWord, tailWord_1645707, baseEnd_1645707] using wordTrace_append hprefix tailTrace_1645707
  have hstable : (prefixWord ++ tailWord_1645707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1645707).length < 2 ^ (prefixWord ++ tailWord_1645707).sum := by decide
  have hdescent : baseEnd_1645707 < baseStart_1645707 := by decide
  rcases family_descends (prefixWord ++ tailWord_1645707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1645738 : List Nat := [3, 1, 5, 1, 1, 2, 1, 2, 2, 2, 3]
def baseStart_1645738 : Nat := 118140960795 + 1645738 * 2 ^ 59
def prefixEnd_1645738 : Nat := 4983230072969 + 3 ^ 40 * 1645738 * 2
def baseEnd_1645738 : Nat := 845054625369187276206395

theorem tailTrace_1645738 : CollatzResearch.WordTrace tailWord_1645738 prefixEnd_1645738 845054625369187276206395 := by
  unfold tailWord_1645738
  simp only [CollatzResearch.WordTrace]
  refine ⟨15006249027944942629602467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40016664074519847012273245 15006249027944942629602467)
  ·
    refine ⟨22509373541917413944403701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15006249027944942629602467 22509373541917413944403701)
    ·
      refine ⟨2110253769554757557287847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22509373541917413944403701 2110253769554757557287847)
      ·
        refine ⟨3165380654332136335931771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2110253769554757557287847 3165380654332136335931771)
        ·
          refine ⟨4748070981498204503897657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3165380654332136335931771 4748070981498204503897657)
          ·
            refine ⟨3561053236123653377923243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4748070981498204503897657 3561053236123653377923243)
            ·
              refine ⟨5341579854185480066884865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3561053236123653377923243 5341579854185480066884865)
              ·
                refine ⟨4006184890639110050163649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5341579854185480066884865 4006184890639110050163649)
                ·
                  refine ⟨3004638667979332537622737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4006184890639110050163649 3004638667979332537622737)
                  ·
                    refine ⟨2253479000984499403217053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3004638667979332537622737 2253479000984499403217053)
                    ·
                      refine ⟨845054625369187276206395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2253479000984499403217053 845054625369187276206395)
                      ·
                        rfl

theorem cell23_1645738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_1645738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1645738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1645738 prefixEnd_1645738 := by exact prefixLift 1645738
  have htrace : WordTrace (prefixWord ++ tailWord_1645738) baseStart_1645738 baseEnd_1645738 := by
    simpa [prefixWord, tailWord_1645738, baseEnd_1645738] using wordTrace_append hprefix tailTrace_1645738
  have hstable : (prefixWord ++ tailWord_1645738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1645738).length < 2 ^ (prefixWord ++ tailWord_1645738).sum := by decide
  have hdescent : baseEnd_1645738 < baseStart_1645738 := by decide
  rcases family_descends (prefixWord ++ tailWord_1645738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1645745 : List Nat := [1, 2, 2, 5, 1, 2, 3, 2, 1, 4]
def baseStart_1645745 : Nat := 118140960795 + 1645745 * 2 ^ 59
def prefixEnd_1645745 : Nat := 4983230072969 + 3 ^ 40 * 1645745 * 2
def baseEnd_1645745 : Nat := 281686073244589582939621

theorem tailTrace_1645745 : CollatzResearch.WordTrace tailWord_1645745 prefixEnd_1645745 281686073244589582939621 := by
  unfold tailWord_1645745
  simp only [CollatzResearch.WordTrace]
  refine ⟨60025251422754410713914689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40016834281836273809276459 60025251422754410713914689)
  ·
    refine ⟨45018938567065808035436017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60025251422754410713914689 45018938567065808035436017)
    ·
      refine ⟨33764203925299356026577013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45018938567065808035436017 33764203925299356026577013)
      ·
        refine ⟨3165394117996814627491595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33764203925299356026577013 3165394117996814627491595)
        ·
          refine ⟨4748091176995221941237393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3165394117996814627491595 4748091176995221941237393)
          ·
            refine ⟨3561068382746416455928045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4748091176995221941237393 3561068382746416455928045)
            ·
              refine ⟨1335400643529906170973017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3561068382746416455928045 1335400643529906170973017)
              ·
                refine ⟨1001550482647429628229763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1335400643529906170973017 1001550482647429628229763)
                ·
                  refine ⟨1502325723971144442344645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1001550482647429628229763 1502325723971144442344645)
                  ·
                    refine ⟨281686073244589582939621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1502325723971144442344645 281686073244589582939621)
                    ·
                      rfl

theorem cell23_1645745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 3, 2, 1, 4].length) (baseStart_1645745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1645745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1645745 prefixEnd_1645745 := by exact prefixLift 1645745
  have htrace : WordTrace (prefixWord ++ tailWord_1645745) baseStart_1645745 baseEnd_1645745 := by
    simpa [prefixWord, tailWord_1645745, baseEnd_1645745] using wordTrace_append hprefix tailTrace_1645745
  have hstable : (prefixWord ++ tailWord_1645745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1645745).length < 2 ^ (prefixWord ++ tailWord_1645745).sum := by decide
  have hdescent : baseEnd_1645745 < baseStart_1645745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1645745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1645758 : List Nat := [4, 2, 1, 1, 3, 3, 2, 1, 6]
def baseStart_1645758 : Nat := 118140960795 + 1645758 * 2 ^ 59
def prefixEnd_1645758 : Nat := 4983230072969 + 3 ^ 40 * 1645758 * 2
def baseEnd_1645758 : Nat := 93896099442475244217367

theorem tailTrace_1645758 : CollatzResearch.WordTrace tailWord_1645758 prefixEnd_1645758 93896099442475244217367 := by
  unfold tailWord_1645758
  simp only [CollatzResearch.WordTrace]
  refine ⟨7503215696463414241767241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40017150381138209289425285 7503215696463414241767241)
  ·
    refine ⟨5627411772347560681325431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7503215696463414241767241 5627411772347560681325431)
    ·
      refine ⟨8441117658521341021988147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5627411772347560681325431 8441117658521341021988147)
      ·
        refine ⟨12661676487782011532982221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8441117658521341021988147 12661676487782011532982221)
        ·
          refine ⟨4748128682918254324868333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12661676487782011532982221 4748128682918254324868333)
          ·
            refine ⟨1780548256094345371825625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4748128682918254324868333 1780548256094345371825625)
            ·
              refine ⟨1335411192070759028869219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1780548256094345371825625 1335411192070759028869219)
              ·
                refine ⟨2003116788106138543303829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1335411192070759028869219 2003116788106138543303829)
                ·
                  refine ⟨93896099442475244217367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2003116788106138543303829 93896099442475244217367)
                  ·
                    rfl

theorem cell23_1645758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 2, 1, 6].length) (baseStart_1645758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1645758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1645758 prefixEnd_1645758 := by exact prefixLift 1645758
  have htrace : WordTrace (prefixWord ++ tailWord_1645758) baseStart_1645758 baseEnd_1645758 := by
    simpa [prefixWord, tailWord_1645758, baseEnd_1645758] using wordTrace_append hprefix tailTrace_1645758
  have hstable : (prefixWord ++ tailWord_1645758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1645758).length < 2 ^ (prefixWord ++ tailWord_1645758).sum := by decide
  have hdescent : baseEnd_1645758 < baseStart_1645758 := by decide
  rcases family_descends (prefixWord ++ tailWord_1645758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1645767 : List Nat := [1, 1, 4, 1, 1, 1, 1, 2, 5, 6]
def baseStart_1645767 : Nat := 118140960795 + 1645767 * 2 ^ 59
def prefixEnd_1645767 : Nat := 4983230072969 + 3 ^ 40 * 1645767 * 2
def baseEnd_1645767 : Nat := 281689838769389220914587

theorem tailTrace_1645767 : CollatzResearch.WordTrace tailWord_1645767 prefixEnd_1645767 281689838769389220914587 := by
  unfold tailWord_1645767
  simp only [CollatzResearch.WordTrace]
  refine ⟨60026053828674708471215555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40017369219116472314143703 60026053828674708471215555)
  ·
    refine ⟨90039080743012062706823333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60026053828674708471215555 90039080743012062706823333)
    ·
      refine ⟨16882327639314761757529375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90039080743012062706823333 16882327639314761757529375)
      ·
        refine ⟨25323491458972142636294063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16882327639314761757529375 25323491458972142636294063)
        ·
          refine ⟨37985237188458213954441095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25323491458972142636294063 37985237188458213954441095)
          ·
            refine ⟨56977855782687320931661643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37985237188458213954441095 56977855782687320931661643)
            ·
              refine ⟨85466783674030981397492465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56977855782687320931661643 85466783674030981397492465)
              ·
                refine ⟨64100087755523236048119349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85466783674030981397492465 64100087755523236048119349)
                ·
                  refine ⟨6009383227080303379511189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 64100087755523236048119349 6009383227080303379511189)
                  ·
                    refine ⟨281689838769389220914587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6009383227080303379511189 281689838769389220914587)
                    ·
                      rfl

theorem cell23_1645767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 5, 6].length) (baseStart_1645767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1645767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1645767 prefixEnd_1645767 := by exact prefixLift 1645767
  have htrace : WordTrace (prefixWord ++ tailWord_1645767) baseStart_1645767 baseEnd_1645767 := by
    simpa [prefixWord, tailWord_1645767, baseEnd_1645767] using wordTrace_append hprefix tailTrace_1645767
  have hstable : (prefixWord ++ tailWord_1645767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1645767).length < 2 ^ (prefixWord ++ tailWord_1645767).sum := by decide
  have hdescent : baseEnd_1645767 < baseStart_1645767 := by decide
  rcases family_descends (prefixWord ++ tailWord_1645767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1645778 : List Nat := [3, 2, 2, 2, 1, 1, 4, 1, 2, 3, 2]
def baseStart_1645778 : Nat := 118140960795 + 1645778 * 2 ^ 59
def prefixEnd_1645778 : Nat := 4983230072969 + 3 ^ 40 * 1645778 * 2
def baseEnd_1645778 : Nat := 845075164595367119706211

theorem tailTrace_1645778 : CollatzResearch.WordTrace tailWord_1645778 prefixEnd_1645778 845075164595367119706211 := by
  unfold tailWord_1645778
  simp only [CollatzResearch.WordTrace]
  refine ⟨15006613757908714337466497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40017636687756571566577325 15006613757908714337466497)
  ·
    refine ⟨11254960318431535753099873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15006613757908714337466497 11254960318431535753099873)
    ·
      refine ⟨8441220238823651814824905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11254960318431535753099873 8441220238823651814824905)
      ·
        refine ⟨6330915179117738861118679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8441220238823651814824905 6330915179117738861118679)
        ·
          refine ⟨9496372768676608291678019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6330915179117738861118679 9496372768676608291678019)
          ·
            refine ⟨14244559153014912437517029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9496372768676608291678019 14244559153014912437517029)
            ·
              refine ⟨2670854841190296082034443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14244559153014912437517029 2670854841190296082034443)
              ·
                refine ⟨4006282261785444123051665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2670854841190296082034443 4006282261785444123051665)
                ·
                  refine ⟨3004711696339083092288749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4006282261785444123051665 3004711696339083092288749)
                  ·
                    refine ⟨1126766886127156159608281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3004711696339083092288749 1126766886127156159608281)
                    ·
                      refine ⟨845075164595367119706211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1126766886127156159608281 845075164595367119706211)
                      ·
                        rfl

theorem cell23_1645778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 4, 1, 2, 3, 2].length) (baseStart_1645778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1645778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1645778 prefixEnd_1645778 := by exact prefixLift 1645778
  have htrace : WordTrace (prefixWord ++ tailWord_1645778) baseStart_1645778 baseEnd_1645778 := by
    simpa [prefixWord, tailWord_1645778, baseEnd_1645778] using wordTrace_append hprefix tailTrace_1645778
  have hstable : (prefixWord ++ tailWord_1645778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1645778).length < 2 ^ (prefixWord ++ tailWord_1645778).sum := by decide
  have hdescent : baseEnd_1645778 < baseStart_1645778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1645778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1645787 : List Nat := [1, 1, 1, 1, 1, 1, 1, 4, 2, 6, 4]
def baseStart_1645787 : Nat := 118140960795 + 1645787 * 2 ^ 59
def prefixEnd_1645787 : Nat := 4983230072969 + 3 ^ 40 * 1645787 * 2
def baseEnd_1645787 : Nat := 845079785921257584493669

theorem tailTrace_1645787 : CollatzResearch.WordTrace tailWord_1645787 prefixEnd_1645787 845079785921257584493669 := by
  unfold tailWord_1645787
  simp only [CollatzResearch.WordTrace]
  refine ⟨60026783288602251886943615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40017855525734834591295743 60026783288602251886943615)
  ·
    refine ⟨90040174932903377830415423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60026783288602251886943615 90040174932903377830415423)
    ·
      refine ⟨135060262399355066745623135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90040174932903377830415423 135060262399355066745623135)
      ·
        refine ⟨202590393599032600118434703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135060262399355066745623135 202590393599032600118434703)
        ·
          refine ⟨303885590398548900177652055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202590393599032600118434703 303885590398548900177652055)
          ·
            refine ⟨455828385597823350266478083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 303885590398548900177652055 455828385597823350266478083)
            ·
              refine ⟨683742578396735025399717125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 455828385597823350266478083 683742578396735025399717125)
              ·
                refine ⟨128201733449387817262446961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 683742578396735025399717125 128201733449387817262446961)
                ·
                  refine ⟨96151300087040862946835221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 128201733449387817262446961 96151300087040862946835221)
                  ·
                    refine ⟨4507092191580040450632901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 96151300087040862946835221 4507092191580040450632901)
                    ·
                      refine ⟨845079785921257584493669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4507092191580040450632901 845079785921257584493669)
                      ·
                        rfl

theorem cell23_1645787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 6, 4].length) (baseStart_1645787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1645787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1645787 prefixEnd_1645787 := by exact prefixLift 1645787
  have htrace : WordTrace (prefixWord ++ tailWord_1645787) baseStart_1645787 baseEnd_1645787 := by
    simpa [prefixWord, tailWord_1645787, baseEnd_1645787] using wordTrace_append hprefix tailTrace_1645787
  have hstable : (prefixWord ++ tailWord_1645787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1645787).length < 2 ^ (prefixWord ++ tailWord_1645787).sum := by decide
  have hdescent : baseEnd_1645787 < baseStart_1645787 := by decide
  rcases family_descends (prefixWord ++ tailWord_1645787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1645797 : List Nat := [1, 3, 1, 4, 14]
def baseStart_1645797 : Nat := 118140960795 + 1645797 * 2 ^ 59
def prefixEnd_1645797 : Nat := 4983230072969 + 3 ^ 40 * 1645797 * 2
def baseEnd_1645797 : Nat := 1159238574386560418887

theorem tailTrace_1645797 : CollatzResearch.WordTrace tailWord_1645797 prefixEnd_1645797 1159238574386560418887 := by
  unfold tailWord_1645797
  simp only [CollatzResearch.WordTrace]
  refine ⟨60027148018566023594807645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40018098679044015729871763 60027148018566023594807645)
  ·
    refine ⟨22510180506962258848052867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60027148018566023594807645 22510180506962258848052867)
    ·
      refine ⟨33765270760443388272079301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22510180506962258848052867 33765270760443388272079301)
      ·
        refine ⟨6330988267583135301014869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33765270760443388272079301 6330988267583135301014869)
        ·
          refine ⟨1159238574386560418887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 6330988267583135301014869 1159238574386560418887)
          ·
            rfl

theorem cell23_1645797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 14].length) (baseStart_1645797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1645797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1645797 prefixEnd_1645797 := by exact prefixLift 1645797
  have htrace : WordTrace (prefixWord ++ tailWord_1645797) baseStart_1645797 baseEnd_1645797 := by
    simpa [prefixWord, tailWord_1645797, baseEnd_1645797] using wordTrace_append hprefix tailTrace_1645797
  have hstable : (prefixWord ++ tailWord_1645797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1645797).length < 2 ^ (prefixWord ++ tailWord_1645797).sum := by decide
  have hdescent : baseEnd_1645797 < baseStart_1645797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1645797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1645802 : List Nat := [3, 1, 3, 1, 1, 5, 2, 2, 1, 1, 3]
def baseStart_1645802 : Nat := 118140960795 + 1645802 * 2 ^ 59
def prefixEnd_1645802 : Nat := 4983230072969 + 3 ^ 40 * 1645802 * 2
def baseEnd_1645802 : Nat := 845087488131075025806101

theorem tailTrace_1645802 : CollatzResearch.WordTrace tailWord_1645802 prefixEnd_1645802 845087488131075025806101 := by
  unfold tailWord_1645802
  simp only [CollatzResearch.WordTrace]
  refine ⟨15006832595886977362184915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40018220255698606299159773 15006832595886977362184915)
  ·
    refine ⟨22510248893830466043277373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15006832595886977362184915 22510248893830466043277373)
    ·
      refine ⟨8441343335186424766229015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22510248893830466043277373 8441343335186424766229015)
      ·
        refine ⟨12662015002779637149343523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8441343335186424766229015 12662015002779637149343523)
        ·
          refine ⟨18993022504169455724015285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12662015002779637149343523 18993022504169455724015285)
          ·
            refine ⟨1780595859765886474126433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18993022504169455724015285 1780595859765886474126433)
            ·
              refine ⟨1335446894824414855594825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1780595859765886474126433 1335446894824414855594825)
              ·
                refine ⟨1001585171118311141696119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1335446894824414855594825 1001585171118311141696119)
                ·
                  refine ⟨1502377756677466712544179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1001585171118311141696119 1502377756677466712544179)
                  ·
                    refine ⟨2253566635016200068816269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1502377756677466712544179 2253566635016200068816269)
                    ·
                      refine ⟨845087488131075025806101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2253566635016200068816269 845087488131075025806101)
                      ·
                        rfl

theorem cell23_1645802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 2, 2, 1, 1, 3].length) (baseStart_1645802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1645802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1645802 prefixEnd_1645802 := by exact prefixLift 1645802
  have htrace : WordTrace (prefixWord ++ tailWord_1645802) baseStart_1645802 baseEnd_1645802 := by
    simpa [prefixWord, tailWord_1645802, baseEnd_1645802] using wordTrace_append hprefix tailTrace_1645802
  have hstable : (prefixWord ++ tailWord_1645802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1645802).length < 2 ^ (prefixWord ++ tailWord_1645802).sum := by decide
  have hdescent : baseEnd_1645802 < baseStart_1645802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1645802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1645841 : List Nat := [1, 2, 2, 1, 1, 4, 2, 2, 4, 1, 3]
def baseStart_1645841 : Nat := 118140960795 + 1645841 * 2 ^ 59
def prefixEnd_1645841 : Nat := 4983230072969 + 3 ^ 40 * 1645841 * 2
def baseEnd_1645841 : Nat := 845107513876600373218421

theorem tailTrace_1645841 : CollatzResearch.WordTrace tailWord_1645841 prefixEnd_1645841 845107513876600373218421 := by
  unfold tailWord_1645841
  simp only [CollatzResearch.WordTrace]
  refine ⟨60028752830406619109409377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40019168553604412739606251 60028752830406619109409377)
  ·
    refine ⟨45021564622804964332057033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60028752830406619109409377 45021564622804964332057033)
    ·
      refine ⟨33766173467103723249042775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45021564622804964332057033 33766173467103723249042775)
      ·
        refine ⟨50649260200655584873564163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33766173467103723249042775 50649260200655584873564163)
        ·
          refine ⟨75973890300983377310346245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50649260200655584873564163 75973890300983377310346245)
          ·
            refine ⟨14245104431434383245689921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75973890300983377310346245 14245104431434383245689921)
            ·
              refine ⟨10683828323575787434267441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14245104431434383245689921 10683828323575787434267441)
              ·
                refine ⟨8012871242681840575700581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10683828323575787434267441 8012871242681840575700581)
                ·
                  refine ⟨1502413358002845107943859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8012871242681840575700581 1502413358002845107943859)
                  ·
                    refine ⟨2253620037004267661915789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1502413358002845107943859 2253620037004267661915789)
                    ·
                      refine ⟨845107513876600373218421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2253620037004267661915789 845107513876600373218421)
                      ·
                        rfl

theorem cell23_1645841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 2, 4, 1, 3].length) (baseStart_1645841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1645841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1645841 prefixEnd_1645841 := by exact prefixLift 1645841
  have htrace : WordTrace (prefixWord ++ tailWord_1645841) baseStart_1645841 baseEnd_1645841 := by
    simpa [prefixWord, tailWord_1645841, baseEnd_1645841] using wordTrace_append hprefix tailTrace_1645841
  have hstable : (prefixWord ++ tailWord_1645841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1645841).length < 2 ^ (prefixWord ++ tailWord_1645841).sum := by decide
  have hdescent : baseEnd_1645841 < baseStart_1645841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1645841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1645875 : List Nat := [1, 1, 1, 2, 5, 3, 3, 1, 2, 1, 3]
def baseStart_1645875 : Nat := 118140960795 + 1645875 * 2 ^ 59
def prefixEnd_1645875 : Nat := 4983230072969 + 3 ^ 40 * 1645875 * 2
def baseEnd_1645875 : Nat := 845124972218853240193265

theorem tailTrace_1645875 : CollatzResearch.WordTrace tailWord_1645875 prefixEnd_1645875 845124972218853240193265 := by
  unfold tailWord_1645875
  simp only [CollatzResearch.WordTrace]
  refine ⟨60029992912283442916147079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40019995274855628610764719 60029992912283442916147079)
  ·
    refine ⟨90044989368425164374220619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60029992912283442916147079 90044989368425164374220619)
    ·
      refine ⟨135067484052637746561330929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90044989368425164374220619 135067484052637746561330929)
      ·
        refine ⟨101300613039478309920998197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135067484052637746561330929 101300613039478309920998197)
        ·
          refine ⟨9496932472451091555093581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 101300613039478309920998197 9496932472451091555093581)
          ·
            refine ⟨3561349677169159333160093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9496932472451091555093581 3561349677169159333160093)
            ·
              refine ⟨1335506128938434749935035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3561349677169159333160093 1335506128938434749935035)
              ·
                refine ⟨2003259193407652124902553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1335506128938434749935035 2003259193407652124902553)
                ·
                  refine ⟨1502444395055739093676915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2003259193407652124902553 1502444395055739093676915)
                  ·
                    refine ⟨2253666592583608640515373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1502444395055739093676915 2253666592583608640515373)
                    ·
                      refine ⟨845124972218853240193265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2253666592583608640515373 845124972218853240193265)
                      ·
                        rfl

theorem cell23_1645875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 3, 1, 2, 1, 3].length) (baseStart_1645875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1645875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1645875 prefixEnd_1645875 := by exact prefixLift 1645875
  have htrace : WordTrace (prefixWord ++ tailWord_1645875) baseStart_1645875 baseEnd_1645875 := by
    simpa [prefixWord, tailWord_1645875, baseEnd_1645875] using wordTrace_append hprefix tailTrace_1645875
  have hstable : (prefixWord ++ tailWord_1645875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1645875).length < 2 ^ (prefixWord ++ tailWord_1645875).sum := by decide
  have hdescent : baseEnd_1645875 < baseStart_1645875 := by decide
  rcases family_descends (prefixWord ++ tailWord_1645875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1645910 : List Nat := [5, 2, 3, 1, 1, 1, 3, 2, 1, 2, 2]
def baseStart_1645910 : Nat := 118140960795 + 1645910 * 2 ^ 59
def prefixEnd_1645910 : Nat := 4983230072969 + 3 ^ 40 * 1645910 * 2
def baseEnd_1645910 : Nat := 845142944041760603255605

theorem tailTrace_1645910 : CollatzResearch.WordTrace tailWord_1645910 prefixEnd_1645910 845142944041760603255605 := by
  unfold tailWord_1645910
  simp only [CollatzResearch.WordTrace]
  refine ⟨3751954341697290243354449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40020846311437762595780789 3751954341697290243354449)
  ·
    refine ⟨2813965756272967682515837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3751954341697290243354449 2813965756272967682515837)
    ·
      refine ⟨1055237158602362880943439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2813965756272967682515837 1055237158602362880943439)
      ·
        refine ⟨1582855737903544321415159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1055237158602362880943439 1582855737903544321415159)
        ·
          refine ⟨2374283606855316482122739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1582855737903544321415159 2374283606855316482122739)
          ·
            refine ⟨3561425410282974723184109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2374283606855316482122739 3561425410282974723184109)
            ·
              refine ⟨1335534528856115521194041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3561425410282974723184109 1335534528856115521194041)
              ·
                refine ⟨1001650896642086640895531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1335534528856115521194041 1001650896642086640895531)
                ·
                  refine ⟨1502476344963129961343297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1001650896642086640895531 1502476344963129961343297)
                  ·
                    refine ⟨1126857258722347471007473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1502476344963129961343297 1126857258722347471007473)
                    ·
                      refine ⟨845142944041760603255605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1126857258722347471007473 845142944041760603255605)
                      ·
                        rfl

theorem cell23_1645910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_1645910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1645910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1645910 prefixEnd_1645910 := by exact prefixLift 1645910
  have htrace : WordTrace (prefixWord ++ tailWord_1645910) baseStart_1645910 baseEnd_1645910 := by
    simpa [prefixWord, tailWord_1645910, baseEnd_1645910] using wordTrace_append hprefix tailTrace_1645910
  have hstable : (prefixWord ++ tailWord_1645910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1645910).length < 2 ^ (prefixWord ++ tailWord_1645910).sum := by decide
  have hdescent : baseEnd_1645910 < baseStart_1645910 := by decide
  rcases family_descends (prefixWord ++ tailWord_1645910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1645921 : List Nat := [1, 2, 3, 1, 1, 1, 1, 8, 5]
def baseStart_1645921 : Nat := 118140960795 + 1645921 * 2 ^ 59
def prefixEnd_1645921 : Nat := 4983230072969 + 3 ^ 40 * 1645921 * 2
def baseEnd_1645921 : Nat := 93905399147662228913117

theorem tailTrace_1645921 : CollatzResearch.WordTrace tailWord_1645921 prefixEnd_1645921 93905399147662228913117 := by
  unfold tailWord_1645921
  simp only [CollatzResearch.WordTrace]
  refine ⟨60031670670116792772321617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40021113780077861848214411 60031670670116792772321617)
  ·
    refine ⟨45023753002587594579241213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60031670670116792772321617 45023753002587594579241213)
    ·
      refine ⟨16883907375970347967215455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45023753002587594579241213 16883907375970347967215455)
      ·
        refine ⟨25325861063955521950823183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16883907375970347967215455 25325861063955521950823183)
        ·
          refine ⟨37988791595933282926234775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25325861063955521950823183 37988791595933282926234775)
          ·
            refine ⟨56983187393899924389352163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37988791595933282926234775 56983187393899924389352163)
            ·
              refine ⟨85474781090849886584028245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56983187393899924389352163 85474781090849886584028245)
              ·
                refine ⟨1001657590908397108406581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 85474781090849886584028245 1001657590908397108406581)
                ·
                  refine ⟨93905399147662228913117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1001657590908397108406581 93905399147662228913117)
                  ·
                    rfl

theorem cell23_1645921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 8, 5].length) (baseStart_1645921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1645921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1645921 prefixEnd_1645921 := by exact prefixLift 1645921
  have htrace : WordTrace (prefixWord ++ tailWord_1645921) baseStart_1645921 baseEnd_1645921 := by
    simpa [prefixWord, tailWord_1645921, baseEnd_1645921] using wordTrace_append hprefix tailTrace_1645921
  have hstable : (prefixWord ++ tailWord_1645921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1645921).length < 2 ^ (prefixWord ++ tailWord_1645921).sum := by decide
  have hdescent : baseEnd_1645921 < baseStart_1645921 := by decide
  rcases family_descends (prefixWord ++ tailWord_1645921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1645932 : List Nat := [2, 2, 1, 1, 5, 1, 4, 1, 2, 2, 2]
def baseStart_1645932 : Nat := 118140960795 + 1645932 * 2 ^ 59
def prefixEnd_1645932 : Nat := 4983230072969 + 3 ^ 40 * 1645932 * 2
def baseEnd_1645932 : Nat := 845154240616159517180503

theorem tailTrace_1645932 : CollatzResearch.WordTrace tailWord_1645932 prefixEnd_1645932 845154240616159517180503 := by
  unfold tailWord_1645932
  simp only [CollatzResearch.WordTrace]
  refine ⟨30016035936538470825486025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40021381248717961100648033 30016035936538470825486025)
  ·
    refine ⟨22512026952403853119114519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30016035936538470825486025 22512026952403853119114519)
    ·
      refine ⟨33768040428605779678671779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22512026952403853119114519 33768040428605779678671779)
      ·
        refine ⟨50652060642908669518007669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33768040428605779678671779 50652060642908669518007669)
        ·
          refine ⟨4748630685272687767313219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 50652060642908669518007669 4748630685272687767313219)
          ·
            refine ⟨7122946027909031650969829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4748630685272687767313219 7122946027909031650969829)
            ·
              refine ⟨1335552380232943434556843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7122946027909031650969829 1335552380232943434556843)
              ·
                refine ⟨2003328570349415151835265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1335552380232943434556843 2003328570349415151835265)
                ·
                  refine ⟨1502496427762061363876449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2003328570349415151835265 1502496427762061363876449)
                  ·
                    refine ⟨1126872320821546022907337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1502496427762061363876449 1126872320821546022907337)
                    ·
                      refine ⟨845154240616159517180503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1126872320821546022907337 845154240616159517180503)
                      ·
                        rfl

theorem cell23_1645932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 2, 2].length) (baseStart_1645932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1645932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1645932 prefixEnd_1645932 := by exact prefixLift 1645932
  have htrace : WordTrace (prefixWord ++ tailWord_1645932) baseStart_1645932 baseEnd_1645932 := by
    simpa [prefixWord, tailWord_1645932, baseEnd_1645932] using wordTrace_append hprefix tailTrace_1645932
  have hstable : (prefixWord ++ tailWord_1645932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1645932).length < 2 ^ (prefixWord ++ tailWord_1645932).sum := by decide
  have hdescent : baseEnd_1645932 < baseStart_1645932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1645932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1645971 : List Nat := [1, 1, 1, 2, 1, 2, 1, 1, 5, 6, 2]
def baseStart_1645971 : Nat := 118140960795 + 1645971 * 2 ^ 59
def prefixEnd_1645971 : Nat := 4983230072969 + 3 ^ 40 * 1645971 * 2
def baseEnd_1645971 : Nat := 845174266361684864592823

theorem tailTrace_1645971 : CollatzResearch.WordTrace tailWord_1645971 prefixEnd_1645971 845174266361684864592823 := by
  unfold tailWord_1645971
  simp only [CollatzResearch.WordTrace]
  refine ⟨60033494319935651311641767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40022329546623767541094511 60033494319935651311641767)
  ·
    refine ⟨90050241479903476967462651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60033494319935651311641767 90050241479903476967462651)
    ·
      refine ⟨135075362219855215451193977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90050241479903476967462651 135075362219855215451193977)
      ·
        refine ⟨101306521664891411588395483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135075362219855215451193977 101306521664891411588395483)
        ·
          refine ⟨151959782497337117382593225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101306521664891411588395483 151959782497337117382593225)
          ·
            refine ⟨113969836873002838036944919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151959782497337117382593225 113969836873002838036944919)
            ·
              refine ⟨170954755309504257055417379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113969836873002838036944919 170954755309504257055417379)
              ·
                refine ⟨256432132964256385583126069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 170954755309504257055417379 256432132964256385583126069)
                ·
                  refine ⟨24040512465399036148418069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 256432132964256385583126069 24040512465399036148418069)
                  ·
                    refine ⟨1126899021815579819457097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24040512465399036148418069 1126899021815579819457097)
                    ·
                      refine ⟨845174266361684864592823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1126899021815579819457097 845174266361684864592823)
                      ·
                        rfl

theorem cell23_1645971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 5, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 5, 6, 2].length) (baseStart_1645971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1645971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1645971 prefixEnd_1645971 := by exact prefixLift 1645971
  have htrace : WordTrace (prefixWord ++ tailWord_1645971) baseStart_1645971 baseEnd_1645971 := by
    simpa [prefixWord, tailWord_1645971, baseEnd_1645971] using wordTrace_append hprefix tailTrace_1645971
  have hstable : (prefixWord ++ tailWord_1645971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1645971).length < 2 ^ (prefixWord ++ tailWord_1645971).sum := by decide
  have hdescent : baseEnd_1645971 < baseStart_1645971 := by decide
  rcases family_descends (prefixWord ++ tailWord_1645971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1645972 : List Nat := [2, 4, 2, 1, 2, 3, 2, 2, 5]
def baseStart_1645972 : Nat := 118140960795 + 1645972 * 2 ^ 59
def prefixEnd_1645972 : Nat := 4983230072969 + 3 ^ 40 * 1645972 * 2
def baseEnd_1645972 : Nat := 93908308871371040075591

theorem tailTrace_1645972 : CollatzResearch.WordTrace tailWord_1645972 prefixEnd_1645972 93908308871371040075591 := by
  unfold tailWord_1645972
  simp only [CollatzResearch.WordTrace]
  refine ⟨30016765396466014241214085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40022353861954685654952113 30016765396466014241214085)
  ·
    refine ⟨5628143511837377670227641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30016765396466014241214085 5628143511837377670227641)
    ·
      refine ⟨4221107633878033252670731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5628143511837377670227641 4221107633878033252670731)
      ·
        refine ⟨6331661450817049879006097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4221107633878033252670731 6331661450817049879006097)
        ·
          refine ⟨4748746088112787409254573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6331661450817049879006097 4748746088112787409254573)
          ·
            refine ⟨1780779783042295278470465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4748746088112787409254573 1780779783042295278470465)
            ·
              refine ⟨1335584837281721458852849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1780779783042295278470465 1335584837281721458852849)
              ·
                refine ⟨1001688627961291094139637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1335584837281721458852849 1001688627961291094139637)
                ·
                  refine ⟨93908308871371040075591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1001688627961291094139637 93908308871371040075591)
                  ·
                    rfl

theorem cell23_1645972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 2, 2, 5].length) (baseStart_1645972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1645972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1645972 prefixEnd_1645972 := by exact prefixLift 1645972
  have htrace : WordTrace (prefixWord ++ tailWord_1645972) baseStart_1645972 baseEnd_1645972 := by
    simpa [prefixWord, tailWord_1645972, baseEnd_1645972] using wordTrace_append hprefix tailTrace_1645972
  have hstable : (prefixWord ++ tailWord_1645972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1645972).length < 2 ^ (prefixWord ++ tailWord_1645972).sum := by decide
  have hdescent : baseEnd_1645972 < baseStart_1645972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1645972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1646005 : List Nat := [1, 3, 3, 2, 2, 3, 1, 1, 2, 1, 4]
def baseStart_1646005 : Nat := 118140960795 + 1646005 * 2 ^ 59
def prefixEnd_1646005 : Nat := 4983230072969 + 3 ^ 40 * 1646005 * 2
def baseEnd_1646005 : Nat := 845191724703937731567667

theorem tailTrace_1646005 : CollatzResearch.WordTrace tailWord_1646005 prefixEnd_1646005 845191724703937731567667 := by
  unfold tailWord_1646005
  simp only [CollatzResearch.WordTrace]
  refine ⟨60034734401812475118379469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40023156267874983412252979 60034734401812475118379469)
  ·
    refine ⟨22513025400679678169392301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60034734401812475118379469 22513025400679678169392301)
    ·
      refine ⟨8442384525254879313522113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22513025400679678169392301 8442384525254879313522113)
      ·
        refine ⟨6331788393941159485141585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8442384525254879313522113 6331788393941159485141585)
        ·
          refine ⟨4748841295455869613856189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6331788393941159485141585 4748841295455869613856189)
          ·
            refine ⟨1780815485795951105196071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4748841295455869613856189 1780815485795951105196071)
            ·
              refine ⟨2671223228693926657794107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1780815485795951105196071 2671223228693926657794107)
              ·
                refine ⟨4006834843040889986691161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2671223228693926657794107 4006834843040889986691161)
                ·
                  refine ⟨3005126132280667490018371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4006834843040889986691161 3005126132280667490018371)
                  ·
                    refine ⟨4507689198421001235027557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3005126132280667490018371 4507689198421001235027557)
                    ·
                      refine ⟨845191724703937731567667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4507689198421001235027557 845191724703937731567667)
                      ·
                        rfl

theorem cell23_1646005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 1, 1, 2, 1, 4].length) (baseStart_1646005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1646005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1646005 prefixEnd_1646005 := by exact prefixLift 1646005
  have htrace : WordTrace (prefixWord ++ tailWord_1646005) baseStart_1646005 baseEnd_1646005 := by
    simpa [prefixWord, tailWord_1646005, baseEnd_1646005] using wordTrace_append hprefix tailTrace_1646005
  have hstable : (prefixWord ++ tailWord_1646005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646005).length < 2 ^ (prefixWord ++ tailWord_1646005).sum := by decide
  have hdescent : baseEnd_1646005 < baseStart_1646005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1646008 : List Nat := [2, 1, 2, 1, 2, 2, 5, 1, 2, 2, 3]
def baseStart_1646008 : Nat := 118140960795 + 1646008 * 2 ^ 59
def prefixEnd_1646008 : Nat := 4983230072969 + 3 ^ 40 * 1646008 * 2
def baseEnd_1646008 : Nat := 845193265145901219830153

theorem tailTrace_1646008 : CollatzResearch.WordTrace tailWord_1646008 prefixEnd_1646008 845193265145901219830153 := by
  unfold tailWord_1646008
  simp only [CollatzResearch.WordTrace]
  refine ⟨30017421910400803315369339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40023229213867737753825785 30017421910400803315369339)
  ·
    refine ⟨45026132865601204973054009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30017421910400803315369339 45026132865601204973054009)
    ·
      refine ⟨33769599649200903729790507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45026132865601204973054009 33769599649200903729790507)
      ·
        refine ⟨50654399473801355594685761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33769599649200903729790507 50654399473801355594685761)
        ·
          refine ⟨37990799605351016696014321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50654399473801355594685761 37990799605351016696014321)
          ·
            refine ⟨28493099704013262522010741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37990799605351016696014321 28493099704013262522010741)
            ·
              refine ⟨2671228097251243361438507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28493099704013262522010741 2671228097251243361438507)
              ·
                refine ⟨4006842145876865042157761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2671228097251243361438507 4006842145876865042157761)
                ·
                  refine ⟨3005131609407648781618321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4006842145876865042157761 3005131609407648781618321)
                  ·
                    refine ⟨2253848707055736586213741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3005131609407648781618321 2253848707055736586213741)
                    ·
                      refine ⟨845193265145901219830153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2253848707055736586213741 845193265145901219830153)
                      ·
                        rfl

theorem cell23_1646008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 5, 1, 2, 2, 3].length) (baseStart_1646008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1646008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1646008 prefixEnd_1646008 := by exact prefixLift 1646008
  have htrace : WordTrace (prefixWord ++ tailWord_1646008) baseStart_1646008 baseEnd_1646008 := by
    simpa [prefixWord, tailWord_1646008, baseEnd_1646008] using wordTrace_append hprefix tailTrace_1646008
  have hstable : (prefixWord ++ tailWord_1646008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646008).length < 2 ^ (prefixWord ++ tailWord_1646008).sum := by decide
  have hdescent : baseEnd_1646008 < baseStart_1646008 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1646028 : List Nat := [2, 2, 1, 4, 2, 1, 3, 2, 6]
def baseStart_1646028 : Nat := 118140960795 + 1646028 * 2 ^ 59
def prefixEnd_1646028 : Nat := 4983230072969 + 3 ^ 40 * 1646028 * 2
def baseEnd_1646028 : Nat := 93911503862110126842229

theorem tailTrace_1646028 : CollatzResearch.WordTrace tailWord_1646028 prefixEnd_1646028 93911503862110126842229 := by
  unfold tailWord_1646028
  simp only [CollatzResearch.WordTrace]
  refine ⟨30017786640364575023233369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40023715520486100030977825 30017786640364575023233369)
  ·
    refine ⟨22513339980273431267425027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30017786640364575023233369 22513339980273431267425027)
    ·
      refine ⟨33770009970410146901137541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22513339980273431267425027 33770009970410146901137541)
      ·
        refine ⟨6331876869451902543963289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33770009970410146901137541 6331876869451902543963289)
        ·
          refine ⟨4748907652088926907972467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6331876869451902543963289 4748907652088926907972467)
          ·
            refine ⟨7123361478133390361958701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4748907652088926907972467 7123361478133390361958701)
            ·
              refine ⟨2671260554300021385734513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7123361478133390361958701 2671260554300021385734513)
              ·
                refine ⟨2003445415725016039300885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2671260554300021385734513 2003445415725016039300885)
                ·
                  refine ⟨93911503862110126842229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2003445415725016039300885 93911503862110126842229)
                  ·
                    rfl

theorem cell23_1646028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 3, 2, 6].length) (baseStart_1646028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1646028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1646028 prefixEnd_1646028 := by exact prefixLift 1646028
  have htrace : WordTrace (prefixWord ++ tailWord_1646028) baseStart_1646028 baseEnd_1646028 := by
    simpa [prefixWord, tailWord_1646028, baseEnd_1646028] using wordTrace_append hprefix tailTrace_1646028
  have hstable : (prefixWord ++ tailWord_1646028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646028).length < 2 ^ (prefixWord ++ tailWord_1646028).sum := by decide
  have hdescent : baseEnd_1646028 < baseStart_1646028 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1646045 : List Nat := [1, 4, 3, 1, 1, 3, 3, 1, 6]
def baseStart_1646045 : Nat := 118140960795 + 1646045 * 2 ^ 59
def prefixEnd_1646045 : Nat := 4983230072969 + 3 ^ 40 * 1646045 * 2
def baseEnd_1646045 : Nat := 93912473770013063896387

theorem tailTrace_1646045 : CollatzResearch.WordTrace tailWord_1646045 prefixEnd_1646045 93912473770013063896387 := by
  unfold tailWord_1646045
  simp only [CollatzResearch.WordTrace]
  refine ⟨60036193321667561949835589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40024128881111707966557059 60036193321667561949835589)
  ·
    refine ⟨11256786247812667865594173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60036193321667561949835589 11256786247812667865594173)
    ·
      refine ⟨4221294842929750449597815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11256786247812667865594173 4221294842929750449597815)
      ·
        refine ⟨6331942264394625674396723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4221294842929750449597815 6331942264394625674396723)
        ·
          refine ⟨9497913396591938511595085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6331942264394625674396723 9497913396591938511595085)
          ·
            refine ⟨3561717523721976941848157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9497913396591938511595085 3561717523721976941848157)
            ·
              refine ⟨1335644071395741353193059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3561717523721976941848157 1335644071395741353193059)
              ·
                refine ⟨2003466107093612029789589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1335644071395741353193059 2003466107093612029789589)
                ·
                  refine ⟨93912473770013063896387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2003466107093612029789589 93912473770013063896387)
                  ·
                    rfl

theorem cell23_1646045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 3, 1, 6].length) (baseStart_1646045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1646045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1646045 prefixEnd_1646045 := by exact prefixLift 1646045
  have htrace : WordTrace (prefixWord ++ tailWord_1646045) baseStart_1646045 baseEnd_1646045 := by
    simpa [prefixWord, tailWord_1646045, baseEnd_1646045] using wordTrace_append hprefix tailTrace_1646045
  have hstable : (prefixWord ++ tailWord_1646045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646045).length < 2 ^ (prefixWord ++ tailWord_1646045).sum := by decide
  have hdescent : baseEnd_1646045 < baseStart_1646045 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1646048 : List Nat := [2, 1, 1, 3, 1, 1, 2, 1, 6, 3, 2]
def baseStart_1646048 : Nat := 118140960795 + 1646048 * 2 ^ 59
def prefixEnd_1646048 : Nat := 4983230072969 + 3 ^ 40 * 1646048 * 2
def baseEnd_1646048 : Nat := 845213804372081063329969

theorem tailTrace_1646048 : CollatzResearch.WordTrace tailWord_1646048 prefixEnd_1646048 845213804372081063329969 := by
  unfold tailWord_1646048
  simp only [CollatzResearch.WordTrace]
  refine ⟨30018151370328346731097399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40024201827104462308129865 30018151370328346731097399)
  ·
    refine ⟨45027227055492520096646099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30018151370328346731097399 45027227055492520096646099)
    ·
      refine ⟨67540840583238780144969149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45027227055492520096646099 67540840583238780144969149)
      ·
        refine ⟨25327815218714542554363431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67540840583238780144969149 25327815218714542554363431)
        ·
          refine ⟨37991722828071813831545147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25327815218714542554363431 37991722828071813831545147)
          ·
            refine ⟨56987584242107720747317721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37991722828071813831545147 56987584242107720747317721)
            ·
              refine ⟨42740688181580790560488291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56987584242107720747317721 42740688181580790560488291)
              ·
                refine ⟨64111032272371185840732437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42740688181580790560488291 64111032272371185840732437)
                ·
                  refine ⟨3005204637767399336284333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 64111032272371185840732437 3005204637767399336284333)
                  ·
                    refine ⟨1126951739162774751106625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3005204637767399336284333 1126951739162774751106625)
                    ·
                      refine ⟨845213804372081063329969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1126951739162774751106625 845213804372081063329969)
                      ·
                        rfl

theorem cell23_1646048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 6, 3, 2].length) (baseStart_1646048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1646048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1646048 prefixEnd_1646048 := by exact prefixLift 1646048
  have htrace : WordTrace (prefixWord ++ tailWord_1646048) baseStart_1646048 baseEnd_1646048 := by
    simpa [prefixWord, tailWord_1646048, baseEnd_1646048] using wordTrace_append hprefix tailTrace_1646048
  have hstable : (prefixWord ++ tailWord_1646048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646048).length < 2 ^ (prefixWord ++ tailWord_1646048).sum := by decide
  have hdescent : baseEnd_1646048 < baseStart_1646048 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1646055 : List Nat := [1, 1, 5, 2, 1, 2, 2, 2, 3, 1, 3]
def baseStart_1646055 : Nat := 118140960795 + 1646055 * 2 ^ 59
def prefixEnd_1646055 : Nat := 4983230072969 + 3 ^ 40 * 1646055 * 2
def baseEnd_1646055 : Nat := 845217398736662535942437

theorem tailTrace_1646055 : CollatzResearch.WordTrace tailWord_1646055 prefixEnd_1646055 845217398736662535942437 := by
  unfold tailWord_1646055
  simp only [CollatzResearch.WordTrace]
  refine ⟨60036558051631333657699619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40024372034420889105133079 60036558051631333657699619)
  ·
    refine ⟨90054837077447000486549429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60036558051631333657699619 90054837077447000486549429)
    ·
      refine ⟨8442640976010656295614009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 90054837077447000486549429 8442640976010656295614009)
      ·
        refine ⟨6331980732007992221710507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8442640976010656295614009 6331980732007992221710507)
        ·
          refine ⟨9497971098011988332565761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6331980732007992221710507 9497971098011988332565761)
          ·
            refine ⟨7123478323508991249424321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9497971098011988332565761 7123478323508991249424321)
            ·
              refine ⟨5342608742631743437068241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7123478323508991249424321 5342608742631743437068241)
              ·
                refine ⟨4006956556973807577801181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5342608742631743437068241 4006956556973807577801181)
                ·
                  refine ⟨1502608708865177841675443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4006956556973807577801181 1502608708865177841675443)
                  ·
                    refine ⟨2253913063297766762513165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1502608708865177841675443 2253913063297766762513165)
                    ·
                      refine ⟨845217398736662535942437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2253913063297766762513165 845217398736662535942437)
                      ·
                        rfl

theorem cell23_1646055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 2, 3, 1, 3].length) (baseStart_1646055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1646055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1646055 prefixEnd_1646055 := by exact prefixLift 1646055
  have htrace : WordTrace (prefixWord ++ tailWord_1646055) baseStart_1646055 baseEnd_1646055 := by
    simpa [prefixWord, tailWord_1646055, baseEnd_1646055] using wordTrace_append hprefix tailTrace_1646055
  have hstable : (prefixWord ++ tailWord_1646055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646055).length < 2 ^ (prefixWord ++ tailWord_1646055).sum := by decide
  have hdescent : baseEnd_1646055 < baseStart_1646055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1646072 : List Nat := [2, 1, 2, 1, 1, 5, 3, 3, 1, 1, 3]
def baseStart_1646072 : Nat := 118140960795 + 1646072 * 2 ^ 59
def prefixEnd_1646072 : Nat := 4983230072969 + 3 ^ 40 * 1646072 * 2
def baseEnd_1646072 : Nat := 845226127907788969429859

theorem tailTrace_1646072 : CollatzResearch.WordTrace tailWord_1646072 prefixEnd_1646072 845226127907788969429859 := by
  unfold tailWord_1646072
  simp only [CollatzResearch.WordTrace]
  refine ⟨30018589046284872780534235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40024785395046497040712313 30018589046284872780534235)
  ·
    refine ⟨45027883569427309170801353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30018589046284872780534235 45027883569427309170801353)
    ·
      refine ⟨33770912677070481878101015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45027883569427309170801353 33770912677070481878101015)
      ·
        refine ⟨50656369015605722817151523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33770912677070481878101015 50656369015605722817151523)
        ·
          refine ⟨75984553523408584225727285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50656369015605722817151523 75984553523408584225727285)
          ·
            refine ⟨7123551892819554771161933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 75984553523408584225727285 7123551892819554771161933)
            ·
              refine ⟨2671331959807333039185725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7123551892819554771161933 2671331959807333039185725)
              ·
                refine ⟨1001749484927749889694647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2671331959807333039185725 1001749484927749889694647)
                ·
                  refine ⟨1502624227391624834541971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1001749484927749889694647 1502624227391624834541971)
                  ·
                    refine ⟨2253936341087437251812957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1502624227391624834541971 2253936341087437251812957)
                    ·
                      refine ⟨845226127907788969429859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2253936341087437251812957 845226127907788969429859)
                      ·
                        rfl

theorem cell23_1646072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 3, 3, 1, 1, 3].length) (baseStart_1646072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1646072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1646072 prefixEnd_1646072 := by exact prefixLift 1646072
  have htrace : WordTrace (prefixWord ++ tailWord_1646072) baseStart_1646072 baseEnd_1646072 := by
    simpa [prefixWord, tailWord_1646072, baseEnd_1646072] using wordTrace_append hprefix tailTrace_1646072
  have hstable : (prefixWord ++ tailWord_1646072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646072).length < 2 ^ (prefixWord ++ tailWord_1646072).sum := by decide
  have hdescent : baseEnd_1646072 < baseStart_1646072 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1646082 : List Nat := [3, 4, 1, 2, 1, 1, 1, 1, 4, 3, 2]
def baseStart_1646082 : Nat := 118140960795 + 1646082 * 2 ^ 59
def prefixEnd_1646082 : Nat := 4983230072969 + 3 ^ 40 * 1646082 * 2
def baseEnd_1646082 : Nat := 845231262714333930304813

theorem tailTrace_1646082 : CollatzResearch.WordTrace tailWord_1646082 prefixEnd_1646082 845231262714333930304813 := by
  unfold tailWord_1646082
  simp only [CollatzResearch.WordTrace]
  refine ⟨15009385705633379317233125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40025028548355678179288333 15009385705633379317233125)
  ·
    refine ⟨2814259819806258621981211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15009385705633379317233125 2814259819806258621981211)
    ·
      refine ⟨4221389729709387932971817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2814259819806258621981211 4221389729709387932971817)
      ·
        refine ⟨3166042297282040949728863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4221389729709387932971817 3166042297282040949728863)
        ·
          refine ⟨4749063445923061424593295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3166042297282040949728863 4749063445923061424593295)
          ·
            refine ⟨7123595168884592136889943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4749063445923061424593295 7123595168884592136889943)
            ·
              refine ⟨10685392753326888205334915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7123595168884592136889943 10685392753326888205334915)
              ·
                refine ⟨16028089129990332308002373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10685392753326888205334915 16028089129990332308002373)
                ·
                  refine ⟨3005266711873187307750445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16028089129990332308002373 3005266711873187307750445)
                  ·
                    refine ⟨1126975016952445240406417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3005266711873187307750445 1126975016952445240406417)
                    ·
                      refine ⟨845231262714333930304813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1126975016952445240406417 845231262714333930304813)
                      ·
                        rfl

theorem cell23_1646082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 1, 4, 3, 2].length) (baseStart_1646082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1646082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1646082 prefixEnd_1646082 := by exact prefixLift 1646082
  have htrace : WordTrace (prefixWord ++ tailWord_1646082) baseStart_1646082 baseEnd_1646082 := by
    simpa [prefixWord, tailWord_1646082, baseEnd_1646082] using wordTrace_append hprefix tailTrace_1646082
  have hstable : (prefixWord ++ tailWord_1646082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646082).length < 2 ^ (prefixWord ++ tailWord_1646082).sum := by decide
  have hdescent : baseEnd_1646082 < baseStart_1646082 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1646088 : List Nat := [2, 1, 3, 2, 1, 1, 4, 1, 4, 4]
def baseStart_1646088 : Nat := 118140960795 + 1646088 * 2 ^ 59
def prefixEnd_1646088 : Nat := 4983230072969 + 3 ^ 40 * 1646088 * 2
def baseEnd_1646088 : Nat := 281744781199420302276595

theorem tailTrace_1646088 : CollatzResearch.WordTrace tailWord_1646088 prefixEnd_1646088 281744781199420302276595 := by
  unfold tailWord_1646088
  simp only [CollatzResearch.WordTrace]
  refine ⟨30018880830255890146825459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40025174440341186862433945 30018880830255890146825459)
  ·
    refine ⟨45028321245383835220238189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30018880830255890146825459 45028321245383835220238189)
    ·
      refine ⟨16885620467018938207589321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45028321245383835220238189 16885620467018938207589321)
      ·
        refine ⟨12664215350264203655691991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16885620467018938207589321 12664215350264203655691991)
        ·
          refine ⟨18996323025396305483537987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12664215350264203655691991 18996323025396305483537987)
          ·
            refine ⟨28494484538094458225306981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18996323025396305483537987 28494484538094458225306981)
            ·
              refine ⟨5342715850892710917245059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28494484538094458225306981 5342715850892710917245059)
              ·
                refine ⟨8014073776339066375867589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5342715850892710917245059 8014073776339066375867589)
                ·
                  refine ⟨1502638833063574945475173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8014073776339066375867589 1502638833063574945475173)
                  ·
                    refine ⟨281744781199420302276595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1502638833063574945475173 281744781199420302276595)
                    ·
                      rfl

theorem cell23_1646088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 1, 4, 4].length) (baseStart_1646088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1646088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1646088 prefixEnd_1646088 := by exact prefixLift 1646088
  have htrace : WordTrace (prefixWord ++ tailWord_1646088) baseStart_1646088 baseEnd_1646088 := by
    simpa [prefixWord, tailWord_1646088, baseEnd_1646088] using wordTrace_append hprefix tailTrace_1646088
  have hstable : (prefixWord ++ tailWord_1646088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646088).length < 2 ^ (prefixWord ++ tailWord_1646088).sum := by decide
  have hdescent : baseEnd_1646088 < baseStart_1646088 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1646101 : List Nat := [1, 3, 2, 1, 3, 2, 1, 10]
def baseStart_1646101 : Nat := 118140960795 + 1646101 * 2 ^ 59
def prefixEnd_1646101 : Nat := 4983230072969 + 3 ^ 40 * 1646101 * 2
def baseEnd_1646101 : Nat := 31305222920250716887675

theorem tailTrace_1646101 : CollatzResearch.WordTrace tailWord_1646101 prefixEnd_1646101 31305222920250716887675 := by
  unfold tailWord_1646101
  simp only [CollatzResearch.WordTrace]
  refine ⟨60038235809464683513874157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40025490539643122342582771 60038235809464683513874157)
  ·
    refine ⟨22514338428549256317702809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60038235809464683513874157 22514338428549256317702809)
    ·
      refine ⟨16885753821411942238277107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22514338428549256317702809 16885753821411942238277107)
      ·
        refine ⟨25328630732117913357415661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16885753821411942238277107 25328630732117913357415661)
        ·
          refine ⟨9498236524544217509030873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25328630732117913357415661 9498236524544217509030873)
          ·
            refine ⟨7123677393408163131773155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9498236524544217509030873 7123677393408163131773155)
            ·
              refine ⟨10685516090112244697659733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7123677393408163131773155 10685516090112244697659733)
              ·
                refine ⟨31305222920250716887675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 10685516090112244697659733 31305222920250716887675)
                ·
                  rfl

theorem cell23_1646101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 10].length) (baseStart_1646101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1646101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1646101 prefixEnd_1646101 := by exact prefixLift 1646101
  have htrace : WordTrace (prefixWord ++ tailWord_1646101) baseStart_1646101 baseEnd_1646101 := by
    simpa [prefixWord, tailWord_1646101, baseEnd_1646101] using wordTrace_append hprefix tailTrace_1646101
  have hstable : (prefixWord ++ tailWord_1646101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646101).length < 2 ^ (prefixWord ++ tailWord_1646101).sum := by decide
  have hdescent : baseEnd_1646101 < baseStart_1646101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1646108 : List Nat := [2, 2, 3, 1, 2, 1, 2, 3, 1, 2, 4]
def baseStart_1646108 : Nat := 118140960795 + 1646108 * 2 ^ 59
def prefixEnd_1646108 : Nat := 4983230072969 + 3 ^ 40 * 1646108 * 2
def baseEnd_1646108 : Nat := 845244613211350828579693

theorem tailTrace_1646108 : CollatzResearch.WordTrace tailWord_1646108 prefixEnd_1646108 845244613211350828579693 := by
  unfold tailWord_1646108
  simp only [CollatzResearch.WordTrace]
  refine ⟨30019245560219661854689489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40025660746959549139585985 30019245560219661854689489)
  ·
    refine ⟨22514434170164746391017117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30019245560219661854689489 22514434170164746391017117)
    ·
      refine ⟨8442912813811779896631419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22514434170164746391017117 8442912813811779896631419)
      ·
        refine ⟨12664369220717669844947129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8442912813811779896631419 12664369220717669844947129)
        ·
          refine ⟨9498276915538252383710347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12664369220717669844947129 9498276915538252383710347)
          ·
            refine ⟨14247415373307378575565521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9498276915538252383710347 14247415373307378575565521)
            ·
              refine ⟨10685561529980533931674141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14247415373307378575565521 10685561529980533931674141)
              ·
                refine ⟨4007085573742700224377803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10685561529980533931674141 4007085573742700224377803)
                ·
                  refine ⟨6010628360614050336566705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4007085573742700224377803 6010628360614050336566705)
                  ·
                    refine ⟨4507971270460537752425029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6010628360614050336566705 4507971270460537752425029)
                    ·
                      refine ⟨845244613211350828579693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4507971270460537752425029 845244613211350828579693)
                      ·
                        rfl

theorem cell23_1646108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 3, 1, 2, 4].length) (baseStart_1646108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1646108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1646108 prefixEnd_1646108 := by exact prefixLift 1646108
  have htrace : WordTrace (prefixWord ++ tailWord_1646108) baseStart_1646108 baseEnd_1646108 := by
    simpa [prefixWord, tailWord_1646108, baseEnd_1646108] using wordTrace_append hprefix tailTrace_1646108
  have hstable : (prefixWord ++ tailWord_1646108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646108).length < 2 ^ (prefixWord ++ tailWord_1646108).sum := by decide
  have hdescent : baseEnd_1646108 < baseStart_1646108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1646112 : List Nat := [2, 1, 1, 6, 1, 3, 1, 2, 1, 1, 4]
def baseStart_1646112 : Nat := 118140960795 + 1646112 * 2 ^ 59
def prefixEnd_1646112 : Nat := 4983230072969 + 3 ^ 40 * 1646112 * 2
def baseEnd_1646112 : Nat := 845246667133968812929675

theorem tailTrace_1646112 : CollatzResearch.WordTrace tailWord_1646112 prefixEnd_1646112 845246667133968812929675 := by
  unfold tailWord_1646112
  simp only [CollatzResearch.WordTrace]
  refine ⟨30019318506212416196262295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40025758008283221595016393 30019318506212416196262295)
  ·
    refine ⟨45028977759318624294393443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30019318506212416196262295 45028977759318624294393443)
    ·
      refine ⟨67543466638977936441590165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45028977759318624294393443 67543466638977936441590165)
      ·
        refine ⟨3166099998702090770699539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 67543466638977936441590165 3166099998702090770699539)
        ·
          refine ⟨4749149998053136156049309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3166099998702090770699539 4749149998053136156049309)
          ·
            refine ⟨1780931249269926058518491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4749149998053136156049309 1780931249269926058518491)
            ·
              refine ⟨2671396873904889087777737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1780931249269926058518491 2671396873904889087777737)
              ·
                refine ⟨2003547655428666815833303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2671396873904889087777737 2003547655428666815833303)
                ·
                  refine ⟨3005321483143000223749955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2003547655428666815833303 3005321483143000223749955)
                  ·
                    refine ⟨4507982224714500335624933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3005321483143000223749955 4507982224714500335624933)
                    ·
                      refine ⟨845246667133968812929675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4507982224714500335624933 845246667133968812929675)
                      ·
                        rfl

theorem cell23_1646112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_1646112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1646112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1646112 prefixEnd_1646112 := by exact prefixLift 1646112
  have htrace : WordTrace (prefixWord ++ tailWord_1646112) baseStart_1646112 baseEnd_1646112 := by
    simpa [prefixWord, tailWord_1646112, baseEnd_1646112] using wordTrace_append hprefix tailTrace_1646112
  have hstable : (prefixWord ++ tailWord_1646112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646112).length < 2 ^ (prefixWord ++ tailWord_1646112).sum := by decide
  have hdescent : baseEnd_1646112 < baseStart_1646112 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1646115 : List Nat := [1, 1, 1, 4, 5, 1, 1, 1, 3, 2, 3]
def baseStart_1646115 : Nat := 118140960795 + 1646115 * 2 ^ 59
def prefixEnd_1646115 : Nat := 4983230072969 + 3 ^ 40 * 1646115 * 2
def baseEnd_1646115 : Nat := 845248207575932301192161

theorem tailTrace_1646115 : CollatzResearch.WordTrace tailWord_1646115 prefixEnd_1646115 845248207575932301192161 := by
  unfold tailWord_1646115
  simp only [CollatzResearch.WordTrace]
  refine ⟨60038746431413963904883799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40025830954275975936589199 60038746431413963904883799)
  ·
    refine ⟨90058119647120945857325699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60038746431413963904883799 90058119647120945857325699)
    ·
      refine ⟨135087179470681418785988549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90058119647120945857325699 135087179470681418785988549)
      ·
        refine ⟨25328846150752766022372853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 135087179470681418785988549 25328846150752766022372853)
        ·
          refine ⟨2374579326633071814597455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25328846150752766022372853 2374579326633071814597455)
          ·
            refine ⟨3561868989949607721896183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2374579326633071814597455 3561868989949607721896183)
            ·
              refine ⟨5342803484924411582844275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3561868989949607721896183 5342803484924411582844275)
              ·
                refine ⟨8014205227386617374266413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5342803484924411582844275 8014205227386617374266413)
                ·
                  refine ⟨3005326960269981515349905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8014205227386617374266413 3005326960269981515349905)
                  ·
                    refine ⟨2253995220202486136512429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3005326960269981515349905 2253995220202486136512429)
                    ·
                      refine ⟨845248207575932301192161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2253995220202486136512429 845248207575932301192161)
                      ·
                        rfl

theorem cell23_1646115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 1, 3, 2, 3].length) (baseStart_1646115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1646115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1646115 prefixEnd_1646115 := by exact prefixLift 1646115
  have htrace : WordTrace (prefixWord ++ tailWord_1646115) baseStart_1646115 baseEnd_1646115 := by
    simpa [prefixWord, tailWord_1646115, baseEnd_1646115] using wordTrace_append hprefix tailTrace_1646115
  have hstable : (prefixWord ++ tailWord_1646115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646115).length < 2 ^ (prefixWord ++ tailWord_1646115).sum := by decide
  have hdescent : baseEnd_1646115 < baseStart_1646115 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1646162 : List Nat := [3, 2, 2, 1, 2, 2, 2, 3, 2, 1, 3]
def baseStart_1646162 : Nat := 118140960795 + 1646162 * 2 ^ 59
def prefixEnd_1646162 : Nat := 4983230072969 + 3 ^ 40 * 1646162 * 2
def baseEnd_1646162 : Nat := 845272341166693617304445

theorem tailTrace_1646162 : CollatzResearch.WordTrace tailWord_1646162 prefixEnd_1646162 845272341166693617304445 := by
  unfold tailWord_1646162
  simp only [CollatzResearch.WordTrace]
  refine ⟨15010115165560922732961185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40026973774829127287896493 15010115165560922732961185)
  ·
    refine ⟨11257586374170692049720889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15010115165560922732961185 11257586374170692049720889)
    ·
      refine ⟨8443189780628019037290667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11257586374170692049720889 8443189780628019037290667)
      ·
        refine ⟨12664784670942028555936001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8443189780628019037290667 12664784670942028555936001)
        ·
          refine ⟨9498588503206521416952001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12664784670942028555936001 9498588503206521416952001)
          ·
            refine ⟨7123941377404891062714001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9498588503206521416952001 7123941377404891062714001)
            ·
              refine ⟨5342956033053668297035501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7123941377404891062714001 5342956033053668297035501)
              ·
                refine ⟨2003608512395125611388313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5342956033053668297035501 2003608512395125611388313)
                ·
                  refine ⟨1502706384296344208541235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2003608512395125611388313 1502706384296344208541235)
                  ·
                    refine ⟨2254059576444516312811853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1502706384296344208541235 2254059576444516312811853)
                    ·
                      refine ⟨845272341166693617304445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2254059576444516312811853 845272341166693617304445)
                      ·
                        rfl

theorem cell23_1646162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 3, 2, 1, 3].length) (baseStart_1646162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1646162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1646162 prefixEnd_1646162 := by exact prefixLift 1646162
  have htrace : WordTrace (prefixWord ++ tailWord_1646162) baseStart_1646162 baseEnd_1646162 := by
    simpa [prefixWord, tailWord_1646162, baseEnd_1646162] using wordTrace_append hprefix tailTrace_1646162
  have hstable : (prefixWord ++ tailWord_1646162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646162).length < 2 ^ (prefixWord ++ tailWord_1646162).sum := by decide
  have hdescent : baseEnd_1646162 < baseStart_1646162 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1646172 : List Nat := [2, 2, 4, 1, 2, 1, 2, 1, 3, 3, 2]
def baseStart_1646172 : Nat := 118140960795 + 1646172 * 2 ^ 59
def prefixEnd_1646172 : Nat := 4983230072969 + 3 ^ 40 * 1646172 * 2
def baseEnd_1646172 : Nat := 845277475973238578179399

theorem tailTrace_1646172 : CollatzResearch.WordTrace tailWord_1646172 prefixEnd_1646172 845277475973238578179399 := by
  unfold tailWord_1646172
  simp only [CollatzResearch.WordTrace]
  refine ⟨30020412696103731319854385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40027216928138308426472513 30020412696103731319854385)
  ·
    refine ⟨22515309522077798489890789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30020412696103731319854385 22515309522077798489890789)
    ·
      refine ⟨4221620535389587216854523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22515309522077798489890789 4221620535389587216854523)
      ·
        refine ⟨6332430803084380825281785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4221620535389587216854523 6332430803084380825281785)
        ·
          refine ⟨4749323102313285618961339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6332430803084380825281785 4749323102313285618961339)
          ·
            refine ⟨7123984653469928428442009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4749323102313285618961339 7123984653469928428442009)
            ·
              refine ⟨5342988490102446321331507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7123984653469928428442009 5342988490102446321331507)
              ·
                refine ⟨8014482735153669481997261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5342988490102446321331507 8014482735153669481997261)
                ·
                  refine ⟨3005431025682626055748973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8014482735153669481997261 3005431025682626055748973)
                  ·
                    refine ⟨1127036634630984770905865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3005431025682626055748973 1127036634630984770905865)
                    ·
                      refine ⟨845277475973238578179399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1127036634630984770905865 845277475973238578179399)
                      ·
                        rfl

theorem cell23_1646172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 1, 3, 3, 2].length) (baseStart_1646172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1646172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1646172 prefixEnd_1646172 := by exact prefixLift 1646172
  have htrace : WordTrace (prefixWord ++ tailWord_1646172) baseStart_1646172 baseEnd_1646172 := by
    simpa [prefixWord, tailWord_1646172, baseEnd_1646172] using wordTrace_append hprefix tailTrace_1646172
  have hstable : (prefixWord ++ tailWord_1646172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646172).length < 2 ^ (prefixWord ++ tailWord_1646172).sum := by decide
  have hdescent : baseEnd_1646172 < baseStart_1646172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1646185 : List Nat := [1, 2, 1, 1, 1, 4, 4, 2, 1, 4, 2]
def baseStart_1646185 : Nat := 118140960795 + 1646185 * 2 ^ 59
def prefixEnd_1646185 : Nat := 4983230072969 + 3 ^ 40 * 1646185 * 2
def baseEnd_1646185 : Nat := 845284151221747027316839

theorem tailTrace_1646185 : CollatzResearch.WordTrace tailWord_1646185 prefixEnd_1646185 845284151221747027316839 := by
  unfold tailWord_1646185
  simp only [CollatzResearch.WordTrace]
  refine ⟨60041299541160365859932009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40027533027440243906621339 60041299541160365859932009)
  ·
    refine ⟨45030974655870274394949007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60041299541160365859932009 45030974655870274394949007)
    ·
      refine ⟨67546461983805411592423511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45030974655870274394949007 67546461983805411592423511)
      ·
        refine ⟨101319692975708117388635267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67546461983805411592423511 101319692975708117388635267)
        ·
          refine ⟨151979539463562176082952901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101319692975708117388635267 151979539463562176082952901)
          ·
            refine ⟨28496163649417908015553669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 151979539463562176082952901 28496163649417908015553669)
            ·
              refine ⟨5343030684265857752916313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28496163649417908015553669 5343030684265857752916313)
              ·
                refine ⟨4007273013199393314687235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5343030684265857752916313 4007273013199393314687235)
                ·
                  refine ⟨6010909519799089972030853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4007273013199393314687235 6010909519799089972030853)
                  ·
                    refine ⟨1127045534962329369755785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6010909519799089972030853 1127045534962329369755785)
                    ·
                      refine ⟨845284151221747027316839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1127045534962329369755785 845284151221747027316839)
                      ·
                        rfl

theorem cell23_1646185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 2, 1, 4, 2].length) (baseStart_1646185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1646185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1646185 prefixEnd_1646185 := by exact prefixLift 1646185
  have htrace : WordTrace (prefixWord ++ tailWord_1646185) baseStart_1646185 baseEnd_1646185 := by
    simpa [prefixWord, tailWord_1646185, baseEnd_1646185] using wordTrace_append hprefix tailTrace_1646185
  have hstable : (prefixWord ++ tailWord_1646185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646185).length < 2 ^ (prefixWord ++ tailWord_1646185).sum := by decide
  have hdescent : baseEnd_1646185 < baseStart_1646185 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1646189 : List Nat := [1, 5, 1, 1, 4, 1, 1, 3, 1, 3, 2]
def baseStart_1646189 : Nat := 118140960795 + 1646189 * 2 ^ 59
def prefixEnd_1646189 : Nat := 4983230072969 + 3 ^ 40 * 1646189 * 2
def baseEnd_1646189 : Nat := 845286205144365011666821

theorem tailTrace_1646189 : CollatzResearch.WordTrace tailWord_1646189 prefixEnd_1646189 845286205144365011666821 := by
  unfold tailWord_1646189
  simp only [CollatzResearch.WordTrace]
  refine ⟨60041445433145874543077621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40027630288763916362051747 60041445433145874543077621)
  ·
    refine ⟨5628885509357425738413527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 60041445433145874543077621 5628885509357425738413527)
    ·
      refine ⟨8443328264036138607620291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5628885509357425738413527 8443328264036138607620291)
      ·
        refine ⟨12664992396054207911430437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8443328264036138607620291 12664992396054207911430437)
        ·
          refine ⟨2374686074260163983393207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12664992396054207911430437 2374686074260163983393207)
          ·
            refine ⟨3562029111390245975089811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2374686074260163983393207 3562029111390245975089811)
            ·
              refine ⟨5343043667085368962634717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3562029111390245975089811 5343043667085368962634717)
              ·
                refine ⟨2003641375157013360988019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5343043667085368962634717 2003641375157013360988019)
                ·
                  refine ⟨3005462062735520041482029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2003641375157013360988019 3005462062735520041482029)
                  ·
                    refine ⟨1127048273525820015555761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3005462062735520041482029 1127048273525820015555761)
                    ·
                      refine ⟨845286205144365011666821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1127048273525820015555761 845286205144365011666821)
                      ·
                        rfl

theorem cell23_1646189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 3, 1, 3, 2].length) (baseStart_1646189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1646189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1646189 prefixEnd_1646189 := by exact prefixLift 1646189
  have htrace : WordTrace (prefixWord ++ tailWord_1646189) baseStart_1646189 baseEnd_1646189 := by
    simpa [prefixWord, tailWord_1646189, baseEnd_1646189] using wordTrace_append hprefix tailTrace_1646189
  have hstable : (prefixWord ++ tailWord_1646189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646189).length < 2 ^ (prefixWord ++ tailWord_1646189).sum := by decide
  have hdescent : baseEnd_1646189 < baseStart_1646189 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1646191 : List Nat := [1, 1, 2, 1, 3, 2, 1, 1, 11]
def baseStart_1646191 : Nat := 118140960795 + 1646191 * 2 ^ 59
def prefixEnd_1646191 : Nat := 4983230072969 + 3 ^ 40 * 1646191 * 2
def baseEnd_1646191 : Nat := 93920803567297111537979

theorem tailTrace_1646191 : CollatzResearch.WordTrace tailWord_1646191 prefixEnd_1646191 93920803567297111537979 := by
  unfold tailWord_1646191
  simp only [CollatzResearch.WordTrace]
  refine ⟨60041518379138628884650427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40027678919425752589766951 60041518379138628884650427)
  ·
    refine ⟨90062277568707943326975641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60041518379138628884650427 90062277568707943326975641)
    ·
      refine ⟨67546708176530957495231731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90062277568707943326975641 67546708176530957495231731)
      ·
        refine ⟨101320062264796436242847597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67546708176530957495231731 101320062264796436242847597)
        ·
          refine ⟨37995023349298663591067849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101320062264796436242847597 37995023349298663591067849)
          ·
            refine ⟨28496267511973997693300887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37995023349298663591067849 28496267511973997693300887)
            ·
              refine ⟨42744401267960996539951331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28496267511973997693300887 42744401267960996539951331)
              ·
                refine ⟨64116601901941494809926997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42744401267960996539951331 64116601901941494809926997)
                ·
                  refine ⟨93920803567297111537979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 64116601901941494809926997 93920803567297111537979)
                  ·
                    rfl

theorem cell23_1646191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 11].length) (baseStart_1646191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1646191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1646191 prefixEnd_1646191 := by exact prefixLift 1646191
  have htrace : WordTrace (prefixWord ++ tailWord_1646191) baseStart_1646191 baseEnd_1646191 := by
    simpa [prefixWord, tailWord_1646191, baseEnd_1646191] using wordTrace_append hprefix tailTrace_1646191
  have hstable : (prefixWord ++ tailWord_1646191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646191).length < 2 ^ (prefixWord ++ tailWord_1646191).sum := by decide
  have hdescent : baseEnd_1646191 < baseStart_1646191 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1646202 : List Nat := [3, 1, 1, 1, 1, 1, 1, 8, 2, 2, 2]
def baseStart_1646202 : Nat := 118140960795 + 1646202 * 2 ^ 59
def prefixEnd_1646202 : Nat := 4983230072969 + 3 ^ 40 * 1646202 * 2
def baseEnd_1646202 : Nat := 845292880392873460804261

theorem tailTrace_1646202 : CollatzResearch.WordTrace tailWord_1646202 prefixEnd_1646202 845292880392873460804261 := by
  unfold tailWord_1646202
  simp only [CollatzResearch.WordTrace]
  refine ⟨15010479895524694440825215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40027946388065851842200573 15010479895524694440825215)
  ·
    refine ⟨22515719843287041661237823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15010479895524694440825215 22515719843287041661237823)
    ·
      refine ⟨33773579764930562491856735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22515719843287041661237823 33773579764930562491856735)
      ·
        refine ⟨50660369647395843737785103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33773579764930562491856735 50660369647395843737785103)
        ·
          refine ⟨75990554471093765606677655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50660369647395843737785103 75990554471093765606677655)
          ·
            refine ⟨113985831706640648410016483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75990554471093765606677655 113985831706640648410016483)
            ·
              refine ⟨170978747559960972615024725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113985831706640648410016483 170978747559960972615024725)
              ·
                refine ⟨2003657197968292647832321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 170978747559960972615024725 2003657197968292647832321)
                ·
                  refine ⟨1502742898476219485874241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2003657197968292647832321 1502742898476219485874241)
                  ·
                    refine ⟨1127057173857164614405681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1502742898476219485874241 1127057173857164614405681)
                    ·
                      refine ⟨845292880392873460804261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1127057173857164614405681 845292880392873460804261)
                      ·
                        rfl

theorem cell23_1646202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 8, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 8, 2, 2, 2].length) (baseStart_1646202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1646202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1646202 prefixEnd_1646202 := by exact prefixLift 1646202
  have htrace : WordTrace (prefixWord ++ tailWord_1646202) baseStart_1646202 baseEnd_1646202 := by
    simpa [prefixWord, tailWord_1646202, baseEnd_1646202] using wordTrace_append hprefix tailTrace_1646202
  have hstable : (prefixWord ++ tailWord_1646202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646202).length < 2 ^ (prefixWord ++ tailWord_1646202).sum := by decide
  have hdescent : baseEnd_1646202 < baseStart_1646202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1646208 : List Nat := [2, 1, 1, 2, 1, 4, 4, 1, 7]
def baseStart_1646208 : Nat := 118140960795 + 1646208 * 2 ^ 59
def prefixEnd_1646208 : Nat := 4983230072969 + 3 ^ 40 * 1646208 * 2
def baseEnd_1646208 : Nat := 93921773475200048592137

theorem tailTrace_1646208 : CollatzResearch.WordTrace tailWord_1646208 prefixEnd_1646208 93921773475200048592137 := by
  unfold tailWord_1646208
  simp only [CollatzResearch.WordTrace]
  refine ⟨30021069210038520394009639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40028092280051360525346185 30021069210038520394009639)
  ·
    refine ⟨45031603815057780591014459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30021069210038520394009639 45031603815057780591014459)
    ·
      refine ⟨67547405722586670886521689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45031603815057780591014459 67547405722586670886521689)
      ·
        refine ⟨50660554291940003164891267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67547405722586670886521689 50660554291940003164891267)
        ·
          refine ⟨75990831437910004747336901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50660554291940003164891267 75990831437910004747336901)
          ·
            refine ⟨14248280894608125890125669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75990831437910004747336901 14248280894608125890125669)
            ·
              refine ⟨2671552667739023604398563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14248280894608125890125669 2671552667739023604398563)
              ·
                refine ⟨4007329001608535406597845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2671552667739023604398563 4007329001608535406597845)
                ·
                  refine ⟨93921773475200048592137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4007329001608535406597845 93921773475200048592137)
                  ·
                    rfl

theorem cell23_1646208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 4, 1, 7].length) (baseStart_1646208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1646208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1646208 prefixEnd_1646208 := by exact prefixLift 1646208
  have htrace : WordTrace (prefixWord ++ tailWord_1646208) baseStart_1646208 baseEnd_1646208 := by
    simpa [prefixWord, tailWord_1646208, baseEnd_1646208] using wordTrace_append hprefix tailTrace_1646208
  have hstable : (prefixWord ++ tailWord_1646208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646208).length < 2 ^ (prefixWord ++ tailWord_1646208).sum := by decide
  have hdescent : baseEnd_1646208 < baseStart_1646208 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1646219 : List Nat := [1, 1, 1, 1, 4, 1, 7, 1, 2, 2, 2]
def baseStart_1646219 : Nat := 118140960795 + 1646219 * 2 ^ 59
def prefixEnd_1646219 : Nat := 4983230072969 + 3 ^ 40 * 1646219 * 2
def baseEnd_1646219 : Nat := 845301609563999894291683

theorem tailTrace_1646219 : CollatzResearch.WordTrace tailWord_1646219 prefixEnd_1646219 845301609563999894291683 := by
  unfold tailWord_1646219
  simp only [CollatzResearch.WordTrace]
  refine ⟨60042539623037189666669711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40028359748691459777779807 60042539623037189666669711)
  ·
    refine ⟨90063809434555784500004567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60042539623037189666669711 90063809434555784500004567)
    ·
      refine ⟨135095714151833676750006851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90063809434555784500004567 135095714151833676750006851)
      ·
        refine ⟨202643571227750515125010277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135095714151833676750006851 202643571227750515125010277)
        ·
          refine ⟨37995669605203221585939427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 202643571227750515125010277 37995669605203221585939427)
          ·
            refine ⟨56993504407804832378909141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37995669605203221585939427 56993504407804832378909141)
            ·
              refine ⟨1335785259557925758880683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 56993504407804832378909141 1335785259557925758880683)
              ·
                refine ⟨2003677889336888638321025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1335785259557925758880683 2003677889336888638321025)
                ·
                  refine ⟨1502758417002666478740769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2003677889336888638321025 1502758417002666478740769)
                  ·
                    refine ⟨1127068812751999859055577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1502758417002666478740769 1127068812751999859055577)
                    ·
                      refine ⟨845301609563999894291683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1127068812751999859055577 845301609563999894291683)
                      ·
                        rfl

theorem cell23_1646219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 7, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 7, 1, 2, 2, 2].length) (baseStart_1646219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1646219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1646219 prefixEnd_1646219 := by exact prefixLift 1646219
  have htrace : WordTrace (prefixWord ++ tailWord_1646219) baseStart_1646219 baseEnd_1646219 := by
    simpa [prefixWord, tailWord_1646219, baseEnd_1646219] using wordTrace_append hprefix tailTrace_1646219
  have hstable : (prefixWord ++ tailWord_1646219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646219).length < 2 ^ (prefixWord ++ tailWord_1646219).sum := by decide
  have hdescent : baseEnd_1646219 < baseStart_1646219 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1646292 : List Nat := [2, 4, 1, 3, 1, 1, 1, 3, 2, 1, 4]
def baseStart_1646292 : Nat := 118140960795 + 1646292 * 2 ^ 59
def prefixEnd_1646292 : Nat := 4983230072969 + 3 ^ 40 * 1646292 * 2
def baseEnd_1646292 : Nat := 845339093651778108678847

theorem tailTrace_1646292 : CollatzResearch.WordTrace tailWord_1646292 prefixEnd_1646292 845339093651778108678847 := by
  unfold tailWord_1646292
  simp only [CollatzResearch.WordTrace]
  refine ⟨30022601075886361567038565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40030134767848482089384753 30022601075886361567038565)
  ·
    refine ⟨5629237701728692793819731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30022601075886361567038565 5629237701728692793819731)
    ·
      refine ⟨8443856552593039190729597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5629237701728692793819731 8443856552593039190729597)
      ·
        refine ⟨3166446207222389696523599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8443856552593039190729597 3166446207222389696523599)
        ·
          refine ⟨4749669310833584544785399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3166446207222389696523599 4749669310833584544785399)
          ·
            refine ⟨7124503966250376817178099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4749669310833584544785399 7124503966250376817178099)
            ·
              refine ⟨10686755949375565225767149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7124503966250376817178099 10686755949375565225767149)
              ·
                refine ⟨4007533481015836959662681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10686755949375565225767149 4007533481015836959662681)
                ·
                  refine ⟨3005650110761877719747011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4007533481015836959662681 3005650110761877719747011)
                  ·
                    refine ⟨4508475166142816579620517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3005650110761877719747011 4508475166142816579620517)
                    ·
                      refine ⟨845339093651778108678847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4508475166142816579620517 845339093651778108678847)
                      ·
                        rfl

theorem cell23_1646292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_1646292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1646292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1646292 prefixEnd_1646292 := by exact prefixLift 1646292
  have htrace : WordTrace (prefixWord ++ tailWord_1646292) baseStart_1646292 baseEnd_1646292 := by
    simpa [prefixWord, tailWord_1646292, baseEnd_1646292] using wordTrace_append hprefix tailTrace_1646292
  have hstable : (prefixWord ++ tailWord_1646292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646292).length < 2 ^ (prefixWord ++ tailWord_1646292).sum := by decide
  have hdescent : baseEnd_1646292 < baseStart_1646292 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1646312 : List Nat := [2, 1, 4, 1, 3, 1, 2, 2, 2, 2, 3]
def baseStart_1646312 : Nat := 118140960795 + 1646312 * 2 ^ 59
def prefixEnd_1646312 : Nat := 4983230072969 + 3 ^ 40 * 1646312 * 2
def baseEnd_1646312 : Nat := 845349363264868030428755

theorem tailTrace_1646312 : CollatzResearch.WordTrace tailWord_1646312 prefixEnd_1646312 845349363264868030428755 := by
  unfold tailWord_1646312
  simp only [CollatzResearch.WordTrace]
  refine ⟨30022965805850133274902595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40030621074466844366536793 30022965805850133274902595)
  ·
    refine ⟨45034448708775199912353893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30022965805850133274902595 45034448708775199912353893)
    ·
      refine ⟨8443959132895349983566355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45034448708775199912353893 8443959132895349983566355)
      ·
        refine ⟨12665938699343024975349533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8443959132895349983566355 12665938699343024975349533)
        ·
          refine ⟨4749727012253634365756075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12665938699343024975349533 4749727012253634365756075)
          ·
            refine ⟨7124590518380451548634113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4749727012253634365756075 7124590518380451548634113)
            ·
              refine ⟨5343442888785338661475585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7124590518380451548634113 5343442888785338661475585)
              ·
                refine ⟨4007582166589003996106689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5343442888785338661475585 4007582166589003996106689)
                ·
                  refine ⟨3005686624941752997080017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4007582166589003996106689 3005686624941752997080017)
                  ·
                    refine ⟨2254264968706314747810013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3005686624941752997080017 2254264968706314747810013)
                    ·
                      refine ⟨845349363264868030428755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2254264968706314747810013 845349363264868030428755)
                      ·
                        rfl

theorem cell23_1646312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 2, 2, 2, 3].length) (baseStart_1646312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1646312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1646312 prefixEnd_1646312 := by exact prefixLift 1646312
  have htrace : WordTrace (prefixWord ++ tailWord_1646312) baseStart_1646312 baseEnd_1646312 := by
    simpa [prefixWord, tailWord_1646312, baseEnd_1646312] using wordTrace_append hprefix tailTrace_1646312
  have hstable : (prefixWord ++ tailWord_1646312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646312).length < 2 ^ (prefixWord ++ tailWord_1646312).sum := by decide
  have hdescent : baseEnd_1646312 < baseStart_1646312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1646345 : List Nat := [1, 2, 1, 1, 3, 2, 1, 6, 1, 5]
def baseStart_1646345 : Nat := 118140960795 + 1646345 * 2 ^ 59
def prefixEnd_1646345 : Nat := 4983230072969 + 3 ^ 40 * 1646345 * 2
def baseEnd_1646345 : Nat := 281788769375488800438701

theorem tailTrace_1646345 : CollatzResearch.WordTrace tailWord_1646345 prefixEnd_1646345 281788769375488800438701 := by
  unfold tailWord_1646345
  simp only [CollatzResearch.WordTrace]
  refine ⟨60047135220580713185756489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40031423480387142123837659 60047135220580713185756489)
  ·
    refine ⟨45035351415435534889317367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60047135220580713185756489 45035351415435534889317367)
    ·
      refine ⟨67553027123153302333976051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45035351415435534889317367 67553027123153302333976051)
      ·
        refine ⟨101329540684729953500964077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67553027123153302333976051 101329540684729953500964077)
        ·
          refine ⟨37998577756773732562861529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101329540684729953500964077 37998577756773732562861529)
          ·
            refine ⟨28498933317580299422146147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37998577756773732562861529 28498933317580299422146147)
            ·
              refine ⟨42748399976370449133219221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28498933317580299422146147 42748399976370449133219221)
              ·
                refine ⟨2003831248892364803119651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 42748399976370449133219221 2003831248892364803119651)
                ·
                  refine ⟨3005746873338547204679477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2003831248892364803119651 3005746873338547204679477)
                  ·
                    refine ⟨281788769375488800438701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3005746873338547204679477 281788769375488800438701)
                    ·
                      rfl

theorem cell23_1646345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 6, 1, 5].length) (baseStart_1646345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1646345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1646345 prefixEnd_1646345 := by exact prefixLift 1646345
  have htrace : WordTrace (prefixWord ++ tailWord_1646345) baseStart_1646345 baseEnd_1646345 := by
    simpa [prefixWord, tailWord_1646345, baseEnd_1646345] using wordTrace_append hprefix tailTrace_1646345
  have hstable : (prefixWord ++ tailWord_1646345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646345).length < 2 ^ (prefixWord ++ tailWord_1646345).sum := by decide
  have hdescent : baseEnd_1646345 < baseStart_1646345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1646362 : List Nat := [3, 1, 1, 3, 2, 3, 1, 3, 1, 5]
def baseStart_1646362 : Nat := 118140960795 + 1646362 * 2 ^ 59
def prefixEnd_1646362 : Nat := 4983230072969 + 3 ^ 40 * 1646362 * 2
def baseEnd_1646362 : Nat := 281791679099197611601175

theorem tailTrace_1646362 : CollatzResearch.WordTrace tailWord_1646362 prefixEnd_1646362 281791679099197611601175 := by
  unfold tailWord_1646362
  simp only [CollatzResearch.WordTrace]
  refine ⟨15011938815379781272281335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40031836841012750059416893 15011938815379781272281335)
  ·
    refine ⟨22517908223069671908422003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15011938815379781272281335 22517908223069671908422003)
    ·
      refine ⟨33776862334604507862633005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22517908223069671908422003 33776862334604507862633005)
      ·
        refine ⟨12666323375476690448487377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33776862334604507862633005 12666323375476690448487377)
        ·
          refine ⟨9499742531607517836365533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12666323375476690448487377 9499742531607517836365533)
          ·
            refine ⟨3562403449352819188637075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9499742531607517836365533 3562403449352819188637075)
            ·
              refine ⟨5343605174029228782955613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3562403449352819188637075 5343605174029228782955613)
              ·
                refine ⟨2003851940260960793608355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5343605174029228782955613 2003851940260960793608355)
                ·
                  refine ⟨3005777910391441190412533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2003851940260960793608355 3005777910391441190412533)
                  ·
                    refine ⟨281791679099197611601175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3005777910391441190412533 281791679099197611601175)
                    ·
                      rfl

theorem cell23_1646362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 3, 1, 5].length) (baseStart_1646362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1646362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1646362 prefixEnd_1646362 := by exact prefixLift 1646362
  have htrace : WordTrace (prefixWord ++ tailWord_1646362) baseStart_1646362 baseEnd_1646362 := by
    simpa [prefixWord, tailWord_1646362, baseEnd_1646362] using wordTrace_append hprefix tailTrace_1646362
  have hstable : (prefixWord ++ tailWord_1646362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646362).length < 2 ^ (prefixWord ++ tailWord_1646362).sum := by decide
  have hdescent : baseEnd_1646362 < baseStart_1646362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1646376 : List Nat := [2, 1, 5, 1, 1, 2, 2, 4, 1, 1, 3]
def baseStart_1646376 : Nat := 118140960795 + 1646376 * 2 ^ 59
def prefixEnd_1646376 : Nat := 4983230072969 + 3 ^ 40 * 1646376 * 2
def baseEnd_1646376 : Nat := 845382226026755780028461

theorem tailTrace_1646376 : CollatzResearch.WordTrace tailWord_1646376 prefixEnd_1646376 845382226026755780028461 := by
  unfold tailWord_1646376
  simp only [CollatzResearch.WordTrace]
  refine ⟨30024132941734202740067491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40032177255645603653423321 30024132941734202740067491)
  ·
    refine ⟨45036199412601304110101237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30024132941734202740067491 45036199412601304110101237)
    ·
      refine ⟨4222143694931372260321991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 45036199412601304110101237 4222143694931372260321991)
      ·
        refine ⟨6333215542397058390482987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4222143694931372260321991 6333215542397058390482987)
        ·
          refine ⟨9499823313595587585724481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6333215542397058390482987 9499823313595587585724481)
          ·
            refine ⟨7124867485196690689293361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9499823313595587585724481 7124867485196690689293361)
            ·
              refine ⟨5343650613897518016970021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7124867485196690689293361 5343650613897518016970021)
              ·
                refine ⟨1001934490105784628181879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5343650613897518016970021 1001934490105784628181879)
                ·
                  refine ⟨1502901735158676942272819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1001934490105784628181879 1502901735158676942272819)
                  ·
                    refine ⟨2254352602738015413409229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1502901735158676942272819 2254352602738015413409229)
                    ·
                      refine ⟨845382226026755780028461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2254352602738015413409229 845382226026755780028461)
                      ·
                        rfl

theorem cell23_1646376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 4, 1, 1, 3].length) (baseStart_1646376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1646376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1646376 prefixEnd_1646376 := by exact prefixLift 1646376
  have htrace : WordTrace (prefixWord ++ tailWord_1646376) baseStart_1646376 baseEnd_1646376 := by
    simpa [prefixWord, tailWord_1646376, baseEnd_1646376] using wordTrace_append hprefix tailTrace_1646376
  have hstable : (prefixWord ++ tailWord_1646376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646376).length < 2 ^ (prefixWord ++ tailWord_1646376).sum := by decide
  have hdescent : baseEnd_1646376 < baseStart_1646376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1646385 : List Nat := [1, 2, 2, 3, 2, 2, 1, 1, 3, 1, 5]
def baseStart_1646385 : Nat := 118140960795 + 1646385 * 2 ^ 59
def prefixEnd_1646385 : Nat := 4983230072969 + 3 ^ 40 * 1646385 * 2
def baseEnd_1646385 : Nat := 845386847352646244815919

theorem tailTrace_1646385 : CollatzResearch.WordTrace tailWord_1646385 prefixEnd_1646385 845386847352646244815919 := by
  unfold tailWord_1646385
  simp only [CollatzResearch.WordTrace]
  refine ⟨60048594140435800017212609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40032396093623866678141739 60048594140435800017212609)
  ·
    refine ⟨45036445605326850012909457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60048594140435800017212609 45036445605326850012909457)
    ·
      refine ⟨33777334203995137509682093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45036445605326850012909457 33777334203995137509682093)
      ·
        refine ⟨12666500326498176566130785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33777334203995137509682093 12666500326498176566130785)
        ·
          refine ⟨9499875244873632424598089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12666500326498176566130785 9499875244873632424598089)
          ·
            refine ⟨7124906433655224318448567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9499875244873632424598089 7124906433655224318448567)
            ·
              refine ⟨10687359650482836477672851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7124906433655224318448567 10687359650482836477672851)
              ·
                refine ⟨16031039475724254716509277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10687359650482836477672851 16031039475724254716509277)
                ·
                  refine ⟨6011639803396595518690979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16031039475724254716509277 6011639803396595518690979)
                  ·
                    refine ⟨9017459705094893278036469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6011639803396595518690979 9017459705094893278036469)
                    ·
                      refine ⟨845386847352646244815919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9017459705094893278036469 845386847352646244815919)
                      ·
                        rfl

theorem cell23_1646385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 1, 3, 1, 5].length) (baseStart_1646385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1646385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1646385 prefixEnd_1646385 := by exact prefixLift 1646385
  have htrace : WordTrace (prefixWord ++ tailWord_1646385) baseStart_1646385 baseEnd_1646385 := by
    simpa [prefixWord, tailWord_1646385, baseEnd_1646385] using wordTrace_append hprefix tailTrace_1646385
  have hstable : (prefixWord ++ tailWord_1646385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646385).length < 2 ^ (prefixWord ++ tailWord_1646385).sum := by decide
  have hdescent : baseEnd_1646385 < baseStart_1646385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1646392 : List Nat := [2, 1, 2, 1, 3, 5, 1, 1, 1, 6]
def baseStart_1646392 : Nat := 118140960795 + 1646392 * 2 ^ 59
def prefixEnd_1646392 : Nat := 4983230072969 + 3 ^ 40 * 1646392 * 2
def baseEnd_1646392 : Nat := 281796813905742572476129

theorem tailTrace_1646392 : CollatzResearch.WordTrace tailWord_1646392 prefixEnd_1646392 281796813905742572476129 := by
  unfold tailWord_1646392
  simp only [CollatzResearch.WordTrace]
  refine ⟨30024424725705220106358715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40032566300940293475144953 30024424725705220106358715)
  ·
    refine ⟨45036637088557830159538073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30024424725705220106358715 45036637088557830159538073)
    ·
      refine ⟨33777477816418372619653555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45036637088557830159538073 33777477816418372619653555)
      ·
        refine ⟨50666216724627558929480333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33777477816418372619653555 50666216724627558929480333)
        ·
          refine ⟨18999831271735334598555125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50666216724627558929480333 18999831271735334598555125)
          ·
            refine ⟨1781234181725187618614543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18999831271735334598555125 1781234181725187618614543)
            ·
              refine ⟨2671851272587781427921815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1781234181725187618614543 2671851272587781427921815)
              ·
                refine ⟨4007776908881672141882723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2671851272587781427921815 4007776908881672141882723)
                ·
                  refine ⟨6011665363322508212824085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4007776908881672141882723 6011665363322508212824085)
                  ·
                    refine ⟨281796813905742572476129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6011665363322508212824085 281796813905742572476129)
                    ·
                      rfl

theorem cell23_1646392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 1, 1, 1, 6].length) (baseStart_1646392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1646392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1646392 prefixEnd_1646392 := by exact prefixLift 1646392
  have htrace : WordTrace (prefixWord ++ tailWord_1646392) baseStart_1646392 baseEnd_1646392 := by
    simpa [prefixWord, tailWord_1646392, baseEnd_1646392] using wordTrace_append hprefix tailTrace_1646392
  have hstable : (prefixWord ++ tailWord_1646392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646392).length < 2 ^ (prefixWord ++ tailWord_1646392).sum := by decide
  have hdescent : baseEnd_1646392 < baseStart_1646392 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1646399 : List Nat := [1, 1, 2, 2, 6, 1, 2, 2, 1, 1, 4]
def baseStart_1646399 : Nat := 118140960795 + 1646399 * 2 ^ 59
def prefixEnd_1646399 : Nat := 4983230072969 + 3 ^ 40 * 1646399 * 2
def baseEnd_1646399 : Nat := 845394036081809190040855

theorem tailTrace_1646399 : CollatzResearch.WordTrace tailWord_1646399 prefixEnd_1646399 845394036081809190040855 := by
  unfold tailWord_1646399
  simp only [CollatzResearch.WordTrace]
  refine ⟨60049104762385080408222251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40032736508256720272148167 60049104762385080408222251)
  ·
    refine ⟨90073657143577620612333377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60049104762385080408222251 90073657143577620612333377)
    ·
      refine ⟨67555242857683215459250033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90073657143577620612333377 67555242857683215459250033)
      ·
        refine ⟨50666432143262411594437525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67555242857683215459250033 50666432143262411594437525)
        ·
          refine ⟨2374989006715425543489259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 50666432143262411594437525 2374989006715425543489259)
          ·
            refine ⟨3562483510073138315233889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2374989006715425543489259 3562483510073138315233889)
            ·
              refine ⟨2671862632554853736425417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3562483510073138315233889 2671862632554853736425417)
              ·
                refine ⟨2003896974416140302319063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2671862632554853736425417 2003896974416140302319063)
                ·
                  refine ⟨3005845461624210453478595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2003896974416140302319063 3005845461624210453478595)
                  ·
                    refine ⟨4508768192436315680217893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3005845461624210453478595 4508768192436315680217893)
                    ·
                      refine ⟨845394036081809190040855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4508768192436315680217893 845394036081809190040855)
                      ·
                        rfl

theorem cell23_1646399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 2, 2, 1, 1, 4].length) (baseStart_1646399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1646399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1646399 prefixEnd_1646399 := by exact prefixLift 1646399
  have htrace : WordTrace (prefixWord ++ tailWord_1646399) baseStart_1646399 baseEnd_1646399 := by
    simpa [prefixWord, tailWord_1646399, baseEnd_1646399] using wordTrace_append hprefix tailTrace_1646399
  have hstable : (prefixWord ++ tailWord_1646399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646399).length < 2 ^ (prefixWord ++ tailWord_1646399).sum := by decide
  have hdescent : baseEnd_1646399 < baseStart_1646399 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1646433 : List Nat := [1, 2, 3, 1, 1, 1, 7, 2, 1, 2, 2]
def baseStart_1646433 : Nat := 118140960795 + 1646433 * 2 ^ 59
def prefixEnd_1646433 : Nat := 4983230072969 + 3 ^ 40 * 1646433 * 2
def baseEnd_1646433 : Nat := 845411494424062057015699

theorem tailTrace_1646433 : CollatzResearch.WordTrace tailWord_1646433 prefixEnd_1646433 845411494424062057015699 := by
  unfold tailWord_1646433
  simp only [CollatzResearch.WordTrace]
  refine ⟨60050344844261904214959953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40033563229507936143306635 60050344844261904214959953)
  ·
    refine ⟨45037758633196428161219965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60050344844261904214959953 45037758633196428161219965)
    ·
      refine ⟨16889159487448660560457487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45037758633196428161219965 16889159487448660560457487)
      ·
        refine ⟨25333739231172990840686231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16889159487448660560457487 25333739231172990840686231)
        ·
          refine ⟨38000608846759486261029347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25333739231172990840686231 38000608846759486261029347)
          ·
            refine ⟨57000913270139229391544021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38000608846759486261029347 57000913270139229391544021)
            ·
              refine ⟨1335958904768888188864313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 57000913270139229391544021 1335958904768888188864313)
              ·
                refine ⟨1001969178576666141648235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1335958904768888188864313 1001969178576666141648235)
                ·
                  refine ⟨1502953767864999212472353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1001969178576666141648235 1502953767864999212472353)
                  ·
                    refine ⟨1127215325898749409354265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1502953767864999212472353 1127215325898749409354265)
                    ·
                      refine ⟨845411494424062057015699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1127215325898749409354265 845411494424062057015699)
                      ·
                        rfl

theorem cell23_1646433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 7, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 7, 2, 1, 2, 2].length) (baseStart_1646433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1646433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1646433 prefixEnd_1646433 := by exact prefixLift 1646433
  have htrace : WordTrace (prefixWord ++ tailWord_1646433) baseStart_1646433 baseEnd_1646433 := by
    simpa [prefixWord, tailWord_1646433, baseEnd_1646433] using wordTrace_append hprefix tailTrace_1646433
  have hstable : (prefixWord ++ tailWord_1646433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646433).length < 2 ^ (prefixWord ++ tailWord_1646433).sum := by decide
  have hdescent : baseEnd_1646433 < baseStart_1646433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1646449 : List Nat := [1, 2, 2, 2, 1, 3, 3, 3, 2, 1, 3]
def baseStart_1646449 : Nat := 118140960795 + 1646449 * 2 ^ 59
def prefixEnd_1646449 : Nat := 4983230072969 + 3 ^ 40 * 1646449 * 2
def baseEnd_1646449 : Nat := 845419710114533994415625

theorem tailTrace_1646449 : CollatzResearch.WordTrace tailWord_1646449 prefixEnd_1646449 845419710114533994415625 := by
  unfold tailWord_1646449
  simp only [CollatzResearch.WordTrace]
  refine ⟨60050928412203938947542401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40033952274802625965028267 60050928412203938947542401)
  ·
    refine ⟨45038196309152954210656801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60050928412203938947542401 45038196309152954210656801)
    ·
      refine ⟨33778647231864715657992601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45038196309152954210656801 33778647231864715657992601)
      ·
        refine ⟨25333985423898536743494451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33778647231864715657992601 25333985423898536743494451)
        ·
          refine ⟨38000978135847805115241677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25333985423898536743494451 38000978135847805115241677)
          ·
            refine ⟨14250366800942926918215629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38000978135847805115241677 14250366800942926918215629)
            ·
              refine ⟨5343887550353597594330861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14250366800942926918215629 5343887550353597594330861)
              ·
                refine ⟨2003957831382599097874073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5343887550353597594330861 2003957831382599097874073)
                ·
                  refine ⟨1502968373536949323405555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2003957831382599097874073 1502968373536949323405555)
                  ·
                    refine ⟨2254452560305423985108333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1502968373536949323405555 2254452560305423985108333)
                    ·
                      refine ⟨845419710114533994415625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2254452560305423985108333 845419710114533994415625)
                      ·
                        rfl

theorem cell23_1646449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 3, 2, 1, 3].length) (baseStart_1646449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1646449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1646449 prefixEnd_1646449 := by exact prefixLift 1646449
  have htrace : WordTrace (prefixWord ++ tailWord_1646449) baseStart_1646449 baseEnd_1646449 := by
    simpa [prefixWord, tailWord_1646449, baseEnd_1646449] using wordTrace_append hprefix tailTrace_1646449
  have hstable : (prefixWord ++ tailWord_1646449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646449).length < 2 ^ (prefixWord ++ tailWord_1646449).sum := by decide
  have hdescent : baseEnd_1646449 < baseStart_1646449 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1646489 : List Nat := [1, 2, 1, 2, 1, 3, 2, 3, 4, 2, 2]
def baseStart_1646489 : Nat := 118140960795 + 1646489 * 2 ^ 59
def prefixEnd_1646489 : Nat := 4983230072969 + 3 ^ 40 * 1646489 * 2
def baseEnd_1646489 : Nat := 845440249340713837915441

theorem tailTrace_1646489 : CollatzResearch.WordTrace tailWord_1646489 prefixEnd_1646489 845440249340713837915441 := by
  unfold tailWord_1646489
  simp only [CollatzResearch.WordTrace]
  refine ⟨60052387332059025778998521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40034924888039350519332347 60052387332059025778998521)
  ·
    refine ⟨45039290499044269334248891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60052387332059025778998521 45039290499044269334248891)
    ·
      refine ⟨67558935748566404001373337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45039290499044269334248891 67558935748566404001373337)
      ·
        refine ⟨50669201811424803001030003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67558935748566404001373337 50669201811424803001030003)
        ·
          refine ⟨76003802717137204501545005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50669201811424803001030003 76003802717137204501545005)
          ·
            refine ⟨28501426018926451688079377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76003802717137204501545005 28501426018926451688079377)
            ·
              refine ⟨21376069514194838766059533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28501426018926451688079377 21376069514194838766059533)
              ·
                refine ⟨8016026067823064537272325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21376069514194838766059533 8016026067823064537272325)
                ·
                  refine ⟨1503004887716824600738561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8016026067823064537272325 1503004887716824600738561)
                  ·
                    refine ⟨1127253665787618450553921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1503004887716824600738561 1127253665787618450553921)
                    ·
                      refine ⟨845440249340713837915441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1127253665787618450553921 845440249340713837915441)
                      ·
                        rfl

theorem cell23_1646489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 3, 4, 2, 2].length) (baseStart_1646489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1646489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1646489 prefixEnd_1646489 := by exact prefixLift 1646489
  have htrace : WordTrace (prefixWord ++ tailWord_1646489) baseStart_1646489 baseEnd_1646489 := by
    simpa [prefixWord, tailWord_1646489, baseEnd_1646489] using wordTrace_append hprefix tailTrace_1646489
  have hstable : (prefixWord ++ tailWord_1646489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646489).length < 2 ^ (prefixWord ++ tailWord_1646489).sum := by decide
  have hdescent : baseEnd_1646489 < baseStart_1646489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1646542 : List Nat := [4, 1, 1, 1, 2, 2, 2, 1, 4, 5]
def baseStart_1646542 : Nat := 118140960795 + 1646542 * 2 ^ 59
def prefixEnd_1646542 : Nat := 4983230072969 + 3 ^ 40 * 1646542 * 2
def baseEnd_1646542 : Nat := 281822487938467376850899

theorem tailTrace_1646542 : CollatzResearch.WordTrace tailWord_1646542 prefixEnd_1646542 281822487938467376850899 := by
  unfold tailWord_1646542
  simp only [CollatzResearch.WordTrace]
  refine ⟨7506790050108376978834735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40036213600578010553785253 7506790050108376978834735)
  ·
    refine ⟨11260185075162565468252103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7506790050108376978834735 11260185075162565468252103)
    ·
      refine ⟨16890277612743848202378155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11260185075162565468252103 16890277612743848202378155)
      ·
        refine ⟨25335416419115772303567233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16890277612743848202378155 25335416419115772303567233)
        ·
          refine ⟨19001562314336829227675425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25335416419115772303567233 19001562314336829227675425)
          ·
            refine ⟨14251171735752621920756569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19001562314336829227675425 14251171735752621920756569)
            ·
              refine ⟨10688378801814466440567427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14251171735752621920756569 10688378801814466440567427)
              ·
                refine ⟨16032568202721699660851141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10688378801814466440567427 16032568202721699660851141)
                ·
                  refine ⟨3006106538010318686409589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16032568202721699660851141 3006106538010318686409589)
                  ·
                    refine ⟨281822487938467376850899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3006106538010318686409589 281822487938467376850899)
                    ·
                      rfl

theorem cell23_1646542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 1, 4, 5].length) (baseStart_1646542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1646542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1646542 prefixEnd_1646542 := by exact prefixLift 1646542
  have htrace : WordTrace (prefixWord ++ tailWord_1646542) baseStart_1646542 baseEnd_1646542 := by
    simpa [prefixWord, tailWord_1646542, baseEnd_1646542] using wordTrace_append hprefix tailTrace_1646542
  have hstable : (prefixWord ++ tailWord_1646542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646542).length < 2 ^ (prefixWord ++ tailWord_1646542).sum := by decide
  have hdescent : baseEnd_1646542 < baseStart_1646542 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1646599 : List Nat := [1, 1, 4, 3, 1, 2, 1, 1, 4, 2, 3]
def baseStart_1646599 : Nat := 118140960795 + 1646599 * 2 ^ 59
def prefixEnd_1646599 : Nat := 4983230072969 + 3 ^ 40 * 1646599 * 2
def baseEnd_1646599 : Nat := 845496732212708407539935

theorem tailTrace_1646599 : CollatzResearch.WordTrace tailWord_1646599 prefixEnd_1646599 845496732212708407539935 := by
  unfold tailWord_1646599
  simp only [CollatzResearch.WordTrace]
  refine ⟨60056399361660514565502851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40037599574440343043668567 60056399361660514565502851)
  ·
    refine ⟨90084599042490771848254277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60056399361660514565502851 90084599042490771848254277)
    ·
      refine ⟨16890862320467019721547677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90084599042490771848254277 16890862320467019721547677)
      ·
        refine ⟨6334073370175132395580379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16890862320467019721547677 6334073370175132395580379)
        ·
          refine ⟨9501110055262698593370569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6334073370175132395580379 9501110055262698593370569)
          ·
            refine ⟨7125832541447023945027927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9501110055262698593370569 7125832541447023945027927)
            ·
              refine ⟨10688748812170535917541891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7125832541447023945027927 10688748812170535917541891)
              ·
                refine ⟨16033123218255803876312837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10688748812170535917541891 16033123218255803876312837)
                ·
                  refine ⟨3006210603422963226808657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16033123218255803876312837 3006210603422963226808657)
                  ·
                    refine ⟨2254657952567222420106493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3006210603422963226808657 2254657952567222420106493)
                    ·
                      refine ⟨845496732212708407539935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2254657952567222420106493 845496732212708407539935)
                      ·
                        rfl

theorem cell23_1646599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 1, 4, 2, 3].length) (baseStart_1646599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1646599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1646599 prefixEnd_1646599 := by exact prefixLift 1646599
  have htrace : WordTrace (prefixWord ++ tailWord_1646599) baseStart_1646599 baseEnd_1646599 := by
    simpa [prefixWord, tailWord_1646599, baseEnd_1646599] using wordTrace_append hprefix tailTrace_1646599
  have hstable : (prefixWord ++ tailWord_1646599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646599).length < 2 ^ (prefixWord ++ tailWord_1646599).sum := by decide
  have hdescent : baseEnd_1646599 < baseStart_1646599 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1646656 : List Nat := [2, 1, 1, 2, 2, 4, 2, 2, 2, 3, 2]
def baseStart_1646656 : Nat := 118140960795 + 1646656 * 2 ^ 59
def prefixEnd_1646656 : Nat := 4983230072969 + 3 ^ 40 * 1646656 * 2
def baseEnd_1646656 : Nat := 845526000610014684527173

theorem tailTrace_1646656 : CollatzResearch.WordTrace tailWord_1646656 prefixEnd_1646656 845526000610014684527173 := by
  unfold tailWord_1646656
  simp only [CollatzResearch.WordTrace]
  refine ⟨30029239161227006650163911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40038985548302675533551881 30029239161227006650163911)
  ·
    refine ⟨45043858741840509975245867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30029239161227006650163911 45043858741840509975245867)
    ·
      refine ⟨67565788112760764962868801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45043858741840509975245867 67565788112760764962868801)
      ·
        refine ⟨50674341084570573722151601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67565788112760764962868801 50674341084570573722151601)
        ·
          refine ⟨38005755813427930291613701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50674341084570573722151601 38005755813427930291613701)
          ·
            refine ⟨7126079215017736929677569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38005755813427930291613701 7126079215017736929677569)
            ·
              refine ⟨5344559411263302697258177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7126079215017736929677569 5344559411263302697258177)
              ·
                refine ⟨4008419558447477022943633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5344559411263302697258177 4008419558447477022943633)
                ·
                  refine ⟨3006314668835607767207725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4008419558447477022943633 3006314668835607767207725)
                  ·
                    refine ⟨1127368000813352912702897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3006314668835607767207725 1127368000813352912702897)
                    ·
                      refine ⟨845526000610014684527173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1127368000813352912702897 845526000610014684527173)
                      ·
                        rfl

theorem cell23_1646656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 2, 2, 3, 2].length) (baseStart_1646656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1646656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1646656 prefixEnd_1646656 := by exact prefixLift 1646656
  have htrace : WordTrace (prefixWord ++ tailWord_1646656) baseStart_1646656 baseEnd_1646656 := by
    simpa [prefixWord, tailWord_1646656, baseEnd_1646656] using wordTrace_append hprefix tailTrace_1646656
  have hstable : (prefixWord ++ tailWord_1646656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646656).length < 2 ^ (prefixWord ++ tailWord_1646656).sum := by decide
  have hdescent : baseEnd_1646656 < baseStart_1646656 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1646663 : List Nat := [1, 1, 4, 1, 3, 1, 3, 4, 1, 1, 3]
def baseStart_1646663 : Nat := 118140960795 + 1646663 * 2 ^ 59
def prefixEnd_1646663 : Nat := 4983230072969 + 3 ^ 40 * 1646663 * 2
def baseEnd_1646663 : Nat := 845529594974596157139641

theorem tailTrace_1646663 : CollatzResearch.WordTrace tailWord_1646663 prefixEnd_1646663 845529594974596157139641 := by
  unfold tailWord_1646663
  simp only [CollatzResearch.WordTrace]
  refine ⟨60058733633428653495832643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40039155755619102330555095 60058733633428653495832643)
  ·
    refine ⟨90088100450142980243748965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60058733633428653495832643 90088100450142980243748965)
    ·
      refine ⟨16891518834401808795702931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90088100450142980243748965 16891518834401808795702931)
      ·
        refine ⟨25337278251602713193554397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16891518834401808795702931 25337278251602713193554397)
        ·
          refine ⟨9501479344351017447582899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25337278251602713193554397 9501479344351017447582899)
          ·
            refine ⟨14252219016526526171374349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9501479344351017447582899 14252219016526526171374349)
            ·
              refine ⟨5344582131197447314265381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14252219016526526171374349 5344582131197447314265381)
              ·
                refine ⟨1002109149599521371424759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5344582131197447314265381 1002109149599521371424759)
                ·
                  refine ⟨1503163724399282057137139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1002109149599521371424759 1503163724399282057137139)
                  ·
                    refine ⟨2254745586598923085705709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1503163724399282057137139 2254745586598923085705709)
                    ·
                      refine ⟨845529594974596157139641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2254745586598923085705709 845529594974596157139641)
                      ·
                        rfl

theorem cell23_1646663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 4, 1, 1, 3].length) (baseStart_1646663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1646663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1646663 prefixEnd_1646663 := by exact prefixLift 1646663
  have htrace : WordTrace (prefixWord ++ tailWord_1646663) baseStart_1646663 baseEnd_1646663 := by
    simpa [prefixWord, tailWord_1646663, baseEnd_1646663] using wordTrace_append hprefix tailTrace_1646663
  have hstable : (prefixWord ++ tailWord_1646663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646663).length < 2 ^ (prefixWord ++ tailWord_1646663).sum := by decide
  have hdescent : baseEnd_1646663 < baseStart_1646663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1646692 : List Nat := [2, 3, 1, 1, 2, 1, 2, 11]
def baseStart_1646692 : Nat := 118140960795 + 1646692 * 2 ^ 59
def prefixEnd_1646692 : Nat := 4983230072969 + 3 ^ 40 * 1646692 * 2
def baseEnd_1646692 : Nat := 31316462441243575691741

theorem tailTrace_1646692 : CollatzResearch.WordTrace tailWord_1646692 prefixEnd_1646692 31316462441243575691741 := by
  unfold tailWord_1646692
  simp only [CollatzResearch.WordTrace]
  refine ⟨30029895675161795724319165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40039860900215727632425553 30029895675161795724319165)
  ·
    refine ⟨11261210878185673396619687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30029895675161795724319165 11261210878185673396619687)
    ·
      refine ⟨16891816317278510094929531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11261210878185673396619687 16891816317278510094929531)
      ·
        refine ⟨25337724475917765142394297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16891816317278510094929531 25337724475917765142394297)
        ·
          refine ⟨19003293356938323856795723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25337724475917765142394297 19003293356938323856795723)
          ·
            refine ⟨28504940035407485785193585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19003293356938323856795723 28504940035407485785193585)
            ·
              refine ⟨21378705026555614338895189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28504940035407485785193585 21378705026555614338895189)
              ·
                refine ⟨31316462441243575691741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 21378705026555614338895189 31316462441243575691741)
                ·
                  rfl

theorem cell23_1646692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 11].length) (baseStart_1646692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1646692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1646692 prefixEnd_1646692 := by exact prefixLift 1646692
  have htrace : WordTrace (prefixWord ++ tailWord_1646692) baseStart_1646692 baseEnd_1646692 := by
    simpa [prefixWord, tailWord_1646692, baseEnd_1646692] using wordTrace_append hprefix tailTrace_1646692
  have hstable : (prefixWord ++ tailWord_1646692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646692).length < 2 ^ (prefixWord ++ tailWord_1646692).sum := by decide
  have hdescent : baseEnd_1646692 < baseStart_1646692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1646703 : List Nat := [1, 1, 2, 1, 3, 6, 2, 1, 1, 1, 4]
def baseStart_1646703 : Nat := 118140960795 + 1646703 * 2 ^ 59
def prefixEnd_1646703 : Nat := 4983230072969 + 3 ^ 40 * 1646703 * 2
def baseEnd_1646703 : Nat := 845550134200776000639457

theorem tailTrace_1646703 : CollatzResearch.WordTrace tailWord_1646703 prefixEnd_1646703 845550134200776000639457 := by
  unfold tailWord_1646703
  simp only [CollatzResearch.WordTrace]
  refine ⟨60060192553283740327288763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40040128368855826884859175 60060192553283740327288763)
  ·
    refine ⟨90090288829925610490933145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60060192553283740327288763 90090288829925610490933145)
    ·
      refine ⟨67567716622444207868199859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90090288829925610490933145 67567716622444207868199859)
      ·
        refine ⟨101351574933666311802299789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67567716622444207868199859 101351574933666311802299789)
        ·
          refine ⟨38006840600124866925862421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101351574933666311802299789 38006840600124866925862421)
          ·
            refine ⟨1781570653130853137149801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 38006840600124866925862421 1781570653130853137149801)
            ·
              refine ⟨1336177989848139852862351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1781570653130853137149801 1336177989848139852862351)
              ·
                refine ⟨2004266984772209779293527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1336177989848139852862351 2004266984772209779293527)
                ·
                  refine ⟨3006400477158314668940291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2004266984772209779293527 3006400477158314668940291)
                  ·
                    refine ⟨4509600715737472003410437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3006400477158314668940291 4509600715737472003410437)
                    ·
                      refine ⟨845550134200776000639457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4509600715737472003410437 845550134200776000639457)
                      ·
                        rfl

theorem cell23_1646703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 2, 1, 1, 1, 4].length) (baseStart_1646703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1646703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1646703 prefixEnd_1646703 := by exact prefixLift 1646703
  have htrace : WordTrace (prefixWord ++ tailWord_1646703) baseStart_1646703 baseEnd_1646703 := by
    simpa [prefixWord, tailWord_1646703, baseEnd_1646703] using wordTrace_append hprefix tailTrace_1646703
  have hstable : (prefixWord ++ tailWord_1646703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646703).length < 2 ^ (prefixWord ++ tailWord_1646703).sum := by decide
  have hdescent : baseEnd_1646703 < baseStart_1646703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1646712 : List Nat := [2, 1, 2, 1, 1, 1, 3, 2, 2, 2, 6]
def baseStart_1646712 : Nat := 118140960795 + 1646712 * 2 ^ 59
def prefixEnd_1646712 : Nat := 4983230072969 + 3 ^ 40 * 1646712 * 2
def baseEnd_1646712 : Nat := 845554755526666465426915

theorem tailTrace_1646712 : CollatzResearch.WordTrace tailWord_1646712 prefixEnd_1646712 845554755526666465426915 := by
  unfold tailWord_1646712
  simp only [CollatzResearch.WordTrace]
  refine ⟨30030260405125567432183195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40040347206834089909577593 30030260405125567432183195)
  ·
    refine ⟨45045390607688351148274793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30030260405125567432183195 45045390607688351148274793)
    ·
      refine ⟨33784042955766263361206095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45045390607688351148274793 33784042955766263361206095)
      ·
        refine ⟨50676064433649395041809143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33784042955766263361206095 50676064433649395041809143)
        ·
          refine ⟨76014096650474092562713715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50676064433649395041809143 76014096650474092562713715)
          ·
            refine ⟨114021144975711138844070573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76014096650474092562713715 114021144975711138844070573)
            ·
              refine ⟨42757929365891677066526465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 114021144975711138844070573 42757929365891677066526465)
              ·
                refine ⟨32068447024418757799894849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42757929365891677066526465 32068447024418757799894849)
                ·
                  refine ⟨24051335268314068349921137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32068447024418757799894849 24051335268314068349921137)
                  ·
                    refine ⟨18038501451235551262440853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24051335268314068349921137 18038501451235551262440853)
                    ·
                      refine ⟨845554755526666465426915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18038501451235551262440853 845554755526666465426915)
                      ·
                        rfl

theorem cell23_1646712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 2, 2, 6].length) (baseStart_1646712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1646712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1646712 prefixEnd_1646712 := by exact prefixLift 1646712
  have htrace : WordTrace (prefixWord ++ tailWord_1646712) baseStart_1646712 baseEnd_1646712 := by
    simpa [prefixWord, tailWord_1646712, baseEnd_1646712] using wordTrace_append hprefix tailTrace_1646712
  have hstable : (prefixWord ++ tailWord_1646712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646712).length < 2 ^ (prefixWord ++ tailWord_1646712).sum := by decide
  have hdescent : baseEnd_1646712 < baseStart_1646712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1646713 : List Nat := [1, 2, 1, 3, 4, 3, 1, 2, 2, 4]
def baseStart_1646713 : Nat := 118140960795 + 1646713 * 2 ^ 59
def prefixEnd_1646713 : Nat := 4983230072969 + 3 ^ 40 * 1646713 * 2
def baseEnd_1646713 : Nat := 281851756335773653838137

theorem tailTrace_1646713 : CollatzResearch.WordTrace tailWord_1646713 prefixEnd_1646713 281851756335773653838137 := by
  unfold tailWord_1646713
  simp only [CollatzResearch.WordTrace]
  refine ⟨60060557283247512035152793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40040371522165008023435195 60060557283247512035152793)
  ·
    refine ⟨45045417962435634026364595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60060557283247512035152793 45045417962435634026364595)
    ·
      refine ⟨67568126943653451039546893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45045417962435634026364595 67568126943653451039546893)
      ·
        refine ⟨25338047603870044139830085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67568126943653451039546893 25338047603870044139830085)
        ·
          refine ⟨4750883925725633276218141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25338047603870044139830085 4750883925725633276218141)
          ·
            refine ⟨1781581472147112478581803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4750883925725633276218141 1781581472147112478581803)
            ·
              refine ⟨2672372208220668717872705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1781581472147112478581803 2672372208220668717872705)
              ·
                refine ⟨2004279156165501538404529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2672372208220668717872705 2004279156165501538404529)
                ·
                  refine ⟨1503209367124126153803397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2004279156165501538404529 1503209367124126153803397)
                  ·
                    refine ⟨281851756335773653838137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1503209367124126153803397 281851756335773653838137)
                    ·
                      rfl

theorem cell23_1646713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 1, 2, 2, 4].length) (baseStart_1646713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1646713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1646713 prefixEnd_1646713 := by exact prefixLift 1646713
  have htrace : WordTrace (prefixWord ++ tailWord_1646713) baseStart_1646713 baseEnd_1646713 := by
    simpa [prefixWord, tailWord_1646713, baseEnd_1646713] using wordTrace_append hprefix tailTrace_1646713
  have hstable : (prefixWord ++ tailWord_1646713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646713).length < 2 ^ (prefixWord ++ tailWord_1646713).sum := by decide
  have hdescent : baseEnd_1646713 < baseStart_1646713 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1646743 : List Nat := [1, 1, 3, 3, 5, 1, 2, 7]
def baseStart_1646743 : Nat := 118140960795 + 1646743 * 2 ^ 59
def prefixEnd_1646743 : Nat := 4983230072969 + 3 ^ 40 * 1646743 * 2
def baseEnd_1646743 : Nat := 31317432349146512745899

theorem tailTrace_1646743 : CollatzResearch.WordTrace tailWord_1646743 prefixEnd_1646743 31317432349146512745899 := by
  unfold tailWord_1646743
  simp only [CollatzResearch.WordTrace]
  refine ⟨60061651473138827158744883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40041100982092551439163255 60061651473138827158744883)
  ·
    refine ⟨90092477209708240738117325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60061651473138827158744883 90092477209708240738117325)
    ·
      refine ⟨33784678953640590276793997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90092477209708240738117325 33784678953640590276793997)
      ·
        refine ⟨12669254607615221353797749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33784678953640590276793997 12669254607615221353797749)
        ·
          refine ⟨1187742619463927001918539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12669254607615221353797749 1187742619463927001918539)
          ·
            refine ⟨1781613929195890502877809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1187742619463927001918539 1781613929195890502877809)
            ·
              refine ⟨1336210446896917877158357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1781613929195890502877809 1336210446896917877158357)
              ·
                refine ⟨31317432349146512745899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1336210446896917877158357 31317432349146512745899)
                ·
                  rfl

theorem cell23_1646743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 2, 7].length) (baseStart_1646743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1646743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1646743 prefixEnd_1646743 := by exact prefixLift 1646743
  have htrace : WordTrace (prefixWord ++ tailWord_1646743) baseStart_1646743 baseEnd_1646743 := by
    simpa [prefixWord, tailWord_1646743, baseEnd_1646743] using wordTrace_append hprefix tailTrace_1646743
  have hstable : (prefixWord ++ tailWord_1646743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646743).length < 2 ^ (prefixWord ++ tailWord_1646743).sum := by decide
  have hdescent : baseEnd_1646743 < baseStart_1646743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1646749 : List Nat := [1, 4, 2, 1, 1, 3, 1, 1, 2, 2, 5]
def baseStart_1646749 : Nat := 118140960795 + 1646749 * 2 ^ 59
def prefixEnd_1646749 : Nat := 4983230072969 + 3 ^ 40 * 1646749 * 2
def baseEnd_1646749 : Nat := 845573754310882820664245

theorem tailTrace_1646749 : CollatzResearch.WordTrace tailWord_1646749 prefixEnd_1646749 845573754310882820664245 := by
  unfold tailWord_1646749
  simp only [CollatzResearch.WordTrace]
  refine ⟨60061870311117090183463301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40041246874078060122308867 60061870311117090183463301)
  ·
    refine ⟨11261600683334454409399369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60061870311117090183463301 11261600683334454409399369)
    ·
      refine ⟨8446200512500840807049527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11261600683334454409399369 8446200512500840807049527)
      ·
        refine ⟨12669300768751261210574291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8446200512500840807049527 12669300768751261210574291)
        ·
          refine ⟨19003951153126891815861437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12669300768751261210574291 19003951153126891815861437)
          ·
            refine ⟨7126481682422584430948039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19003951153126891815861437 7126481682422584430948039)
            ·
              refine ⟨10689722523633876646422059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7126481682422584430948039 10689722523633876646422059)
              ·
                refine ⟨16034583785450814969633089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10689722523633876646422059 16034583785450814969633089)
                ·
                  refine ⟨12025937839088111227224817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16034583785450814969633089 12025937839088111227224817)
                  ·
                    refine ⟨9019453379316083420418613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12025937839088111227224817 9019453379316083420418613)
                    ·
                      refine ⟨845573754310882820664245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9019453379316083420418613 845573754310882820664245)
                      ·
                        rfl

theorem cell23_1646749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 1, 2, 2, 5].length) (baseStart_1646749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1646749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1646749 prefixEnd_1646749 := by exact prefixLift 1646749
  have htrace : WordTrace (prefixWord ++ tailWord_1646749) baseStart_1646749 baseEnd_1646749 := by
    simpa [prefixWord, tailWord_1646749, baseEnd_1646749] using wordTrace_append hprefix tailTrace_1646749
  have hstable : (prefixWord ++ tailWord_1646749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646749).length < 2 ^ (prefixWord ++ tailWord_1646749).sum := by decide
  have hdescent : baseEnd_1646749 < baseStart_1646749 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1646754 : List Nat := [3, 3, 1, 3, 1, 3, 1, 3, 1, 2, 2]
def baseStart_1646754 : Nat := 118140960795 + 1646754 * 2 ^ 59
def prefixEnd_1646754 : Nat := 4983230072969 + 3 ^ 40 * 1646754 * 2
def baseEnd_1646754 : Nat := 845576321714155301101723

theorem tailTrace_1646754 : CollatzResearch.WordTrace tailWord_1646754 prefixEnd_1646754 845576321714155301101723 := by
  unfold tailWord_1646754
  simp only [CollatzResearch.WordTrace]
  refine ⟨15015513169024744009348829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40041368450732650691596877 15015513169024744009348829)
  ·
    refine ⟨5630817438384279003505811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15015513169024744009348829 5630817438384279003505811)
    ·
      refine ⟨8446226157576418505258717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5630817438384279003505811 8446226157576418505258717)
      ·
        refine ⟨3167334809091156939472019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8446226157576418505258717 3167334809091156939472019)
        ·
          refine ⟨4751002213636735409208029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3167334809091156939472019 4751002213636735409208029)
          ·
            refine ⟨1781625830113775778453011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4751002213636735409208029 1781625830113775778453011)
            ·
              refine ⟨2672438745170663667679517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1781625830113775778453011 2672438745170663667679517)
              ·
                refine ⟨1002164529438998875379819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2672438745170663667679517 1002164529438998875379819)
                ·
                  refine ⟨1503246794158498313069729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1002164529438998875379819 1503246794158498313069729)
                  ·
                    refine ⟨1127435095618873734802297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1503246794158498313069729 1127435095618873734802297)
                    ·
                      refine ⟨845576321714155301101723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1127435095618873734802297 845576321714155301101723)
                      ·
                        rfl

theorem cell23_1646754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 1, 3, 1, 2, 2].length) (baseStart_1646754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1646754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1646754 prefixEnd_1646754 := by exact prefixLift 1646754
  have htrace : WordTrace (prefixWord ++ tailWord_1646754) baseStart_1646754 baseEnd_1646754 := by
    simpa [prefixWord, tailWord_1646754, baseEnd_1646754] using wordTrace_append hprefix tailTrace_1646754
  have hstable : (prefixWord ++ tailWord_1646754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646754).length < 2 ^ (prefixWord ++ tailWord_1646754).sum := by decide
  have hdescent : baseEnd_1646754 < baseStart_1646754 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1646779 : List Nat := [1, 1, 1, 1, 1, 2, 6, 1, 2, 4, 3]
def baseStart_1646779 : Nat := 118140960795 + 1646779 * 2 ^ 59
def prefixEnd_1646779 : Nat := 4983230072969 + 3 ^ 40 * 1646779 * 2
def baseEnd_1646779 : Nat := 845589158730517703289107

theorem tailTrace_1646779 : CollatzResearch.WordTrace tailWord_1646779 prefixEnd_1646779 845589158730517703289107 := by
  unfold tailWord_1646779
  simp only [CollatzResearch.WordTrace]
  refine ⟨60062964501008405307055391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40041976334005603538036927 60062964501008405307055391)
  ·
    refine ⟨90094446751512607960583087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60062964501008405307055391 90094446751512607960583087)
    ·
      refine ⟨135141670127268911940874631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90094446751512607960583087 135141670127268911940874631)
      ·
        refine ⟨202712505190903367911311947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135141670127268911940874631 202712505190903367911311947)
        ·
          refine ⟨304068757786355051866967921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202712505190903367911311947 304068757786355051866967921)
          ·
            refine ⟨228051568339766288900225941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 304068757786355051866967921 228051568339766288900225941)
            ·
              refine ⟨10689917265926544792198091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 228051568339766288900225941 10689917265926544792198091)
              ·
                refine ⟨16034875898889817188297137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10689917265926544792198091 16034875898889817188297137)
                ·
                  refine ⟨12026156924167362891222853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16034875898889817188297137 12026156924167362891222853)
                  ·
                    refine ⟨2254904423281380542104285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12026156924167362891222853 2254904423281380542104285)
                    ·
                      refine ⟨845589158730517703289107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2254904423281380542104285 845589158730517703289107)
                      ·
                        rfl

theorem cell23_1646779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 1, 2, 4, 3].length) (baseStart_1646779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1646779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1646779 prefixEnd_1646779 := by exact prefixLift 1646779
  have htrace : WordTrace (prefixWord ++ tailWord_1646779) baseStart_1646779 baseEnd_1646779 := by
    simpa [prefixWord, tailWord_1646779, baseEnd_1646779] using wordTrace_append hprefix tailTrace_1646779
  have hstable : (prefixWord ++ tailWord_1646779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646779).length < 2 ^ (prefixWord ++ tailWord_1646779).sum := by decide
  have hdescent : baseEnd_1646779 < baseStart_1646779 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1646789 : List Nat := [1, 3, 1, 1, 1, 1, 4, 3, 2, 2, 4]
def baseStart_1646789 : Nat := 118140960795 + 1646789 * 2 ^ 59
def prefixEnd_1646789 : Nat := 4983230072969 + 3 ^ 40 * 1646789 * 2
def baseEnd_1646789 : Nat := 845594293537062664164061

theorem tailTrace_1646789 : CollatzResearch.WordTrace tailWord_1646789 prefixEnd_1646789 845594293537062664164061 := by
  unfold tailWord_1646789
  simp only [CollatzResearch.WordTrace]
  refine ⟨60063329230972177014919421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40042219487314784676612947 60063329230972177014919421)
  ·
    refine ⟨22523748461614566380594783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60063329230972177014919421 22523748461614566380594783)
    ·
      refine ⟨33785622692421849570892175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22523748461614566380594783 33785622692421849570892175)
      ·
        refine ⟨50678434038632774356338263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33785622692421849570892175 50678434038632774356338263)
        ·
          refine ⟨76017651057949161534507395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50678434038632774356338263 76017651057949161534507395)
          ·
            refine ⟨114026476586923742301761093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76017651057949161534507395 114026476586923742301761093)
            ·
              refine ⟨21379964360048201681580205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 114026476586923742301761093 21379964360048201681580205)
              ·
                refine ⟨8017486635018075630592577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21379964360048201681580205 8017486635018075630592577)
                ·
                  refine ⟨6013114976263556722944433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8017486635018075630592577 6013114976263556722944433)
                  ·
                    refine ⟨4509836232197667542208325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6013114976263556722944433 4509836232197667542208325)
                    ·
                      refine ⟨845594293537062664164061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4509836232197667542208325 845594293537062664164061)
                      ·
                        rfl

theorem cell23_1646789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 3, 2, 2, 4].length) (baseStart_1646789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1646789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1646789 prefixEnd_1646789 := by exact prefixLift 1646789
  have htrace : WordTrace (prefixWord ++ tailWord_1646789) baseStart_1646789 baseEnd_1646789 := by
    simpa [prefixWord, tailWord_1646789, baseEnd_1646789] using wordTrace_append hprefix tailTrace_1646789
  have hstable : (prefixWord ++ tailWord_1646789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646789).length < 2 ^ (prefixWord ++ tailWord_1646789).sum := by decide
  have hdescent : baseEnd_1646789 < baseStart_1646789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1646816 : List Nat := [2, 1, 1, 3, 1, 3, 2, 5, 5]
def baseStart_1646816 : Nat := 118140960795 + 1646816 * 2 ^ 59
def prefixEnd_1646816 : Nat := 4983230072969 + 3 ^ 40 * 1646816 * 2
def baseEnd_1646816 : Nat := 93956461946081562058493

theorem tailTrace_1646816 : CollatzResearch.WordTrace tailWord_1646816 prefixEnd_1646816 93956461946081562058493 := by
  unfold tailWord_1646816
  simp only [CollatzResearch.WordTrace]
  refine ⟨30032157000937180313076151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40042876001249573750768201 30032157000937180313076151)
  ·
    refine ⟨45048235501405770469614227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30032157000937180313076151 45048235501405770469614227)
    ·
      refine ⟨67572353252108655704421341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45048235501405770469614227 67572353252108655704421341)
      ·
        refine ⟨25339632469540745889158003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67572353252108655704421341 25339632469540745889158003)
        ·
          refine ⟨38009448704311118833737005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25339632469540745889158003 38009448704311118833737005)
          ·
            refine ⟨14253543264116669562651377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38009448704311118833737005 14253543264116669562651377)
            ·
              refine ⟨10690157448087502171988533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14253543264116669562651377 10690157448087502171988533)
              ·
                refine ⟨1002202260758203328623925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10690157448087502171988533 1002202260758203328623925)
                ·
                  refine ⟨93956461946081562058493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1002202260758203328623925 93956461946081562058493)
                  ·
                    rfl

theorem cell23_1646816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 5, 5].length) (baseStart_1646816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1646816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1646816 prefixEnd_1646816 := by exact prefixLift 1646816
  have htrace : WordTrace (prefixWord ++ tailWord_1646816) baseStart_1646816 baseEnd_1646816 := by
    simpa [prefixWord, tailWord_1646816, baseEnd_1646816] using wordTrace_append hprefix tailTrace_1646816
  have hstable : (prefixWord ++ tailWord_1646816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646816).length < 2 ^ (prefixWord ++ tailWord_1646816).sum := by decide
  have hdescent : baseEnd_1646816 < baseStart_1646816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1646826 : List Nat := [3, 1, 3, 1, 1, 2, 2, 2, 2, 3, 3]
def baseStart_1646826 : Nat := 118140960795 + 1646826 * 2 ^ 59
def prefixEnd_1646826 : Nat := 4983230072969 + 3 ^ 40 * 1646826 * 2
def baseEnd_1646826 : Nat := 845613292321279019401391

theorem tailTrace_1646826 : CollatzResearch.WordTrace tailWord_1646826 prefixEnd_1646826 845613292321279019401391 := by
  unfold tailWord_1646826
  simp only [CollatzResearch.WordTrace]
  refine ⟨15016169682959533083504083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40043119154558754889344221 15016169682959533083504083)
  ·
    refine ⟨22524254524439299625256125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15016169682959533083504083 22524254524439299625256125)
    ·
      refine ⟨8446595446664737359471047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22524254524439299625256125 8446595446664737359471047)
      ·
        refine ⟨12669893169997106039206571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8446595446664737359471047 12669893169997106039206571)
        ·
          refine ⟨19004839754995659058809857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12669893169997106039206571 19004839754995659058809857)
          ·
            refine ⟨14253629816246744294107393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19004839754995659058809857 14253629816246744294107393)
            ·
              refine ⟨10690222362185058220580545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14253629816246744294107393 10690222362185058220580545)
              ·
                refine ⟨8017666771638793665435409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10690222362185058220580545 8017666771638793665435409)
                ·
                  refine ⟨6013250078729095249076557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8017666771638793665435409 6013250078729095249076557)
                  ·
                    refine ⟨2254968779523410718403709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6013250078729095249076557 2254968779523410718403709)
                    ·
                      refine ⟨845613292321279019401391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2254968779523410718403709 845613292321279019401391)
                      ·
                        rfl

theorem cell23_1646826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 2, 2, 3, 3].length) (baseStart_1646826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1646826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1646826 prefixEnd_1646826 := by exact prefixLift 1646826
  have htrace : WordTrace (prefixWord ++ tailWord_1646826) baseStart_1646826 baseEnd_1646826 := by
    simpa [prefixWord, tailWord_1646826, baseEnd_1646826] using wordTrace_append hprefix tailTrace_1646826
  have hstable : (prefixWord ++ tailWord_1646826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646826).length < 2 ^ (prefixWord ++ tailWord_1646826).sum := by decide
  have hdescent : baseEnd_1646826 < baseStart_1646826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1646833 : List Nat := [1, 2, 2, 2, 2, 1, 6, 2, 5]
def baseStart_1646833 : Nat := 118140960795 + 1646833 * 2 ^ 59
def prefixEnd_1646833 : Nat := 4983230072969 + 3 ^ 40 * 1646833 * 2
def baseEnd_1646833 : Nat := 93957431853984499112651

theorem tailTrace_1646833 : CollatzResearch.WordTrace tailWord_1646833 prefixEnd_1646833 93957431853984499112651 := by
  unfold tailWord_1646833
  simp only [CollatzResearch.WordTrace]
  refine ⟨60064934042812772529521153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40043289361875181686347435 60064934042812772529521153)
  ·
    refine ⟨45048700532109579397140865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60064934042812772529521153 45048700532109579397140865)
    ·
      refine ⟨33786525399082184547855649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45048700532109579397140865 33786525399082184547855649)
      ·
        refine ⟨25339894049311638410891737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33786525399082184547855649 25339894049311638410891737)
        ·
          refine ⟨19004920536983728808168803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25339894049311638410891737 19004920536983728808168803)
          ·
            refine ⟨28507380805475593212253205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19004920536983728808168803 28507380805475593212253205)
            ·
              refine ⟨1336283475256668431824369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 28507380805475593212253205 1336283475256668431824369)
              ·
                refine ⟨1002212606442501323868277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1336283475256668431824369 1002212606442501323868277)
                ·
                  refine ⟨93957431853984499112651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1002212606442501323868277 93957431853984499112651)
                  ·
                    rfl

theorem cell23_1646833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 6, 2, 5].length) (baseStart_1646833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1646833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1646833 prefixEnd_1646833 := by exact prefixLift 1646833
  have htrace : WordTrace (prefixWord ++ tailWord_1646833) baseStart_1646833 baseEnd_1646833 := by
    simpa [prefixWord, tailWord_1646833, baseEnd_1646833] using wordTrace_append hprefix tailTrace_1646833
  have hstable : (prefixWord ++ tailWord_1646833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646833).length < 2 ^ (prefixWord ++ tailWord_1646833).sum := by decide
  have hdescent : baseEnd_1646833 < baseStart_1646833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1646846 : List Nat := [4, 2, 2, 1, 1, 1, 2, 2, 1, 7]
def baseStart_1646846 : Nat := 118140960795 + 1646846 * 2 ^ 59
def prefixEnd_1646846 : Nat := 4983230072969 + 3 ^ 40 * 1646846 * 2
def baseEnd_1646846 : Nat := 281874520644789647050433

theorem tailTrace_1646846 : CollatzResearch.WordTrace tailWord_1646846 prefixEnd_1646846 281874520644789647050433 := by
  unfold tailWord_1646846
  simp only [CollatzResearch.WordTrace]
  refine ⟨7508176023970709468718049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40043605461177117166496261 7508176023970709468718049)
  ·
    refine ⟨5631132017978032101538537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7508176023970709468718049 5631132017978032101538537)
    ·
      refine ⟨4223349013483524076153903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5631132017978032101538537 4223349013483524076153903)
      ·
        refine ⟨6335023520225286114230855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4223349013483524076153903 6335023520225286114230855)
        ·
          refine ⟨9502535280337929171346283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6335023520225286114230855 9502535280337929171346283)
          ·
            refine ⟨14253802920506893757019425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9502535280337929171346283 14253802920506893757019425)
            ·
              refine ⟨10690352190380170317764569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14253802920506893757019425 10690352190380170317764569)
              ·
                refine ⟨8017764142785127738323427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10690352190380170317764569 8017764142785127738323427)
                ·
                  refine ⟨12026646214177691607485141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8017764142785127738323427 12026646214177691607485141)
                  ·
                    refine ⟨281874520644789647050433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12026646214177691607485141 281874520644789647050433)
                    ·
                      rfl

theorem cell23_1646846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 2, 1, 7].length) (baseStart_1646846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1646846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1646846 prefixEnd_1646846 := by exact prefixLift 1646846
  have htrace : WordTrace (prefixWord ++ tailWord_1646846) baseStart_1646846 baseEnd_1646846 := by
    simpa [prefixWord, tailWord_1646846, baseEnd_1646846] using wordTrace_append hprefix tailTrace_1646846
  have hstable : (prefixWord ++ tailWord_1646846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646846).length < 2 ^ (prefixWord ++ tailWord_1646846).sum := by decide
  have hdescent : baseEnd_1646846 < baseStart_1646846 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1646876 : List Nat := [2, 2, 3, 1, 1, 1, 1, 1, 7, 4]
def baseStart_1646876 : Nat := 118140960795 + 1646876 * 2 ^ 59
def prefixEnd_1646876 : Nat := 4983230072969 + 3 ^ 40 * 1646876 * 2
def baseEnd_1646876 : Nat := 281879655451334607925387

theorem tailTrace_1646876 : CollatzResearch.WordTrace tailWord_1646876 prefixEnd_1646876 281879655451334607925387 := by
  unfold tailWord_1646876
  simp only [CollatzResearch.WordTrace]
  refine ⟨30033251190828495436668241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40044334921104660582224321 30033251190828495436668241)
  ·
    refine ⟨22524938393121371577501181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30033251190828495436668241 22524938393121371577501181)
    ·
      refine ⟨8446851897420514341562943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22524938393121371577501181 8446851897420514341562943)
      ·
        refine ⟨12670277846130771512344415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8446851897420514341562943 12670277846130771512344415)
        ·
          refine ⟨19005416769196157268516623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12670277846130771512344415 19005416769196157268516623)
          ·
            refine ⟨28508125153794235902774935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19005416769196157268516623 28508125153794235902774935)
            ·
              refine ⟨42762187730691353854162403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28508125153794235902774935 42762187730691353854162403)
              ·
                refine ⟨64143281596037030781243605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42762187730691353854162403 64143281596037030781243605)
                ·
                  refine ⟨1503358162407117908935397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 64143281596037030781243605 1503358162407117908935397)
                  ·
                    refine ⟨281879655451334607925387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1503358162407117908935397 281879655451334607925387)
                    ·
                      rfl

theorem cell23_1646876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 7, 4].length) (baseStart_1646876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1646876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1646876 prefixEnd_1646876 := by exact prefixLift 1646876
  have htrace : WordTrace (prefixWord ++ tailWord_1646876) baseStart_1646876 baseEnd_1646876 := by
    simpa [prefixWord, tailWord_1646876, baseEnd_1646876] using wordTrace_append hprefix tailTrace_1646876
  have hstable : (prefixWord ++ tailWord_1646876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646876).length < 2 ^ (prefixWord ++ tailWord_1646876).sum := by decide
  have hdescent : baseEnd_1646876 < baseStart_1646876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1646900 : List Nat := [2, 5, 1, 1, 1, 2, 2, 1, 2, 4, 2]
def baseStart_1646900 : Nat := 118140960795 + 1646900 * 2 ^ 59
def prefixEnd_1646900 : Nat := 4983230072969 + 3 ^ 40 * 1646900 * 2
def baseEnd_1646900 : Nat := 845651289889711729876051

theorem tailTrace_1646900 : CollatzResearch.WordTrace tailWord_1646900 prefixEnd_1646900 845651289889711729876051 := by
  unfold tailWord_1646900
  simp only [CollatzResearch.WordTrace]
  refine ⟨30033688866785021486105077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40044918489046695314806769 30033688866785021486105077)
  ·
    refine ⟨2815658331261095764322351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30033688866785021486105077 2815658331261095764322351)
    ·
      refine ⟨4223487496891643646483527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2815658331261095764322351 4223487496891643646483527)
      ·
        refine ⟨6335231245337465469725291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4223487496891643646483527 6335231245337465469725291)
        ·
          refine ⟨9502846868006198204587937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6335231245337465469725291 9502846868006198204587937)
          ·
            refine ⟨7127135151004648653440953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9502846868006198204587937 7127135151004648653440953)
            ·
              refine ⟨5345351363253486490080715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7127135151004648653440953 5345351363253486490080715)
              ·
                refine ⟨8018027044880229735121073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5345351363253486490080715 8018027044880229735121073)
                ·
                  refine ⟨6013520283660172301340805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8018027044880229735121073 6013520283660172301340805)
                  ·
                    refine ⟨1127535053186282306501401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6013520283660172301340805 1127535053186282306501401)
                    ·
                      refine ⟨845651289889711729876051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1127535053186282306501401 845651289889711729876051)
                      ·
                        rfl

theorem cell23_1646900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 1, 2, 4, 2].length) (baseStart_1646900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1646900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1646900 prefixEnd_1646900 := by exact prefixLift 1646900
  have htrace : WordTrace (prefixWord ++ tailWord_1646900) baseStart_1646900 baseEnd_1646900 := by
    simpa [prefixWord, tailWord_1646900, baseEnd_1646900] using wordTrace_append hprefix tailTrace_1646900
  have hstable : (prefixWord ++ tailWord_1646900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646900).length < 2 ^ (prefixWord ++ tailWord_1646900).sum := by decide
  have hdescent : baseEnd_1646900 < baseStart_1646900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1646943 : List Nat := [1, 1, 2, 3, 1, 2, 3, 1, 4, 3, 2]
def baseStart_1646943 : Nat := 118140960795 + 1646943 * 2 ^ 59
def prefixEnd_1646943 : Nat := 4983230072969 + 3 ^ 40 * 1646943 * 2
def baseEnd_1646943 : Nat := 845673369557855061638353

theorem tailTrace_1646943 : CollatzResearch.WordTrace tailWord_1646943 prefixEnd_1646943 845673369557855061638353 := by
  unfold tailWord_1646943
  simp only [CollatzResearch.WordTrace]
  refine ⟨60068946072414261316025483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40045964048276174210683655 60068946072414261316025483)
  ·
    refine ⟨90103419108621391974038225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60068946072414261316025483 90103419108621391974038225)
    ·
      refine ⟨67577564331466043980528669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90103419108621391974038225 67577564331466043980528669)
      ·
        refine ⟨25341586624299766492698251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67577564331466043980528669 25341586624299766492698251)
        ·
          refine ⟨38012379936449649739047377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25341586624299766492698251 38012379936449649739047377)
          ·
            refine ⟨28509284952337237304285533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38012379936449649739047377 28509284952337237304285533)
            ·
              refine ⟨10690981857126463989107075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28509284952337237304285533 10690981857126463989107075)
              ·
                refine ⟨16036472785689695983660613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10690981857126463989107075 16036472785689695983660613)
                ·
                  refine ⟨3006838647316817996936365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16036472785689695983660613 3006838647316817996936365)
                  ·
                    refine ⟨1127564492743806748851137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3006838647316817996936365 1127564492743806748851137)
                    ·
                      refine ⟨845673369557855061638353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1127564492743806748851137 845673369557855061638353)
                      ·
                        rfl

theorem cell23_1646943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 1, 4, 3, 2].length) (baseStart_1646943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1646943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1646943 prefixEnd_1646943 := by exact prefixLift 1646943
  have htrace : WordTrace (prefixWord ++ tailWord_1646943) baseStart_1646943 baseEnd_1646943 := by
    simpa [prefixWord, tailWord_1646943, baseEnd_1646943] using wordTrace_append hprefix tailTrace_1646943
  have hstable : (prefixWord ++ tailWord_1646943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646943).length < 2 ^ (prefixWord ++ tailWord_1646943).sum := by decide
  have hdescent : baseEnd_1646943 < baseStart_1646943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1646973 : List Nat := [1, 4, 1, 1, 2, 4, 1, 1, 3, 1, 4]
def baseStart_1646973 : Nat := 118140960795 + 1646973 * 2 ^ 59
def prefixEnd_1646973 : Nat := 4983230072969 + 3 ^ 40 * 1646973 * 2
def baseEnd_1646973 : Nat := 845688773977489944263215

theorem tailTrace_1646973 : CollatzResearch.WordTrace tailWord_1646973 prefixEnd_1646973 845688773977489944263215 := by
  unfold tailWord_1646973
  simp only [CollatzResearch.WordTrace]
  refine ⟨60070040262305576439617573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40046693508203717626411715 60070040262305576439617573)
  ·
    refine ⟨11263132549182295582428295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60070040262305576439617573 11263132549182295582428295)
    ·
      refine ⟨16894698823773443373642443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11263132549182295582428295 16894698823773443373642443)
      ·
        refine ⟨25342048235660165060463665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16894698823773443373642443 25342048235660165060463665)
        ·
          refine ⟨19006536176745123795347749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25342048235660165060463665 19006536176745123795347749)
          ·
            refine ⟨3563725533139710711627703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19006536176745123795347749 3563725533139710711627703)
            ·
              refine ⟨5345588299709566067441555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3563725533139710711627703 5345588299709566067441555)
              ·
                refine ⟨8018382449564349101162333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5345588299709566067441555 8018382449564349101162333)
                ·
                  refine ⟨3006893418586630912935875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8018382449564349101162333 3006893418586630912935875)
                  ·
                    refine ⟨4510340127879946369403813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3006893418586630912935875 4510340127879946369403813)
                    ·
                      refine ⟨845688773977489944263215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4510340127879946369403813 845688773977489944263215)
                      ·
                        rfl

theorem cell23_1646973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 1, 3, 1, 4].length) (baseStart_1646973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1646973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1646973 prefixEnd_1646973 := by exact prefixLift 1646973
  have htrace : WordTrace (prefixWord ++ tailWord_1646973) baseStart_1646973 baseEnd_1646973 := by
    simpa [prefixWord, tailWord_1646973, baseEnd_1646973] using wordTrace_append hprefix tailTrace_1646973
  have hstable : (prefixWord ++ tailWord_1646973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646973).length < 2 ^ (prefixWord ++ tailWord_1646973).sum := by decide
  have hdescent : baseEnd_1646973 < baseStart_1646973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1646977 : List Nat := [1, 2, 4, 3, 1, 2, 2, 1, 2, 3, 2]
def baseStart_1646977 : Nat := 118140960795 + 1646977 * 2 ^ 59
def prefixEnd_1646977 : Nat := 4983230072969 + 3 ^ 40 * 1646977 * 2
def baseEnd_1646977 : Nat := 845690827900107928613197

theorem tailTrace_1646977 : CollatzResearch.WordTrace tailWord_1646977 prefixEnd_1646977 845690827900107928613197 := by
  unfold tailWord_1646977
  simp only [CollatzResearch.WordTrace]
  refine ⟨60070186154291085122763185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40046790769527390081842123 60070186154291085122763185)
  ·
    refine ⟨45052639615718313842072389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60070186154291085122763185 45052639615718313842072389)
    ·
      refine ⟨8447369927947183845388573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45052639615718313842072389 8447369927947183845388573)
      ·
        refine ⟨3167763722980193942020715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8447369927947183845388573 3167763722980193942020715)
        ·
          refine ⟨4751645584470290913031073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3167763722980193942020715 4751645584470290913031073)
          ·
            refine ⟨3563734188352718184773305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4751645584470290913031073 3563734188352718184773305)
            ·
              refine ⟨2672800641264538638579979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3563734188352718184773305 2672800641264538638579979)
              ·
                refine ⟨4009200961896807957869969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2672800641264538638579979 4009200961896807957869969)
                ·
                  refine ⟨3006900721422605968402477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4009200961896807957869969 3006900721422605968402477)
                  ·
                    refine ⟨1127587770533477238150929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3006900721422605968402477 1127587770533477238150929)
                    ·
                      refine ⟨845690827900107928613197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1127587770533477238150929 845690827900107928613197)
                      ·
                        rfl

theorem cell23_1646977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 2, 1, 2, 3, 2].length) (baseStart_1646977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1646977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1646977 prefixEnd_1646977 := by exact prefixLift 1646977
  have htrace : WordTrace (prefixWord ++ tailWord_1646977) baseStart_1646977 baseEnd_1646977 := by
    simpa [prefixWord, tailWord_1646977, baseEnd_1646977] using wordTrace_append hprefix tailTrace_1646977
  have hstable : (prefixWord ++ tailWord_1646977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646977).length < 2 ^ (prefixWord ++ tailWord_1646977).sum := by decide
  have hdescent : baseEnd_1646977 < baseStart_1646977 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1646996 : List Nat := [2, 4, 2, 1, 14]
def baseStart_1646996 : Nat := 118140960795 + 1646996 * 2 ^ 59
def prefixEnd_1646996 : Nat := 4983230072969 + 3 ^ 40 * 1646996 * 2
def baseEnd_1646996 : Nat := 1160083105668783750721

theorem tailTrace_1646996 : CollatzResearch.WordTrace tailWord_1646996 prefixEnd_1646996 1160083105668783750721 := by
  unfold tailWord_1646996
  simp only [CollatzResearch.WordTrace]
  refine ⟨30035439570611125683852421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40047252760814834245136561 30035439570611125683852421)
  ·
    refine ⟨5631644919489586065722329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30035439570611125683852421 5631644919489586065722329)
    ·
      refine ⟨4223733689617189549291747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5631644919489586065722329 4223733689617189549291747)
      ·
        refine ⟨6335600534425784323937621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4223733689617189549291747 6335600534425784323937621)
        ·
          refine ⟨1160083105668783750721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 6335600534425784323937621 1160083105668783750721)
          ·
            rfl

theorem cell23_1646996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 14].length) (baseStart_1646996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1646996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1646996 prefixEnd_1646996 := by exact prefixLift 1646996
  have htrace : WordTrace (prefixWord ++ tailWord_1646996) baseStart_1646996 baseEnd_1646996 := by
    simpa [prefixWord, tailWord_1646996, baseEnd_1646996] using wordTrace_append hprefix tailTrace_1646996
  have hstable : (prefixWord ++ tailWord_1646996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1646996).length < 2 ^ (prefixWord ++ tailWord_1646996).sum := by decide
  have hdescent : baseEnd_1646996 < baseStart_1646996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1646996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647000 : List Nat := [2, 1, 2, 5, 1, 1, 1, 4, 2, 4]
def baseStart_1647000 : Nat := 118140960795 + 1647000 * 2 ^ 59
def prefixEnd_1647000 : Nat := 4983230072969 + 3 ^ 40 * 1647000 * 2
def baseEnd_1647000 : Nat := 281900879318387112875197

theorem tailTrace_1647000 : CollatzResearch.WordTrace tailWord_1647000 prefixEnd_1647000 281900879318387112875197 := by
  unfold tailWord_1647000
  simp only [CollatzResearch.WordTrace]
  refine ⟨30035512516603880025425227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40047350022138506700566969 30035512516603880025425227)
  ·
    refine ⟨45053268774905820038137841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30035512516603880025425227 45053268774905820038137841)
    ·
      refine ⟨33789951581179365028603381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45053268774905820038137841 33789951581179365028603381)
      ·
        refine ⟨3167807960735565471431567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33789951581179365028603381 3167807960735565471431567)
        ·
          refine ⟨4751711941103348207147351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3167807960735565471431567 4751711941103348207147351)
          ·
            refine ⟨7127567911655022310721027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4751711941103348207147351 7127567911655022310721027)
            ·
              refine ⟨10691351867482533466081541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7127567911655022310721027 10691351867482533466081541)
              ·
                refine ⟨2004628475152975024890289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10691351867482533466081541 2004628475152975024890289)
                ·
                  refine ⟨1503471356364731268667717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2004628475152975024890289 1503471356364731268667717)
                  ·
                    refine ⟨281900879318387112875197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1503471356364731268667717 281900879318387112875197)
                    ·
                      rfl

theorem cell23_1647000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 4, 2, 4].length) (baseStart_1647000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1647000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1647000 prefixEnd_1647000 := by exact prefixLift 1647000
  have htrace : WordTrace (prefixWord ++ tailWord_1647000) baseStart_1647000 baseEnd_1647000 := by
    simpa [prefixWord, tailWord_1647000, baseEnd_1647000] using wordTrace_append hprefix tailTrace_1647000
  have hstable : (prefixWord ++ tailWord_1647000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647000).length < 2 ^ (prefixWord ++ tailWord_1647000).sum := by decide
  have hdescent : baseEnd_1647000 < baseStart_1647000 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647023 : List Nat := [1, 1, 2, 1, 2, 2, 1, 1, 8, 1, 3]
def baseStart_1647023 : Nat := 118140960795 + 1647023 * 2 ^ 59
def prefixEnd_1647023 : Nat := 4983230072969 + 3 ^ 40 * 1647023 * 2
def baseEnd_1647023 : Nat := 845714448010214748637985

theorem tailTrace_1647023 : CollatzResearch.WordTrace tailWord_1647023 prefixEnd_1647023 845714448010214748637985 := by
  unfold tailWord_1647023
  simp only [CollatzResearch.WordTrace]
  refine ⟨60071863912124434978937723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40047909274749623319291815 60071863912124434978937723)
  ·
    refine ⟨90107795868186652468406585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60071863912124434978937723 90107795868186652468406585)
    ·
      refine ⟨67580846901139989351304939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90107795868186652468406585 67580846901139989351304939)
      ·
        refine ⟨101371270351709984026957409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67580846901139989351304939 101371270351709984026957409)
        ·
          refine ⟨76028452763782488020218057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101371270351709984026957409 76028452763782488020218057)
          ·
            refine ⟨57021339572836866015163543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76028452763782488020218057 57021339572836866015163543)
            ·
              refine ⟨85532009359255299022745315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57021339572836866015163543 85532009359255299022745315)
              ·
                refine ⟨128298014038882948534117973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85532009359255299022745315 128298014038882948534117973)
                ·
                  refine ⟨1503492352018159553134195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 128298014038882948534117973 1503492352018159553134195)
                  ·
                    refine ⟨2255238528027239329701293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1503492352018159553134195 2255238528027239329701293)
                    ·
                      refine ⟨845714448010214748637985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2255238528027239329701293 845714448010214748637985)
                      ·
                        rfl

theorem cell23_1647023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 8, 1, 3].length) (baseStart_1647023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1647023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1647023 prefixEnd_1647023 := by exact prefixLift 1647023
  have htrace : WordTrace (prefixWord ++ tailWord_1647023) baseStart_1647023 baseEnd_1647023 := by
    simpa [prefixWord, tailWord_1647023, baseEnd_1647023] using wordTrace_append hprefix tailTrace_1647023
  have hstable : (prefixWord ++ tailWord_1647023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647023).length < 2 ^ (prefixWord ++ tailWord_1647023).sum := by decide
  have hdescent : baseEnd_1647023 < baseStart_1647023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647026 : List Nat := [3, 2, 1, 1, 1, 1, 3, 2, 2, 7]
def baseStart_1647026 : Nat := 118140960795 + 1647026 * 2 ^ 59
def prefixEnd_1647026 : Nat := 4983230072969 + 3 ^ 40 * 1647026 * 2
def baseEnd_1647026 : Nat := 281905329484059412300157

theorem tailTrace_1647026 : CollatzResearch.WordTrace tailWord_1647026 prefixEnd_1647026 281905329484059412300157 := by
  unfold tailWord_1647026
  simp only [CollatzResearch.WordTrace]
  refine ⟨15017993332778391622824233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40047982220742377660864621 15017993332778391622824233)
  ·
    refine ⟨11263494999583793717118175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15017993332778391622824233 11263494999583793717118175)
    ·
      refine ⟨16895242499375690575677263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11263494999583793717118175 16895242499375690575677263)
      ·
        refine ⟨25342863749063535863515895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16895242499375690575677263 25342863749063535863515895)
        ·
          refine ⟨38014295623595303795273843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25342863749063535863515895 38014295623595303795273843)
          ·
            refine ⟨57021443435392955692910765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38014295623595303795273843 57021443435392955692910765)
            ·
              refine ⟨21383041288272358384841537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57021443435392955692910765 21383041288272358384841537)
              ·
                refine ⟨16037280966204268788631153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21383041288272358384841537 16037280966204268788631153)
                ·
                  refine ⟨12027960724653201591473365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16037280966204268788631153 12027960724653201591473365)
                  ·
                    refine ⟨281905329484059412300157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12027960724653201591473365 281905329484059412300157)
                    ·
                      rfl

theorem cell23_1647026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 2, 2, 7].length) (baseStart_1647026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1647026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1647026 prefixEnd_1647026 := by exact prefixLift 1647026
  have htrace : WordTrace (prefixWord ++ tailWord_1647026) baseStart_1647026 baseEnd_1647026 := by
    simpa [prefixWord, tailWord_1647026, baseEnd_1647026] using wordTrace_append hprefix tailTrace_1647026
  have hstable : (prefixWord ++ tailWord_1647026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647026).length < 2 ^ (prefixWord ++ tailWord_1647026).sum := by decide
  have hdescent : baseEnd_1647026 < baseStart_1647026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647028 : List Nat := [2, 5, 2, 2, 2, 1, 1, 1, 2, 3, 2]
def baseStart_1647028 : Nat := 118140960795 + 1647028 * 2 ^ 59
def prefixEnd_1647028 : Nat := 4983230072969 + 3 ^ 40 * 1647028 * 2
def baseEnd_1647028 : Nat := 845717015413487229075463

theorem tailTrace_1647028 : CollatzResearch.WordTrace tailWord_1647028 prefixEnd_1647028 845717015413487229075463 := by
  unfold tailWord_1647028
  simp only [CollatzResearch.WordTrace]
  refine ⟨30036023138553160416434869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40048030851404213888579825 30036023138553160416434869)
  ·
    refine ⟨2815877169239358789040769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30036023138553160416434869 2815877169239358789040769)
    ·
      refine ⟨2111907876929519091780577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2815877169239358789040769 2111907876929519091780577)
      ·
        refine ⟨1583930907697139318835433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2111907876929519091780577 1583930907697139318835433)
        ·
          refine ⟨1187948180772854489126575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1583930907697139318835433 1187948180772854489126575)
          ·
            refine ⟨1781922271159281733689863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1187948180772854489126575 1781922271159281733689863)
            ·
              refine ⟨2672883406738922600534795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1781922271159281733689863 2672883406738922600534795)
              ·
                refine ⟨4009325110108383900802193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2672883406738922600534795 4009325110108383900802193)
                ·
                  refine ⟨3006993832581287925601645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4009325110108383900802193 3006993832581287925601645)
                  ·
                    refine ⟨1127622687217982972100617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3006993832581287925601645 1127622687217982972100617)
                    ·
                      refine ⟨845717015413487229075463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1127622687217982972100617 845717015413487229075463)
                      ·
                        rfl

theorem cell23_1647028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_1647028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1647028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1647028 prefixEnd_1647028 := by exact prefixLift 1647028
  have htrace : WordTrace (prefixWord ++ tailWord_1647028) baseStart_1647028 baseEnd_1647028 := by
    simpa [prefixWord, tailWord_1647028, baseEnd_1647028] using wordTrace_append hprefix tailTrace_1647028
  have hstable : (prefixWord ++ tailWord_1647028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647028).length < 2 ^ (prefixWord ++ tailWord_1647028).sum := by decide
  have hdescent : baseEnd_1647028 < baseStart_1647028 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647063 : List Nat := [1, 1, 3, 2, 1, 1, 1, 1, 2, 8, 2]
def baseStart_1647063 : Nat := 118140960795 + 1647063 * 2 ^ 59
def prefixEnd_1647063 : Nat := 4983230072969 + 3 ^ 40 * 1647063 * 2
def baseEnd_1647063 : Nat := 845734987236394592137801

theorem tailTrace_1647063 : CollatzResearch.WordTrace tailWord_1647063 prefixEnd_1647063 845734987236394592137801 := by
  unfold tailWord_1647063
  simp only [CollatzResearch.WordTrace]
  refine ⟨60073322831979521810393843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40048881887986347873595895 60073322831979521810393843)
  ·
    refine ⟨90109984247969282715590765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60073322831979521810393843 90109984247969282715590765)
    ·
      refine ⟨33791244092988481018346537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90109984247969282715590765 33791244092988481018346537)
      ·
        refine ⟨25343433069741360763759903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33791244092988481018346537 25343433069741360763759903)
        ·
          refine ⟨38015149604612041145639855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25343433069741360763759903 38015149604612041145639855)
          ·
            refine ⟨57022724406918061718459783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38015149604612041145639855 57022724406918061718459783)
            ·
              refine ⟨85534086610377092577689675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57022724406918061718459783 85534086610377092577689675)
              ·
                refine ⟨128301129915565638866534513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85534086610377092577689675 128301129915565638866534513)
                ·
                  refine ⟨96225847436674229149900885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 128301129915565638866534513 96225847436674229149900885)
                  ·
                    refine ⟨1127646649648526122850401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 96225847436674229149900885 1127646649648526122850401)
                    ·
                      refine ⟨845734987236394592137801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1127646649648526122850401 845734987236394592137801)
                      ·
                        rfl

theorem cell23_1647063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 8, 2].length) (baseStart_1647063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1647063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1647063 prefixEnd_1647063 := by exact prefixLift 1647063
  have htrace : WordTrace (prefixWord ++ tailWord_1647063) baseStart_1647063 baseEnd_1647063 := by
    simpa [prefixWord, tailWord_1647063, baseEnd_1647063] using wordTrace_append hprefix tailTrace_1647063
  have hstable : (prefixWord ++ tailWord_1647063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647063).length < 2 ^ (prefixWord ++ tailWord_1647063).sum := by decide
  have hdescent : baseEnd_1647063 < baseStart_1647063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647113 : List Nat := [1, 2, 1, 1, 3, 1, 2, 4, 2, 3, 3]
def baseStart_1647113 : Nat := 118140960795 + 1647113 * 2 ^ 59
def prefixEnd_1647113 : Nat := 4983230072969 + 3 ^ 40 * 1647113 * 2
def baseEnd_1647113 : Nat := 845760661269119396512571

theorem tailTrace_1647113 : CollatzResearch.WordTrace tailWord_1647113 prefixEnd_1647113 845760661269119396512571 := by
  unfold tailWord_1647113
  simp only [CollatzResearch.WordTrace]
  refine ⟨60075146481798380349713993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40050097654532253566475995 60075146481798380349713993)
  ·
    refine ⟨45056359861348785262285495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60075146481798380349713993 45056359861348785262285495)
    ·
      refine ⟨67584539792023177893428243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45056359861348785262285495 67584539792023177893428243)
      ·
        refine ⟨101376809688034766840142365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67584539792023177893428243 101376809688034766840142365)
        ·
          refine ⟨38016303633013037565053387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101376809688034766840142365 38016303633013037565053387)
          ·
            refine ⟨57024455449519556347580081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38016303633013037565053387 57024455449519556347580081)
            ·
              refine ⟨42768341587139667260685061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57024455449519556347580081 42768341587139667260685061)
              ·
                refine ⟨8019064047588687611378449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42768341587139667260685061 8019064047588687611378449)
                ·
                  refine ⟨6014298035691515708533837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8019064047588687611378449 6014298035691515708533837)
                  ·
                    refine ⟨2255361763384318390700189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6014298035691515708533837 2255361763384318390700189)
                    ·
                      refine ⟨845760661269119396512571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2255361763384318390700189 845760661269119396512571)
                      ·
                        rfl

theorem cell23_1647113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 4, 2, 3, 3].length) (baseStart_1647113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1647113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1647113 prefixEnd_1647113 := by exact prefixLift 1647113
  have htrace : WordTrace (prefixWord ++ tailWord_1647113) baseStart_1647113 baseEnd_1647113 := by
    simpa [prefixWord, tailWord_1647113, baseEnd_1647113] using wordTrace_append hprefix tailTrace_1647113
  have hstable : (prefixWord ++ tailWord_1647113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647113).length < 2 ^ (prefixWord ++ tailWord_1647113).sum := by decide
  have hdescent : baseEnd_1647113 < baseStart_1647113 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647153 : List Nat := [1, 2, 2, 3, 1, 1, 2, 3, 1, 3, 4]
def baseStart_1647153 : Nat := 118140960795 + 1647153 * 2 ^ 59
def prefixEnd_1647153 : Nat := 4983230072969 + 3 ^ 40 * 1647153 * 2
def baseEnd_1647153 : Nat := 845781200495299240012387

theorem tailTrace_1647153 : CollatzResearch.WordTrace tailWord_1647153 prefixEnd_1647153 845781200495299240012387 := by
  unfold tailWord_1647153
  simp only [CollatzResearch.WordTrace]
  refine ⟨60076605401653467181170113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40051070267768978120780075 60076605401653467181170113)
  ·
    refine ⟨45057454051240100385877585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60076605401653467181170113 45057454051240100385877585)
    ·
      refine ⟨33793090538430075289408189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45057454051240100385877585 33793090538430075289408189)
      ·
        refine ⟨12672408951911278233528071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33793090538430075289408189 12672408951911278233528071)
        ·
          refine ⟨19008613427866917350292107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12672408951911278233528071 19008613427866917350292107)
          ·
            refine ⟨28512920141800376025438161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19008613427866917350292107 28512920141800376025438161)
            ·
              refine ⟨21384690106350282019078621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28512920141800376025438161 21384690106350282019078621)
              ·
                refine ⟨8019258789881355757154483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21384690106350282019078621 8019258789881355757154483)
                ·
                  refine ⟨12028888184822033635731725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8019258789881355757154483 12028888184822033635731725)
                  ·
                    refine ⟨4510833069308262613399397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12028888184822033635731725 4510833069308262613399397)
                    ·
                      refine ⟨845781200495299240012387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4510833069308262613399397 845781200495299240012387)
                      ·
                        rfl

theorem cell23_1647153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 3, 1, 3, 4].length) (baseStart_1647153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1647153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1647153 prefixEnd_1647153 := by exact prefixLift 1647153
  have htrace : WordTrace (prefixWord ++ tailWord_1647153) baseStart_1647153 baseEnd_1647153 := by
    simpa [prefixWord, tailWord_1647153, baseEnd_1647153] using wordTrace_append hprefix tailTrace_1647153
  have hstable : (prefixWord ++ tailWord_1647153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647153).length < 2 ^ (prefixWord ++ tailWord_1647153).sum := by decide
  have hdescent : baseEnd_1647153 < baseStart_1647153 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647174 : List Nat := [6, 1, 1, 1, 2, 1, 1, 1, 2, 5, 2]
def baseStart_1647174 : Nat := 118140960795 + 1647174 * 2 ^ 59
def prefixEnd_1647174 : Nat := 4983230072969 + 3 ^ 40 * 1647174 * 2
def baseEnd_1647174 : Nat := 845791983589043657849791

theorem tailTrace_1647174 : CollatzResearch.WordTrace tailWord_1647174 prefixEnd_1647174 845791983589043657849791 := by
  unfold tailWord_1647174
  simp only [CollatzResearch.WordTrace]
  refine ⟨1877417854205543367740143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 40051580889718258511789717 1877417854205543367740143)
  ·
    refine ⟨2816126781308315051610215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1877417854205543367740143 2816126781308315051610215)
    ·
      refine ⟨4224190171962472577415323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2816126781308315051610215 4224190171962472577415323)
      ·
        refine ⟨6336285257943708866122985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4224190171962472577415323 6336285257943708866122985)
        ·
          refine ⟨4752213943457781649592239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6336285257943708866122985 4752213943457781649592239)
          ·
            refine ⟨7128320915186672474388359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4752213943457781649592239 7128320915186672474388359)
            ·
              refine ⟨10692481372780008711582539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7128320915186672474388359 10692481372780008711582539)
              ·
                refine ⟨16038722059170013067373809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10692481372780008711582539 16038722059170013067373809)
                ·
                  refine ⟨12029041544377509800530357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16038722059170013067373809 12029041544377509800530357)
                  ·
                    refine ⟨1127722644785391543799721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12029041544377509800530357 1127722644785391543799721)
                    ·
                      refine ⟨845791983589043657849791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1127722644785391543799721 845791983589043657849791)
                      ·
                        rfl

theorem cell23_1647174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 1, 2, 5, 2].length) (baseStart_1647174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1647174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1647174 prefixEnd_1647174 := by exact prefixLift 1647174
  have htrace : WordTrace (prefixWord ++ tailWord_1647174) baseStart_1647174 baseEnd_1647174 := by
    simpa [prefixWord, tailWord_1647174, baseEnd_1647174] using wordTrace_append hprefix tailTrace_1647174
  have hstable : (prefixWord ++ tailWord_1647174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647174).length < 2 ^ (prefixWord ++ tailWord_1647174).sum := by decide
  have hdescent : baseEnd_1647174 < baseStart_1647174 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647180 : List Nat := [2, 2, 1, 3, 1, 2, 2, 3, 3, 4]
def baseStart_1647180 : Nat := 118140960795 + 1647180 * 2 ^ 59
def prefixEnd_1647180 : Nat := 4983230072969 + 3 ^ 40 * 1647180 * 2
def baseEnd_1647180 : Nat := 281931688157656878124921

theorem tailTrace_1647180 : CollatzResearch.WordTrace tailWord_1647180 prefixEnd_1647180 281931688157656878124921 := by
  unfold tailWord_1647180
  simp only [CollatzResearch.WordTrace]
  refine ⟨30038795086277825396201497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40051726781703767194935329 30038795086277825396201497)
  ·
    refine ⟨22529096314708369047151123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30038795086277825396201497 22529096314708369047151123)
    ·
      refine ⟨33793644472062553570726685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22529096314708369047151123 33793644472062553570726685)
      ·
        refine ⟨12672616677023457589022507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33793644472062553570726685 12672616677023457589022507)
        ·
          refine ⟨19008925015535186383533761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12672616677023457589022507 19008925015535186383533761)
          ·
            refine ⟨14256693761651389787650321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19008925015535186383533761 14256693761651389787650321)
            ·
              refine ⟨10692520321238542340737741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14256693761651389787650321 10692520321238542340737741)
              ·
                refine ⟨4009695120464453377776653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10692520321238542340737741 4009695120464453377776653)
                ·
                  refine ⟨1503635670174170016666245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4009695120464453377776653 1503635670174170016666245)
                  ·
                    refine ⟨281931688157656878124921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1503635670174170016666245 281931688157656878124921)
                    ·
                      rfl

theorem cell23_1647180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 3, 3, 4].length) (baseStart_1647180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1647180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1647180 prefixEnd_1647180 := by exact prefixLift 1647180
  have htrace : WordTrace (prefixWord ++ tailWord_1647180) baseStart_1647180 baseEnd_1647180 := by
    simpa [prefixWord, tailWord_1647180, baseEnd_1647180] using wordTrace_append hprefix tailTrace_1647180
  have hstable : (prefixWord ++ tailWord_1647180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647180).length < 2 ^ (prefixWord ++ tailWord_1647180).sum := by decide
  have hdescent : baseEnd_1647180 < baseStart_1647180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647214 : List Nat := [4, 1, 2, 2, 2, 1, 1, 5, 1, 4]
def baseStart_1647214 : Nat := 118140960795 + 1647214 * 2 ^ 59
def prefixEnd_1647214 : Nat := 4983230072969 + 3 ^ 40 * 1647214 * 2
def baseEnd_1647214 : Nat := 281937507605074500449869

theorem tailTrace_1647214 : CollatzResearch.WordTrace tailWord_1647214 prefixEnd_1647214 281937507605074500449869 := by
  unfold tailWord_1647214
  simp only [CollatzResearch.WordTrace]
  refine ⟨7509853781804059324892587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40052553502954983066093797 7509853781804059324892587)
  ·
    refine ⟨11264780672706088987338881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7509853781804059324892587 11264780672706088987338881)
    ·
      refine ⟨8448585504529566740504161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11264780672706088987338881 8448585504529566740504161)
      ·
        refine ⟨6336439128397175055378121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8448585504529566740504161 6336439128397175055378121)
        ·
          refine ⟨4752329346297881291533591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6336439128397175055378121 4752329346297881291533591)
          ·
            refine ⟨7128494019446821937300387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4752329346297881291533591 7128494019446821937300387)
            ·
              refine ⟨10692741029170232905950581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7128494019446821937300387 10692741029170232905950581)
              ·
                refine ⟨1002444471484709334932867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10692741029170232905950581 1002444471484709334932867)
                ·
                  refine ⟨1503666707227064002399301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1002444471484709334932867 1503666707227064002399301)
                  ·
                    refine ⟨281937507605074500449869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1503666707227064002399301 281937507605074500449869)
                    ·
                      rfl

theorem cell23_1647214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 5, 1, 4].length) (baseStart_1647214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1647214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1647214 prefixEnd_1647214 := by exact prefixLift 1647214
  have htrace : WordTrace (prefixWord ++ tailWord_1647214) baseStart_1647214 baseEnd_1647214 := by
    simpa [prefixWord, tailWord_1647214, baseEnd_1647214] using wordTrace_append hprefix tailTrace_1647214
  have hstable : (prefixWord ++ tailWord_1647214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647214).length < 2 ^ (prefixWord ++ tailWord_1647214).sum := by decide
  have hdescent : baseEnd_1647214 < baseStart_1647214 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647237 : List Nat := [1, 3, 1, 1, 4, 2, 1, 3, 3, 1, 3]
def baseStart_1647237 : Nat := 118140960795 + 1647237 * 2 ^ 59
def prefixEnd_1647237 : Nat := 4983230072969 + 3 ^ 40 * 1647237 * 2
def baseEnd_1647237 : Nat := 845824332870276911362001

theorem tailTrace_1647237 : CollatzResearch.WordTrace tailWord_1647237 prefixEnd_1647237 845824332870276911362001 := by
  unfold tailWord_1647237
  simp only [CollatzResearch.WordTrace]
  refine ⟨60079669133349149527227965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40053112755566099684818643 60079669133349149527227965)
  ·
    refine ⟨22529875925005931072710487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60079669133349149527227965 22529875925005931072710487)
    ·
      refine ⟨33794813887508896609065731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22529875925005931072710487 33794813887508896609065731)
      ·
        refine ⟨50692220831263344913598597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33794813887508896609065731 50692220831263344913598597)
        ·
          refine ⟨9504791405861877171299737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50692220831263344913598597 9504791405861877171299737)
          ·
            refine ⟨7128593554396407878474803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9504791405861877171299737 7128593554396407878474803)
            ·
              refine ⟨10692890331594611817712205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7128593554396407878474803 10692890331594611817712205)
              ·
                refine ⟨4009833874347979431642077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10692890331594611817712205 4009833874347979431642077)
                ·
                  refine ⟨1503687702880492286865779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4009833874347979431642077 1503687702880492286865779)
                  ·
                    refine ⟨2255531554320738430298669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1503687702880492286865779 2255531554320738430298669)
                    ·
                      refine ⟨845824332870276911362001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2255531554320738430298669 845824332870276911362001)
                      ·
                        rfl

theorem cell23_1647237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 3, 3, 1, 3].length) (baseStart_1647237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1647237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1647237 prefixEnd_1647237 := by exact prefixLift 1647237
  have htrace : WordTrace (prefixWord ++ tailWord_1647237) baseStart_1647237 baseEnd_1647237 := by
    simpa [prefixWord, tailWord_1647237, baseEnd_1647237] using wordTrace_append hprefix tailTrace_1647237
  have hstable : (prefixWord ++ tailWord_1647237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647237).length < 2 ^ (prefixWord ++ tailWord_1647237).sum := by decide
  have hdescent : baseEnd_1647237 < baseStart_1647237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647243 : List Nat := [1, 1, 1, 1, 4, 1, 2, 1, 2, 5, 4]
def baseStart_1647243 : Nat := 118140960795 + 1647243 * 2 ^ 59
def prefixEnd_1647243 : Nat := 4983230072969 + 3 ^ 40 * 1647243 * 2
def baseEnd_1647243 : Nat := 845827413754203887886973

theorem tailTrace_1647243 : CollatzResearch.WordTrace tailWord_1647243 prefixEnd_1647243 845827413754203887886973 := by
  unfold tailWord_1647243
  simp only [CollatzResearch.WordTrace]
  refine ⟨60079887971327412551946383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40053258647551608367964255 60079887971327412551946383)
  ·
    refine ⟨90119831956991118827919575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60079887971327412551946383 90119831956991118827919575)
    ·
      refine ⟨135179747935486678241879363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90119831956991118827919575 135179747935486678241879363)
      ·
        refine ⟨202769621903230017362819045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135179747935486678241879363 202769621903230017362819045)
        ·
          refine ⟨38019304106855628255528571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 202769621903230017362819045 38019304106855628255528571)
          ·
            refine ⟨57028956160283442383292857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38019304106855628255528571 57028956160283442383292857)
            ·
              refine ⟨42771717120212581787469643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57028956160283442383292857 42771717120212581787469643)
              ·
                refine ⟨64157575680318872681204465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42771717120212581787469643 64157575680318872681204465)
                ·
                  refine ⟨48118181760239154510903349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64157575680318872681204465 48118181760239154510903349)
                  ·
                    refine ⟨4511079540022420735397189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48118181760239154510903349 4511079540022420735397189)
                    ·
                      refine ⟨845827413754203887886973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4511079540022420735397189 845827413754203887886973)
                      ·
                        rfl

theorem cell23_1647243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 5, 4].length) (baseStart_1647243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1647243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1647243 prefixEnd_1647243 := by exact prefixLift 1647243
  have htrace : WordTrace (prefixWord ++ tailWord_1647243) baseStart_1647243 baseEnd_1647243 := by
    simpa [prefixWord, tailWord_1647243, baseEnd_1647243] using wordTrace_append hprefix tailTrace_1647243
  have hstable : (prefixWord ++ tailWord_1647243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647243).length < 2 ^ (prefixWord ++ tailWord_1647243).sum := by decide
  have hdescent : baseEnd_1647243 < baseStart_1647243 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647273 : List Nat := [1, 2, 1, 1, 1, 1, 2, 4, 3, 1, 6]
def baseStart_1647273 : Nat := 118140960795 + 1647273 * 2 ^ 59
def prefixEnd_1647273 : Nat := 4983230072969 + 3 ^ 40 * 1647273 * 2
def baseEnd_1647273 : Nat := 845842818173838770511835

theorem tailTrace_1647273 : CollatzResearch.WordTrace tailWord_1647273 prefixEnd_1647273 845842818173838770511835 := by
  unfold tailWord_1647273
  simp only [CollatzResearch.WordTrace]
  refine ⟨60080982161218727675538473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40053988107479151783692315 60080982161218727675538473)
  ·
    refine ⟨45060736620914045756653855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60080982161218727675538473 45060736620914045756653855)
    ·
      refine ⟨67591104931371068634980783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45060736620914045756653855 67591104931371068634980783)
      ·
        refine ⟨101386657397056602952471175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67591104931371068634980783 101386657397056602952471175)
        ·
          refine ⟨152079986095584904428706763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101386657397056602952471175 152079986095584904428706763)
          ·
            refine ⟨228119979143377356643060145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152079986095584904428706763 228119979143377356643060145)
            ·
              refine ⟨171089984357533017482295109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 228119979143377356643060145 171089984357533017482295109)
              ·
                refine ⟨32079372067037440777930333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 171089984357533017482295109 32079372067037440777930333)
                ·
                  refine ⟨12029764525139040291723875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32079372067037440777930333 12029764525139040291723875)
                  ·
                    refine ⟨18044646787708560437585813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12029764525139040291723875 18044646787708560437585813)
                    ·
                      refine ⟨845842818173838770511835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18044646787708560437585813 845842818173838770511835)
                      ·
                        rfl

theorem cell23_1647273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 3, 1, 6].length) (baseStart_1647273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1647273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1647273 prefixEnd_1647273 := by exact prefixLift 1647273
  have htrace : WordTrace (prefixWord ++ tailWord_1647273) baseStart_1647273 baseEnd_1647273 := by
    simpa [prefixWord, tailWord_1647273, baseEnd_1647273] using wordTrace_append hprefix tailTrace_1647273
  have hstable : (prefixWord ++ tailWord_1647273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647273).length < 2 ^ (prefixWord ++ tailWord_1647273).sum := by decide
  have hdescent : baseEnd_1647273 < baseStart_1647273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647280 : List Nat := [2, 1, 1, 1, 2, 1, 3, 2, 5, 2, 3]
def baseStart_1647280 : Nat := 118140960795 + 1647280 * 2 ^ 59
def prefixEnd_1647280 : Nat := 4983230072969 + 3 ^ 40 * 1647280 * 2
def baseEnd_1647280 : Nat := 845846412538420243124303

theorem tailTrace_1647280 : CollatzResearch.WordTrace tailWord_1647280 prefixEnd_1647280 845846412538420243124303 := by
  unfold tailWord_1647280
  simp only [CollatzResearch.WordTrace]
  refine ⟨30040618736096683935521647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40054158314795578580695529 30040618736096683935521647)
  ·
    refine ⟨45060928104145025903282471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30040618736096683935521647 45060928104145025903282471)
    ·
      refine ⟨67591392156217538854923707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45060928104145025903282471 67591392156217538854923707)
      ·
        refine ⟨101387088234326308282385561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67591392156217538854923707 101387088234326308282385561)
        ·
          refine ⟨76040316175744731211789171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101387088234326308282385561 76040316175744731211789171)
          ·
            refine ⟨114060474263617096817683757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76040316175744731211789171 114060474263617096817683757)
            ·
              refine ⟨42772677848856411306631409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 114060474263617096817683757 42772677848856411306631409)
              ·
                refine ⟨32079508386642308479973557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42772677848856411306631409 32079508386642308479973557)
                ·
                  refine ⟨3007453911247716419997521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32079508386642308479973557 3007453911247716419997521)
                  ·
                    refine ⟨2255590433435787314998141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3007453911247716419997521 2255590433435787314998141)
                    ·
                      refine ⟨845846412538420243124303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2255590433435787314998141 845846412538420243124303)
                      ·
                        rfl

theorem cell23_1647280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 5, 2, 3].length) (baseStart_1647280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1647280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1647280 prefixEnd_1647280 := by exact prefixLift 1647280
  have htrace : WordTrace (prefixWord ++ tailWord_1647280) baseStart_1647280 baseEnd_1647280 := by
    simpa [prefixWord, tailWord_1647280, baseEnd_1647280] using wordTrace_append hprefix tailTrace_1647280
  have hstable : (prefixWord ++ tailWord_1647280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647280).length < 2 ^ (prefixWord ++ tailWord_1647280).sum := by decide
  have hdescent : baseEnd_1647280 < baseStart_1647280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647281 : List Nat := [1, 2, 2, 6, 1, 1, 1, 2, 2, 3, 2]
def baseStart_1647281 : Nat := 118140960795 + 1647281 * 2 ^ 59
def prefixEnd_1647281 : Nat := 4983230072969 + 3 ^ 40 * 1647281 * 2
def baseEnd_1647281 : Nat := 845846926019074739211799

theorem tailTrace_1647281 : CollatzResearch.WordTrace tailWord_1647281 prefixEnd_1647281 845846926019074739211799 := by
  unfold tailWord_1647281
  simp only [CollatzResearch.WordTrace]
  refine ⟨60081273945189745041829697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40054182630126496694553131 60081273945189745041829697)
  ·
    refine ⟨45060955458892308781372273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60081273945189745041829697 45060955458892308781372273)
    ·
      refine ⟨33795716594169231586029205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45060955458892308781372273 33795716594169231586029205)
      ·
        refine ⟨1584174215351682730595119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 33795716594169231586029205 1584174215351682730595119)
        ·
          refine ⟨2376261323027524095892679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1584174215351682730595119 2376261323027524095892679)
          ·
            refine ⟨3564391984541286143839019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2376261323027524095892679 3564391984541286143839019)
            ·
              refine ⟨5346587976811929215758529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3564391984541286143839019 5346587976811929215758529)
              ·
                refine ⟨4009940982608946911818897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5346587976811929215758529 4009940982608946911818897)
                ·
                  refine ⟨3007455736956710183864173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4009940982608946911818897 3007455736956710183864173)
                  ·
                    refine ⟨1127795901358766318949065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3007455736956710183864173 1127795901358766318949065)
                    ·
                      refine ⟨845846926019074739211799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1127795901358766318949065 845846926019074739211799)
                      ·
                        rfl

theorem cell23_1647281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_1647281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1647281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1647281 prefixEnd_1647281 := by exact prefixLift 1647281
  have htrace : WordTrace (prefixWord ++ tailWord_1647281) baseStart_1647281 baseEnd_1647281 := by
    simpa [prefixWord, tailWord_1647281, baseEnd_1647281] using wordTrace_append hprefix tailTrace_1647281
  have hstable : (prefixWord ++ tailWord_1647281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647281).length < 2 ^ (prefixWord ++ tailWord_1647281).sum := by decide
  have hdescent : baseEnd_1647281 < baseStart_1647281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647283 : List Nat := [1, 1, 1, 2, 3, 4, 11]
def baseStart_1647283 : Nat := 118140960795 + 1647283 * 2 ^ 59
def prefixEnd_1647283 : Nat := 4983230072969 + 3 ^ 40 * 1647283 * 2
def baseEnd_1647283 : Nat := 10442567320745478165269

theorem tailTrace_1647283 : CollatzResearch.WordTrace tailWord_1647283 prefixEnd_1647283 10442567320745478165269 := by
  unfold tailWord_1647283
  simp only [CollatzResearch.WordTrace]
  refine ⟨60081346891182499383402503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40054231260788332922268335 60081346891182499383402503)
  ·
    refine ⟨90122020336773749075103755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60081346891182499383402503 90122020336773749075103755)
    ·
      refine ⟨135183030505160623612655633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90122020336773749075103755 135183030505160623612655633)
      ·
        refine ⟨101387272878870467709491725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135183030505160623612655633 101387272878870467709491725)
        ·
          refine ⟨38020227329576425391059397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101387272878870467709491725 38020227329576425391059397)
          ·
            refine ⟨7128792624295579760823637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38020227329576425391059397 7128792624295579760823637)
            ·
              refine ⟨10442567320745478165269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 7128792624295579760823637 10442567320745478165269)
              ·
                rfl

theorem cell23_1647283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 11].length) (baseStart_1647283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1647283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1647283 prefixEnd_1647283 := by exact prefixLift 1647283
  have htrace : WordTrace (prefixWord ++ tailWord_1647283) baseStart_1647283 baseEnd_1647283 := by
    simpa [prefixWord, tailWord_1647283, baseEnd_1647283] using wordTrace_append hprefix tailTrace_1647283
  have hstable : (prefixWord ++ tailWord_1647283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647283).length < 2 ^ (prefixWord ++ tailWord_1647283).sum := by decide
  have hdescent : baseEnd_1647283 < baseStart_1647283 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647300 : List Nat := [2, 3, 3, 1, 1, 2, 1, 10]
def baseStart_1647300 : Nat := 118140960795 + 1647300 * 2 ^ 59
def prefixEnd_1647300 : Nat := 4983230072969 + 3 ^ 40 * 1647300 * 2
def baseEnd_1647300 : Nat := 31328025264870746847193

theorem tailTrace_1647300 : CollatzResearch.WordTrace tailWord_1647300 prefixEnd_1647300 31328025264870746847193 := by
  unfold tailWord_1647300
  simp only [CollatzResearch.WordTrace]
  refine ⟨30040983466060455643385677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40054644621413940857847569 30040983466060455643385677)
  ·
    refine ⟨11265368799772670866269629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30040983466060455643385677 11265368799772670866269629)
    ·
      refine ⟨4224513299914751574851111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11265368799772670866269629 4224513299914751574851111)
      ·
        refine ⟨6336769949872127362276667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4224513299914751574851111 6336769949872127362276667)
        ·
          refine ⟨9505154924808191043415001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6336769949872127362276667 9505154924808191043415001)
          ·
            refine ⟨7128866193606143282561251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9505154924808191043415001 7128866193606143282561251)
            ·
              refine ⟨10693299290409214923841877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7128866193606143282561251 10693299290409214923841877)
              ·
                refine ⟨31328025264870746847193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 10693299290409214923841877 31328025264870746847193)
                ·
                  rfl

theorem cell23_1647300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 10].length) (baseStart_1647300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1647300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1647300 prefixEnd_1647300 := by exact prefixLift 1647300
  have htrace : WordTrace (prefixWord ++ tailWord_1647300) baseStart_1647300 baseEnd_1647300 := by
    simpa [prefixWord, tailWord_1647300, baseEnd_1647300] using wordTrace_append hprefix tailTrace_1647300
  have hstable : (prefixWord ++ tailWord_1647300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647300).length < 2 ^ (prefixWord ++ tailWord_1647300).sum := by decide
  have hdescent : baseEnd_1647300 < baseStart_1647300 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647304 : List Nat := [2, 1, 3, 1, 2, 3, 4, 1, 2, 4]
def baseStart_1647304 : Nat := 118140960795 + 1647304 * 2 ^ 59
def prefixEnd_1647304 : Nat := 4983230072969 + 3 ^ 40 * 1647304 * 2
def baseEnd_1647304 : Nat := 281952912024709383074731

theorem tailTrace_1647304 : CollatzResearch.WordTrace tailWord_1647304 prefixEnd_1647304 281952912024709383074731 := by
  unfold tailWord_1647304
  simp only [CollatzResearch.WordTrace]
  refine ⟨30041056412053209984958483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40054741882737613313277977 30041056412053209984958483)
  ·
    refine ⟨45061584618079814977437725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30041056412053209984958483 45061584618079814977437725)
    ·
      refine ⟨16898094231779930616539147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45061584618079814977437725 16898094231779930616539147)
      ·
        refine ⟨25347141347669895924808721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16898094231779930616539147 25347141347669895924808721)
        ·
          refine ⟨19010356010752421943606541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25347141347669895924808721 19010356010752421943606541)
          ·
            refine ⟨7128883504032158228852453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19010356010752421943606541 7128883504032158228852453)
            ·
              refine ⟨1336665657006029667909835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7128883504032158228852453 1336665657006029667909835)
              ·
                refine ⟨2004998485509044501864753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1336665657006029667909835 2004998485509044501864753)
                ·
                  refine ⟨1503748864131783376398565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2004998485509044501864753 1503748864131783376398565)
                  ·
                    refine ⟨281952912024709383074731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1503748864131783376398565 281952912024709383074731)
                    ·
                      rfl

theorem cell23_1647304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 4, 1, 2, 4].length) (baseStart_1647304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1647304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1647304 prefixEnd_1647304 := by exact prefixLift 1647304
  have htrace : WordTrace (prefixWord ++ tailWord_1647304) baseStart_1647304 baseEnd_1647304 := by
    simpa [prefixWord, tailWord_1647304, baseEnd_1647304] using wordTrace_append hprefix tailTrace_1647304
  have hstable : (prefixWord ++ tailWord_1647304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647304).length < 2 ^ (prefixWord ++ tailWord_1647304).sum := by decide
  have hdescent : baseEnd_1647304 < baseStart_1647304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647314 : List Nat := [3, 2, 2, 2, 3, 1, 1, 1, 3, 2, 3]
def baseStart_1647314 : Nat := 118140960795 + 1647314 * 2 ^ 59
def prefixEnd_1647314 : Nat := 4983230072969 + 3 ^ 40 * 1647314 * 2
def baseEnd_1647314 : Nat := 845863870880673110099147

theorem tailTrace_1647314 : CollatzResearch.WordTrace tailWord_1647314 prefixEnd_1647314 845863870880673110099147 := by
  unfold tailWord_1647314
  simp only [CollatzResearch.WordTrace]
  refine ⟨15020619388517547919445249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40054985036046794451853997 15020619388517547919445249)
  ·
    refine ⟨11265464541388160939583937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15020619388517547919445249 11265464541388160939583937)
    ·
      refine ⟨8449098406041120704687953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11265464541388160939583937 8449098406041120704687953)
      ·
        refine ⟨6336823804530840528515965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8449098406041120704687953 6336823804530840528515965)
        ·
          refine ⟨2376308926699065198193487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6336823804530840528515965 2376308926699065198193487)
          ·
            refine ⟨3564463390048597797290231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2376308926699065198193487 3564463390048597797290231)
            ·
              refine ⟨5346695085072896695935347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3564463390048597797290231 5346695085072896695935347)
              ·
                refine ⟨8020042627609345043903021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5346695085072896695935347 8020042627609345043903021)
                ·
                  refine ⟨3007515985353504391463633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8020042627609345043903021 3007515985353504391463633)
                  ·
                    refine ⟨2255636989015128293597725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3007515985353504391463633 2255636989015128293597725)
                    ·
                      refine ⟨845863870880673110099147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2255636989015128293597725 845863870880673110099147)
                      ·
                        rfl

theorem cell23_1647314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 1, 3, 2, 3].length) (baseStart_1647314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1647314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1647314 prefixEnd_1647314 := by exact prefixLift 1647314
  have htrace : WordTrace (prefixWord ++ tailWord_1647314) baseStart_1647314 baseEnd_1647314 := by
    simpa [prefixWord, tailWord_1647314, baseEnd_1647314] using wordTrace_append hprefix tailTrace_1647314
  have hstable : (prefixWord ++ tailWord_1647314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647314).length < 2 ^ (prefixWord ++ tailWord_1647314).sum := by decide
  have hdescent : baseEnd_1647314 < baseStart_1647314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647324 : List Nat := [2, 2, 5, 1, 1, 2, 1, 2, 1, 2, 4]
def baseStart_1647324 : Nat := 118140960795 + 1647324 * 2 ^ 59
def prefixEnd_1647324 : Nat := 4983230072969 + 3 ^ 40 * 1647324 * 2
def baseEnd_1647324 : Nat := 845869005687218070974101

theorem tailTrace_1647324 : CollatzResearch.WordTrace tailWord_1647324 prefixEnd_1647324 845869005687218070974101 := by
  unfold tailWord_1647324
  simp only [CollatzResearch.WordTrace]
  refine ⟨30041421142016981692822513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40055228189355975590430017 30041421142016981692822513)
  ·
    refine ⟨22531065856512736269616885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30041421142016981692822513 22531065856512736269616885)
    ·
      refine ⟨2112287424048069025276583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22531065856512736269616885 2112287424048069025276583)
      ·
        refine ⟨3168431136072103537914875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2112287424048069025276583 3168431136072103537914875)
        ·
          refine ⟨4752646704108155306872313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3168431136072103537914875 4752646704108155306872313)
          ·
            refine ⟨3564485028081116480154235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4752646704108155306872313 3564485028081116480154235)
            ·
              refine ⟨5346727542121674720231353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3564485028081116480154235 5346727542121674720231353)
              ·
                refine ⟨4010045656591256040173515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5346727542121674720231353 4010045656591256040173515)
                ·
                  refine ⟨6015068484886884060260273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4010045656591256040173515 6015068484886884060260273)
                  ·
                    refine ⟨4511301363665163045195205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6015068484886884060260273 4511301363665163045195205)
                    ·
                      refine ⟨845869005687218070974101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4511301363665163045195205 845869005687218070974101)
                      ·
                        rfl

theorem cell23_1647324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_1647324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1647324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1647324 prefixEnd_1647324 := by exact prefixLift 1647324
  have htrace : WordTrace (prefixWord ++ tailWord_1647324) baseStart_1647324 baseEnd_1647324 := by
    simpa [prefixWord, tailWord_1647324, baseEnd_1647324] using wordTrace_append hprefix tailTrace_1647324
  have hstable : (prefixWord ++ tailWord_1647324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647324).length < 2 ^ (prefixWord ++ tailWord_1647324).sum := by decide
  have hdescent : baseEnd_1647324 < baseStart_1647324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647327 : List Nat := [1, 1, 2, 3, 2, 4, 1, 2, 1, 3, 3]
def baseStart_1647327 : Nat := 118140960795 + 1647327 * 2 ^ 59
def prefixEnd_1647327 : Nat := 4983230072969 + 3 ^ 40 * 1647327 * 2
def baseEnd_1647327 : Nat := 845870546129181559236587

theorem tailTrace_1647327 : CollatzResearch.WordTrace tailWord_1647327 prefixEnd_1647327 845870546129181559236587 := by
  unfold tailWord_1647327
  simp only [CollatzResearch.WordTrace]
  refine ⟨60082951703023094898004235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40055301135348729932002823 60082951703023094898004235)
  ·
    refine ⟨90124427554534642347006353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60082951703023094898004235 90124427554534642347006353)
    ·
      refine ⟨67593320665900981760254765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90124427554534642347006353 67593320665900981760254765)
      ·
        refine ⟨25347495249712868160095537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67593320665900981760254765 25347495249712868160095537)
        ·
          refine ⟨19010621437284651120071653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25347495249712868160095537 19010621437284651120071653)
          ·
            refine ⟨3564491519490872085013435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19010621437284651120071653 3564491519490872085013435)
            ·
              refine ⟨5346737279236308127520153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3564491519490872085013435 5346737279236308127520153)
              ·
                refine ⟨4010052959427231095640115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5346737279236308127520153 4010052959427231095640115)
                ·
                  refine ⟨6015079439140846643460173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4010052959427231095640115 6015079439140846643460173)
                  ·
                    refine ⟨2255654789677817491297565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6015079439140846643460173 2255654789677817491297565)
                    ·
                      refine ⟨845870546129181559236587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2255654789677817491297565 845870546129181559236587)
                      ·
                        rfl

theorem cell23_1647327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 2, 1, 3, 3].length) (baseStart_1647327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1647327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1647327 prefixEnd_1647327 := by exact prefixLift 1647327
  have htrace : WordTrace (prefixWord ++ tailWord_1647327) baseStart_1647327 baseEnd_1647327 := by
    simpa [prefixWord, tailWord_1647327, baseEnd_1647327] using wordTrace_append hprefix tailTrace_1647327
  have hstable : (prefixWord ++ tailWord_1647327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647327).length < 2 ^ (prefixWord ++ tailWord_1647327).sum := by decide
  have hdescent : baseEnd_1647327 < baseStart_1647327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647331 : List Nat := [1, 1, 1, 7, 1, 2, 3, 1, 1, 2, 3]
def baseStart_1647331 : Nat := 118140960795 + 1647331 * 2 ^ 59
def prefixEnd_1647331 : Nat := 4983230072969 + 3 ^ 40 * 1647331 * 2
def baseEnd_1647331 : Nat := 845872600051799543586569

theorem tailTrace_1647331 : CollatzResearch.WordTrace tailWord_1647331 prefixEnd_1647331 845872600051799543586569 := by
  unfold tailWord_1647331
  simp only [CollatzResearch.WordTrace]
  refine ⟨60083097595008603581149847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40055398396672402387433231 60083097595008603581149847)
  ·
    refine ⟨90124646392512905371724771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60083097595008603581149847 90124646392512905371724771)
    ·
      refine ⟨135186969588769358057587157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90124646392512905371724771 135186969588769358057587157)
      ·
        refine ⟨3168444599736781829474699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 135186969588769358057587157 3168444599736781829474699)
        ·
          refine ⟨4752666899605172744212049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3168444599736781829474699 4752666899605172744212049)
          ·
            refine ⟨3564500174703879558159037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4752666899605172744212049 3564500174703879558159037)
            ·
              refine ⟨1336687565513954834309639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3564500174703879558159037 1336687565513954834309639)
              ·
                refine ⟨2005031348270932251464459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1336687565513954834309639 2005031348270932251464459)
                ·
                  refine ⟨3007547022406398377196689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2005031348270932251464459 3007547022406398377196689)
                  ·
                    refine ⟨2255660266804798782897517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3007547022406398377196689 2255660266804798782897517)
                    ·
                      refine ⟨845872600051799543586569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2255660266804798782897517 845872600051799543586569)
                      ·
                        rfl

theorem cell23_1647331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 3, 1, 1, 2, 3].length) (baseStart_1647331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1647331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1647331 prefixEnd_1647331 := by exact prefixLift 1647331
  have htrace : WordTrace (prefixWord ++ tailWord_1647331) baseStart_1647331 baseEnd_1647331 := by
    simpa [prefixWord, tailWord_1647331, baseEnd_1647331] using wordTrace_append hprefix tailTrace_1647331
  have hstable : (prefixWord ++ tailWord_1647331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647331).length < 2 ^ (prefixWord ++ tailWord_1647331).sum := by decide
  have hdescent : baseEnd_1647331 < baseStart_1647331 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647344 : List Nat := [2, 1, 1, 1, 3, 1, 6, 2, 2, 1, 3]
def baseStart_1647344 : Nat := 118140960795 + 1647344 * 2 ^ 59
def prefixEnd_1647344 : Nat := 4983230072969 + 3 ^ 40 * 1647344 * 2
def baseEnd_1647344 : Nat := 845879275300307992724009

theorem tailTrace_1647344 : CollatzResearch.WordTrace tailWord_1647344 prefixEnd_1647344 845879275300307992724009 := by
  unfold tailWord_1647344
  simp only [CollatzResearch.WordTrace]
  refine ⟨30041785871980753400686543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40055714495974337867582057 30041785871980753400686543)
  ·
    refine ⟨45062678807971130101029815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30041785871980753400686543 45062678807971130101029815)
    ·
      refine ⟨67594018211956695151544723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45062678807971130101029815 67594018211956695151544723)
      ·
        refine ⟨101391027317935042727317085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67594018211956695151544723 101391027317935042727317085)
        ·
          refine ⟨38021635244225641022743907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101391027317935042727317085 38021635244225641022743907)
          ·
            refine ⟨57032452866338461534115861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38021635244225641022743907 57032452866338461534115861)
            ·
              refine ⟨2673396228109615384411681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 57032452866338461534115861 2673396228109615384411681)
              ·
                refine ⟨2005047171082211538308761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2673396228109615384411681 2005047171082211538308761)
                ·
                  refine ⟨1503785378311658653731571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2005047171082211538308761 1503785378311658653731571)
                  ·
                    refine ⟨2255678067467487980597357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1503785378311658653731571 2255678067467487980597357)
                    ·
                      refine ⟨845879275300307992724009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2255678067467487980597357 845879275300307992724009)
                      ·
                        rfl

theorem cell23_1647344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 6, 2, 2, 1, 3].length) (baseStart_1647344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1647344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1647344 prefixEnd_1647344 := by exact prefixLift 1647344
  have htrace : WordTrace (prefixWord ++ tailWord_1647344) baseStart_1647344 baseEnd_1647344 := by
    simpa [prefixWord, tailWord_1647344, baseEnd_1647344] using wordTrace_append hprefix tailTrace_1647344
  have hstable : (prefixWord ++ tailWord_1647344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647344).length < 2 ^ (prefixWord ++ tailWord_1647344).sum := by decide
  have hdescent : baseEnd_1647344 < baseStart_1647344 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647384 : List Nat := [2, 1, 2, 3, 1, 1, 1, 4, 4, 2, 2]
def baseStart_1647384 : Nat := 118140960795 + 1647384 * 2 ^ 59
def prefixEnd_1647384 : Nat := 4983230072969 + 3 ^ 40 * 1647384 * 2
def baseEnd_1647384 : Nat := 845899814526487836223825

theorem tailTrace_1647384 : CollatzResearch.WordTrace tailWord_1647384 prefixEnd_1647384 845899814526487836223825 := by
  unfold tailWord_1647384
  simp only [CollatzResearch.WordTrace]
  refine ⟨30042515331908296816414603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40056687109211062421886137 30042515331908296816414603)
  ·
    refine ⟨45063772997862445224621905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30042515331908296816414603 45063772997862445224621905)
    ·
      refine ⟨33797829748396833918466429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45063772997862445224621905 33797829748396833918466429)
      ·
        refine ⟨12674186155648812719424911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33797829748396833918466429 12674186155648812719424911)
        ·
          refine ⟨19011279233473219079137367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12674186155648812719424911 19011279233473219079137367)
          ·
            refine ⟨28516918850209828618706051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19011279233473219079137367 28516918850209828618706051)
            ·
              refine ⟨42775378275314742928059077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28516918850209828618706051 42775378275314742928059077)
              ·
                refine ⟨8020383426621514299011077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42775378275314742928059077 8020383426621514299011077)
                ·
                  refine ⟨1503821892491533931064577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8020383426621514299011077 1503821892491533931064577)
                  ·
                    refine ⟨1127866419368650448298433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1503821892491533931064577 1127866419368650448298433)
                    ·
                      refine ⟨845899814526487836223825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1127866419368650448298433 845899814526487836223825)
                      ·
                        rfl

theorem cell23_1647384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 4, 4, 2, 2].length) (baseStart_1647384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1647384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1647384 prefixEnd_1647384 := by exact prefixLift 1647384
  have htrace : WordTrace (prefixWord ++ tailWord_1647384) baseStart_1647384 baseEnd_1647384 := by
    simpa [prefixWord, tailWord_1647384, baseEnd_1647384] using wordTrace_append hprefix tailTrace_1647384
  have hstable : (prefixWord ++ tailWord_1647384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647384).length < 2 ^ (prefixWord ++ tailWord_1647384).sum := by decide
  have hdescent : baseEnd_1647384 < baseStart_1647384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647388 : List Nat := [2, 2, 3, 1, 1, 5, 2, 1, 1, 3, 2]
def baseStart_1647388 : Nat := 118140960795 + 1647388 * 2 ^ 59
def prefixEnd_1647388 : Nat := 4983230072969 + 3 ^ 40 * 1647388 * 2
def baseEnd_1647388 : Nat := 845901868449105820573807

theorem tailTrace_1647388 : CollatzResearch.WordTrace tailWord_1647388 prefixEnd_1647388 845901868449105820573807 := by
  unfold tailWord_1647388
  simp only [CollatzResearch.WordTrace]
  refine ⟨30042588277901051157987409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40056784370534734877316545 30042588277901051157987409)
  ·
    refine ⟨22531941208425788368490557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30042588277901051157987409 22531941208425788368490557)
    ·
      refine ⟨8449477953159670638183959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22531941208425788368490557 8449477953159670638183959)
      ·
        refine ⟨12674216929739505957275939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8449477953159670638183959 12674216929739505957275939)
        ·
          refine ⟨19011325394609258935913909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12674216929739505957275939 19011325394609258935913909)
          ·
            refine ⟨1782311755744618025241929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19011325394609258935913909 1782311755744618025241929)
            ·
              refine ⟨1336733816808463518931447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1782311755744618025241929 1336733816808463518931447)
              ·
                refine ⟨2005100725212695278397171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1336733816808463518931447 2005100725212695278397171)
                ·
                  refine ⟨3007651087819042917595757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2005100725212695278397171 3007651087819042917595757)
                  ·
                    refine ⟨1127869157932141094098409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3007651087819042917595757 1127869157932141094098409)
                    ·
                      refine ⟨845901868449105820573807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1127869157932141094098409 845901868449105820573807)
                      ·
                        rfl

theorem cell23_1647388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 2, 1, 1, 3, 2].length) (baseStart_1647388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1647388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1647388 prefixEnd_1647388 := by exact prefixLift 1647388
  have htrace : WordTrace (prefixWord ++ tailWord_1647388) baseStart_1647388 baseEnd_1647388 := by
    simpa [prefixWord, tailWord_1647388, baseEnd_1647388] using wordTrace_append hprefix tailTrace_1647388
  have hstable : (prefixWord ++ tailWord_1647388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647388).length < 2 ^ (prefixWord ++ tailWord_1647388).sum := by decide
  have hdescent : baseEnd_1647388 < baseStart_1647388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647418 : List Nat := [3, 1, 1, 1, 7, 1, 1, 1, 1, 4, 2]
def baseStart_1647418 : Nat := 118140960795 + 1647418 * 2 ^ 59
def prefixEnd_1647418 : Nat := 4983230072969 + 3 ^ 40 * 1647418 * 2
def baseEnd_1647418 : Nat := 845917272868740703198669

theorem tailTrace_1647418 : CollatzResearch.WordTrace tailWord_1647418 prefixEnd_1647418 845917272868740703198669 := by
  unfold tailWord_1647418
  simp only [CollatzResearch.WordTrace]
  refine ⟨15021567686423354359891727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40057513830462278293044605 15021567686423354359891727)
  ·
    refine ⟨22532351529635031539837591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15021567686423354359891727 22532351529635031539837591)
    ·
      refine ⟨33798527294452547309756387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22532351529635031539837591 33798527294452547309756387)
      ·
        refine ⟨50697790941678820964634581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33798527294452547309756387 50697790941678820964634581)
        ·
          refine ⟨1188229475195597366358623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 50697790941678820964634581 1188229475195597366358623)
          ·
            refine ⟨1782344212793396049537935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1188229475195597366358623 1782344212793396049537935)
            ·
              refine ⟨2673516319190094074306903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1782344212793396049537935 2673516319190094074306903)
              ·
                refine ⟨4010274478785141111460355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2673516319190094074306903 4010274478785141111460355)
                ·
                  refine ⟨6015411718177711667190533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4010274478785141111460355 6015411718177711667190533)
                  ·
                    refine ⟨1127889697158320937598225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6015411718177711667190533 1127889697158320937598225)
                    ·
                      refine ⟨845917272868740703198669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1127889697158320937598225 845917272868740703198669)
                      ·
                        rfl

theorem cell23_1647418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 1, 1, 1, 4, 2].length) (baseStart_1647418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1647418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1647418 prefixEnd_1647418 := by exact prefixLift 1647418
  have htrace : WordTrace (prefixWord ++ tailWord_1647418) baseStart_1647418 baseEnd_1647418 := by
    simpa [prefixWord, tailWord_1647418, baseEnd_1647418] using wordTrace_append hprefix tailTrace_1647418
  have hstable : (prefixWord ++ tailWord_1647418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647418).length < 2 ^ (prefixWord ++ tailWord_1647418).sum := by decide
  have hdescent : baseEnd_1647418 < baseStart_1647418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647441 : List Nat := [1, 2, 2, 1, 6, 2, 1, 3, 5]
def baseStart_1647441 : Nat := 118140960795 + 1647441 * 2 ^ 59
def prefixEnd_1647441 : Nat := 4983230072969 + 3 ^ 40 * 1647441 * 2
def baseEnd_1647441 : Nat := 93992120324866012579007

theorem tailTrace_1647441 : CollatzResearch.WordTrace tailWord_1647441 prefixEnd_1647441 93992120324866012579007 := by
  unfold tailWord_1647441
  simp only [CollatzResearch.WordTrace]
  refine ⟨60087109624610092367654177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40058073083073394911769451 60087109624610092367654177)
  ·
    refine ⟨45065332218457569275740633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60087109624610092367654177 45065332218457569275740633)
    ·
      refine ⟨33798999163843176956805475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45065332218457569275740633 33798999163843176956805475)
      ·
        refine ⟨50698498745764765435208213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33798999163843176956805475 50698498745764765435208213)
        ·
          refine ⟨2376492128707723379775385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 50698498745764765435208213 2376492128707723379775385)
          ·
            refine ⟨1782369096530792534831539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2376492128707723379775385 1782369096530792534831539)
            ·
              refine ⟨2673553644796188802247309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1782369096530792534831539 2673553644796188802247309)
              ·
                refine ⟨1002582616798570800842741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2673553644796188802247309 1002582616798570800842741)
                ·
                  refine ⟨93992120324866012579007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1002582616798570800842741 93992120324866012579007)
                  ·
                    rfl

theorem cell23_1647441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 1, 3, 5].length) (baseStart_1647441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1647441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1647441 prefixEnd_1647441 := by exact prefixLift 1647441
  have htrace : WordTrace (prefixWord ++ tailWord_1647441) baseStart_1647441 baseEnd_1647441 := by
    simpa [prefixWord, tailWord_1647441, baseEnd_1647441] using wordTrace_append hprefix tailTrace_1647441
  have hstable : (prefixWord ++ tailWord_1647441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647441).length < 2 ^ (prefixWord ++ tailWord_1647441).sum := by decide
  have hdescent : baseEnd_1647441 < baseStart_1647441 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647458 : List Nat := [3, 3, 2, 1, 3, 1, 3, 2, 5]
def baseStart_1647458 : Nat := 118140960795 + 1647458 * 2 ^ 59
def prefixEnd_1647458 : Nat := 4983230072969 + 3 ^ 40 * 1647458 * 2
def baseEnd_1647458 : Nat := 93993090232768949633165

theorem tailTrace_1647458 : CollatzResearch.WordTrace tailWord_1647458 prefixEnd_1647458 93993090232768949633165 := by
  unfold tailWord_1647458
  simp only [CollatzResearch.WordTrace]
  refine ⟨15021932416387126067755757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40058486443699002847348685 15021932416387126067755757)
  ·
    refine ⟨5633224656145172275408409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15021932416387126067755757 5633224656145172275408409)
    ·
      refine ⟨4224918492108879206556307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5633224656145172275408409 4224918492108879206556307)
      ·
        refine ⟨6337377738163318809834461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4224918492108879206556307 6337377738163318809834461)
        ·
          refine ⟨2376516651811244553687923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6337377738163318809834461 2376516651811244553687923)
          ·
            refine ⟨3564774977716866830531885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2376516651811244553687923 3564774977716866830531885)
            ·
              refine ⟨1336790616643825061449457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3564774977716866830531885 1336790616643825061449457)
              ·
                refine ⟨1002592962482868796087093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1336790616643825061449457 1002592962482868796087093)
                ·
                  refine ⟨93993090232768949633165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1002592962482868796087093 93993090232768949633165)
                  ·
                    rfl

theorem cell23_1647458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 3, 2, 5].length) (baseStart_1647458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1647458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1647458 prefixEnd_1647458 := by exact prefixLift 1647458
  have htrace : WordTrace (prefixWord ++ tailWord_1647458) baseStart_1647458 baseEnd_1647458 := by
    simpa [prefixWord, tailWord_1647458, baseEnd_1647458] using wordTrace_append hprefix tailTrace_1647458
  have hstable : (prefixWord ++ tailWord_1647458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647458).length < 2 ^ (prefixWord ++ tailWord_1647458).sum := by decide
  have hdescent : baseEnd_1647458 < baseStart_1647458 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647474 : List Nat := [3, 2, 1, 2, 1, 1, 2, 3, 2, 4, 2]
def baseStart_1647474 : Nat := 118140960795 + 1647474 * 2 ^ 59
def prefixEnd_1647474 : Nat := 4983230072969 + 3 ^ 40 * 1647474 * 2
def baseEnd_1647474 : Nat := 845946027785392484098411

theorem tailTrace_1647474 : CollatzResearch.WordTrace tailWord_1647474 prefixEnd_1647474 845946027785392484098411 := by
  unfold tailWord_1647474
  simp only [CollatzResearch.WordTrace]
  refine ⟨15022078308372634750901369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40058875488993692669070317 15022078308372634750901369)
  ·
    refine ⟨11266558731279476063176027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15022078308372634750901369 11266558731279476063176027)
    ·
      refine ⟨16899838096919214094764041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11266558731279476063176027 16899838096919214094764041)
      ·
        refine ⟨12674878572689410571073031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16899838096919214094764041 12674878572689410571073031)
        ·
          refine ⟨19012317859034115856609547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12674878572689410571073031 19012317859034115856609547)
          ·
            refine ⟨28518476788551173784914321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19012317859034115856609547 28518476788551173784914321)
            ·
              refine ⟨21388857591413380338685741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28518476788551173784914321 21388857591413380338685741)
              ·
                refine ⟨8020821596780017627007153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21388857591413380338685741 8020821596780017627007153)
                ·
                  refine ⟨6015616197585013220255365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8020821596780017627007153 6015616197585013220255365)
                  ·
                    refine ⟨1127928037047189978797881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6015616197585013220255365 1127928037047189978797881)
                    ·
                      refine ⟨845946027785392484098411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1127928037047189978797881 845946027785392484098411)
                      ·
                        rfl

theorem cell23_1647474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 3, 2, 4, 2].length) (baseStart_1647474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1647474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1647474 prefixEnd_1647474 := by exact prefixLift 1647474
  have htrace : WordTrace (prefixWord ++ tailWord_1647474) baseStart_1647474 baseEnd_1647474 := by
    simpa [prefixWord, tailWord_1647474, baseEnd_1647474] using wordTrace_append hprefix tailTrace_1647474
  have hstable : (prefixWord ++ tailWord_1647474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647474).length < 2 ^ (prefixWord ++ tailWord_1647474).sum := by decide
  have hdescent : baseEnd_1647474 < baseStart_1647474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647480 : List Nat := [2, 1, 2, 1, 1, 1, 1, 4, 10]
def baseStart_1647480 : Nat := 118140960795 + 1647480 * 2 ^ 59
def prefixEnd_1647480 : Nat := 4983230072969 + 3 ^ 40 * 1647480 * 2
def baseEnd_1647480 : Nat := 93994345407702162291487

theorem tailTrace_1647480 : CollatzResearch.WordTrace tailWord_1647480 prefixEnd_1647480 93994345407702162291487 := by
  unfold tailWord_1647480
  simp only [CollatzResearch.WordTrace]
  refine ⟨30044266035734401014161947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40059021380979201352215929 30044266035734401014161947)
  ·
    refine ⟨45066399053601601521242921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30044266035734401014161947 45066399053601601521242921)
    ·
      refine ⟨33799799290201201140932191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45066399053601601521242921 33799799290201201140932191)
      ·
        refine ⟨50699698935301801711398287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33799799290201201140932191 50699698935301801711398287)
        ·
          refine ⟨76049548402952702567097431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50699698935301801711398287 76049548402952702567097431)
          ·
            refine ⟨114074322604429053850646147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76049548402952702567097431 114074322604429053850646147)
            ·
              refine ⟨171111483906643580775969221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114074322604429053850646147 171111483906643580775969221)
              ·
                refine ⟨32083403232495671395494229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 171111483906643580775969221 32083403232495671395494229)
                ·
                  refine ⟨93994345407702162291487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 32083403232495671395494229 93994345407702162291487)
                  ·
                    rfl

theorem cell23_1647480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 10].length) (baseStart_1647480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1647480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1647480 prefixEnd_1647480 := by exact prefixLift 1647480
  have htrace : WordTrace (prefixWord ++ tailWord_1647480) baseStart_1647480 baseEnd_1647480 := by
    simpa [prefixWord, tailWord_1647480, baseEnd_1647480] using wordTrace_append hprefix tailTrace_1647480
  have hstable : (prefixWord ++ tailWord_1647480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647480).length < 2 ^ (prefixWord ++ tailWord_1647480).sum := by decide
  have hdescent : baseEnd_1647480 < baseStart_1647480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647517 : List Nat := [1, 4, 2, 1, 2, 1, 2, 1, 1, 2, 6]
def baseStart_1647517 : Nat := 118140960795 + 1647517 * 2 ^ 59
def prefixEnd_1647517 : Nat := 4983230072969 + 3 ^ 40 * 1647517 * 2
def baseEnd_1647517 : Nat := 845968107453535815860713

theorem tailTrace_1647517 : CollatzResearch.WordTrace tailWord_1647517 prefixEnd_1647517 845968107453535815860713 := by
  unfold tailWord_1647517
  simp only [CollatzResearch.WordTrace]
  refine ⟨60089881572334757347420805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40059921048223171564947203 60089881572334757347420805)
  ·
    refine ⟨11266852794812767002641401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60089881572334757347420805 11266852794812767002641401)
    ·
      refine ⟨8450139596109575251981051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11266852794812767002641401 8450139596109575251981051)
      ·
        refine ⟨12675209394164362877971577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8450139596109575251981051 12675209394164362877971577)
        ·
          refine ⟨9506407045623272158478683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12675209394164362877971577 9506407045623272158478683)
          ·
            refine ⟨14259610568434908237718025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9506407045623272158478683 14259610568434908237718025)
            ·
              refine ⟨10694707926326181178288519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14259610568434908237718025 10694707926326181178288519)
              ·
                refine ⟨16042061889489271767432779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10694707926326181178288519 16042061889489271767432779)
                ·
                  refine ⟨24063092834233907651149169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16042061889489271767432779 24063092834233907651149169)
                  ·
                    refine ⟨18047319625675430738361877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24063092834233907651149169 18047319625675430738361877)
                    ·
                      refine ⟨845968107453535815860713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18047319625675430738361877 845968107453535815860713)
                      ·
                        rfl

theorem cell23_1647517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 1, 1, 2, 6].length) (baseStart_1647517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1647517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1647517 prefixEnd_1647517 := by exact prefixLift 1647517
  have htrace : WordTrace (prefixWord ++ tailWord_1647517) baseStart_1647517 baseEnd_1647517 := by
    simpa [prefixWord, tailWord_1647517, baseEnd_1647517] using wordTrace_append hprefix tailTrace_1647517
  have hstable : (prefixWord ++ tailWord_1647517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647517).length < 2 ^ (prefixWord ++ tailWord_1647517).sum := by decide
  have hdescent : baseEnd_1647517 < baseStart_1647517 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647541 : List Nat := [1, 3, 3, 2, 1, 1, 3, 2, 3, 1, 3]
def baseStart_1647541 : Nat := 118140960795 + 1647541 * 2 ^ 59
def prefixEnd_1647541 : Nat := 4983230072969 + 3 ^ 40 * 1647541 * 2
def baseEnd_1647541 : Nat := 845980430989243721960603

theorem tailTrace_1647541 : CollatzResearch.WordTrace tailWord_1647541 prefixEnd_1647541 845980430989243721960603 := by
  unfold tailWord_1647541
  simp only [CollatzResearch.WordTrace]
  refine ⟨60090756924247809446294477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40060504616165206297529651 60090756924247809446294477)
  ·
    refine ⟨22534033846592928542360429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60090756924247809446294477 22534033846592928542360429)
    ·
      refine ⟨8450262692472348203385161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22534033846592928542360429 8450262692472348203385161)
      ·
        refine ⟨6337697019354261152538871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8450262692472348203385161 6337697019354261152538871)
        ·
          refine ⟨9506545529031391728808307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6337697019354261152538871 9506545529031391728808307)
          ·
            refine ⟨14259818293547087593212461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9506545529031391728808307 14259818293547087593212461)
            ·
              refine ⟨5347431860080157847454673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14259818293547087593212461 5347431860080157847454673)
              ·
                refine ⟨4010573895060118385591005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5347431860080157847454673 4010573895060118385591005)
                ·
                  refine ⟨1503965210647544394596627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4010573895060118385591005 1503965210647544394596627)
                  ·
                    refine ⟨2255947815971316591894941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1503965210647544394596627 2255947815971316591894941)
                    ·
                      refine ⟨845980430989243721960603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2255947815971316591894941 845980430989243721960603)
                      ·
                        rfl

theorem cell23_1647541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 2, 3, 1, 3].length) (baseStart_1647541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1647541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1647541 prefixEnd_1647541 := by exact prefixLift 1647541
  have htrace : WordTrace (prefixWord ++ tailWord_1647541) baseStart_1647541 baseEnd_1647541 := by
    simpa [prefixWord, tailWord_1647541, baseEnd_1647541] using wordTrace_append hprefix tailTrace_1647541
  have hstable : (prefixWord ++ tailWord_1647541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647541).length < 2 ^ (prefixWord ++ tailWord_1647541).sum := by decide
  have hdescent : baseEnd_1647541 < baseStart_1647541 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647542 : List Nat := [5, 1, 4, 1, 1, 2, 1, 1, 2, 1, 4]
def baseStart_1647542 : Nat := 118140960795 + 1647542 * 2 ^ 59
def prefixEnd_1647542 : Nat := 4983230072969 + 3 ^ 40 * 1647542 * 2
def baseEnd_1647542 : Nat := 845980944469898218048099

theorem tailTrace_1647542 : CollatzResearch.WordTrace tailWord_1647542 prefixEnd_1647542 845980944469898218048099 := by
  unfold tailWord_1647542
  simp only [CollatzResearch.WordTrace]
  refine ⟨3755674587327761663567555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40060528931496124411387253 3755674587327761663567555)
  ·
    refine ⟨5633511880991642495351333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3755674587327761663567555 5633511880991642495351333)
    ·
      refine ⟨1056283477685932967878375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5633511880991642495351333 1056283477685932967878375)
      ·
        refine ⟨1584425216528899451817563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1056283477685932967878375 1584425216528899451817563)
        ·
          refine ⟨2376637824793349177726345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1584425216528899451817563 2376637824793349177726345)
          ·
            refine ⟨1782478368595011883294759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2376637824793349177726345 1782478368595011883294759)
            ·
              refine ⟨2673717552892517824942139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1782478368595011883294759 2673717552892517824942139)
              ·
                refine ⟨4010576329338776737413209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2673717552892517824942139 4010576329338776737413209)
                ·
                  refine ⟨3007932247004082553059907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4010576329338776737413209 3007932247004082553059907)
                  ·
                    refine ⟨4511898370506123829589861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3007932247004082553059907 4511898370506123829589861)
                    ·
                      refine ⟨845980944469898218048099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4511898370506123829589861 845980944469898218048099)
                      ·
                        rfl

theorem cell23_1647542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_1647542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1647542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1647542 prefixEnd_1647542 := by exact prefixLift 1647542
  have htrace : WordTrace (prefixWord ++ tailWord_1647542) baseStart_1647542 baseEnd_1647542 := by
    simpa [prefixWord, tailWord_1647542, baseEnd_1647542] using wordTrace_append hprefix tailTrace_1647542
  have hstable : (prefixWord ++ tailWord_1647542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647542).length < 2 ^ (prefixWord ++ tailWord_1647542).sum := by decide
  have hdescent : baseEnd_1647542 < baseStart_1647542 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647547 : List Nat := [1, 1, 1, 1, 1, 2, 2, 2, 7, 1, 4]
def baseStart_1647547 : Nat := 118140960795 + 1647547 * 2 ^ 59
def prefixEnd_1647547 : Nat := 4983230072969 + 3 ^ 40 * 1647547 * 2
def baseEnd_1647547 : Nat := 845983511873170698485575

theorem tailTrace_1647547 : CollatzResearch.WordTrace tailWord_1647547 prefixEnd_1647547 845983511873170698485575 := by
  unfold tailWord_1647547
  simp only [CollatzResearch.WordTrace]
  refine ⟨60090975762226072471012895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40060650508150714980675263 60090975762226072471012895)
  ·
    refine ⟨90136463643339108706519343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60090975762226072471012895 90136463643339108706519343)
    ·
      refine ⟨135204695465008663059779015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90136463643339108706519343 135204695465008663059779015)
      ·
        refine ⟨202807043197512994589668523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135204695465008663059779015 202807043197512994589668523)
        ·
          refine ⟨304210564796269491884502785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202807043197512994589668523 304210564796269491884502785)
          ·
            refine ⟨228157923597202118913377089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 304210564796269491884502785 228157923597202118913377089)
            ·
              refine ⟨171118442697901589185032817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 228157923597202118913377089 171118442697901589185032817)
              ·
                refine ⟨128338832023426191888774613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 171118442697901589185032817 128338832023426191888774613)
                ·
                  refine ⟨3007941375549051372393155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 128338832023426191888774613 3007941375549051372393155)
                  ·
                    refine ⟨4511912063323577058589733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3007941375549051372393155 4511912063323577058589733)
                    ·
                      refine ⟨845983511873170698485575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4511912063323577058589733 845983511873170698485575)
                      ·
                        rfl

theorem cell23_1647547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 7, 1, 4].length) (baseStart_1647547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1647547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1647547 prefixEnd_1647547 := by exact prefixLift 1647547
  have htrace : WordTrace (prefixWord ++ tailWord_1647547) baseStart_1647547 baseEnd_1647547 := by
    simpa [prefixWord, tailWord_1647547, baseEnd_1647547] using wordTrace_append hprefix tailTrace_1647547
  have hstable : (prefixWord ++ tailWord_1647547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647547).length < 2 ^ (prefixWord ++ tailWord_1647547).sum := by decide
  have hdescent : baseEnd_1647547 < baseStart_1647547 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647587 : List Nat := [1, 1, 1, 6, 1, 1, 2, 10]
def baseStart_1647587 : Nat := 118140960795 + 1647587 * 2 ^ 59
def prefixEnd_1647587 : Nat := 4983230072969 + 3 ^ 40 * 1647587 * 2
def baseEnd_1647587 : Nat := 31333483374050020073533

theorem tailTrace_1647587 : CollatzResearch.WordTrace tailWord_1647587 prefixEnd_1647587 31333483374050020073533 := by
  unfold tailWord_1647587
  simp only [CollatzResearch.WordTrace]
  refine ⟨60092434682081159302469015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40061623121387439534979343 60092434682081159302469015)
  ·
    refine ⟨90138652023121738953703523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60092434682081159302469015 90138652023121738953703523)
    ·
      refine ⟨135207978034682608430555285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90138652023121738953703523 135207978034682608430555285)
      ·
        refine ⟨6337873970375747270182279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 135207978034682608430555285 6337873970375747270182279)
        ·
          refine ⟨9506810955563620905273419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6337873970375747270182279 9506810955563620905273419)
          ·
            refine ⟨14260216433345431357910129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9506810955563620905273419 14260216433345431357910129)
            ·
              refine ⟨10695162325009073518432597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14260216433345431357910129 10695162325009073518432597)
              ·
                refine ⟨31333483374050020073533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 10695162325009073518432597 31333483374050020073533)
                ·
                  rfl

theorem cell23_1647587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 10].length) (baseStart_1647587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1647587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1647587 prefixEnd_1647587 := by exact prefixLift 1647587
  have htrace : WordTrace (prefixWord ++ tailWord_1647587) baseStart_1647587 baseEnd_1647587 := by
    simpa [prefixWord, tailWord_1647587, baseEnd_1647587] using wordTrace_append hprefix tailTrace_1647587
  have hstable : (prefixWord ++ tailWord_1647587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647587).length < 2 ^ (prefixWord ++ tailWord_1647587).sum := by decide
  have hdescent : baseEnd_1647587 < baseStart_1647587 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647591 : List Nat := [1, 1, 5, 2, 2, 3, 1, 1, 1, 6]
def baseStart_1647591 : Nat := 118140960795 + 1647591 * 2 ^ 59
def prefixEnd_1647591 : Nat := 4983230072969 + 3 ^ 40 * 1647591 * 2
def baseEnd_1647591 : Nat := 282002035007322842111791

theorem tailTrace_1647591 : CollatzResearch.WordTrace tailWord_1647591 prefixEnd_1647591 282002035007322842111791 := by
  unfold tailWord_1647591
  simp only [CollatzResearch.WordTrace]
  refine ⟨60092580574066667985614627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40061720382711111990409751 60092580574066667985614627)
  ·
    refine ⟨90138870861100001978421941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60092580574066667985614627 90138870861100001978421941)
    ·
      refine ⟨8450519143228125185477057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 90138870861100001978421941 8450519143228125185477057)
      ·
        refine ⟨6337889357421093889107793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8450519143228125185477057 6337889357421093889107793)
        ·
          refine ⟨4753417018065820416830845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6337889357421093889107793 4753417018065820416830845)
          ·
            refine ⟨1782531381774682656311567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4753417018065820416830845 1782531381774682656311567)
            ·
              refine ⟨2673797072662023984467351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1782531381774682656311567 2673797072662023984467351)
              ·
                refine ⟨4010695608993035976701027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2673797072662023984467351 4010695608993035976701027)
                ·
                  refine ⟨6016043413489553965051541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4010695608993035976701027 6016043413489553965051541)
                  ·
                    refine ⟨282002035007322842111791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6016043413489553965051541 282002035007322842111791)
                    ·
                      rfl

theorem cell23_1647591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 1, 1, 1, 6].length) (baseStart_1647591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1647591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1647591 prefixEnd_1647591 := by exact prefixLift 1647591
  have htrace : WordTrace (prefixWord ++ tailWord_1647591) baseStart_1647591 baseEnd_1647591 := by
    simpa [prefixWord, tailWord_1647591, baseEnd_1647591] using wordTrace_append hprefix tailTrace_1647591
  have hstable : (prefixWord ++ tailWord_1647591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647591).length < 2 ^ (prefixWord ++ tailWord_1647591).sum := by decide
  have hdescent : baseEnd_1647591 < baseStart_1647591 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647594 : List Nat := [3, 1, 3, 1, 2, 3, 1, 1, 1, 1, 6]
def baseStart_1647594 : Nat := 118140960795 + 1647594 * 2 ^ 59
def prefixEnd_1647594 : Nat := 4983230072969 + 3 ^ 40 * 1647594 * 2
def baseEnd_1647594 : Nat := 846007645463932014597859

theorem tailTrace_1647594 : CollatzResearch.WordTrace tailWord_1647594 prefixEnd_1647594 846007645463932014597859 := by
  unfold tailWord_1647594
  simp only [CollatzResearch.WordTrace]
  refine ⟨15023172498263949874493459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40061793328703866331982557 15023172498263949874493459)
  ·
    refine ⟨22534758747395924811740189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15023172498263949874493459 22534758747395924811740189)
    ·
      refine ⟨8450534530273471804402571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22534758747395924811740189 8450534530273471804402571)
      ·
        refine ⟨12675801795410207706603857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8450534530273471804402571 12675801795410207706603857)
        ·
          refine ⟨9506851346557655779952893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12675801795410207706603857 9506851346557655779952893)
          ·
            refine ⟨3565069254959120917482335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9506851346557655779952893 3565069254959120917482335)
            ·
              refine ⟨5347603882438681376223503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3565069254959120917482335 5347603882438681376223503)
              ·
                refine ⟨8021405823658022064335255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5347603882438681376223503 8021405823658022064335255)
                ·
                  refine ⟨12032108735487033096502883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8021405823658022064335255 12032108735487033096502883)
                  ·
                    refine ⟨18048163103230549644754325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12032108735487033096502883 18048163103230549644754325)
                    ·
                      refine ⟨846007645463932014597859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18048163103230549644754325 846007645463932014597859)
                      ·
                        rfl

theorem cell23_1647594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 1, 1, 1, 6].length) (baseStart_1647594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1647594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1647594 prefixEnd_1647594 := by exact prefixLift 1647594
  have htrace : WordTrace (prefixWord ++ tailWord_1647594) baseStart_1647594 baseEnd_1647594 := by
    simpa [prefixWord, tailWord_1647594, baseEnd_1647594] using wordTrace_append hprefix tailTrace_1647594
  have hstable : (prefixWord ++ tailWord_1647594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647594).length < 2 ^ (prefixWord ++ tailWord_1647594).sum := by decide
  have hdescent : baseEnd_1647594 < baseStart_1647594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647598 : List Nat := [4, 1, 2, 1, 4, 1, 2, 2, 1, 1, 4]
def baseStart_1647598 : Nat := 118140960795 + 1647598 * 2 ^ 59
def prefixEnd_1647598 : Nat := 4983230072969 + 3 ^ 40 * 1647598 * 2
def baseEnd_1647598 : Nat := 846009699386549998947841

theorem tailTrace_1647598 : CollatzResearch.WordTrace tailWord_1647598 prefixEnd_1647598 846009699386549998947841 := by
  unfold tailWord_1647598
  simp only [CollatzResearch.WordTrace]
  refine ⟨7511604485630163522639931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40061890590027538787412965 7511604485630163522639931)
  ·
    refine ⟨11267406728445245283959897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7511604485630163522639931 11267406728445245283959897)
    ·
      refine ⟨8450555046333933962969923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11267406728445245283959897 8450555046333933962969923)
      ·
        refine ⟨12675832569500900944454885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8450555046333933962969923 12675832569500900944454885)
        ·
          refine ⟨2376718606781418927085291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12675832569500900944454885 2376718606781418927085291)
          ·
            refine ⟨3565077910172128390627937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2376718606781418927085291 3565077910172128390627937)
            ·
              refine ⟨2673808432629096292970953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3565077910172128390627937 2673808432629096292970953)
              ·
                refine ⟨2005356324471822219728215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2673808432629096292970953 2005356324471822219728215)
                ·
                  refine ⟨3008034486707733329592323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2005356324471822219728215 3008034486707733329592323)
                  ·
                    refine ⟨4512051730061599994388485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3008034486707733329592323 4512051730061599994388485)
                    ·
                      refine ⟨846009699386549998947841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4512051730061599994388485 846009699386549998947841)
                      ·
                        rfl

theorem cell23_1647598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 2, 2, 1, 1, 4].length) (baseStart_1647598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1647598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1647598 prefixEnd_1647598 := by exact prefixLift 1647598
  have htrace : WordTrace (prefixWord ++ tailWord_1647598) baseStart_1647598 baseEnd_1647598 := by
    simpa [prefixWord, tailWord_1647598, baseEnd_1647598] using wordTrace_append hprefix tailTrace_1647598
  have hstable : (prefixWord ++ tailWord_1647598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647598).length < 2 ^ (prefixWord ++ tailWord_1647598).sum := by decide
  have hdescent : baseEnd_1647598 < baseStart_1647598 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647601 : List Nat := [1, 2, 2, 2, 4, 1, 1, 4, 1, 2, 3]
def baseStart_1647601 : Nat := 118140960795 + 1647601 * 2 ^ 59
def prefixEnd_1647601 : Nat := 4983230072969 + 3 ^ 40 * 1647601 * 2
def baseEnd_1647601 : Nat := 846011239828513487210327

theorem tailTrace_1647601 : CollatzResearch.WordTrace tailWord_1647601 prefixEnd_1647601 846011239828513487210327 := by
  unfold tailWord_1647601
  simp only [CollatzResearch.WordTrace]
  refine ⟨60092945304030439693478657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40061963536020293128985771 60092945304030439693478657)
  ·
    refine ⟨45069708978022829770108993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60092945304030439693478657 45069708978022829770108993)
    ·
      refine ⟨33802281733517122327581745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45069708978022829770108993 33802281733517122327581745)
      ·
        refine ⟨25351711300137841745686309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33802281733517122327581745 25351711300137841745686309)
        ·
          refine ⟨4753445868775845327316183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25351711300137841745686309 4753445868775845327316183)
          ·
            refine ⟨7130168803163767990974275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4753445868775845327316183 7130168803163767990974275)
            ·
              refine ⟨10695253204745651986461413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7130168803163767990974275 10695253204745651986461413)
              ·
                refine ⟨2005359975889809747461515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10695253204745651986461413 2005359975889809747461515)
                ·
                  refine ⟨3008039963834714621192273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2005359975889809747461515 3008039963834714621192273)
                  ·
                    refine ⟨2256029972876035965894205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3008039963834714621192273 2256029972876035965894205)
                    ·
                      refine ⟨846011239828513487210327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2256029972876035965894205 846011239828513487210327)
                      ·
                        rfl

theorem cell23_1647601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 4, 1, 2, 3].length) (baseStart_1647601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1647601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1647601 prefixEnd_1647601 := by exact prefixLift 1647601
  have htrace : WordTrace (prefixWord ++ tailWord_1647601) baseStart_1647601 baseEnd_1647601 := by
    simpa [prefixWord, tailWord_1647601, baseEnd_1647601] using wordTrace_append hprefix tailTrace_1647601
  have hstable : (prefixWord ++ tailWord_1647601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647601).length < 2 ^ (prefixWord ++ tailWord_1647601).sum := by decide
  have hdescent : baseEnd_1647601 < baseStart_1647601 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647657 : List Nat := [1, 2, 1, 1, 1, 1, 1, 1, 2, 7, 5]
def baseStart_1647657 : Nat := 118140960795 + 1647657 * 2 ^ 59
def prefixEnd_1647657 : Nat := 4983230072969 + 3 ^ 40 * 1647657 * 2
def baseEnd_1647657 : Nat := 846039994745165268110069

theorem tailTrace_1647657 : CollatzResearch.WordTrace tailWord_1647657 prefixEnd_1647657 846039994745165268110069 := by
  unfold tailWord_1647657
  simp only [CollatzResearch.WordTrace]
  refine ⟨60094987791827561257517225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40063325194551707505011483 60094987791827561257517225)
  ·
    refine ⟨45071240843870670943137919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60094987791827561257517225 45071240843870670943137919)
    ·
      refine ⟨67606861265806006414706879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45071240843870670943137919 67606861265806006414706879)
      ·
        refine ⟨101410291898709009622060319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67606861265806006414706879 101410291898709009622060319)
        ·
          refine ⟨152115437848063514433090479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101410291898709009622060319 152115437848063514433090479)
          ·
            refine ⟨228173156772095271649635719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152115437848063514433090479 228173156772095271649635719)
            ·
              refine ⟨342259735158142907474453579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 228173156772095271649635719 342259735158142907474453579)
              ·
                refine ⟨513389602737214361211680369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 342259735158142907474453579 513389602737214361211680369)
                ·
                  refine ⟨385042202052910770908760277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 513389602737214361211680369 385042202052910770908760277)
                  ·
                    refine ⟨9024426610615096193174069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 385042202052910770908760277 9024426610615096193174069)
                    ·
                      refine ⟨846039994745165268110069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9024426610615096193174069 846039994745165268110069)
                      ·
                        rfl

theorem cell23_1647657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 7, 5].length) (baseStart_1647657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1647657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1647657 prefixEnd_1647657 := by exact prefixLift 1647657
  have htrace : WordTrace (prefixWord ++ tailWord_1647657) baseStart_1647657 baseEnd_1647657 := by
    simpa [prefixWord, tailWord_1647657, baseEnd_1647657] using wordTrace_append hprefix tailTrace_1647657
  have hstable : (prefixWord ++ tailWord_1647657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647657).length < 2 ^ (prefixWord ++ tailWord_1647657).sum := by decide
  have hdescent : baseEnd_1647657 < baseStart_1647657 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647674 : List Nat := [3, 1, 1, 1, 3, 1, 4, 1, 2, 1, 5]
def baseStart_1647674 : Nat := 118140960795 + 1647674 * 2 ^ 59
def prefixEnd_1647674 : Nat := 4983230072969 + 3 ^ 40 * 1647674 * 2
def baseEnd_1647674 : Nat := 846048723916291701597491

theorem tailTrace_1647674 : CollatzResearch.WordTrace tailWord_1647674 prefixEnd_1647674 846048723916291701597491 := by
  unfold tailWord_1647674
  simp only [CollatzResearch.WordTrace]
  refine ⟨15023901958191493290221519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40063738555177315440590717 15023901958191493290221519)
  ·
    refine ⟨22535852937287239935332279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15023901958191493290221519 22535852937287239935332279)
    ·
      refine ⟨33803779405930859902998419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22535852937287239935332279 33803779405930859902998419)
      ·
        refine ⟨50705669108896289854497629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33803779405930859902998419 50705669108896289854497629)
        ·
          refine ⟨19014625915836108695436611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50705669108896289854497629 19014625915836108695436611)
          ·
            refine ⟨28521938873754163043154917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19014625915836108695436611 28521938873754163043154917)
            ·
              refine ⟨5347863538828905570591547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28521938873754163043154917 5347863538828905570591547)
              ·
                refine ⟨8021795308243358355887321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5347863538828905570591547 8021795308243358355887321)
                ·
                  refine ⟨6016346481182518766915491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8021795308243358355887321 6016346481182518766915491)
                  ·
                    refine ⟨9024519721773778150373237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6016346481182518766915491 9024519721773778150373237)
                    ·
                      refine ⟨846048723916291701597491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9024519721773778150373237 846048723916291701597491)
                      ·
                        rfl

theorem cell23_1647674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 1, 2, 1, 5].length) (baseStart_1647674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1647674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1647674 prefixEnd_1647674 := by exact prefixLift 1647674
  have htrace : WordTrace (prefixWord ++ tailWord_1647674) baseStart_1647674 baseEnd_1647674 := by
    simpa [prefixWord, tailWord_1647674, baseEnd_1647674] using wordTrace_append hprefix tailTrace_1647674
  have hstable : (prefixWord ++ tailWord_1647674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647674).length < 2 ^ (prefixWord ++ tailWord_1647674).sum := by decide
  have hdescent : baseEnd_1647674 < baseStart_1647674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647694 : List Nat := [4, 1, 1, 1, 1, 3, 2, 3, 7]
def baseStart_1647694 : Nat := 118140960795 + 1647694 * 2 ^ 59
def prefixEnd_1647694 : Nat := 4983230072969 + 3 ^ 40 * 1647694 * 2
def baseEnd_1647694 : Nat := 94006554836597958149711

theorem tailTrace_1647694 : CollatzResearch.WordTrace tailWord_1647694 prefixEnd_1647694 94006554836597958149711 := by
  unfold tailWord_1647694
  simp only [CollatzResearch.WordTrace]
  refine ⟨7512042161586689572076767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40064224861795677717742757 7512042161586689572076767)
  ·
    refine ⟨11268063242380034358115151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7512042161586689572076767 11268063242380034358115151)
    ·
      refine ⟨16902094863570051537172727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11268063242380034358115151 16902094863570051537172727)
      ·
        refine ⟨25353142295355077305759091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16902094863570051537172727 25353142295355077305759091)
        ·
          refine ⟨38029713443032615958638637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25353142295355077305759091 38029713443032615958638637)
          ·
            refine ⟨14261142541137230984489489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38029713443032615958638637 14261142541137230984489489)
            ·
              refine ⟨10695856905852923238367117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14261142541137230984489489 10695856905852923238367117)
              ·
                refine ⟨4010946339694846214387669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10695856905852923238367117 4010946339694846214387669)
                ·
                  refine ⟨94006554836597958149711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4010946339694846214387669 94006554836597958149711)
                  ·
                    rfl

theorem cell23_1647694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 3, 7].length) (baseStart_1647694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1647694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1647694 prefixEnd_1647694 := by exact prefixLift 1647694
  have htrace : WordTrace (prefixWord ++ tailWord_1647694) baseStart_1647694 baseEnd_1647694 := by
    simpa [prefixWord, tailWord_1647694, baseEnd_1647694] using wordTrace_append hprefix tailTrace_1647694
  have hstable : (prefixWord ++ tailWord_1647694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647694).length < 2 ^ (prefixWord ++ tailWord_1647694).sum := by decide
  have hdescent : baseEnd_1647694 < baseStart_1647694 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647724 : List Nat := [2, 2, 1, 1, 3, 2, 3, 1, 1, 7]
def baseStart_1647724 : Nat := 118140960795 + 1647724 * 2 ^ 59
def prefixEnd_1647724 : Nat := 4983230072969 + 3 ^ 40 * 1647724 * 2
def baseEnd_1647724 : Nat := 282024799316338835324087

theorem tailTrace_1647724 : CollatzResearch.WordTrace tailWord_1647724 prefixEnd_1647724 282024799316338835324087 := by
  unfold tailWord_1647724
  simp only [CollatzResearch.WordTrace]
  refine ⟨30048715741292415850103113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40064954321723221133470817 30048715741292415850103113)
  ·
    refine ⟨22536536805969311887577335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30048715741292415850103113 22536536805969311887577335)
    ·
      refine ⟨33804805208953967831366003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22536536805969311887577335 33804805208953967831366003)
      ·
        refine ⟨50707207813430951747049005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33804805208953967831366003 50707207813430951747049005)
        ·
          refine ⟨19015202930036606905143377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50707207813430951747049005 19015202930036606905143377)
          ·
            refine ⟨14261402197527455178857533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19015202930036606905143377 14261402197527455178857533)
            ·
              refine ⟨5348025824072795692071575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14261402197527455178857533 5348025824072795692071575)
              ·
                refine ⟨8022038736109193538107363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5348025824072795692071575 8022038736109193538107363)
                ·
                  refine ⟨12033058104163790307161045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8022038736109193538107363 12033058104163790307161045)
                  ·
                    refine ⟨282024799316338835324087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12033058104163790307161045 282024799316338835324087)
                    ·
                      rfl

theorem cell23_1647724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 7].length) (baseStart_1647724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1647724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1647724 prefixEnd_1647724 := by exact prefixLift 1647724
  have htrace : WordTrace (prefixWord ++ tailWord_1647724) baseStart_1647724 baseEnd_1647724 := by
    simpa [prefixWord, tailWord_1647724, baseEnd_1647724] using wordTrace_append hprefix tailTrace_1647724
  have hstable : (prefixWord ++ tailWord_1647724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647724).length < 2 ^ (prefixWord ++ tailWord_1647724).sum := by decide
  have hdescent : baseEnd_1647724 < baseStart_1647724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647781 : List Nat := [1, 3, 1, 2, 1, 4, 2, 1, 1, 4, 3]
def baseStart_1647781 : Nat := 118140960795 + 1647781 * 2 ^ 59
def prefixEnd_1647781 : Nat := 4983230072969 + 3 ^ 40 * 1647781 * 2
def baseEnd_1647781 : Nat := 846103666346322782959499

theorem tailTrace_1647781 : CollatzResearch.WordTrace tailWord_1647781 prefixEnd_1647781 846103666346322782959499 := by
  unfold tailWord_1647781
  simp only [CollatzResearch.WordTrace]
  refine ⟨60099510443378330435031197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40066340295585553623354131 60099510443378330435031197)
  ·
    refine ⟨22537316416266873913136699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60099510443378330435031197 22537316416266873913136699)
    ·
      refine ⟨33805974624400310869705049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22537316416266873913136699 33805974624400310869705049)
      ·
        refine ⟨25354480968300233152278787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33805974624400310869705049 25354480968300233152278787)
        ·
          refine ⟨38031721452450349728418181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25354480968300233152278787 38031721452450349728418181)
          ·
            refine ⟨7130947772334440574078409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38031721452450349728418181 7130947772334440574078409)
            ·
              refine ⟨5348210829250830430558807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7130947772334440574078409 5348210829250830430558807)
              ·
                refine ⟨8022316243876245645838211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5348210829250830430558807 8022316243876245645838211)
                ·
                  refine ⟨12033474365814368468757317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8022316243876245645838211 12033474365814368468757317)
                  ·
                    refine ⟨2256276443590194087891997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12033474365814368468757317 2256276443590194087891997)
                    ·
                      refine ⟨846103666346322782959499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2256276443590194087891997 846103666346322782959499)
                      ·
                        rfl

theorem cell23_1647781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 1, 1, 4, 3].length) (baseStart_1647781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1647781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1647781 prefixEnd_1647781 := by exact prefixLift 1647781
  have htrace : WordTrace (prefixWord ++ tailWord_1647781) baseStart_1647781 baseEnd_1647781 := by
    simpa [prefixWord, tailWord_1647781, baseEnd_1647781] using wordTrace_append hprefix tailTrace_1647781
  have hstable : (prefixWord ++ tailWord_1647781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647781).length < 2 ^ (prefixWord ++ tailWord_1647781).sum := by decide
  have hdescent : baseEnd_1647781 < baseStart_1647781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647788 : List Nat := [2, 2, 1, 1, 1, 1, 1, 9, 1, 4]
def baseStart_1647788 : Nat := 118140960795 + 1647788 * 2 ^ 59
def prefixEnd_1647788 : Nat := 4983230072969 + 3 ^ 40 * 1647788 * 2
def baseEnd_1647788 : Nat := 282035753570301418523989

theorem tailTrace_1647788 : CollatzResearch.WordTrace tailWord_1647788 prefixEnd_1647788 282035753570301418523989 := by
  unfold tailWord_1647788
  simp only [CollatzResearch.WordTrace]
  refine ⟨30049882877176485315268009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40066510502901980420357345 30049882877176485315268009)
  ·
    refine ⟨22537412157882363986451007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30049882877176485315268009 22537412157882363986451007)
    ·
      refine ⟨33806118236823545979676511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22537412157882363986451007 33806118236823545979676511)
      ·
        refine ⟨50709177355235318969514767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33806118236823545979676511 50709177355235318969514767)
        ·
          refine ⟨76063766032852978454272151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50709177355235318969514767 76063766032852978454272151)
          ·
            refine ⟨114095649049279467681408227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76063766032852978454272151 114095649049279467681408227)
            ·
              refine ⟨171143473573919201522112341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114095649049279467681408227 171143473573919201522112341)
              ·
                refine ⟨1002793790472182821418627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 171143473573919201522112341 1002793790472182821418627)
                ·
                  refine ⟨1504190685708274232127941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1002793790472182821418627 1504190685708274232127941)
                  ·
                    refine ⟨282035753570301418523989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1504190685708274232127941 282035753570301418523989)
                    ·
                      rfl

theorem cell23_1647788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 9, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 9, 1, 4].length) (baseStart_1647788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1647788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1647788 prefixEnd_1647788 := by exact prefixLift 1647788
  have htrace : WordTrace (prefixWord ++ tailWord_1647788) baseStart_1647788 baseEnd_1647788 := by
    simpa [prefixWord, tailWord_1647788, baseEnd_1647788] using wordTrace_append hprefix tailTrace_1647788
  have hstable : (prefixWord ++ tailWord_1647788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647788).length < 2 ^ (prefixWord ++ tailWord_1647788).sum := by decide
  have hdescent : baseEnd_1647788 < baseStart_1647788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647818 : List Nat := [3, 1, 2, 1, 3, 2, 4, 1, 6]
def baseStart_1647818 : Nat := 118140960795 + 1647818 * 2 ^ 59
def prefixEnd_1647818 : Nat := 4983230072969 + 3 ^ 40 * 1647818 * 2
def baseEnd_1647818 : Nat := 94013629458948793132981

theorem tailTrace_1647818 : CollatzResearch.WordTrace tailWord_1647818 prefixEnd_1647818 94013629458948793132981 := by
  unfold tailWord_1647818
  simp only [CollatzResearch.WordTrace]
  refine ⟨15025214986061071438532027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40067239962829523836085405 15025214986061071438532027)
  ·
    refine ⟨22537822479091607157798041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15025214986061071438532027 22537822479091607157798041)
    ·
      refine ⟨16903366859318705368348531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22537822479091607157798041 16903366859318705368348531)
      ·
        refine ⟨25355050288978058052522797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16903366859318705368348531 25355050288978058052522797)
        ·
          refine ⟨9508143858366771769696049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25355050288978058052522797 9508143858366771769696049)
          ·
            refine ⟨7131107893775078827272037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9508143858366771769696049 7131107893775078827272037)
            ·
              refine ⟨1337082730082827280113507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7131107893775078827272037 1337082730082827280113507)
              ·
                refine ⟨2005624095124240920170261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1337082730082827280113507 2005624095124240920170261)
                ·
                  refine ⟨94013629458948793132981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2005624095124240920170261 94013629458948793132981)
                  ·
                    rfl

theorem cell23_1647818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 4, 1, 6].length) (baseStart_1647818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1647818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1647818 prefixEnd_1647818 := by exact prefixLift 1647818
  have htrace : WordTrace (prefixWord ++ tailWord_1647818) baseStart_1647818 baseEnd_1647818 := by
    simpa [prefixWord, tailWord_1647818, baseEnd_1647818] using wordTrace_append hprefix tailTrace_1647818
  have hstable : (prefixWord ++ tailWord_1647818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647818).length < 2 ^ (prefixWord ++ tailWord_1647818).sum := by decide
  have hdescent : baseEnd_1647818 < baseStart_1647818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647898 : List Nat := [3, 1, 1, 3, 3, 1, 2, 2, 1, 2, 4]
def baseStart_1647898 : Nat := 118140960795 + 1647898 * 2 ^ 59
def prefixEnd_1647898 : Nat := 4983230072969 + 3 ^ 40 * 1647898 * 2
def baseEnd_1647898 : Nat := 846163743582898825196461

theorem tailTrace_1647898 : CollatzResearch.WordTrace tailWord_1647898 prefixEnd_1647898 846163743582898825196461 := by
  unfold tailWord_1647898
  simp only [CollatzResearch.WordTrace]
  refine ⟨15025944445988614854260087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40069185189302972944693565 15025944445988614854260087)
  ·
    refine ⟨22538916668982922281390131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15025944445988614854260087 22538916668982922281390131)
    ·
      refine ⟨33808375003474383422085197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22538916668982922281390131 33808375003474383422085197)
      ·
        refine ⟨12678140626302893783281949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33808375003474383422085197 12678140626302893783281949)
        ·
          refine ⟨4754302734863585168730731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12678140626302893783281949 4754302734863585168730731)
          ·
            refine ⟨7131454102295377753096097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4754302734863585168730731 7131454102295377753096097)
            ·
              refine ⟨5348590576721533314822073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7131454102295377753096097 5348590576721533314822073)
              ·
                refine ⟨4011442932541149986116555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5348590576721533314822073 4011442932541149986116555)
                ·
                  refine ⟨6017164398811724979174833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4011442932541149986116555 6017164398811724979174833)
                  ·
                    refine ⟨4512873299108793734381125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6017164398811724979174833 4512873299108793734381125)
                    ·
                      refine ⟨846163743582898825196461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4512873299108793734381125 846163743582898825196461)
                      ·
                        rfl

theorem cell23_1647898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 2, 1, 2, 4].length) (baseStart_1647898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1647898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1647898 prefixEnd_1647898 := by exact prefixLift 1647898
  have htrace : WordTrace (prefixWord ++ tailWord_1647898) baseStart_1647898 baseEnd_1647898 := by
    simpa [prefixWord, tailWord_1647898, baseEnd_1647898] using wordTrace_append hprefix tailTrace_1647898
  have hstable : (prefixWord ++ tailWord_1647898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647898).length < 2 ^ (prefixWord ++ tailWord_1647898).sum := by decide
  have hdescent : baseEnd_1647898 < baseStart_1647898 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647912 : List Nat := [2, 1, 5, 1, 2, 3, 1, 2, 2, 4]
def baseStart_1647912 : Nat := 118140960795 + 1647912 * 2 ^ 59
def prefixEnd_1647912 : Nat := 4983230072969 + 3 ^ 40 * 1647912 * 2
def baseEnd_1647912 : Nat := 282056977437353923473799

theorem tailTrace_1647912 : CollatzResearch.WordTrace tailWord_1647912 prefixEnd_1647912 282056977437353923473799 := by
  unfold tailWord_1647912
  simp only [CollatzResearch.WordTrace]
  refine ⟨30052144202951869904024995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40069525603935826538699993 30052144202951869904024995)
  ·
    refine ⟨45078216304427804856037493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30052144202951869904024995 45078216304427804856037493)
    ·
      refine ⟨4226082778540106705253515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 45078216304427804856037493 4226082778540106705253515)
      ·
        refine ⟨6339124167810160057880273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4226082778540106705253515 6339124167810160057880273)
        ·
          refine ⟨4754343125857620043410205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6339124167810160057880273 4754343125857620043410205)
          ·
            refine ⟨1782878672196607516278827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4754343125857620043410205 1782878672196607516278827)
            ·
              refine ⟨2674318008294911274418241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1782878672196607516278827 2674318008294911274418241)
              ·
                refine ⟨2005738506221183455813681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2674318008294911274418241 2005738506221183455813681)
                ·
                  refine ⟨1504303879665887591860261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2005738506221183455813681 1504303879665887591860261)
                  ·
                    refine ⟨282056977437353923473799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1504303879665887591860261 282056977437353923473799)
                    ·
                      rfl

theorem cell23_1647912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 1, 2, 2, 4].length) (baseStart_1647912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1647912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1647912 prefixEnd_1647912 := by exact prefixLift 1647912
  have htrace : WordTrace (prefixWord ++ tailWord_1647912) baseStart_1647912 baseEnd_1647912 := by
    simpa [prefixWord, tailWord_1647912, baseEnd_1647912] using wordTrace_append hprefix tailTrace_1647912
  have hstable : (prefixWord ++ tailWord_1647912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647912).length < 2 ^ (prefixWord ++ tailWord_1647912).sum := by decide
  have hdescent : baseEnd_1647912 < baseStart_1647912 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647935 : List Nat := [1, 1, 2, 2, 4, 4, 1, 1, 1, 3, 3]
def baseStart_1647935 : Nat := 118140960795 + 1647935 * 2 ^ 59
def prefixEnd_1647935 : Nat := 4983230072969 + 3 ^ 40 * 1647935 * 2
def baseEnd_1647935 : Nat := 846182742367115180433791

theorem tailTrace_1647935 : CollatzResearch.WordTrace tailWord_1647935 prefixEnd_1647935 846182742367115180433791 := by
  unfold tailWord_1647935
  simp only [CollatzResearch.WordTrace]
  refine ⟨60105127284820414736137259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40070084856546943157424839 60105127284820414736137259)
  ·
    refine ⟨90157690927230622104205889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60105127284820414736137259 90157690927230622104205889)
    ·
      refine ⟨67618268195422966578154417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90157690927230622104205889 67618268195422966578154417)
      ·
        refine ⟨50713701146567224933615813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67618268195422966578154417 50713701146567224933615813)
        ·
          refine ⟨9508818964981354675052965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50713701146567224933615813 9508818964981354675052965)
          ·
            refine ⟨1782903555934004001572431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9508818964981354675052965 1782903555934004001572431)
            ·
              refine ⟨2674355333901006002358647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1782903555934004001572431 2674355333901006002358647)
              ·
                refine ⟨4011533000851509003537971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2674355333901006002358647 4011533000851509003537971)
                ·
                  refine ⟨6017299501277263505306957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4011533000851509003537971 6017299501277263505306957)
                  ·
                    refine ⟨2256487312978973814490109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6017299501277263505306957 2256487312978973814490109)
                    ·
                      refine ⟨846182742367115180433791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2256487312978973814490109 846182742367115180433791)
                      ·
                        rfl

theorem cell23_1647935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 1, 1, 1, 3, 3].length) (baseStart_1647935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1647935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1647935 prefixEnd_1647935 := by exact prefixLift 1647935
  have htrace : WordTrace (prefixWord ++ tailWord_1647935) baseStart_1647935 baseEnd_1647935 := by
    simpa [prefixWord, tailWord_1647935, baseEnd_1647935] using wordTrace_append hprefix tailTrace_1647935
  have hstable : (prefixWord ++ tailWord_1647935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647935).length < 2 ^ (prefixWord ++ tailWord_1647935).sum := by decide
  have hdescent : baseEnd_1647935 < baseStart_1647935 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647941 : List Nat := [1, 3, 1, 1, 1, 2, 1, 4, 2, 3, 4]
def baseStart_1647941 : Nat := 118140960795 + 1647941 * 2 ^ 59
def prefixEnd_1647941 : Nat := 4983230072969 + 3 ^ 40 * 1647941 * 2
def baseEnd_1647941 : Nat := 846185823251042156958763

theorem tailTrace_1647941 : CollatzResearch.WordTrace tailWord_1647941 prefixEnd_1647941 846185823251042156958763 := by
  unfold tailWord_1647941
  simp only [CollatzResearch.WordTrace]
  refine ⟨60105346122798677760855677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40070230748532451840570451 60105346122798677760855677)
  ·
    refine ⟨22539504796049504160320879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60105346122798677760855677 22539504796049504160320879)
    ·
      refine ⟨33809257194074256240481319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22539504796049504160320879 33809257194074256240481319)
      ·
        refine ⟨50713885791111384360721979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33809257194074256240481319 50713885791111384360721979)
        ·
          refine ⟨76070828686667076541082969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50713885791111384360721979 76070828686667076541082969)
          ·
            refine ⟨57053121515000307405812227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76070828686667076541082969 57053121515000307405812227)
            ·
              refine ⟨85579682272500461108718341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57053121515000307405812227 85579682272500461108718341)
              ·
                refine ⟨16046190426093836457884689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 85579682272500461108718341 16046190426093836457884689)
                ·
                  refine ⟨12034642819570377343413517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16046190426093836457884689 12034642819570377343413517)
                  ·
                    refine ⟨4512991057338891503780069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12034642819570377343413517 4512991057338891503780069)
                    ·
                      refine ⟨846185823251042156958763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4512991057338891503780069 846185823251042156958763)
                      ·
                        rfl

theorem cell23_1647941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 4, 2, 3, 4].length) (baseStart_1647941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1647941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1647941 prefixEnd_1647941 := by exact prefixLift 1647941
  have htrace : WordTrace (prefixWord ++ tailWord_1647941) baseStart_1647941 baseEnd_1647941 := by
    simpa [prefixWord, tailWord_1647941, baseEnd_1647941] using wordTrace_append hprefix tailTrace_1647941
  have hstable : (prefixWord ++ tailWord_1647941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647941).length < 2 ^ (prefixWord ++ tailWord_1647941).sum := by decide
  have hdescent : baseEnd_1647941 < baseStart_1647941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647942 : List Nat := [6, 1, 1, 3, 1, 1, 1, 9]
def baseStart_1647942 : Nat := 118140960795 + 1647942 * 2 ^ 59
def prefixEnd_1647942 : Nat := 4983230072969 + 3 ^ 40 * 1647942 * 2
def baseEnd_1647942 : Nat := 31340234693766542705417

theorem tailTrace_1647942 : CollatzResearch.WordTrace tailWord_1647942 prefixEnd_1647942 31340234693766542705417 := by
  unfold tailWord_1647942
  simp only [CollatzResearch.WordTrace]
  refine ⟨1878293206118595466613815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 40070255063863369954428053 1878293206118595466613815)
  ·
    refine ⟨2817439809177893199920723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1878293206118595466613815 2817439809177893199920723)
    ·
      refine ⟨4226159713766839799881085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2817439809177893199920723 4226159713766839799881085)
      ·
        refine ⟨1584809892662564924955407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4226159713766839799881085 1584809892662564924955407)
        ·
          refine ⟨2377214838993847387433111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1584809892662564924955407 2377214838993847387433111)
          ·
            refine ⟨3565822258490771081149667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2377214838993847387433111 3565822258490771081149667)
            ·
              refine ⟨5348733387736156621724501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3565822258490771081149667 5348733387736156621724501)
              ·
                refine ⟨31340234693766542705417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5348733387736156621724501 31340234693766542705417)
                ·
                  rfl

theorem cell23_1647942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 9].length) (baseStart_1647942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1647942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1647942 prefixEnd_1647942 := by exact prefixLift 1647942
  have htrace : WordTrace (prefixWord ++ tailWord_1647942) baseStart_1647942 baseEnd_1647942 := by
    simpa [prefixWord, tailWord_1647942, baseEnd_1647942] using wordTrace_append hprefix tailTrace_1647942
  have hstable : (prefixWord ++ tailWord_1647942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647942).length < 2 ^ (prefixWord ++ tailWord_1647942).sum := by decide
  have hdescent : baseEnd_1647942 < baseStart_1647942 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647945 : List Nat := [1, 2, 1, 1, 2, 3, 3, 4, 1, 3, 2]
def baseStart_1647945 : Nat := 118140960795 + 1647945 * 2 ^ 59
def prefixEnd_1647945 : Nat := 4983230072969 + 3 ^ 40 * 1647945 * 2
def baseEnd_1647945 : Nat := 846187877173660141308745

theorem tailTrace_1647945 : CollatzResearch.WordTrace tailWord_1647945 prefixEnd_1647945 846187877173660141308745 := by
  unfold tailWord_1647945
  simp only [CollatzResearch.WordTrace]
  refine ⟨60105492014784186444001289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40070328009856124296000859 60105492014784186444001289)
  ·
    refine ⟨45079119011088139833000967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60105492014784186444001289 45079119011088139833000967)
    ·
      refine ⟨67618678516632209749501451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45079119011088139833000967 67618678516632209749501451)
      ·
        refine ⟨101428017774948314624252177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67618678516632209749501451 101428017774948314624252177)
        ·
          refine ⟨76071013331211235968189133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101428017774948314624252177 76071013331211235968189133)
          ·
            refine ⟨28526629999204213488070925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76071013331211235968189133 28526629999204213488070925)
            ·
              refine ⟨10697486249701580058026597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28526629999204213488070925 10697486249701580058026597)
              ·
                refine ⟨2005778671819046260879987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10697486249701580058026597 2005778671819046260879987)
                ·
                  refine ⟨3008668007728569391319981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2005778671819046260879987 3008668007728569391319981)
                  ·
                    refine ⟨1128250502898213521744993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3008668007728569391319981 1128250502898213521744993)
                    ·
                      refine ⟨846187877173660141308745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1128250502898213521744993 846187877173660141308745)
                      ·
                        rfl

theorem cell23_1647945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 4, 1, 3, 2].length) (baseStart_1647945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1647945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1647945 prefixEnd_1647945 := by exact prefixLift 1647945
  have htrace : WordTrace (prefixWord ++ tailWord_1647945) baseStart_1647945 baseEnd_1647945 := by
    simpa [prefixWord, tailWord_1647945, baseEnd_1647945] using wordTrace_append hprefix tailTrace_1647945
  have hstable : (prefixWord ++ tailWord_1647945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647945).length < 2 ^ (prefixWord ++ tailWord_1647945).sum := by decide
  have hdescent : baseEnd_1647945 < baseStart_1647945 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1647961 : List Nat := [1, 2, 1, 2, 2, 2, 3, 1, 1, 3, 5]
def baseStart_1647961 : Nat := 118140960795 + 1647961 * 2 ^ 59
def prefixEnd_1647961 : Nat := 4983230072969 + 3 ^ 40 * 1647961 * 2
def baseEnd_1647961 : Nat := 846196092864132078708671

theorem tailTrace_1647961 : CollatzResearch.WordTrace tailWord_1647961 prefixEnd_1647961 846196092864132078708671 := by
  unfold tailWord_1647961
  simp only [CollatzResearch.WordTrace]
  refine ⟨60106075582726221176583737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40070717055150814117722491 60106075582726221176583737)
  ·
    refine ⟨45079556687044665882437803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60106075582726221176583737 45079556687044665882437803)
    ·
      refine ⟨67619335030566998823656705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45079556687044665882437803 67619335030566998823656705)
      ·
        refine ⟨50714501272925249117742529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67619335030566998823656705 50714501272925249117742529)
        ·
          refine ⟨38035875954693936838306897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50714501272925249117742529 38035875954693936838306897)
          ·
            refine ⟨28526906966020452628730173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38035875954693936838306897 28526906966020452628730173)
            ·
              refine ⟨10697590112257669735773815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28526906966020452628730173 10697590112257669735773815)
              ·
                refine ⟨16046385168386504603660723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10697590112257669735773815 16046385168386504603660723)
                ·
                  refine ⟨24069577752579756905491085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16046385168386504603660723 24069577752579756905491085)
                  ·
                    refine ⟨9026091657217408839559157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24069577752579756905491085 9026091657217408839559157)
                    ·
                      refine ⟨846196092864132078708671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9026091657217408839559157 846196092864132078708671)
                      ·
                        rfl

theorem cell23_1647961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 1, 1, 3, 5].length) (baseStart_1647961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1647961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1647961 prefixEnd_1647961 := by exact prefixLift 1647961
  have htrace : WordTrace (prefixWord ++ tailWord_1647961) baseStart_1647961 baseEnd_1647961 := by
    simpa [prefixWord, tailWord_1647961, baseEnd_1647961] using wordTrace_append hprefix tailTrace_1647961
  have hstable : (prefixWord ++ tailWord_1647961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1647961).length < 2 ^ (prefixWord ++ tailWord_1647961).sum := by decide
  have hdescent : baseEnd_1647961 < baseStart_1647961 := by decide
  rcases family_descends (prefixWord ++ tailWord_1647961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1648041 : List Nat := [1, 2, 1, 1, 1, 1, 3, 1, 4, 8]
def baseStart_1648041 : Nat := 118140960795 + 1648041 * 2 ^ 59
def prefixEnd_1648041 : Nat := 4983230072969 + 3 ^ 40 * 1648041 * 2
def baseEnd_1648041 : Nat := 282079057105497255236101

theorem tailTrace_1648041 : CollatzResearch.WordTrace tailWord_1648041 prefixEnd_1648041 282079057105497255236101 := by
  unfold tailWord_1648041
  simp only [CollatzResearch.WordTrace]
  refine ⟨60108993422436394839495977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40072662281624263226330651 60108993422436394839495977)
  ·
    refine ⟨45081745066827296129621983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60108993422436394839495977 45081745066827296129621983)
    ·
      refine ⟨67622617600240944194432975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45081745066827296129621983 67622617600240944194432975)
      ·
        refine ⟨101433926400361416291649463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67622617600240944194432975 101433926400361416291649463)
        ·
          refine ⟨152150889600542124437474195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101433926400361416291649463 152150889600542124437474195)
          ·
            refine ⟨228226334400813186656211293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152150889600542124437474195 228226334400813186656211293)
            ·
              refine ⟨85584875400304944996079235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 228226334400813186656211293 85584875400304944996079235)
              ·
                refine ⟨128377313100457417494118853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85584875400304944996079235 128377313100457417494118853)
                ·
                  refine ⟨24070746206335765780147285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 128377313100457417494118853 24070746206335765780147285)
                  ·
                    refine ⟨282079057105497255236101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 24070746206335765780147285 282079057105497255236101)
                    ·
                      rfl

theorem cell23_1648041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 4, 8].length) (baseStart_1648041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1648041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1648041 prefixEnd_1648041 := by exact prefixLift 1648041
  have htrace : WordTrace (prefixWord ++ tailWord_1648041) baseStart_1648041 baseEnd_1648041 := by
    simpa [prefixWord, tailWord_1648041, baseEnd_1648041] using wordTrace_append hprefix tailTrace_1648041
  have hstable : (prefixWord ++ tailWord_1648041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1648041).length < 2 ^ (prefixWord ++ tailWord_1648041).sum := by decide
  have hdescent : baseEnd_1648041 < baseStart_1648041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1648041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1648078 : List Nat := [4, 1, 1, 1, 2, 1, 3, 1, 2, 1, 6]
def baseStart_1648078 : Nat := 118140960795 + 1648078 * 2 ^ 59
def prefixEnd_1648078 : Nat := 4983230072969 + 3 ^ 40 * 1648078 * 2
def baseEnd_1648078 : Nat := 846256170100708120945633

theorem tailTrace_1648078 : CollatzResearch.WordTrace tailWord_1648078 prefixEnd_1648078 846256170100708120945633 := by
  unfold tailWord_1648078
  simp only [CollatzResearch.WordTrace]
  refine ⟨7513792865412793769824111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40073561948868233439061925 7513792865412793769824111)
  ·
    refine ⟨11270689298119190654736167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7513792865412793769824111 11270689298119190654736167)
    ·
      refine ⟨16906033947178785982104251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11270689298119190654736167 16906033947178785982104251)
      ·
        refine ⟨25359050920768178973156377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16906033947178785982104251 25359050920768178973156377)
        ·
          refine ⟨19019288190576134229867283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25359050920768178973156377 19019288190576134229867283)
          ·
            refine ⟨28528932285864201344800925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19019288190576134229867283 28528932285864201344800925)
            ·
              refine ⟨10698349607199075504300347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28528932285864201344800925 10698349607199075504300347)
              ·
                refine ⟨16047524410798613256450521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10698349607199075504300347 16047524410798613256450521)
                ·
                  refine ⟨12035643308098959942337891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16047524410798613256450521 12035643308098959942337891)
                  ·
                    refine ⟨18053464962148439913506837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12035643308098959942337891 18053464962148439913506837)
                    ·
                      refine ⟨846256170100708120945633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18053464962148439913506837 846256170100708120945633)
                      ·
                        rfl

theorem cell23_1648078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 1, 2, 1, 6].length) (baseStart_1648078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1648078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1648078 prefixEnd_1648078 := by exact prefixLift 1648078
  have htrace : WordTrace (prefixWord ++ tailWord_1648078) baseStart_1648078 baseEnd_1648078 := by
    simpa [prefixWord, tailWord_1648078, baseEnd_1648078] using wordTrace_append hprefix tailTrace_1648078
  have hstable : (prefixWord ++ tailWord_1648078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1648078).length < 2 ^ (prefixWord ++ tailWord_1648078).sum := by decide
  have hdescent : baseEnd_1648078 < baseStart_1648078 := by decide
  rcases family_descends (prefixWord ++ tailWord_1648078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1648085 : List Nat := [1, 3, 2, 3, 1, 1, 2, 1, 4, 2, 3]
def baseStart_1648085 : Nat := 118140960795 + 1648085 * 2 ^ 59
def prefixEnd_1648085 : Nat := 4983230072969 + 3 ^ 40 * 1648085 * 2
def baseEnd_1648085 : Nat := 846259764465289593558101

theorem tailTrace_1648085 : CollatzResearch.WordTrace tailWord_1648085 prefixEnd_1648085 846259764465289593558101 := by
  unfold tailWord_1648085
  simp only [CollatzResearch.WordTrace]
  refine ⟨60110598234276990354097709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40073732156184660236065139 60110598234276990354097709)
  ·
    refine ⟨22541474337853871382786641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60110598234276990354097709 22541474337853871382786641)
    ·
      refine ⟨16906105753390403537089981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22541474337853871382786641 16906105753390403537089981)
      ·
        refine ⟨6339789657521401326408743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16906105753390403537089981 6339789657521401326408743)
        ·
          refine ⟨9509684486282101989613115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6339789657521401326408743 9509684486282101989613115)
          ·
            refine ⟨14264526729423152984419673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9509684486282101989613115 14264526729423152984419673)
            ·
              refine ⟨10698395047067364738314755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14264526729423152984419673 10698395047067364738314755)
              ·
                refine ⟨16047592570601047107472133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10698395047067364738314755 16047592570601047107472133)
                ·
                  refine ⟨3008923606987696332651025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16047592570601047107472133 3008923606987696332651025)
                  ·
                    refine ⟨2256692705240772249488269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3008923606987696332651025 2256692705240772249488269)
                    ·
                      refine ⟨846259764465289593558101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2256692705240772249488269 846259764465289593558101)
                      ·
                        rfl

theorem cell23_1648085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 1, 4, 2, 3].length) (baseStart_1648085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1648085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1648085 prefixEnd_1648085 := by exact prefixLift 1648085
  have htrace : WordTrace (prefixWord ++ tailWord_1648085) baseStart_1648085 baseEnd_1648085 := by
    simpa [prefixWord, tailWord_1648085, baseEnd_1648085] using wordTrace_append hprefix tailTrace_1648085
  have hstable : (prefixWord ++ tailWord_1648085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1648085).length < 2 ^ (prefixWord ++ tailWord_1648085).sum := by decide
  have hdescent : baseEnd_1648085 < baseStart_1648085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1648085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1648115 : List Nat := [1, 1, 1, 2, 2, 2, 2, 3, 5, 1, 3]
def baseStart_1648115 : Nat := 118140960795 + 1648115 * 2 ^ 59
def prefixEnd_1648115 : Nat := 4983230072969 + 3 ^ 40 * 1648115 * 2
def baseEnd_1648115 : Nat := 846275168884924476182963

theorem tailTrace_1648115 : CollatzResearch.WordTrace tailWord_1648115 prefixEnd_1648115 846275168884924476182963 := by
  unfold tailWord_1648115
  simp only [CollatzResearch.WordTrace]
  refine ⟨60111692424168305477689799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40074461616112203651793199 60111692424168305477689799)
  ·
    refine ⟨90167538636252458216534699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60111692424168305477689799 90167538636252458216534699)
    ·
      refine ⟨135251307954378687324802049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90167538636252458216534699 135251307954378687324802049)
      ·
        refine ⟨101438480965784015493601537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135251307954378687324802049 101438480965784015493601537)
        ·
          refine ⟨76078860724338011620201153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101438480965784015493601537 76078860724338011620201153)
          ·
            refine ⟨57059145543253508715150865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76078860724338011620201153 57059145543253508715150865)
            ·
              refine ⟨42794359157440131536363149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57059145543253508715150865 42794359157440131536363149)
              ·
                refine ⟨16047884684040049326136181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42794359157440131536363149 16047884684040049326136181)
                ·
                  refine ⟨1504489189128754624325267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16047884684040049326136181 1504489189128754624325267)
                  ·
                    refine ⟨2256733783693131936487901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1504489189128754624325267 2256733783693131936487901)
                    ·
                      refine ⟨846275168884924476182963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2256733783693131936487901 846275168884924476182963)
                      ·
                        rfl

theorem cell23_1648115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 5, 1, 3].length) (baseStart_1648115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1648115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1648115 prefixEnd_1648115 := by exact prefixLift 1648115
  have htrace : WordTrace (prefixWord ++ tailWord_1648115) baseStart_1648115 baseEnd_1648115 := by
    simpa [prefixWord, tailWord_1648115, baseEnd_1648115] using wordTrace_append hprefix tailTrace_1648115
  have hstable : (prefixWord ++ tailWord_1648115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1648115).length < 2 ^ (prefixWord ++ tailWord_1648115).sum := by decide
  have hdescent : baseEnd_1648115 < baseStart_1648115 := by decide
  rcases family_descends (prefixWord ++ tailWord_1648115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1648149 : List Nat := [1, 3, 2, 1, 3, 4, 1, 1, 3, 1, 3]
def baseStart_1648149 : Nat := 118140960795 + 1648149 * 2 ^ 59
def prefixEnd_1648149 : Nat := 4983230072969 + 3 ^ 40 * 1648149 * 2
def baseEnd_1648149 : Nat := 846292627227177343157807

theorem tailTrace_1648149 : CollatzResearch.WordTrace tailWord_1648149 prefixEnd_1648149 846292627227177343157807 := by
  unfold tailWord_1648149
  simp only [CollatzResearch.WordTrace]
  refine ⟨60112932506045129284427501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40075288337363419522951667 60112932506045129284427501)
  ·
    refine ⟨22542349689766923481660313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60112932506045129284427501 22542349689766923481660313)
    ·
      refine ⟨16906762267325192611245235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22542349689766923481660313 16906762267325192611245235)
      ·
        refine ⟨25360143400987788916867853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16906762267325192611245235 25360143400987788916867853)
        ·
          refine ⟨9510053775370420843825445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25360143400987788916867853 9510053775370420843825445)
          ·
            refine ⟨1783135082881953908217271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9510053775370420843825445 1783135082881953908217271)
            ·
              refine ⟨2674702624322930862325907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1783135082881953908217271 2674702624322930862325907)
              ·
                refine ⟨4012053936484396293488861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2674702624322930862325907 4012053936484396293488861)
                ·
                  refine ⟨1504520226181648610058323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4012053936484396293488861 1504520226181648610058323)
                  ·
                    refine ⟨2256780339272472915087485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1504520226181648610058323 2256780339272472915087485)
                    ·
                      refine ⟨846292627227177343157807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2256780339272472915087485 846292627227177343157807)
                      ·
                        rfl

theorem cell23_1648149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 1, 1, 3, 1, 3].length) (baseStart_1648149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1648149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1648149 prefixEnd_1648149 := by exact prefixLift 1648149
  have htrace : WordTrace (prefixWord ++ tailWord_1648149) baseStart_1648149 baseEnd_1648149 := by
    simpa [prefixWord, tailWord_1648149, baseEnd_1648149] using wordTrace_append hprefix tailTrace_1648149
  have hstable : (prefixWord ++ tailWord_1648149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1648149).length < 2 ^ (prefixWord ++ tailWord_1648149).sum := by decide
  have hdescent : baseEnd_1648149 < baseStart_1648149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1648149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1648185 : List Nat := [1, 2, 1, 5, 1, 2, 1, 1, 3, 2, 4]
def baseStart_1648185 : Nat := 118140960795 + 1648185 * 2 ^ 59
def prefixEnd_1648185 : Nat := 4983230072969 + 3 ^ 40 * 1648185 * 2
def baseEnd_1648185 : Nat := 846311112530739202307641

theorem tailTrace_1648185 : CollatzResearch.WordTrace tailWord_1648185 prefixEnd_1648185 846311112530739202307641 := by
  unfold tailWord_1648185
  simp only [CollatzResearch.WordTrace]
  refine ⟨60114245533914707432738009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40076163689276471621825339 60114245533914707432738009)
  ·
    refine ⟨45085684150436030574553507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60114245533914707432738009 45085684150436030574553507)
    ·
      refine ⟨67628526225654045861830261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45085684150436030574553507 67628526225654045861830261)
      ·
        refine ⟨6340174333655066799546587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 67628526225654045861830261 6340174333655066799546587)
        ·
          refine ⟨9510261500482600199319881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6340174333655066799546587 9510261500482600199319881)
          ·
            refine ⟨7132696125361950149489911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9510261500482600199319881 7132696125361950149489911)
            ·
              refine ⟨10699044188042925224234867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7132696125361950149489911 10699044188042925224234867)
              ·
                refine ⟨16048566282064387836352301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10699044188042925224234867 16048566282064387836352301)
                ·
                  refine ⟨6018212355774145438632113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16048566282064387836352301 6018212355774145438632113)
                  ·
                    refine ⟨4513659266830609078974085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6018212355774145438632113 4513659266830609078974085)
                    ·
                      refine ⟨846311112530739202307641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4513659266830609078974085 846311112530739202307641)
                      ·
                        rfl

theorem cell23_1648185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_1648185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1648185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1648185 prefixEnd_1648185 := by exact prefixLift 1648185
  have htrace : WordTrace (prefixWord ++ tailWord_1648185) baseStart_1648185 baseEnd_1648185 := by
    simpa [prefixWord, tailWord_1648185, baseEnd_1648185] using wordTrace_append hprefix tailTrace_1648185
  have hstable : (prefixWord ++ tailWord_1648185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1648185).length < 2 ^ (prefixWord ++ tailWord_1648185).sum := by decide
  have hdescent : baseEnd_1648185 < baseStart_1648185 := by decide
  rcases family_descends (prefixWord ++ tailWord_1648185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1648199 : List Nat := [1, 1, 4, 1, 5, 1, 2, 2, 2, 4]
def baseStart_1648199 : Nat := 118140960795 + 1648199 * 2 ^ 59
def prefixEnd_1648199 : Nat := 4983230072969 + 3 ^ 40 * 1648199 * 2
def baseEnd_1648199 : Nat := 282106100419967382510859

theorem tailTrace_1648199 : CollatzResearch.WordTrace tailWord_1648199 prefixEnd_1648199 282106100419967382510859 := by
  unfold tailWord_1648199
  simp only [CollatzResearch.WordTrace]
  refine ⟨60114756155863987823747651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40076504103909325215831767 60114756155863987823747651)
  ·
    refine ⟨90172134233795981735621477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60114756155863987823747651 90172134233795981735621477)
    ·
      refine ⟨16907275168836746575429027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90172134233795981735621477 16907275168836746575429027)
      ·
        refine ⟨25360912753255119863143541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16907275168836746575429027 25360912753255119863143541)
        ·
          refine ⟨2377585570617667487169707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25360912753255119863143541 2377585570617667487169707)
          ·
            refine ⟨3566378355926501230754561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2377585570617667487169707 3566378355926501230754561)
            ·
              refine ⟨2674783766944875923065921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3566378355926501230754561 2674783766944875923065921)
              ·
                refine ⟨2006087825208656942299441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2674783766944875923065921 2006087825208656942299441)
                ·
                  refine ⟨1504565868906492706724581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2006087825208656942299441 1504565868906492706724581)
                  ·
                    refine ⟨282106100419967382510859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1504565868906492706724581 282106100419967382510859)
                    ·
                      rfl

theorem cell23_1648199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 2, 2, 2, 4].length) (baseStart_1648199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1648199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1648199 prefixEnd_1648199 := by exact prefixLift 1648199
  have htrace : WordTrace (prefixWord ++ tailWord_1648199) baseStart_1648199 baseEnd_1648199 := by
    simpa [prefixWord, tailWord_1648199, baseEnd_1648199] using wordTrace_append hprefix tailTrace_1648199
  have hstable : (prefixWord ++ tailWord_1648199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1648199).length < 2 ^ (prefixWord ++ tailWord_1648199).sum := by decide
  have hdescent : baseEnd_1648199 < baseStart_1648199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1648199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1648208 : List Nat := [2, 1, 1, 1, 1, 3, 3, 1, 1, 9]
def baseStart_1648208 : Nat := 118140960795 + 1648208 * 2 ^ 59
def prefixEnd_1648208 : Nat := 4983230072969 + 3 ^ 40 * 1648208 * 2
def baseEnd_1648208 : Nat := 282107640861930870773345

theorem tailTrace_1648208 : CollatzResearch.WordTrace tailWord_1648208 prefixEnd_1648208 282107640861930870773345 := by
  unfold tailWord_1648208
  simp only [CollatzResearch.WordTrace]
  refine ⟨30057542206415691180412639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40076722941887588240550185 30057542206415691180412639)
  ·
    refine ⟨45086313309623536770618959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30057542206415691180412639 45086313309623536770618959)
    ·
      refine ⟨67629469964435305155928439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45086313309623536770618959 67629469964435305155928439)
      ·
        refine ⟨101444204946652957733892659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67629469964435305155928439 101444204946652957733892659)
        ·
          refine ⟨152166307419979436600838989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101444204946652957733892659 152166307419979436600838989)
          ·
            refine ⟨57062365282492288725314621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 152166307419979436600838989 57062365282492288725314621)
            ·
              refine ⟨21398386980934608271992983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57062365282492288725314621 21398386980934608271992983)
              ·
                refine ⟨32097580471401912407989475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21398386980934608271992983 32097580471401912407989475)
                ·
                  refine ⟨48146370707102868611984213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32097580471401912407989475 48146370707102868611984213)
                  ·
                    refine ⟨282107640861930870773345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 48146370707102868611984213 282107640861930870773345)
                    ·
                      rfl

theorem cell23_1648208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 1, 9].length) (baseStart_1648208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1648208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1648208 prefixEnd_1648208 := by exact prefixLift 1648208
  have htrace : WordTrace (prefixWord ++ tailWord_1648208) baseStart_1648208 baseEnd_1648208 := by
    simpa [prefixWord, tailWord_1648208, baseEnd_1648208] using wordTrace_append hprefix tailTrace_1648208
  have hstable : (prefixWord ++ tailWord_1648208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1648208).length < 2 ^ (prefixWord ++ tailWord_1648208).sum := by decide
  have hdescent : baseEnd_1648208 < baseStart_1648208 := by decide
  rcases family_descends (prefixWord ++ tailWord_1648208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1648249 : List Nat := [1, 2, 1, 3, 3, 1, 3, 3, 1, 3, 2]
def baseStart_1648249 : Nat := 118140960795 + 1648249 * 2 ^ 59
def prefixEnd_1648249 : Nat := 4983230072969 + 3 ^ 40 * 1648249 * 2
def baseEnd_1648249 : Nat := 846343975292626951907347

theorem tailTrace_1648249 : CollatzResearch.WordTrace tailWord_1648249 prefixEnd_1648249 846343975292626951907347 := by
  unfold tailWord_1648249
  simp only [CollatzResearch.WordTrace]
  refine ⟨60116579805682846363067801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40077719870455230908711867 60116579805682846363067801)
  ·
    refine ⟨45087434854262134772300851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60116579805682846363067801 45087434854262134772300851)
    ·
      refine ⟨67631152281393202158451277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45087434854262134772300851 67631152281393202158451277)
      ·
        refine ⟨25361682105522450809419229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67631152281393202158451277 25361682105522450809419229)
        ·
          refine ⟨9510630789570919053532211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25361682105522450809419229 9510630789570919053532211)
          ·
            refine ⟨14265946184356378580298317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9510630789570919053532211 14265946184356378580298317)
            ·
              refine ⟨5349729819133641967611869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14265946184356378580298317 5349729819133641967611869)
              ·
                refine ⟨2006148682175115737854451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5349729819133641967611869 2006148682175115737854451)
                ·
                  refine ⟨3009223023262673606781677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2006148682175115737854451 3009223023262673606781677)
                  ·
                    refine ⟨1128458633723502602543129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3009223023262673606781677 1128458633723502602543129)
                    ·
                      refine ⟨846343975292626951907347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1128458633723502602543129 846343975292626951907347)
                      ·
                        rfl

theorem cell23_1648249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 3, 1, 3, 2].length) (baseStart_1648249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1648249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1648249 prefixEnd_1648249 := by exact prefixLift 1648249
  have htrace : WordTrace (prefixWord ++ tailWord_1648249) baseStart_1648249 baseEnd_1648249 := by
    simpa [prefixWord, tailWord_1648249, baseEnd_1648249] using wordTrace_append hprefix tailTrace_1648249
  have hstable : (prefixWord ++ tailWord_1648249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1648249).length < 2 ^ (prefixWord ++ tailWord_1648249).sum := by decide
  have hdescent : baseEnd_1648249 < baseStart_1648249 := by decide
  rcases family_descends (prefixWord ++ tailWord_1648249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1648265 : List Nat := [1, 2, 1, 1, 4, 1, 2, 1, 1, 6, 3]
def baseStart_1648265 : Nat := 118140960795 + 1648265 * 2 ^ 59
def prefixEnd_1648265 : Nat := 4983230072969 + 3 ^ 40 * 1648265 * 2
def baseEnd_1648265 : Nat := 846352190983098889307273

theorem tailTrace_1648265 : CollatzResearch.WordTrace tailWord_1648265 prefixEnd_1648265 846352190983098889307273 := by
  unfold tailWord_1648265
  simp only [CollatzResearch.WordTrace]
  refine ⟨60117163373624881095650249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40078108915749920730433499 60117163373624881095650249)
  ·
    refine ⟨45087872530218660821737687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60117163373624881095650249 45087872530218660821737687)
    ·
      refine ⟨67631808795327991232606531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45087872530218660821737687 67631808795327991232606531)
      ·
        refine ⟨101447713192991986848909797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67631808795327991232606531 101447713192991986848909797)
        ·
          refine ⟨19021446223685997534170587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 101447713192991986848909797 19021446223685997534170587)
          ·
            refine ⟨28532169335528996301255881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19021446223685997534170587 28532169335528996301255881)
            ·
              refine ⟨21399127001646747225941911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28532169335528996301255881 21399127001646747225941911)
              ·
                refine ⟨32098690502470120838912867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21399127001646747225941911 32098690502470120838912867)
                ·
                  refine ⟨48148035753705181258369301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32098690502470120838912867 48148035753705181258369301)
                  ·
                    refine ⟨2256939175954930371486061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 48148035753705181258369301 2256939175954930371486061)
                    ·
                      refine ⟨846352190983098889307273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2256939175954930371486061 846352190983098889307273)
                      ·
                        rfl

theorem cell23_1648265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 6, 3].length) (baseStart_1648265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1648265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1648265 prefixEnd_1648265 := by exact prefixLift 1648265
  have htrace : WordTrace (prefixWord ++ tailWord_1648265) baseStart_1648265 baseEnd_1648265 := by
    simpa [prefixWord, tailWord_1648265, baseEnd_1648265] using wordTrace_append hprefix tailTrace_1648265
  have hstable : (prefixWord ++ tailWord_1648265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1648265).length < 2 ^ (prefixWord ++ tailWord_1648265).sum := by decide
  have hdescent : baseEnd_1648265 < baseStart_1648265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1648265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1648279 : List Nat := [1, 1, 3, 3, 2, 2, 3, 1, 1, 4, 2]
def baseStart_1648279 : Nat := 118140960795 + 1648279 * 2 ^ 59
def prefixEnd_1648279 : Nat := 4983230072969 + 3 ^ 40 * 1648279 * 2
def baseEnd_1648279 : Nat := 846359379712261834532209

theorem tailTrace_1648279 : CollatzResearch.WordTrace tailWord_1648279 prefixEnd_1648279 846359379712261834532209 := by
  unfold tailWord_1648279
  simp only [CollatzResearch.WordTrace]
  refine ⟨60117673995574161486659891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40078449330382774324439927 60117673995574161486659891)
  ·
    refine ⟨90176510993361242229989837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60117673995574161486659891 90176510993361242229989837)
    ·
      refine ⟨33816191622510465836246189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90176510993361242229989837 33816191622510465836246189)
      ·
        refine ⟨12681071858441424688592321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33816191622510465836246189 12681071858441424688592321)
        ·
          refine ⟨9510803893831068516444241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12681071858441424688592321 9510803893831068516444241)
          ·
            refine ⟨7133102920373301387333181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9510803893831068516444241 7133102920373301387333181)
            ·
              refine ⟨2674913595139988020249943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7133102920373301387333181 2674913595139988020249943)
              ·
                refine ⟨4012370392709982030374915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2674913595139988020249943 4012370392709982030374915)
                ·
                  refine ⟨6018555589064973045562373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4012370392709982030374915 6018555589064973045562373)
                  ·
                    refine ⟨1128479172949682446042945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6018555589064973045562373 1128479172949682446042945)
                    ·
                      refine ⟨846359379712261834532209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1128479172949682446042945 846359379712261834532209)
                      ·
                        rfl

theorem cell23_1648279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 3, 1, 1, 4, 2].length) (baseStart_1648279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1648279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1648279 prefixEnd_1648279 := by exact prefixLift 1648279
  have htrace : WordTrace (prefixWord ++ tailWord_1648279) baseStart_1648279 baseEnd_1648279 := by
    simpa [prefixWord, tailWord_1648279, baseEnd_1648279] using wordTrace_append hprefix tailTrace_1648279
  have hstable : (prefixWord ++ tailWord_1648279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1648279).length < 2 ^ (prefixWord ++ tailWord_1648279).sum := by decide
  have hdescent : baseEnd_1648279 < baseStart_1648279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1648279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1648319 : List Nat := [1, 1, 2, 2, 2, 3, 5, 2, 5]
def baseStart_1648319 : Nat := 118140960795 + 1648319 * 2 ^ 59
def prefixEnd_1648319 : Nat := 4983230072969 + 3 ^ 40 * 1648319 * 2
def baseEnd_1648319 : Nat := 94042213215382408670225

theorem tailTrace_1648319 : CollatzResearch.WordTrace tailWord_1648319 prefixEnd_1648319 94042213215382408670225 := by
  unfold tailWord_1648319
  simp only [CollatzResearch.WordTrace]
  refine ⟨60119132915429248318116011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40079421943619498878744007 60119132915429248318116011)
  ·
    refine ⟨90178699373143872477174017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60119132915429248318116011 90178699373143872477174017)
    ·
      refine ⟨67634024529857904357880513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90178699373143872477174017 67634024529857904357880513)
      ·
        refine ⟨50725518397393428268410385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67634024529857904357880513 50725518397393428268410385)
        ·
          refine ⟨38044138798045071201307789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50725518397393428268410385 38044138798045071201307789)
          ·
            refine ⟨14266552049266901700490421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38044138798045071201307789 14266552049266901700490421)
            ·
              refine ⟨1337489254618772034420977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14266552049266901700490421 1337489254618772034420977)
              ·
                refine ⟨1003116940964079025815733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1337489254618772034420977 1003116940964079025815733)
                ·
                  refine ⟨94042213215382408670225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1003116940964079025815733 94042213215382408670225)
                  ·
                    rfl

theorem cell23_1648319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 5, 2, 5].length) (baseStart_1648319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1648319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1648319 prefixEnd_1648319 := by exact prefixLift 1648319
  have htrace : WordTrace (prefixWord ++ tailWord_1648319) baseStart_1648319 baseEnd_1648319 := by
    simpa [prefixWord, tailWord_1648319, baseEnd_1648319] using wordTrace_append hprefix tailTrace_1648319
  have hstable : (prefixWord ++ tailWord_1648319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1648319).length < 2 ^ (prefixWord ++ tailWord_1648319).sum := by decide
  have hdescent : baseEnd_1648319 < baseStart_1648319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1648319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1648325 : List Nat := [1, 3, 1, 1, 1, 1, 2, 5, 1, 2, 5]
def baseStart_1648325 : Nat := 118140960795 + 1648325 * 2 ^ 59
def prefixEnd_1648325 : Nat := 4983230072969 + 3 ^ 40 * 1648325 * 2
def baseEnd_1648325 : Nat := 846382999822368654556997

theorem tailTrace_1648325 : CollatzResearch.WordTrace tailWord_1648325 prefixEnd_1648325 846382999822368654556997 := by
  unfold tailWord_1648325
  simp only [CollatzResearch.WordTrace]
  refine ⟨60119351753407511342834429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40079567835605007561889619 60119351753407511342834429)
  ·
    refine ⟨22544756907527816753562911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60119351753407511342834429 22544756907527816753562911)
    ·
      refine ⟨33817135361291725130344367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22544756907527816753562911 33817135361291725130344367)
      ·
        refine ⟨50725703041937587695516551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33817135361291725130344367 50725703041937587695516551)
        ·
          refine ⟨76088554562906381543274827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50725703041937587695516551 76088554562906381543274827)
          ·
            refine ⟨114132831844359572314912241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76088554562906381543274827 114132831844359572314912241)
            ·
              refine ⟨85599623883269679236184181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114132831844359572314912241 85599623883269679236184181)
              ·
                refine ⟨8024964739056532428392267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 85599623883269679236184181 8024964739056532428392267)
                ·
                  refine ⟨12037447108584798642588401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8024964739056532428392267 12037447108584798642588401)
                  ·
                    refine ⟨9028085331438598981941301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12037447108584798642588401 9028085331438598981941301)
                    ·
                      refine ⟨846382999822368654556997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9028085331438598981941301 846382999822368654556997)
                      ·
                        rfl

theorem cell23_1648325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 5, 1, 2, 5].length) (baseStart_1648325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1648325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1648325 prefixEnd_1648325 := by exact prefixLift 1648325
  have htrace : WordTrace (prefixWord ++ tailWord_1648325) baseStart_1648325 baseEnd_1648325 := by
    simpa [prefixWord, tailWord_1648325, baseEnd_1648325] using wordTrace_append hprefix tailTrace_1648325
  have hstable : (prefixWord ++ tailWord_1648325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1648325).length < 2 ^ (prefixWord ++ tailWord_1648325).sum := by decide
  have hdescent : baseEnd_1648325 < baseStart_1648325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1648325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1648330 : List Nat := [3, 1, 2, 1, 5, 2, 2, 1, 2, 2, 2]
def baseStart_1648330 : Nat := 118140960795 + 1648330 * 2 ^ 59
def prefixEnd_1648330 : Nat := 4983230072969 + 3 ^ 40 * 1648330 * 2
def baseEnd_1648330 : Nat := 846385567225641134994475

theorem tailTrace_1648330 : CollatzResearch.WordTrace tailWord_1648330 prefixEnd_1648330 846385567225641134994475 := by
  unfold tailWord_1648330
  simp only [CollatzResearch.WordTrace]
  refine ⟨15029883529597349299191611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40079689412259598131177629 15029883529597349299191611)
  ·
    refine ⟨22544825294396023948787417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15029883529597349299191611 22544825294396023948787417)
    ·
      refine ⟨16908618970797017961590563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22544825294396023948787417 16908618970797017961590563)
      ·
        refine ⟨25362928456195526942385845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16908618970797017961590563 25362928456195526942385845)
        ·
          refine ⟨2377774542768330650848673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25362928456195526942385845 2377774542768330650848673)
          ·
            refine ⟨1783330907076247988136505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2377774542768330650848673 1783330907076247988136505)
            ·
              refine ⟨1337498180307185991102379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1783330907076247988136505 1337498180307185991102379)
              ·
                refine ⟨2006247270460778986653569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1337498180307185991102379 2006247270460778986653569)
                ·
                  refine ⟨1504685452845584239990177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2006247270460778986653569 1504685452845584239990177)
                  ·
                    refine ⟨1128514089634188179992633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1504685452845584239990177 1128514089634188179992633)
                    ·
                      refine ⟨846385567225641134994475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1128514089634188179992633 846385567225641134994475)
                      ·
                        rfl

theorem cell23_1648330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 2, 1, 2, 2, 2].length) (baseStart_1648330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1648330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1648330 prefixEnd_1648330 := by exact prefixLift 1648330
  have htrace : WordTrace (prefixWord ++ tailWord_1648330) baseStart_1648330 baseEnd_1648330 := by
    simpa [prefixWord, tailWord_1648330, baseEnd_1648330] using wordTrace_append hprefix tailTrace_1648330
  have hstable : (prefixWord ++ tailWord_1648330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1648330).length < 2 ^ (prefixWord ++ tailWord_1648330).sum := by decide
  have hdescent : baseEnd_1648330 < baseStart_1648330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1648330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1648335 : List Nat := [1, 1, 2, 1, 1, 3, 1, 3, 3, 3, 4]
def baseStart_1648335 : Nat := 118140960795 + 1648335 * 2 ^ 59
def prefixEnd_1648335 : Nat := 4983230072969 + 3 ^ 40 * 1648335 * 2
def baseEnd_1648335 : Nat := 846388134628913615431951

theorem tailTrace_1648335 : CollatzResearch.WordTrace tailWord_1648335 prefixEnd_1648335 846388134628913615431951 := by
  unfold tailWord_1648335
  simp only [CollatzResearch.WordTrace]
  refine ⟨60119716483371283050698459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40079810988914188700465639 60119716483371283050698459)
  ·
    refine ⟨90179574725056924576047689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60119716483371283050698459 90179574725056924576047689)
    ·
      refine ⟨67634681043792693432035767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90179574725056924576047689 67634681043792693432035767)
      ·
        refine ⟨101452021565689040148053651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67634681043792693432035767 101452021565689040148053651)
        ·
          refine ⟨152178032348533560222080477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101452021565689040148053651 152178032348533560222080477)
          ·
            refine ⟨57066762130700085083280179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 152178032348533560222080477 57066762130700085083280179)
            ·
              refine ⟨85600143196050127624920269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57066762130700085083280179 85600143196050127624920269)
              ·
                refine ⟨32100053698518797859345101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85600143196050127624920269 32100053698518797859345101)
                ·
                  refine ⟨12037520136944549197254413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32100053698518797859345101 12037520136944549197254413)
                  ·
                    refine ⟨4514070051354205948970405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12037520136944549197254413 4514070051354205948970405)
                    ·
                      refine ⟨846388134628913615431951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4514070051354205948970405 846388134628913615431951)
                      ·
                        rfl

theorem cell23_1648335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 3, 3, 4].length) (baseStart_1648335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1648335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1648335 prefixEnd_1648335 := by exact prefixLift 1648335
  have htrace : WordTrace (prefixWord ++ tailWord_1648335) baseStart_1648335 baseEnd_1648335 := by
    simpa [prefixWord, tailWord_1648335, baseEnd_1648335] using wordTrace_append hprefix tailTrace_1648335
  have hstable : (prefixWord ++ tailWord_1648335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1648335).length < 2 ^ (prefixWord ++ tailWord_1648335).sum := by decide
  have hdescent : baseEnd_1648335 < baseStart_1648335 := by decide
  rcases family_descends (prefixWord ++ tailWord_1648335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1648352 : List Nat := [2, 1, 1, 3, 1, 2, 3, 3, 2, 1, 4]
def baseStart_1648352 : Nat := 118140960795 + 1648352 * 2 ^ 59
def prefixEnd_1648352 : Nat := 4983230072969 + 3 ^ 40 * 1648352 * 2
def baseEnd_1648352 : Nat := 846396863800040048919373

theorem tailTrace_1648352 : CollatzResearch.WordTrace tailWord_1648352 prefixEnd_1648352 846396863800040048919373 := by
  unfold tailWord_1648352
  simp only [CollatzResearch.WordTrace]
  refine ⟨30060168262154847477033655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40080224349539796636044873 30060168262154847477033655)
  ·
    refine ⟨45090252393232271215550483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30060168262154847477033655 45090252393232271215550483)
    ·
      refine ⟨67635378589848406823325725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45090252393232271215550483 67635378589848406823325725)
      ·
        refine ⟨25363266971193152558747147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67635378589848406823325725 25363266971193152558747147)
        ·
          refine ⟨38044900456789728838120721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25363266971193152558747147 38044900456789728838120721)
          ·
            refine ⟨28533675342592296628590541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38044900456789728838120721 28533675342592296628590541)
            ·
              refine ⟨10700128253472111235721453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28533675342592296628590541 10700128253472111235721453)
              ·
                refine ⟨4012548095052041713395545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10700128253472111235721453 4012548095052041713395545)
                ·
                  refine ⟨3009411071289031285046659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4012548095052041713395545 3009411071289031285046659)
                  ·
                    refine ⟨4514116606933546927569989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3009411071289031285046659 4514116606933546927569989)
                    ·
                      refine ⟨846396863800040048919373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4514116606933546927569989 846396863800040048919373)
                      ·
                        rfl

theorem cell23_1648352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 3, 2, 1, 4].length) (baseStart_1648352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1648352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1648352 prefixEnd_1648352 := by exact prefixLift 1648352
  have htrace : WordTrace (prefixWord ++ tailWord_1648352) baseStart_1648352 baseEnd_1648352 := by
    simpa [prefixWord, tailWord_1648352, baseEnd_1648352] using wordTrace_append hprefix tailTrace_1648352
  have hstable : (prefixWord ++ tailWord_1648352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1648352).length < 2 ^ (prefixWord ++ tailWord_1648352).sum := by decide
  have hdescent : baseEnd_1648352 < baseStart_1648352 := by decide
  rcases family_descends (prefixWord ++ tailWord_1648352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1648375 : List Nat := [1, 1, 3, 1, 1, 1, 4, 3, 8]
def baseStart_1648375 : Nat := 118140960795 + 1648375 * 2 ^ 59
def prefixEnd_1648375 : Nat := 4983230072969 + 3 ^ 40 * 1648375 * 2
def baseEnd_1648375 : Nat := 94045408206121495436863

theorem tailTrace_1648375 : CollatzResearch.WordTrace tailWord_1648375 prefixEnd_1648375 94045408206121495436863 := by
  unfold tailWord_1648375
  simp only [CollatzResearch.WordTrace]
  refine ⟨60121175403226369882154579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40080783602150913254769719 60121175403226369882154579)
  ·
    refine ⟨90181763104839554823231869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60121175403226369882154579 90181763104839554823231869)
    ·
      refine ⟨33818161164314833058711951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90181763104839554823231869 33818161164314833058711951)
      ·
        refine ⟨50727241746472249588067927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33818161164314833058711951 50727241746472249588067927)
        ·
          refine ⟨76090862619708374382101891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50727241746472249588067927 76090862619708374382101891)
          ·
            refine ⟨114136293929562561573152837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76090862619708374382101891 114136293929562561573152837)
            ·
              refine ⟨21400555111792980294966157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 114136293929562561573152837 21400555111792980294966157)
              ·
                refine ⟨8025208166922367610612309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21400555111792980294966157 8025208166922367610612309)
                ·
                  refine ⟨94045408206121495436863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8025208166922367610612309 94045408206121495436863)
                  ·
                    rfl

theorem cell23_1648375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 3, 8].length) (baseStart_1648375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1648375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1648375 prefixEnd_1648375 := by exact prefixLift 1648375
  have htrace : WordTrace (prefixWord ++ tailWord_1648375) baseStart_1648375 baseEnd_1648375 := by
    simpa [prefixWord, tailWord_1648375, baseEnd_1648375] using wordTrace_append hprefix tailTrace_1648375
  have hstable : (prefixWord ++ tailWord_1648375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1648375).length < 2 ^ (prefixWord ++ tailWord_1648375).sum := by decide
  have hdescent : baseEnd_1648375 < baseStart_1648375 := by decide
  rcases family_descends (prefixWord ++ tailWord_1648375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1648386 : List Nat := [3, 4, 1, 1, 1, 1, 3, 1, 2, 4, 2]
def baseStart_1648386 : Nat := 118140960795 + 1648386 * 2 ^ 59
def prefixEnd_1648386 : Nat := 4983230072969 + 3 ^ 40 * 1648386 * 2
def baseEnd_1648386 : Nat := 846414322142292915894217

theorem tailTrace_1648386 : CollatzResearch.WordTrace tailWord_1648386 prefixEnd_1648386 846414322142292915894217 := by
  unfold tailWord_1648386
  simp only [CollatzResearch.WordTrace]
  refine ⟨15030394151546629690201253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40081051070791012507203341 15030394151546629690201253)
  ·
    refine ⟨2818198903414993066912735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15030394151546629690201253 2818198903414993066912735)
    ·
      refine ⟨4227298355122489600369103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2818198903414993066912735 4227298355122489600369103)
      ·
        refine ⟨6340947532683734400553655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4227298355122489600369103 6340947532683734400553655)
        ·
          refine ⟨9511421299025601600830483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6340947532683734400553655 9511421299025601600830483)
          ·
            refine ⟨14267131948538402401245725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9511421299025601600830483 14267131948538402401245725)
            ·
              refine ⟨5350174480701900900467147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14267131948538402401245725 5350174480701900900467147)
              ·
                refine ⟨8025261721052851350700721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5350174480701900900467147 8025261721052851350700721)
                ·
                  refine ⟨6018946290789638513025541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8025261721052851350700721 6018946290789638513025541)
                  ·
                    refine ⟨1128552429523057221192289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6018946290789638513025541 1128552429523057221192289)
                    ·
                      refine ⟨846414322142292915894217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1128552429523057221192289 846414322142292915894217)
                      ·
                        rfl

theorem cell23_1648386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 1, 2, 4, 2].length) (baseStart_1648386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1648386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1648386 prefixEnd_1648386 := by exact prefixLift 1648386
  have htrace : WordTrace (prefixWord ++ tailWord_1648386) baseStart_1648386 baseEnd_1648386 := by
    simpa [prefixWord, tailWord_1648386, baseEnd_1648386] using wordTrace_append hprefix tailTrace_1648386
  have hstable : (prefixWord ++ tailWord_1648386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1648386).length < 2 ^ (prefixWord ++ tailWord_1648386).sum := by decide
  have hdescent : baseEnd_1648386 < baseStart_1648386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1648386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1648392 : List Nat := [2, 1, 3, 2, 2, 1, 1, 5, 6]
def baseStart_1648392 : Nat := 118140960795 + 1648392 * 2 ^ 59
def prefixEnd_1648392 : Nat := 4983230072969 + 3 ^ 40 * 1648392 * 2
def baseEnd_1648392 : Nat := 94046378114024432491021

theorem tailTrace_1648392 : CollatzResearch.WordTrace tailWord_1648392 prefixEnd_1648392 94046378114024432491021 := by
  unfold tailWord_1648392
  simp only [CollatzResearch.WordTrace]
  refine ⟨30060897722082390892761715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40081196962776521190348953 30060897722082390892761715)
  ·
    refine ⟨45091346583123586339142573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30060897722082390892761715 45091346583123586339142573)
    ·
      refine ⟨16909254968671344877178465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45091346583123586339142573 16909254968671344877178465)
      ·
        refine ⟨12681941226503508657883849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16909254968671344877178465 12681941226503508657883849)
        ·
          refine ⟨9511455919877631493412887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12681941226503508657883849 9511455919877631493412887)
          ·
            refine ⟨14267183879816447240119331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9511455919877631493412887 14267183879816447240119331)
            ·
              refine ⟨21400775819724670860178997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14267183879816447240119331 21400775819724670860178997)
              ·
                refine ⟨2006322733099187893141781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21400775819724670860178997 2006322733099187893141781)
                ·
                  refine ⟨94046378114024432491021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2006322733099187893141781 94046378114024432491021)
                  ·
                    rfl

theorem cell23_1648392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 5, 6].length) (baseStart_1648392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1648392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1648392 prefixEnd_1648392 := by exact prefixLift 1648392
  have htrace : WordTrace (prefixWord ++ tailWord_1648392) baseStart_1648392 baseEnd_1648392 := by
    simpa [prefixWord, tailWord_1648392, baseEnd_1648392] using wordTrace_append hprefix tailTrace_1648392
  have hstable : (prefixWord ++ tailWord_1648392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1648392).length < 2 ^ (prefixWord ++ tailWord_1648392).sum := by decide
  have hdescent : baseEnd_1648392 < baseStart_1648392 := by decide
  rcases family_descends (prefixWord ++ tailWord_1648392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1648446 : List Nat := [4, 2, 1, 2, 2, 1, 1, 2, 1, 5, 2]
def baseStart_1648446 : Nat := 118140960795 + 1648446 * 2 ^ 59
def prefixEnd_1648446 : Nat := 4983230072969 + 3 ^ 40 * 1648446 * 2
def baseEnd_1648446 : Nat := 846445130981562681143941

theorem tailTrace_1648446 : CollatzResearch.WordTrace tailWord_1648446 prefixEnd_1648446 846445130981562681143941 := by
  unfold tailWord_1648446
  simp only [CollatzResearch.WordTrace]
  refine ⟨7515470623246143625998649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40082509990646099338659461 7515470623246143625998649)
  ·
    refine ⟨5636602967434607719498987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7515470623246143625998649 5636602967434607719498987)
    ·
      refine ⟨8454904451151911579248481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5636602967434607719498987 8454904451151911579248481)
      ·
        refine ⟨6341178338363933684436361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8454904451151911579248481 6341178338363933684436361)
        ·
          refine ⟨4755883753772950263327271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6341178338363933684436361 4755883753772950263327271)
          ·
            refine ⟨7133825630659425394990907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4755883753772950263327271 7133825630659425394990907)
            ·
              refine ⟨10700738445989138092486361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7133825630659425394990907 10700738445989138092486361)
              ·
                refine ⟨8025553834491853569364771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10700738445989138092486361 8025553834491853569364771)
                ·
                  refine ⟨12038330751737780354047157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8025553834491853569364771 12038330751737780354047157)
                  ·
                    refine ⟨1128593507975416908191921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12038330751737780354047157 1128593507975416908191921)
                    ·
                      refine ⟨846445130981562681143941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1128593507975416908191921 846445130981562681143941)
                      ·
                        rfl

theorem cell23_1648446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 2, 1, 5, 2].length) (baseStart_1648446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1648446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1648446 prefixEnd_1648446 := by exact prefixLift 1648446
  have htrace : WordTrace (prefixWord ++ tailWord_1648446) baseStart_1648446 baseEnd_1648446 := by
    simpa [prefixWord, tailWord_1648446, baseEnd_1648446] using wordTrace_append hprefix tailTrace_1648446
  have hstable : (prefixWord ++ tailWord_1648446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1648446).length < 2 ^ (prefixWord ++ tailWord_1648446).sum := by decide
  have hdescent : baseEnd_1648446 < baseStart_1648446 := by decide
  rcases family_descends (prefixWord ++ tailWord_1648446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1648469 : List Nat := [1, 3, 2, 2, 2, 2, 1, 2, 4, 4]
def baseStart_1648469 : Nat := 118140960795 + 1648469 * 2 ^ 59
def prefixEnd_1648469 : Nat := 4983230072969 + 3 ^ 40 * 1648469 * 2
def baseEnd_1648469 : Nat := 282152313678872030385445

theorem tailTrace_1648469 : CollatzResearch.WordTrace tailWord_1648469 prefixEnd_1648469 282152313678872030385445 := by
  unfold tailWord_1648469
  simp only [CollatzResearch.WordTrace]
  refine ⟨60124603864885823936076461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40083069243257215957384307 60124603864885823936076461)
  ·
    refine ⟨22546726449332183976028673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60124603864885823936076461 22546726449332183976028673)
    ·
      refine ⟨16910044836999137982021505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22546726449332183976028673 16910044836999137982021505)
      ·
        refine ⟨12682533627749353486516129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16910044836999137982021505 12682533627749353486516129)
        ·
          refine ⟨9511900220812015114887097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12682533627749353486516129 9511900220812015114887097)
          ·
            refine ⟨7133925165609011336165323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9511900220812015114887097 7133925165609011336165323)
            ·
              refine ⟨10700887748413517004247985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7133925165609011336165323 10700887748413517004247985)
              ·
                refine ⟨8025665811310137753185989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10700887748413517004247985 8025665811310137753185989)
                ·
                  refine ⟨1504812339620650828722373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8025665811310137753185989 1504812339620650828722373)
                  ·
                    refine ⟨282152313678872030385445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1504812339620650828722373 282152313678872030385445)
                    ·
                      rfl

theorem cell23_1648469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 2, 4, 4].length) (baseStart_1648469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1648469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1648469 prefixEnd_1648469 := by exact prefixLift 1648469
  have htrace : WordTrace (prefixWord ++ tailWord_1648469) baseStart_1648469 baseEnd_1648469 := by
    simpa [prefixWord, tailWord_1648469, baseEnd_1648469] using wordTrace_append hprefix tailTrace_1648469
  have hstable : (prefixWord ++ tailWord_1648469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1648469).length < 2 ^ (prefixWord ++ tailWord_1648469).sum := by decide
  have hdescent : baseEnd_1648469 < baseStart_1648469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1648469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1648479 : List Nat := [1, 1, 2, 3, 1, 5, 2, 1, 1, 1, 5]
def baseStart_1648479 : Nat := 118140960795 + 1648479 * 2 ^ 59
def prefixEnd_1648479 : Nat := 4983230072969 + 3 ^ 40 * 1648479 * 2
def baseEnd_1648479 : Nat := 846462075843161052031289

theorem tailTrace_1648479 : CollatzResearch.WordTrace tailWord_1648479 prefixEnd_1648479 846462075843161052031289 := by
  unfold tailWord_1648479
  simp only [CollatzResearch.WordTrace]
  refine ⟨60124968594849595643940491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40083312396566397095960327 60124968594849595643940491)
  ·
    refine ⟨90187452892274393465910737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60124968594849595643940491 90187452892274393465910737)
    ·
      refine ⟨67640589669205795099433053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90187452892274393465910737 67640589669205795099433053)
      ·
        refine ⟨25365221125952173162287395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67640589669205795099433053 25365221125952173162287395)
        ·
          refine ⟨38047831688928259743431093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25365221125952173162287395 38047831688928259743431093)
          ·
            refine ⟨3566984220837024350946665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38047831688928259743431093 3566984220837024350946665)
            ·
              refine ⟨2675238165627768263209999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3566984220837024350946665 2675238165627768263209999)
              ·
                refine ⟨4012857248441652394814999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2675238165627768263209999 4012857248441652394814999)
                ·
                  refine ⟨6019285872662478592222499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4012857248441652394814999 6019285872662478592222499)
                  ·
                    refine ⟨9028928808993717888333749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6019285872662478592222499 9028928808993717888333749)
                    ·
                      refine ⟨846462075843161052031289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9028928808993717888333749 846462075843161052031289)
                      ·
                        rfl

theorem cell23_1648479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 2, 1, 1, 1, 5].length) (baseStart_1648479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1648479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1648479 prefixEnd_1648479 := by exact prefixLift 1648479
  have htrace : WordTrace (prefixWord ++ tailWord_1648479) baseStart_1648479 baseEnd_1648479 := by
    simpa [prefixWord, tailWord_1648479, baseEnd_1648479] using wordTrace_append hprefix tailTrace_1648479
  have hstable : (prefixWord ++ tailWord_1648479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1648479).length < 2 ^ (prefixWord ++ tailWord_1648479).sum := by decide
  have hdescent : baseEnd_1648479 < baseStart_1648479 := by decide
  rcases family_descends (prefixWord ++ tailWord_1648479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1648493 : List Nat := [1, 5, 1, 1, 1, 1, 5, 1, 3, 2, 2]
def baseStart_1648493 : Nat := 118140960795 + 1648493 * 2 ^ 59
def prefixEnd_1648493 : Nat := 4983230072969 + 3 ^ 40 * 1648493 * 2
def baseEnd_1648493 : Nat := 846469264572323997256225

theorem tailTrace_1648493 : CollatzResearch.WordTrace tailWord_1648493 prefixEnd_1648493 846469264572323997256225 := by
  unfold tailWord_1648493
  simp only [CollatzResearch.WordTrace]
  refine ⟨60125479216798876034950133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40083652811199250689966755 60125479216798876034950133)
  ·
    refine ⟨5636763676574894628276575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 60125479216798876034950133 5636763676574894628276575)
    ·
      refine ⟨8455145514862341942414863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5636763676574894628276575 8455145514862341942414863)
      ·
        refine ⟨12682718272293512913622295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8455145514862341942414863 12682718272293512913622295)
        ·
          refine ⟨19024077408440269370433443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12682718272293512913622295 19024077408440269370433443)
          ·
            refine ⟨28536116112660404055650165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19024077408440269370433443 28536116112660404055650165)
            ·
              refine ⟨2675260885561912880217203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28536116112660404055650165 2675260885561912880217203)
              ·
                refine ⟨4012891328342869320325805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2675260885561912880217203 4012891328342869320325805)
                ·
                  refine ⟨1504834248128575995122177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4012891328342869320325805 1504834248128575995122177)
                  ·
                    refine ⟨1128625686096431996341633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1504834248128575995122177 1128625686096431996341633)
                    ·
                      refine ⟨846469264572323997256225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1128625686096431996341633 846469264572323997256225)
                      ·
                        rfl

theorem cell23_1648493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 5, 1, 3, 2, 2].length) (baseStart_1648493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1648493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1648493 prefixEnd_1648493 := by exact prefixLift 1648493
  have htrace : WordTrace (prefixWord ++ tailWord_1648493) baseStart_1648493 baseEnd_1648493 := by
    simpa [prefixWord, tailWord_1648493, baseEnd_1648493] using wordTrace_append hprefix tailTrace_1648493
  have hstable : (prefixWord ++ tailWord_1648493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1648493).length < 2 ^ (prefixWord ++ tailWord_1648493).sum := by decide
  have hdescent : baseEnd_1648493 < baseStart_1648493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1648493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1648509 : List Nat := [1, 4, 1, 1, 2, 1, 1, 5, 1, 3, 3]
def baseStart_1648509 : Nat := 118140960795 + 1648509 * 2 ^ 59
def prefixEnd_1648509 : Nat := 4983230072969 + 3 ^ 40 * 1648509 * 2
def baseEnd_1648509 : Nat := 846477480262795934656151

theorem tailTrace_1648509 : CollatzResearch.WordTrace tailWord_1648509 prefixEnd_1648509 846477480262795934656151 := by
  unfold tailWord_1648509
  simp only [CollatzResearch.WordTrace]
  refine ⟨60126062784740910767532581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40084041856493940511688387 60126062784740910767532581)
  ·
    refine ⟨11273636772138920768912359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60126062784740910767532581 11273636772138920768912359)
    ·
      refine ⟨16910455158208381153368539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11273636772138920768912359 16910455158208381153368539)
      ·
        refine ⟨25365682737312571730052809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16910455158208381153368539 25365682737312571730052809)
        ·
          refine ⟨19024262052984428797539607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25365682737312571730052809 19024262052984428797539607)
          ·
            refine ⟨28536393079476643196309411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19024262052984428797539607 28536393079476643196309411)
            ·
              refine ⟨42804589619214964794464117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28536393079476643196309411 42804589619214964794464117)
              ·
                refine ⟨4012930276801402949481011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42804589619214964794464117 4012930276801402949481011)
                ·
                  refine ⟨6019395415202104424221517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4012930276801402949481011 6019395415202104424221517)
                  ·
                    refine ⟨2257273280700789159083069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6019395415202104424221517 2257273280700789159083069)
                    ·
                      refine ⟨846477480262795934656151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2257273280700789159083069 846477480262795934656151)
                      ·
                        rfl

theorem cell23_1648509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 5, 1, 3, 3].length) (baseStart_1648509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1648509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1648509 prefixEnd_1648509 := by exact prefixLift 1648509
  have htrace : WordTrace (prefixWord ++ tailWord_1648509) baseStart_1648509 baseEnd_1648509 := by
    simpa [prefixWord, tailWord_1648509, baseEnd_1648509] using wordTrace_append hprefix tailTrace_1648509
  have hstable : (prefixWord ++ tailWord_1648509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1648509).length < 2 ^ (prefixWord ++ tailWord_1648509).sum := by decide
  have hdescent : baseEnd_1648509 < baseStart_1648509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1648509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1648510 : List Nat := [4, 2, 3, 1, 1, 3, 1, 2, 1, 1, 4]
def baseStart_1648510 : Nat := 118140960795 + 1648510 * 2 ^ 59
def prefixEnd_1648510 : Nat := 4983230072969 + 3 ^ 40 * 1648510 * 2
def baseEnd_1648510 : Nat := 846477993743450430743647

theorem tailTrace_1648510 : CollatzResearch.WordTrace tailWord_1648510 prefixEnd_1648510 846477993743450430743647 := by
  unfold tailWord_1648510
  simp only [CollatzResearch.WordTrace]
  refine ⟨7515762407217160992289873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40084066171824858625545989 7515762407217160992289873)
  ·
    refine ⟨5636821805412870744217405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7515762407217160992289873 5636821805412870744217405)
    ·
      refine ⟨2113808177029826529081527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5636821805412870744217405 2113808177029826529081527)
      ·
        refine ⟨3170712265544739793622291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2113808177029826529081527 3170712265544739793622291)
        ·
          refine ⟨4756068398317109690433437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3170712265544739793622291 4756068398317109690433437)
          ·
            refine ⟨1783525649368916133912539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4756068398317109690433437 1783525649368916133912539)
            ·
              refine ⟨2675288474053374200868809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1783525649368916133912539 2675288474053374200868809)
              ·
                refine ⟨2006466355540030650651607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2675288474053374200868809 2006466355540030650651607)
                ·
                  refine ⟨3009699533310045975977411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2006466355540030650651607 3009699533310045975977411)
                  ·
                    refine ⟨4514549299965068963966117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3009699533310045975977411 4514549299965068963966117)
                    ·
                      refine ⟨846477993743450430743647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4514549299965068963966117 846477993743450430743647)
                      ·
                        rfl

theorem cell23_1648510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_1648510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1648510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1648510 prefixEnd_1648510 := by exact prefixLift 1648510
  have htrace : WordTrace (prefixWord ++ tailWord_1648510) baseStart_1648510 baseEnd_1648510 := by
    simpa [prefixWord, tailWord_1648510, baseEnd_1648510] using wordTrace_append hprefix tailTrace_1648510
  have hstable : (prefixWord ++ tailWord_1648510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1648510).length < 2 ^ (prefixWord ++ tailWord_1648510).sum := by decide
  have hdescent : baseEnd_1648510 < baseStart_1648510 := by decide
  rcases family_descends (prefixWord ++ tailWord_1648510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1648513 : List Nat := [1, 2, 4, 4, 1, 1, 1, 1, 3, 2, 3]
def baseStart_1648513 : Nat := 118140960795 + 1648513 * 2 ^ 59
def prefixEnd_1648513 : Nat := 4983230072969 + 3 ^ 40 * 1648513 * 2
def baseEnd_1648513 : Nat := 846479534185413919006133

theorem tailTrace_1648513 : CollatzResearch.WordTrace tailWord_1648513 prefixEnd_1648513 846479534185413919006133 := by
  unfold tailWord_1648513
  simp only [CollatzResearch.WordTrace]
  refine ⟨60126208676726419450678193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40084139117817612967118795 60126208676726419450678193)
  ·
    refine ⟨45094656507544814588008645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60126208676726419450678193 45094656507544814588008645)
    ·
      refine ⟨8455248095164652735251621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45094656507544814588008645 8455248095164652735251621)
      ·
        refine ⟨1585359017843372387859679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8455248095164652735251621 1585359017843372387859679)
        ·
          refine ⟨2378038526765058581789519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1585359017843372387859679 2378038526765058581789519)
          ·
            refine ⟨3567057790147587872684279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2378038526765058581789519 3567057790147587872684279)
            ·
              refine ⟨5350586685221381809026419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3567057790147587872684279 5350586685221381809026419)
              ·
                refine ⟨8025880027832072713539629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5350586685221381809026419 8025880027832072713539629)
                ·
                  refine ⟨3009705010437027267577361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8025880027832072713539629 3009705010437027267577361)
                  ·
                    refine ⟨2257278757827770450683021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3009705010437027267577361 2257278757827770450683021)
                    ·
                      refine ⟨846479534185413919006133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2257278757827770450683021 846479534185413919006133)
                      ·
                        rfl

theorem cell23_1648513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_1648513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1648513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1648513 prefixEnd_1648513 := by exact prefixLift 1648513
  have htrace : WordTrace (prefixWord ++ tailWord_1648513) baseStart_1648513 baseEnd_1648513 := by
    simpa [prefixWord, tailWord_1648513, baseEnd_1648513] using wordTrace_append hprefix tailTrace_1648513
  have hstable : (prefixWord ++ tailWord_1648513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1648513).length < 2 ^ (prefixWord ++ tailWord_1648513).sum := by decide
  have hdescent : baseEnd_1648513 < baseStart_1648513 := by decide
  rcases family_descends (prefixWord ++ tailWord_1648513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1648530 : List Nat := [3, 2, 3, 2, 1, 2, 3, 1, 1, 2, 3]
def baseStart_1648530 : Nat := 118140960795 + 1648530 * 2 ^ 59
def prefixEnd_1648530 : Nat := 4983230072969 + 3 ^ 40 * 1648530 * 2
def baseEnd_1648530 : Nat := 846488263356540352493555

theorem tailTrace_1648530 : CollatzResearch.WordTrace tailWord_1648530 prefixEnd_1648530 846488263356540352493555 := by
  unfold tailWord_1648530
  simp only [CollatzResearch.WordTrace]
  refine ⟨15031707179416207838511761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40084552478443220902698029 15031707179416207838511761)
  ·
    refine ⟨11273780384562155878883821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15031707179416207838511761 11273780384562155878883821)
    ·
      refine ⟨4227667644210808454581433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11273780384562155878883821 4227667644210808454581433)
      ·
        refine ⟨3170750733158106340936075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4227667644210808454581433 3170750733158106340936075)
        ·
          refine ⟨4756126099737159511404113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3170750733158106340936075 4756126099737159511404113)
          ·
            refine ⟨3567094574802869633553085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4756126099737159511404113 3567094574802869633553085)
            ·
              refine ⟨1337660465551076112582407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3567094574802869633553085 1337660465551076112582407)
              ·
                refine ⟨2006490698326614168873611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1337660465551076112582407 2006490698326614168873611)
                ·
                  refine ⟨3009736047489921253310417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2006490698326614168873611 3009736047489921253310417)
                  ·
                    refine ⟨2257302035617440939982813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3009736047489921253310417 2257302035617440939982813)
                    ·
                      refine ⟨846488263356540352493555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2257302035617440939982813 846488263356540352493555)
                      ·
                        rfl

theorem cell23_1648530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 3, 1, 1, 2, 3].length) (baseStart_1648530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1648530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1648530 prefixEnd_1648530 := by exact prefixLift 1648530
  have htrace : WordTrace (prefixWord ++ tailWord_1648530) baseStart_1648530 baseEnd_1648530 := by
    simpa [prefixWord, tailWord_1648530, baseEnd_1648530] using wordTrace_append hprefix tailTrace_1648530
  have hstable : (prefixWord ++ tailWord_1648530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1648530).length < 2 ^ (prefixWord ++ tailWord_1648530).sum := by decide
  have hdescent : baseEnd_1648530 < baseStart_1648530 := by decide
  rcases family_descends (prefixWord ++ tailWord_1648530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1648569 : List Nat := [1, 2, 1, 4, 2, 1, 1, 2, 2, 4, 3]
def baseStart_1648569 : Nat := 118140960795 + 1648569 * 2 ^ 59
def prefixEnd_1648569 : Nat := 4983230072969 + 3 ^ 40 * 1648569 * 2
def baseEnd_1648569 : Nat := 846508289102065699905875

theorem tailTrace_1648569 : CollatzResearch.WordTrace tailWord_1648569 prefixEnd_1648569 846508289102065699905875 := by
  unfold tailWord_1648569
  simp only [CollatzResearch.WordTrace]
  refine ⟨60128251164523541014716761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40085500776349027343144507 60128251164523541014716761)
  ·
    refine ⟨45096188373392655761037571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60128251164523541014716761 45096188373392655761037571)
    ·
      refine ⟨67644282560088983641556357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45096188373392655761037571 67644282560088983641556357)
      ·
        refine ⟨12683302980016684432791817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67644282560088983641556357 12683302980016684432791817)
        ·
          refine ⟨9512477235012513324593863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12683302980016684432791817 9512477235012513324593863)
          ·
            refine ⟨14268715852518769986890795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9512477235012513324593863 14268715852518769986890795)
            ·
              refine ⟨21403073778778154980336193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14268715852518769986890795 21403073778778154980336193)
              ·
                refine ⟨16052305334083616235252145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21403073778778154980336193 16052305334083616235252145)
                ·
                  refine ⟨12039229000562712176439109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16052305334083616235252145 12039229000562712176439109)
                  ·
                    refine ⟨2257355437605508533082333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12039229000562712176439109 2257355437605508533082333)
                    ·
                      refine ⟨846508289102065699905875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2257355437605508533082333 846508289102065699905875)
                      ·
                        rfl

theorem cell23_1648569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 2, 2, 4, 3].length) (baseStart_1648569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1648569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1648569 prefixEnd_1648569 := by exact prefixLift 1648569
  have htrace : WordTrace (prefixWord ++ tailWord_1648569) baseStart_1648569 baseEnd_1648569 := by
    simpa [prefixWord, tailWord_1648569, baseEnd_1648569] using wordTrace_append hprefix tailTrace_1648569
  have hstable : (prefixWord ++ tailWord_1648569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1648569).length < 2 ^ (prefixWord ++ tailWord_1648569).sum := by decide
  have hdescent : baseEnd_1648569 < baseStart_1648569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1648569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1648599 : List Nat := [1, 1, 3, 2, 1, 1, 3, 1, 4, 3, 3]
def baseStart_1648599 : Nat := 118140960795 + 1648599 * 2 ^ 59
def prefixEnd_1648599 : Nat := 4983230072969 + 3 ^ 40 * 1648599 * 2
def baseEnd_1648599 : Nat := 846523693521700582530737

theorem tailTrace_1648599 : CollatzResearch.WordTrace tailWord_1648599 prefixEnd_1648599 846523693521700582530737 := by
  unfold tailWord_1648599
  simp only [CollatzResearch.WordTrace]
  refine ⟨60129345354414856138308851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40086230236276570758872567 60129345354414856138308851)
  ·
    refine ⟨90194018031622284207463277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60129345354414856138308851 90194018031622284207463277)
    ·
      refine ⟨33822756761858356577798729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90194018031622284207463277 33822756761858356577798729)
      ·
        refine ⟨25367067571393767433349047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33822756761858356577798729 25367067571393767433349047)
        ·
          refine ⟨38050601357090651150023571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25367067571393767433349047 38050601357090651150023571)
          ·
            refine ⟨57075902035635976725035357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38050601357090651150023571 57075902035635976725035357)
            ·
              refine ⟨21403463263363491271888259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57075902035635976725035357 21403463263363491271888259)
              ·
                refine ⟨32105194895045236907832389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21403463263363491271888259 32105194895045236907832389)
                ·
                  refine ⟨6019724042820981920218573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32105194895045236907832389 6019724042820981920218573)
                  ·
                    refine ⟨2257396516057868220081965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6019724042820981920218573 2257396516057868220081965)
                    ·
                      refine ⟨846523693521700582530737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2257396516057868220081965 846523693521700582530737)
                      ·
                        rfl

theorem cell23_1648599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 4, 3, 3].length) (baseStart_1648599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1648599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1648599 prefixEnd_1648599 := by exact prefixLift 1648599
  have htrace : WordTrace (prefixWord ++ tailWord_1648599) baseStart_1648599 baseEnd_1648599 := by
    simpa [prefixWord, tailWord_1648599, baseEnd_1648599] using wordTrace_append hprefix tailTrace_1648599
  have hstable : (prefixWord ++ tailWord_1648599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1648599).length < 2 ^ (prefixWord ++ tailWord_1648599).sum := by decide
  have hdescent : baseEnd_1648599 < baseStart_1648599 := by decide
  rcases family_descends (prefixWord ++ tailWord_1648599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1648639 : List Nat := [1, 1, 2, 2, 1, 2, 1, 2, 6, 1, 4]
def baseStart_1648639 : Nat := 118140960795 + 1648639 * 2 ^ 59
def prefixEnd_1648639 : Nat := 4983230072969 + 3 ^ 40 * 1648639 * 2
def baseEnd_1648639 : Nat := 846544232747880426030553

theorem tailTrace_1648639 : CollatzResearch.WordTrace tailWord_1648639 prefixEnd_1648639 846544232747880426030553 := by
  unfold tailWord_1648639
  simp only [CollatzResearch.WordTrace]
  refine ⟨60130804274269942969764971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40087202849513295313176647 60130804274269942969764971)
  ·
    refine ⟨90196206411404914454647457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60130804274269942969764971 90196206411404914454647457)
    ·
      refine ⟨67647154808553685840985593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90196206411404914454647457 67647154808553685840985593)
      ·
        refine ⟨50735366106415264380739195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67647154808553685840985593 50735366106415264380739195)
        ·
          refine ⟨76103049159622896571108793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50735366106415264380739195 76103049159622896571108793)
          ·
            refine ⟨57077286869717172428331595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76103049159622896571108793 57077286869717172428331595)
            ·
              refine ⟨85615930304575758642497393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57077286869717172428331595 85615930304575758642497393)
              ·
                refine ⟨64211947728431818981873045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85615930304575758642497393 64211947728431818981873045)
                ·
                  refine ⟨3009935049770241514775299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 64211947728431818981873045 3009935049770241514775299)
                  ·
                    refine ⟨4514902574655362272162949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3009935049770241514775299 4514902574655362272162949)
                    ·
                      refine ⟨846544232747880426030553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4514902574655362272162949 846544232747880426030553)
                      ·
                        rfl

theorem cell23_1648639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 6, 1, 4].length) (baseStart_1648639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1648639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1648639 prefixEnd_1648639 := by exact prefixLift 1648639
  have htrace : WordTrace (prefixWord ++ tailWord_1648639) baseStart_1648639 baseEnd_1648639 := by
    simpa [prefixWord, tailWord_1648639, baseEnd_1648639] using wordTrace_append hprefix tailTrace_1648639
  have hstable : (prefixWord ++ tailWord_1648639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1648639).length < 2 ^ (prefixWord ++ tailWord_1648639).sum := by decide
  have hdescent : baseEnd_1648639 < baseStart_1648639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1648639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1648710 : List Nat := [6, 1, 1, 1, 1, 1, 1, 4, 2, 2, 3]
def baseStart_1648710 : Nat := 118140960795 + 1648710 * 2 ^ 59
def prefixEnd_1648710 : Nat := 4983230072969 + 3 ^ 40 * 1648710 * 2
def baseEnd_1648710 : Nat := 846580689874349648242727

theorem tailTrace_1648710 : CollatzResearch.WordTrace tailWord_1648710 prefixEnd_1648710 846580689874349648242727 := by
  unfold tailWord_1648710
  simp only [CollatzResearch.WordTrace]
  refine ⟨1879168558031647565487487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 40088929238008481397066389 1879168558031647565487487)
  ·
    refine ⟨2818752837047471348231231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1879168558031647565487487 2818752837047471348231231)
    ·
      refine ⟨4228129255571207022346847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2818752837047471348231231 4228129255571207022346847)
      ·
        refine ⟨6342193883356810533520271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4228129255571207022346847 6342193883356810533520271)
        ·
          refine ⟨9513290825035215800280407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6342193883356810533520271 9513290825035215800280407)
          ·
            refine ⟨14269936237552823700420611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9513290825035215800280407 14269936237552823700420611)
            ·
              refine ⟨21404904356329235550630917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14269936237552823700420611 21404904356329235550630917)
              ·
                refine ⟨4013419566811731665743297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21404904356329235550630917 4013419566811731665743297)
                ·
                  refine ⟨3010064675108798749307473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4013419566811731665743297 3010064675108798749307473)
                  ·
                    refine ⟨2257548506331599061980605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3010064675108798749307473 2257548506331599061980605)
                    ·
                      refine ⟨846580689874349648242727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2257548506331599061980605 846580689874349648242727)
                      ·
                        rfl

theorem cell23_1648710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 4, 2, 2, 3].length) (baseStart_1648710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1648710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1648710 prefixEnd_1648710 := by exact prefixLift 1648710
  have htrace : WordTrace (prefixWord ++ tailWord_1648710) baseStart_1648710 baseEnd_1648710 := by
    simpa [prefixWord, tailWord_1648710, baseEnd_1648710] using wordTrace_append hprefix tailTrace_1648710
  have hstable : (prefixWord ++ tailWord_1648710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1648710).length < 2 ^ (prefixWord ++ tailWord_1648710).sum := by decide
  have hdescent : baseEnd_1648710 < baseStart_1648710 := by decide
  rcases family_descends (prefixWord ++ tailWord_1648710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1648773 : List Nat := [1, 3, 1, 1, 5, 2, 1, 1, 4, 4]
def baseStart_1648773 : Nat := 118140960795 + 1648773 * 2 ^ 59
def prefixEnd_1648773 : Nat := 4983230072969 + 3 ^ 40 * 1648773 * 2
def baseEnd_1648773 : Nat := 282204346385194300584979

theorem tailTrace_1648773 : CollatzResearch.WordTrace tailWord_1648773 prefixEnd_1648773 282204346385194300584979 := by
  unfold tailWord_1648773
  simp only [CollatzResearch.WordTrace]
  refine ⟨60135691655784483855142973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40090461103856322570095315 60135691655784483855142973)
  ·
    refine ⟨22550884370919181445678615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60135691655784483855142973 22550884370919181445678615)
    ·
      refine ⟨33826326556378772168517923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22550884370919181445678615 33826326556378772168517923)
      ·
        refine ⟨50739489834568158252776885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33826326556378772168517923 50739489834568158252776885)
        ·
          refine ⟨4756827171990764836197833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 50739489834568158252776885 4756827171990764836197833)
          ·
            refine ⟨3567620378993073627148375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4756827171990764836197833 3567620378993073627148375)
            ·
              refine ⟨5351430568489610440722563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3567620378993073627148375 5351430568489610440722563)
              ·
                refine ⟨8027145852734415661083845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5351430568489610440722563 8027145852734415661083845)
                ·
                  refine ⟨1505089847387702936453221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8027145852734415661083845 1505089847387702936453221)
                  ·
                    refine ⟨282204346385194300584979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1505089847387702936453221 282204346385194300584979)
                    ·
                      rfl

theorem cell23_1648773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 1, 4, 4].length) (baseStart_1648773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1648773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1648773 prefixEnd_1648773 := by exact prefixLift 1648773
  have htrace : WordTrace (prefixWord ++ tailWord_1648773) baseStart_1648773 baseEnd_1648773 := by
    simpa [prefixWord, tailWord_1648773, baseEnd_1648773] using wordTrace_append hprefix tailTrace_1648773
  have hstable : (prefixWord ++ tailWord_1648773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1648773).length < 2 ^ (prefixWord ++ tailWord_1648773).sum := by decide
  have hdescent : baseEnd_1648773 < baseStart_1648773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1648773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1648779 : List Nat := [1, 1, 1, 1, 4, 1, 1, 1, 1, 4, 7]
def baseStart_1648779 : Nat := 118140960795 + 1648779 * 2 ^ 59
def prefixEnd_1648779 : Nat := 4983230072969 + 3 ^ 40 * 1648779 * 2
def baseEnd_1648779 : Nat := 846616120039509878279909

theorem tailTrace_1648779 : CollatzResearch.WordTrace tailWord_1648779 prefixEnd_1648779 846616120039509878279909 := by
  unfold tailWord_1648779
  simp only [CollatzResearch.WordTrace]
  refine ⟨60135910493762746879861391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40090606995841831253240927 60135910493762746879861391)
  ·
    refine ⟨90203865740644120319792087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60135910493762746879861391 90203865740644120319792087)
    ·
      refine ⟨135305798610966180479688131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90203865740644120319792087 135305798610966180479688131)
      ·
        refine ⟨202958697916449270719532197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135305798610966180479688131 202958697916449270719532197)
        ·
          refine ⟨38054755859334238259912287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 202958697916449270719532197 38054755859334238259912287)
          ·
            refine ⟨57082133789001357389868431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38054755859334238259912287 57082133789001357389868431)
            ·
              refine ⟨85623200683502036084802647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57082133789001357389868431 85623200683502036084802647)
              ·
                refine ⟨128434801025253054127203971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85623200683502036084802647 128434801025253054127203971)
                ·
                  refine ⟨192652201537879581190805957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 128434801025253054127203971 192652201537879581190805957)
                  ·
                    refine ⟨36122287788352421473276117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 192652201537879581190805957 36122287788352421473276117)
                    ·
                      refine ⟨846616120039509878279909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 36122287788352421473276117 846616120039509878279909)
                      ·
                        rfl

theorem cell23_1648779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 4, 7].length) (baseStart_1648779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1648779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1648779 prefixEnd_1648779 := by exact prefixLift 1648779
  have htrace : WordTrace (prefixWord ++ tailWord_1648779) baseStart_1648779 baseEnd_1648779 := by
    simpa [prefixWord, tailWord_1648779, baseEnd_1648779] using wordTrace_append hprefix tailTrace_1648779
  have hstable : (prefixWord ++ tailWord_1648779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1648779).length < 2 ^ (prefixWord ++ tailWord_1648779).sum := by decide
  have hdescent : baseEnd_1648779 < baseStart_1648779 := by decide
  rcases family_descends (prefixWord ++ tailWord_1648779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1648786 : List Nat := [3, 2, 3, 1, 1, 1, 2, 10]
def baseStart_1648786 : Nat := 118140960795 + 1648786 * 2 ^ 59
def prefixEnd_1648786 : Nat := 4983230072969 + 3 ^ 40 * 1648786 * 2
def baseEnd_1648786 : Nat := 31356285718670050033051

theorem tailTrace_1648786 : CollatzResearch.WordTrace tailWord_1648786 prefixEnd_1648786 31356285718670050033051 := by
  unfold tailWord_1648786
  simp only [CollatzResearch.WordTrace]
  refine ⟨15034041451184346768841553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40090777203158258050244141 15034041451184346768841553)
  ·
    refine ⟨11275531088388260076631165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15034041451184346768841553 11275531088388260076631165)
    ·
      refine ⟨4228324158145597528736687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11275531088388260076631165 4228324158145597528736687)
      ·
        refine ⟨6342486237218396293105031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4228324158145597528736687 6342486237218396293105031)
        ·
          refine ⟨9513729355827594439657547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6342486237218396293105031 9513729355827594439657547)
          ·
            refine ⟨14270594033741391659486321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9513729355827594439657547 14270594033741391659486321)
            ·
              refine ⟨10702945525306043744614741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14270594033741391659486321 10702945525306043744614741)
              ·
                refine ⟨31356285718670050033051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 10702945525306043744614741 31356285718670050033051)
                ·
                  rfl

theorem cell23_1648786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 10].length) (baseStart_1648786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1648786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1648786 prefixEnd_1648786 := by exact prefixLift 1648786
  have htrace : WordTrace (prefixWord ++ tailWord_1648786) baseStart_1648786 baseEnd_1648786 := by
    simpa [prefixWord, tailWord_1648786, baseEnd_1648786] using wordTrace_append hprefix tailTrace_1648786
  have hstable : (prefixWord ++ tailWord_1648786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1648786).length < 2 ^ (prefixWord ++ tailWord_1648786).sum := by decide
  have hdescent : baseEnd_1648786 < baseStart_1648786 := by decide
  rcases family_descends (prefixWord ++ tailWord_1648786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1648800 : List Nat := [2, 1, 1, 4, 2, 3, 2, 2, 1, 2, 3]
def baseStart_1648800 : Nat := 118140960795 + 1648800 * 2 ^ 59
def prefixEnd_1648800 : Nat := 4983230072969 + 3 ^ 40 * 1648800 * 2
def baseEnd_1648800 : Nat := 846626903133254296117313

theorem tailTrace_1648800 : CollatzResearch.WordTrace tailWord_1648800 prefixEnd_1648800 846626903133254296117313 := by
  unfold tailWord_1648800
  simp only [CollatzResearch.WordTrace]
  refine ⟨30068338213343333733187927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40091117617791111644250569 30068338213343333733187927)
  ·
    refine ⟨45102507320015000599781891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30068338213343333733187927 45102507320015000599781891)
    ·
      refine ⟨67653760980022500899672837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45102507320015000599781891 67653760980022500899672837)
      ·
        refine ⟨12685080183754218918688657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67653760980022500899672837 12685080183754218918688657)
        ·
          refine ⟨9513810137815664189016493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12685080183754218918688657 9513810137815664189016493)
          ·
            refine ⟨3567678801680874070881185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9513810137815664189016493 3567678801680874070881185)
            ·
              refine ⟨2675759101260655553160889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3567678801680874070881185 2675759101260655553160889)
              ·
                refine ⟨2006819325945491664870667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2675759101260655553160889 2006819325945491664870667)
                ·
                  refine ⟨3010228988918237497306001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2006819325945491664870667 3010228988918237497306001)
                  ·
                    refine ⟨2257671741688678122979501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3010228988918237497306001 2257671741688678122979501)
                    ·
                      refine ⟨846626903133254296117313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2257671741688678122979501 846626903133254296117313)
                      ·
                        rfl

theorem cell23_1648800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 2, 2, 1, 2, 3].length) (baseStart_1648800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1648800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1648800 prefixEnd_1648800 := by exact prefixLift 1648800
  have htrace : WordTrace (prefixWord ++ tailWord_1648800) baseStart_1648800 baseEnd_1648800 := by
    simpa [prefixWord, tailWord_1648800, baseEnd_1648800] using wordTrace_append hprefix tailTrace_1648800
  have hstable : (prefixWord ++ tailWord_1648800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1648800).length < 2 ^ (prefixWord ++ tailWord_1648800).sum := by decide
  have hdescent : baseEnd_1648800 < baseStart_1648800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1648800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1648900 : List Nat := [2, 3, 2, 2, 3, 1, 1, 1, 2, 2, 4]
def baseStart_1648900 : Nat := 118140960795 + 1648900 * 2 ^ 59
def prefixEnd_1648900 : Nat := 4983230072969 + 3 ^ 40 * 1648900 * 2
def baseEnd_1648900 : Nat := 846678251198703904866853

theorem tailTrace_1648900 : CollatzResearch.WordTrace tailWord_1648900 prefixEnd_1648900 846678251198703904866853 := by
  unfold tailWord_1648900
  simp only [CollatzResearch.WordTrace]
  refine ⟨30070161863162192272508077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40093549150882923030010769 30070161863162192272508077)
  ·
    refine ⟨11276310698685822102190529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30070161863162192272508077 11276310698685822102190529)
    ·
      refine ⟨8457233024014366576642897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11276310698685822102190529 8457233024014366576642897)
      ·
        refine ⟨6342924768010774932482173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8457233024014366576642897 6342924768010774932482173)
        ·
          refine ⟨2378596788004040599680815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6342924768010774932482173 2378596788004040599680815)
          ·
            refine ⟨3567895182006060899521223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2378596788004040599680815 3567895182006060899521223)
            ·
              refine ⟨5351842773009091349281835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3567895182006060899521223 5351842773009091349281835)
              ·
                refine ⟨8027764159513637023922753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5351842773009091349281835 8027764159513637023922753)
                ·
                  refine ⟨6020823119635227767942065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8027764159513637023922753 6020823119635227767942065)
                  ·
                    refine ⟨4515617339726420825956549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6020823119635227767942065 4515617339726420825956549)
                    ·
                      refine ⟨846678251198703904866853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4515617339726420825956549 846678251198703904866853)
                      ·
                        rfl

theorem cell23_1648900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 1, 2, 2, 4].length) (baseStart_1648900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1648900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1648900 prefixEnd_1648900 := by exact prefixLift 1648900
  have htrace : WordTrace (prefixWord ++ tailWord_1648900) baseStart_1648900 baseEnd_1648900 := by
    simpa [prefixWord, tailWord_1648900, baseEnd_1648900] using wordTrace_append hprefix tailTrace_1648900
  have hstable : (prefixWord ++ tailWord_1648900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1648900).length < 2 ^ (prefixWord ++ tailWord_1648900).sum := by decide
  have hdescent : baseEnd_1648900 < baseStart_1648900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1648900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1648923 : List Nat := [1, 1, 1, 1, 1, 1, 9, 1, 2, 5]
def baseStart_1648923 : Nat := 118140960795 + 1648923 * 2 ^ 59
def prefixEnd_1648923 : Nat := 4983230072969 + 3 ^ 40 * 1648923 * 2
def baseEnd_1648923 : Nat := 282230020417919104959749

theorem tailTrace_1648923 : CollatzResearch.WordTrace tailWord_1648923 prefixEnd_1648923 282230020417919104959749 := by
  unfold tailWord_1648923
  simp only [CollatzResearch.WordTrace]
  refine ⟨60141162605241059473103423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40094108403494039648735615 60141162605241059473103423)
  ·
    refine ⟨90211743907861589209655135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60141162605241059473103423 90211743907861589209655135)
    ·
      refine ⟨135317615861792383814482703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90211743907861589209655135 135317615861792383814482703)
      ·
        refine ⟨202976423792688575721724055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135317615861792383814482703 202976423792688575721724055)
        ·
          refine ⟨304464635689032863582586083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202976423792688575721724055 304464635689032863582586083)
          ·
            refine ⟨456696953533549295373879125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 304464635689032863582586083 456696953533549295373879125)
            ·
              refine ⟨2675958712110640402581323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 456696953533549295373879125 2675958712110640402581323)
              ·
                refine ⟨4013938068165960603871985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2675958712110640402581323 4013938068165960603871985)
                ·
                  refine ⟨3010453551124470452903989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4013938068165960603871985 3010453551124470452903989)
                  ·
                    refine ⟨282230020417919104959749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3010453551124470452903989 282230020417919104959749)
                    ·
                      rfl

theorem cell23_1648923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 9, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 9, 1, 2, 5].length) (baseStart_1648923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1648923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1648923 prefixEnd_1648923 := by exact prefixLift 1648923
  have htrace : WordTrace (prefixWord ++ tailWord_1648923) baseStart_1648923 baseEnd_1648923 := by
    simpa [prefixWord, tailWord_1648923, baseEnd_1648923] using wordTrace_append hprefix tailTrace_1648923
  have hstable : (prefixWord ++ tailWord_1648923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1648923).length < 2 ^ (prefixWord ++ tailWord_1648923).sum := by decide
  have hdescent : baseEnd_1648923 < baseStart_1648923 := by decide
  rcases family_descends (prefixWord ++ tailWord_1648923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1648938 : List Nat := [3, 1, 4, 2, 3, 1, 1, 2, 2, 2, 2]
def baseStart_1648938 : Nat := 118140960795 + 1648938 * 2 ^ 59
def prefixEnd_1648938 : Nat := 4983230072969 + 3 ^ 40 * 1648938 * 2
def baseEnd_1648938 : Nat := 846697763463574756191679

theorem tailTrace_1648938 : CollatzResearch.WordTrace tailWord_1648938 prefixEnd_1648938 846697763463574756191679 := by
  unfold tailWord_1648938
  simp only [CollatzResearch.WordTrace]
  refine ⟨15035427425046679258724867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40094473133457811356599645 15035427425046679258724867)
  ·
    refine ⟨22553141137570018888087301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15035427425046679258724867 22553141137570018888087301)
    ·
      refine ⟨4228713963294378541516369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22553141137570018888087301 4228713963294378541516369)
      ·
        refine ⟨3171535472470783906137277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4228713963294378541516369 3171535472470783906137277)
        ·
          refine ⟨1189325802176543964801479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3171535472470783906137277 1189325802176543964801479)
          ·
            refine ⟨1783988703264815947202219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1189325802176543964801479 1783988703264815947202219)
            ·
              refine ⟨2675983054897223920803329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1783988703264815947202219 2675983054897223920803329)
              ·
                refine ⟨2006987291172917940602497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2675983054897223920803329 2006987291172917940602497)
                ·
                  refine ⟨1505240468379688455451873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2006987291172917940602497 1505240468379688455451873)
                  ·
                    refine ⟨1128930351284766341588905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1505240468379688455451873 1128930351284766341588905)
                    ·
                      refine ⟨846697763463574756191679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1128930351284766341588905 846697763463574756191679)
                      ·
                        rfl

theorem cell23_1648938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 1, 2, 2, 2, 2].length) (baseStart_1648938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1648938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1648938 prefixEnd_1648938 := by exact prefixLift 1648938
  have htrace : WordTrace (prefixWord ++ tailWord_1648938) baseStart_1648938 baseEnd_1648938 := by
    simpa [prefixWord, tailWord_1648938, baseEnd_1648938] using wordTrace_append hprefix tailTrace_1648938
  have hstable : (prefixWord ++ tailWord_1648938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1648938).length < 2 ^ (prefixWord ++ tailWord_1648938).sum := by decide
  have hdescent : baseEnd_1648938 < baseStart_1648938 := by decide
  rcases family_descends (prefixWord ++ tailWord_1648938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1648943 : List Nat := [1, 1, 2, 1, 2, 1, 4, 4, 2, 1, 4]
def baseStart_1648943 : Nat := 118140960795 + 1648943 * 2 ^ 59
def prefixEnd_1648943 : Nat := 4983230072969 + 3 ^ 40 * 1648943 * 2
def baseEnd_1648943 : Nat := 846700330866847236629155

theorem tailTrace_1648943 : CollatzResearch.WordTrace tailWord_1648943 prefixEnd_1648943 846700330866847236629155 := by
  unfold tailWord_1648943
  simp only [CollatzResearch.WordTrace]
  refine ⟨60141892065168602888831483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40094594710112401925887655 60141892065168602888831483)
  ·
    refine ⟨90212838097752904333247225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60141892065168602888831483 90212838097752904333247225)
    ·
      refine ⟨67659628573314678249935419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90212838097752904333247225 67659628573314678249935419)
      ·
        refine ⟨101489442859972017374903129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67659628573314678249935419 101489442859972017374903129)
        ·
          refine ⟨76117082144979013031177347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101489442859972017374903129 76117082144979013031177347)
          ·
            refine ⟨114175623217468519546766021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76117082144979013031177347 114175623217468519546766021)
            ·
              refine ⟨21407929353275347415018629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 114175623217468519546766021 21407929353275347415018629)
              ·
                refine ⟨4013986753739127640315993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21407929353275347415018629 4013986753739127640315993)
                ·
                  refine ⟨3010490065304345730236995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4013986753739127640315993 3010490065304345730236995)
                  ·
                    refine ⟨4515735097956518595355493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3010490065304345730236995 4515735097956518595355493)
                    ·
                      refine ⟨846700330866847236629155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4515735097956518595355493 846700330866847236629155)
                      ·
                        rfl

theorem cell23_1648943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 4, 2, 1, 4].length) (baseStart_1648943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1648943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1648943 prefixEnd_1648943 := by exact prefixLift 1648943
  have htrace : WordTrace (prefixWord ++ tailWord_1648943) baseStart_1648943 baseEnd_1648943 := by
    simpa [prefixWord, tailWord_1648943, baseEnd_1648943] using wordTrace_append hprefix tailTrace_1648943
  have hstable : (prefixWord ++ tailWord_1648943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1648943).length < 2 ^ (prefixWord ++ tailWord_1648943).sum := by decide
  have hdescent : baseEnd_1648943 < baseStart_1648943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1648943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1648963 : List Nat := [1, 1, 1, 3, 1, 3, 3, 2, 1, 4, 3]
def baseStart_1648963 : Nat := 118140960795 + 1648963 * 2 ^ 59
def prefixEnd_1648963 : Nat := 4983230072969 + 3 ^ 40 * 1648963 * 2
def baseEnd_1648963 : Nat := 846710600479937158379063

theorem tailTrace_1648963 : CollatzResearch.WordTrace tailWord_1648963 prefixEnd_1648963 846710600479937158379063 := by
  unfold tailWord_1648963
  simp only [CollatzResearch.WordTrace]
  refine ⟨60142621525096146304559543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40095081016730764203039695 60142621525096146304559543)
  ·
    refine ⟨90213932287644219456839315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60142621525096146304559543 90213932287644219456839315)
    ·
      refine ⟨135320898431466329185258973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90213932287644219456839315 135320898431466329185258973)
      ·
        refine ⟨50745336911799873444472115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135320898431466329185258973 50745336911799873444472115)
        ·
          refine ⟨76118005367699810166708173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50745336911799873444472115 76118005367699810166708173)
          ·
            refine ⟨28544252012887428812515565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76118005367699810166708173 28544252012887428812515565)
            ·
              refine ⟨10704094504832785804693337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28544252012887428812515565 10704094504832785804693337)
              ·
                refine ⟨8028070878624589353520003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10704094504832785804693337 8028070878624589353520003)
                ·
                  refine ⟨12042106317936884030280005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8028070878624589353520003 12042106317936884030280005)
                  ·
                    refine ⟨2257894934613165755677501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12042106317936884030280005 2257894934613165755677501)
                    ·
                      refine ⟨846710600479937158379063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2257894934613165755677501 846710600479937158379063)
                      ·
                        rfl

theorem cell23_1648963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 2, 1, 4, 3].length) (baseStart_1648963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1648963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1648963 prefixEnd_1648963 := by exact prefixLift 1648963
  have htrace : WordTrace (prefixWord ++ tailWord_1648963) baseStart_1648963 baseEnd_1648963 := by
    simpa [prefixWord, tailWord_1648963, baseEnd_1648963] using wordTrace_append hprefix tailTrace_1648963
  have hstable : (prefixWord ++ tailWord_1648963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1648963).length < 2 ^ (prefixWord ++ tailWord_1648963).sum := by decide
  have hdescent : baseEnd_1648963 < baseStart_1648963 := by decide
  rcases family_descends (prefixWord ++ tailWord_1648963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1648980 : List Nat := [2, 4, 1, 1, 2, 2, 2, 1, 1, 4, 3]
def baseStart_1648980 : Nat := 118140960795 + 1648980 * 2 ^ 59
def prefixEnd_1648980 : Nat := 4983230072969 + 3 ^ 40 * 1648980 * 2
def baseEnd_1648980 : Nat := 846719329651063591866485

theorem tailTrace_1648980 : CollatzResearch.WordTrace tailWord_1648980 prefixEnd_1648980 846719329651063591866485 := by
  unfold tailWord_1648980
  simp only [CollatzResearch.WordTrace]
  refine ⟨30071620783017279103964197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40095494377356372138618929 30071620783017279103964197)
  ·
    refine ⟨5638428896815739831993287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30071620783017279103964197 5638428896815739831993287)
    ·
      refine ⟨8457643345223609747989931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5638428896815739831993287 8457643345223609747989931)
      ·
        refine ⟨12686465017835414621984897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8457643345223609747989931 12686465017835414621984897)
        ·
          refine ⟨9514848763376560966488673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12686465017835414621984897 9514848763376560966488673)
          ·
            refine ⟨7136136572532420724866505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9514848763376560966488673 7136136572532420724866505)
            ·
              refine ⟨5352102429399315543649879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7136136572532420724866505 5352102429399315543649879)
              ·
                refine ⟨8028153644098973315474819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5352102429399315543649879 8028153644098973315474819)
                ·
                  refine ⟨12042230466148459973212229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8028153644098973315474819 12042230466148459973212229)
                  ·
                    refine ⟨2257918212402836244977293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12042230466148459973212229 2257918212402836244977293)
                    ·
                      refine ⟨846719329651063591866485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2257918212402836244977293 846719329651063591866485)
                      ·
                        rfl

theorem cell23_1648980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 1, 1, 4, 3].length) (baseStart_1648980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1648980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1648980 prefixEnd_1648980 := by exact prefixLift 1648980
  have htrace : WordTrace (prefixWord ++ tailWord_1648980) baseStart_1648980 baseEnd_1648980 := by
    simpa [prefixWord, tailWord_1648980, baseEnd_1648980] using wordTrace_append hprefix tailTrace_1648980
  have hstable : (prefixWord ++ tailWord_1648980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1648980).length < 2 ^ (prefixWord ++ tailWord_1648980).sum := by decide
  have hdescent : baseEnd_1648980 < baseStart_1648980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1648980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1649004 : List Nat := [2, 2, 1, 1, 7, 1, 1, 1, 3, 4]
def baseStart_1649004 : Nat := 118140960795 + 1649004 * 2 ^ 59
def prefixEnd_1649004 : Nat := 4983230072969 + 3 ^ 40 * 1649004 * 2
def baseEnd_1649004 : Nat := 282243884395590499322125

theorem tailTrace_1649004 : CollatzResearch.WordTrace tailWord_1649004 prefixEnd_1649004 282243884395590499322125 := by
  unfold tailWord_1649004
  simp only [CollatzResearch.WordTrace]
  refine ⟨30072058458973805153401033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40096077945298406871201377 30072058458973805153401033)
  ·
    refine ⟨22554043844230353865050775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30072058458973805153401033 22554043844230353865050775)
    ·
      refine ⟨33831065766345530797576163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22554043844230353865050775 33831065766345530797576163)
      ·
        refine ⟨50746598649518296196364245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33831065766345530797576163 50746598649518296196364245)
        ·
          refine ⟨1189373405848085067102287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 50746598649518296196364245 1189373405848085067102287)
          ·
            refine ⟨1784060108772127600653431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1189373405848085067102287 1784060108772127600653431)
            ·
              refine ⟨2676090163158191400980147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1784060108772127600653431 2676090163158191400980147)
              ·
                refine ⟨4014135244737287101470221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2676090163158191400980147 4014135244737287101470221)
                ·
                  refine ⟨1505300716776482663051333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4014135244737287101470221 1505300716776482663051333)
                  ·
                    refine ⟨282243884395590499322125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1505300716776482663051333 282243884395590499322125)
                    ·
                      rfl

theorem cell23_1649004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 1, 1, 3, 4].length) (baseStart_1649004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1649004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1649004 prefixEnd_1649004 := by exact prefixLift 1649004
  have htrace : WordTrace (prefixWord ++ tailWord_1649004) baseStart_1649004 baseEnd_1649004 := by
    simpa [prefixWord, tailWord_1649004, baseEnd_1649004] using wordTrace_append hprefix tailTrace_1649004
  have hstable : (prefixWord ++ tailWord_1649004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1649004).length < 2 ^ (prefixWord ++ tailWord_1649004).sum := by decide
  have hdescent : baseEnd_1649004 < baseStart_1649004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1649004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1649020 : List Nat := [2, 2, 2, 1, 1, 1, 2, 4, 1, 5, 2]
def baseStart_1649020 : Nat := 118140960795 + 1649020 * 2 ^ 59
def prefixEnd_1649020 : Nat := 4983230072969 + 3 ^ 40 * 1649020 * 2
def baseEnd_1649020 : Nat := 846739868877243435366301

theorem tailTrace_1649020 : CollatzResearch.WordTrace tailWord_1649020 prefixEnd_1649020 846739868877243435366301 := by
  unfold tailWord_1649020
  simp only [CollatzResearch.WordTrace]
  refine ⟨30072350242944822519692257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40096466990593096692923009 30072350242944822519692257)
  ·
    refine ⟨22554262682208616889769193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30072350242944822519692257 22554262682208616889769193)
    ·
      refine ⟨16915697011656462667326895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22554262682208616889769193 16915697011656462667326895)
      ·
        refine ⟨25373545517484694000990343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16915697011656462667326895 25373545517484694000990343)
        ·
          refine ⟨38060318276227041001485515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25373545517484694000990343 38060318276227041001485515)
          ·
            refine ⟨57090477414340561502228273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38060318276227041001485515 57090477414340561502228273)
            ·
              refine ⟨42817858060755421126671205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57090477414340561502228273 42817858060755421126671205)
              ·
                refine ⟨8028348386391641461250851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42817858060755421126671205 8028348386391641461250851)
                ·
                  refine ⟨12042522579587462191876277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8028348386391641461250851 12042522579587462191876277)
                  ·
                    refine ⟨1128986491836324580488401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12042522579587462191876277 1128986491836324580488401)
                    ·
                      refine ⟨846739868877243435366301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1128986491836324580488401 846739868877243435366301)
                      ·
                        rfl

theorem cell23_1649020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 4, 1, 5, 2].length) (baseStart_1649020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1649020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1649020 prefixEnd_1649020 := by exact prefixLift 1649020
  have htrace : WordTrace (prefixWord ++ tailWord_1649020) baseStart_1649020 baseEnd_1649020 := by
    simpa [prefixWord, tailWord_1649020, baseEnd_1649020] using wordTrace_append hprefix tailTrace_1649020
  have hstable : (prefixWord ++ tailWord_1649020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1649020).length < 2 ^ (prefixWord ++ tailWord_1649020).sum := by decide
  have hdescent : baseEnd_1649020 < baseStart_1649020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1649020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1649060 : List Nat := [2, 3, 1, 2, 1, 1, 2, 3, 4, 4]
def baseStart_1649060 : Nat := 118140960795 + 1649060 * 2 ^ 59
def prefixEnd_1649060 : Nat := 4983230072969 + 3 ^ 40 * 1649060 * 2
def baseEnd_1649060 : Nat := 282253469367807759622039

theorem tailTrace_1649060 : CollatzResearch.WordTrace tailWord_1649060 prefixEnd_1649060 282253469367807759622039 := by
  unfold tailWord_1649060
  simp only [CollatzResearch.WordTrace]
  refine ⟨30073079702872365935420317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40097439603829821247227089 30073079702872365935420317)
  ·
    refine ⟨11277404888577137225782619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30073079702872365935420317 11277404888577137225782619)
    ·
      refine ⟨16916107332865705838673929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11277404888577137225782619 16916107332865705838673929)
      ·
        refine ⟨12687080499649279379005447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16916107332865705838673929 12687080499649279379005447)
        ·
          refine ⟨19030620749473919068508171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12687080499649279379005447 19030620749473919068508171)
          ·
            refine ⟨28545931124210878602762257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19030620749473919068508171 28545931124210878602762257)
            ·
              refine ⟨21409448343158158952071693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28545931124210878602762257 21409448343158158952071693)
              ·
                refine ⟨8028543128684309607026885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21409448343158158952071693 8028543128684309607026885)
                ·
                  refine ⟨1505351836628308051317541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8028543128684309607026885 1505351836628308051317541)
                  ·
                    refine ⟨282253469367807759622039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1505351836628308051317541 282253469367807759622039)
                    ·
                      rfl

theorem cell23_1649060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 3, 4, 4].length) (baseStart_1649060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1649060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1649060 prefixEnd_1649060 := by exact prefixLift 1649060
  have htrace : WordTrace (prefixWord ++ tailWord_1649060) baseStart_1649060 baseEnd_1649060 := by
    simpa [prefixWord, tailWord_1649060, baseEnd_1649060] using wordTrace_append hprefix tailTrace_1649060
  have hstable : (prefixWord ++ tailWord_1649060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1649060).length < 2 ^ (prefixWord ++ tailWord_1649060).sum := by decide
  have hdescent : baseEnd_1649060 < baseStart_1649060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1649060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1649077 : List Nat := [1, 3, 3, 2, 3, 1, 2, 1, 1, 6]
def baseStart_1649077 : Nat := 118140960795 + 1649077 * 2 ^ 59
def prefixEnd_1649077 : Nat := 4983230072969 + 3 ^ 40 * 1649077 * 2
def baseEnd_1649077 : Nat := 282256379091516570784513

theorem tailTrace_1649077 : CollatzResearch.WordTrace tailWord_1649077 prefixEnd_1649077 282256379091516570784513 := by
  unfold tailWord_1649077
  simp only [CollatzResearch.WordTrace]
  refine ⟨60146779446683143774209485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40097852964455429182806323 60146779446683143774209485)
  ·
    refine ⟨22555042292506178915328557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60146779446683143774209485 22555042292506178915328557)
    ·
      refine ⟨8458140859689817093248209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22555042292506178915328557 8458140859689817093248209)
      ·
        refine ⟨6343605644767362819936157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8458140859689817093248209 6343605644767362819936157)
        ·
          refine ⟨2378852116787761057476059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6343605644767362819936157 2378852116787761057476059)
          ·
            refine ⟨3568278175181641586214089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2378852116787761057476059 3568278175181641586214089)
            ·
              refine ⟨2676208631386231189660567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3568278175181641586214089 2676208631386231189660567)
              ·
                refine ⟨4014312947079346784490851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2676208631386231189660567 4014312947079346784490851)
                ·
                  refine ⟨6021469420619020176736277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4014312947079346784490851 6021469420619020176736277)
                  ·
                    refine ⟨282256379091516570784513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6021469420619020176736277 282256379091516570784513)
                    ·
                      rfl

theorem cell23_1649077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 2, 1, 1, 6].length) (baseStart_1649077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1649077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1649077 prefixEnd_1649077 := by exact prefixLift 1649077
  have htrace : WordTrace (prefixWord ++ tailWord_1649077) baseStart_1649077 baseEnd_1649077 := by
    simpa [prefixWord, tailWord_1649077, baseEnd_1649077] using wordTrace_append hprefix tailTrace_1649077
  have hstable : (prefixWord ++ tailWord_1649077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1649077).length < 2 ^ (prefixWord ++ tailWord_1649077).sum := by decide
  have hdescent : baseEnd_1649077 < baseStart_1649077 := by decide
  rcases family_descends (prefixWord ++ tailWord_1649077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1649084 : List Nat := [2, 2, 2, 4, 1, 1, 1, 1, 5, 2, 2]
def baseStart_1649084 : Nat := 118140960795 + 1649084 * 2 ^ 59
def prefixEnd_1649084 : Nat := 4983230072969 + 3 ^ 40 * 1649084 * 2
def baseEnd_1649084 : Nat := 846772731639131184966007

theorem tailTrace_1649084 : CollatzResearch.WordTrace tailWord_1649084 prefixEnd_1649084 846772731639131184966007 := by
  unfold tailWord_1649084
  simp only [CollatzResearch.WordTrace]
  refine ⟨30073517378828891984857153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40098023171771855979809537 30073517378828891984857153)
  ·
    refine ⟨22555138034121668988642865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30073517378828891984857153 22555138034121668988642865)
    ·
      refine ⟨16916353525591251741482149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22555138034121668988642865 16916353525591251741482149)
      ·
        refine ⟨3171816286048359701527903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16916353525591251741482149 3171816286048359701527903)
        ·
          refine ⟨4757724429072539552291855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3171816286048359701527903 4757724429072539552291855)
          ·
            refine ⟨7136586643608809328437783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4757724429072539552291855 7136586643608809328437783)
            ·
              refine ⟨10704879965413213992656675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7136586643608809328437783 10704879965413213992656675)
              ·
                refine ⟨16057319948119820988985013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10704879965413213992656675 16057319948119820988985013)
                ·
                  refine ⟨1505373745136233217717345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16057319948119820988985013 1505373745136233217717345)
                  ·
                    refine ⟨1129030308852174913288009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1505373745136233217717345 1129030308852174913288009)
                    ·
                      refine ⟨846772731639131184966007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1129030308852174913288009 846772731639131184966007)
                      ·
                        rfl

theorem cell23_1649084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 1, 5, 2, 2].length) (baseStart_1649084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1649084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1649084 prefixEnd_1649084 := by exact prefixLift 1649084
  have htrace : WordTrace (prefixWord ++ tailWord_1649084) baseStart_1649084 baseEnd_1649084 := by
    simpa [prefixWord, tailWord_1649084, baseEnd_1649084] using wordTrace_append hprefix tailTrace_1649084
  have hstable : (prefixWord ++ tailWord_1649084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1649084).length < 2 ^ (prefixWord ++ tailWord_1649084).sum := by decide
  have hdescent : baseEnd_1649084 < baseStart_1649084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1649084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1649134 : List Nat := [4, 1, 2, 1, 2, 4, 1, 1, 1, 3, 3]
def baseStart_1649134 : Nat := 118140960795 + 1649134 * 2 ^ 59
def prefixEnd_1649134 : Nat := 4983230072969 + 3 ^ 40 * 1649134 * 2
def baseEnd_1649134 : Nat := 846798405671855989340777

theorem tailTrace_1649134 : CollatzResearch.WordTrace tailWord_1649134 prefixEnd_1649134 846798405671855989340777 := by
  unfold tailWord_1649134
  simp only [CollatzResearch.WordTrace]
  refine ⟨7518607300934580313629307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40099238938317761672689637 7518607300934580313629307)
  ·
    refine ⟨11277910951401870470443961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7518607300934580313629307 11277910951401870470443961)
    ·
      refine ⟨8458433213551402852832971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11277910951401870470443961 8458433213551402852832971)
      ·
        refine ⟨12687649820327104279249457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8458433213551402852832971 12687649820327104279249457)
        ·
          refine ⟨9515737365245328209437093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12687649820327104279249457 9515737365245328209437093)
          ·
            refine ⟨1784200755983499039269455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9515737365245328209437093 1784200755983499039269455)
            ·
              refine ⟨2676301133975248558904183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1784200755983499039269455 2676301133975248558904183)
              ·
                refine ⟨4014451700962872838356275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2676301133975248558904183 4014451700962872838356275)
                ·
                  refine ⟨6021677551444309257534413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4014451700962872838356275 6021677551444309257534413)
                  ·
                    refine ⟨2258129081791615971575405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6021677551444309257534413 2258129081791615971575405)
                    ·
                      refine ⟨846798405671855989340777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2258129081791615971575405 846798405671855989340777)
                      ·
                        rfl

theorem cell23_1649134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 1, 1, 1, 3, 3].length) (baseStart_1649134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1649134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1649134 prefixEnd_1649134 := by exact prefixLift 1649134
  have htrace : WordTrace (prefixWord ++ tailWord_1649134) baseStart_1649134 baseEnd_1649134 := by
    simpa [prefixWord, tailWord_1649134, baseEnd_1649134] using wordTrace_append hprefix tailTrace_1649134
  have hstable : (prefixWord ++ tailWord_1649134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1649134).length < 2 ^ (prefixWord ++ tailWord_1649134).sum := by decide
  have hdescent : baseEnd_1649134 < baseStart_1649134 := by decide
  rcases family_descends (prefixWord ++ tailWord_1649134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1649141 : List Nat := [1, 3, 5, 1, 3, 1, 2, 7]
def baseStart_1649141 : Nat := 118140960795 + 1649141 * 2 ^ 59
def prefixEnd_1649141 : Nat := 4983230072969 + 3 ^ 40 * 1649141 * 2
def baseEnd_1649141 : Nat := 31363037038386572664935

theorem tailTrace_1649141 : CollatzResearch.WordTrace tailWord_1649141 prefixEnd_1649141 31363037038386572664935 := by
  unfold tailWord_1649141
  simp only [CollatzResearch.WordTrace]
  refine ⟨60149113718451282704539277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40099409145634188469692851 60149113718451282704539277)
  ·
    refine ⟨22555917644419231014202229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60149113718451282704539277 22555917644419231014202229)
    ·
      refine ⟨2114617279164302907581459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22555917644419231014202229 2114617279164302907581459)
      ·
        refine ⟨3171925918746454361372189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2114617279164302907581459 3171925918746454361372189)
        ·
          refine ⟨1189472219529920385514571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3171925918746454361372189 1189472219529920385514571)
          ·
            refine ⟨1784208329294880578271857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1189472219529920385514571 1784208329294880578271857)
            ·
              refine ⟨1338156246971160433703893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1784208329294880578271857 1338156246971160433703893)
              ·
                refine ⟨31363037038386572664935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1338156246971160433703893 31363037038386572664935)
                ·
                  rfl

theorem cell23_1649141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 2, 7].length) (baseStart_1649141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1649141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1649141 prefixEnd_1649141 := by exact prefixLift 1649141
  have htrace : WordTrace (prefixWord ++ tailWord_1649141) baseStart_1649141 baseEnd_1649141 := by
    simpa [prefixWord, tailWord_1649141, baseEnd_1649141] using wordTrace_append hprefix tailTrace_1649141
  have hstable : (prefixWord ++ tailWord_1649141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1649141).length < 2 ^ (prefixWord ++ tailWord_1649141).sum := by decide
  have hdescent : baseEnd_1649141 < baseStart_1649141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1649141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1649144 : List Nat := [2, 1, 2, 1, 1, 4, 4, 2, 1, 3, 2]
def baseStart_1649144 : Nat := 118140960795 + 1649144 * 2 ^ 59
def prefixEnd_1649144 : Nat := 4983230072969 + 3 ^ 40 * 1649144 * 2
def baseEnd_1649144 : Nat := 846803540478400950215731

theorem tailTrace_1649144 : CollatzResearch.WordTrace tailWord_1649144 prefixEnd_1649144 846803540478400950215731 := by
  unfold tailWord_1649144
  simp only [CollatzResearch.WordTrace]
  refine ⟨30074611568720207108449243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40099482091626942811265657 30074611568720207108449243)
  ·
    refine ⟨45111917353080310662673865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30074611568720207108449243 45111917353080310662673865)
    ·
      refine ⟨33833938014810232997005399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45111917353080310662673865 33833938014810232997005399)
      ·
        refine ⟨50750907022215349495508099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33833938014810232997005399 50750907022215349495508099)
        ·
          refine ⟨76126360533323024243262149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50750907022215349495508099 76126360533323024243262149)
          ·
            refine ⟨14273692599998067045611653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76126360533323024243262149 14273692599998067045611653)
            ·
              refine ⟨2676317362499637571052185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14273692599998067045611653 2676317362499637571052185)
              ·
                refine ⟨2007238021874728178289139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2676317362499637571052185 2007238021874728178289139)
                ·
                  refine ⟨3010857032812092267433709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2007238021874728178289139 3010857032812092267433709)
                  ·
                    refine ⟨1129071387304534600287641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3010857032812092267433709 1129071387304534600287641)
                    ·
                      refine ⟨846803540478400950215731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1129071387304534600287641 846803540478400950215731)
                      ·
                        rfl

theorem cell23_1649144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 4, 2, 1, 3, 2].length) (baseStart_1649144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1649144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1649144 prefixEnd_1649144 := by exact prefixLift 1649144
  have htrace : WordTrace (prefixWord ++ tailWord_1649144) baseStart_1649144 baseEnd_1649144 := by
    simpa [prefixWord, tailWord_1649144, baseEnd_1649144] using wordTrace_append hprefix tailTrace_1649144
  have hstable : (prefixWord ++ tailWord_1649144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1649144).length < 2 ^ (prefixWord ++ tailWord_1649144).sum := by decide
  have hdescent : baseEnd_1649144 < baseStart_1649144 := by decide
  rcases family_descends (prefixWord ++ tailWord_1649144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1649157 : List Nat := [1, 3, 1, 1, 2, 2, 2, 4, 1, 4, 2]
def baseStart_1649157 : Nat := 118140960795 + 1649157 * 2 ^ 59
def prefixEnd_1649157 : Nat := 4983230072969 + 3 ^ 40 * 1649157 * 2
def baseEnd_1649157 : Nat := 846810215726909399353171

theorem tailTrace_1649157 : CollatzResearch.WordTrace tailWord_1649157 prefixEnd_1649157 846810215726909399353171 := by
  unfold tailWord_1649157
  simp only [CollatzResearch.WordTrace]
  refine ⟨60149697286393317437121725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40099798190928878291414483 60149697286393317437121725)
  ·
    refine ⟨22556136482397494038920647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60149697286393317437121725 22556136482397494038920647)
    ·
      refine ⟨33834204723596241058380971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22556136482397494038920647 33834204723596241058380971)
      ·
        refine ⟨50751307085394361587571457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33834204723596241058380971 50751307085394361587571457)
        ·
          refine ⟨38063480314045771190678593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50751307085394361587571457 38063480314045771190678593)
          ·
            refine ⟨28547610235534328393008945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38063480314045771190678593 28547610235534328393008945)
            ·
              refine ⟨21410707676650746294756709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28547610235534328393008945 21410707676650746294756709)
              ·
                refine ⟨4014507689372014930266883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21410707676650746294756709 4014507689372014930266883)
                ·
                  refine ⟨6021761534058022395400325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4014507689372014930266883 6021761534058022395400325)
                  ·
                    refine ⟨1129080287635879199137561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6021761534058022395400325 1129080287635879199137561)
                    ·
                      refine ⟨846810215726909399353171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1129080287635879199137561 846810215726909399353171)
                      ·
                        rfl

theorem cell23_1649157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 4, 1, 4, 2].length) (baseStart_1649157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1649157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1649157 prefixEnd_1649157 := by exact prefixLift 1649157
  have htrace : WordTrace (prefixWord ++ tailWord_1649157) baseStart_1649157 baseEnd_1649157 := by
    simpa [prefixWord, tailWord_1649157, baseEnd_1649157] using wordTrace_append hprefix tailTrace_1649157
  have hstable : (prefixWord ++ tailWord_1649157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1649157).length < 2 ^ (prefixWord ++ tailWord_1649157).sum := by decide
  have hdescent : baseEnd_1649157 < baseStart_1649157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1649157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1649160 : List Nat := [2, 1, 3, 2, 1, 1, 1, 2, 1, 6, 3]
def baseStart_1649160 : Nat := 118140960795 + 1649160 * 2 ^ 59
def prefixEnd_1649160 : Nat := 4983230072969 + 3 ^ 40 * 1649160 * 2
def baseEnd_1649160 : Nat := 846811756168872887615657

theorem tailTrace_1649160 : CollatzResearch.WordTrace tailWord_1649160 prefixEnd_1649160 846811756168872887615657 := by
  unfold tailWord_1649160
  simp only [CollatzResearch.WordTrace]
  refine ⟨30074903352691224474740467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40099871136921632632987289 30074903352691224474740467)
  ·
    refine ⟨45112355029036836712110701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30074903352691224474740467 45112355029036836712110701)
    ·
      refine ⟨16917133135888813767041513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45112355029036836712110701 16917133135888813767041513)
      ·
        refine ⟨12687849851916610325281135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16917133135888813767041513 12687849851916610325281135)
        ·
          refine ⟨19031774777874915487921703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12687849851916610325281135 19031774777874915487921703)
          ·
            refine ⟨28547662166812373231882555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19031774777874915487921703 28547662166812373231882555)
            ·
              refine ⟨42821493250218559847823833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28547662166812373231882555 42821493250218559847823833)
              ·
                refine ⟨32116119937663919885867875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42821493250218559847823833 32116119937663919885867875)
                ·
                  refine ⟨48174179906495879828801813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32116119937663919885867875 48174179906495879828801813)
                  ·
                    refine ⟨2258164683116994366975085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 48174179906495879828801813 2258164683116994366975085)
                    ·
                      refine ⟨846811756168872887615657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2258164683116994366975085 846811756168872887615657)
                      ·
                        rfl

theorem cell23_1649160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 1, 6, 3].length) (baseStart_1649160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1649160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1649160 prefixEnd_1649160 := by exact prefixLift 1649160
  have htrace : WordTrace (prefixWord ++ tailWord_1649160) baseStart_1649160 baseEnd_1649160 := by
    simpa [prefixWord, tailWord_1649160, baseEnd_1649160] using wordTrace_append hprefix tailTrace_1649160
  have hstable : (prefixWord ++ tailWord_1649160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1649160).length < 2 ^ (prefixWord ++ tailWord_1649160).sum := by decide
  have hdescent : baseEnd_1649160 < baseStart_1649160 := by decide
  rcases family_descends (prefixWord ++ tailWord_1649160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1649267 : List Nat := [1, 1, 1, 2, 2, 1, 1, 7, 2, 2, 3]
def baseStart_1649267 : Nat := 118140960795 + 1649267 * 2 ^ 59
def prefixEnd_1649267 : Nat := 4983230072969 + 3 ^ 40 * 1649267 * 2
def baseEnd_1649267 : Nat := 846866698598903968977665

theorem tailTrace_1649267 : CollatzResearch.WordTrace tailWord_1649267 prefixEnd_1649267 846866698598903968977665 := by
  unfold tailWord_1649267
  simp only [CollatzResearch.WordTrace]
  refine ⟨60153709315994806223626055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40102472877329870815750703 60153709315994806223626055)
  ·
    refine ⟨90230563973992209335439083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60153709315994806223626055 90230563973992209335439083)
    ·
      refine ⟨135345845960988314003158625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90230563973992209335439083 135345845960988314003158625)
      ·
        refine ⟨101509384470741235502368969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135345845960988314003158625 101509384470741235502368969)
        ·
          refine ⟨76132038353055926626776727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101509384470741235502368969 76132038353055926626776727)
          ·
            refine ⟨114198057529583889940165091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76132038353055926626776727 114198057529583889940165091)
            ·
              refine ⟨171297086294375834910247637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114198057529583889940165091 171297086294375834910247637)
              ·
                refine ⟨4014775460024433630708929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 171297086294375834910247637 4014775460024433630708929)
                ·
                  refine ⟨3011081595018325223031697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4014775460024433630708929 3011081595018325223031697)
                  ·
                    refine ⟨2258311196263743917273773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3011081595018325223031697 2258311196263743917273773)
                    ·
                      refine ⟨846866698598903968977665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2258311196263743917273773 846866698598903968977665)
                      ·
                        rfl

theorem cell23_1649267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 7, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 7, 2, 2, 3].length) (baseStart_1649267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1649267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1649267 prefixEnd_1649267 := by exact prefixLift 1649267
  have htrace : WordTrace (prefixWord ++ tailWord_1649267) baseStart_1649267 baseEnd_1649267 := by
    simpa [prefixWord, tailWord_1649267, baseEnd_1649267] using wordTrace_append hprefix tailTrace_1649267
  have hstable : (prefixWord ++ tailWord_1649267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1649267).length < 2 ^ (prefixWord ++ tailWord_1649267).sum := by decide
  have hdescent : baseEnd_1649267 < baseStart_1649267 := by decide
  rcases family_descends (prefixWord ++ tailWord_1649267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1649304 : List Nat := [2, 1, 2, 4, 1, 1, 5, 1, 6]
def baseStart_1649304 : Nat := 118140960795 + 1649304 * 2 ^ 59
def prefixEnd_1649304 : Nat := 4983230072969 + 3 ^ 40 * 1649304 * 2
def baseEnd_1649304 : Nat := 94098410820346702690555

theorem tailTrace_1649304 : CollatzResearch.WordTrace tailWord_1649304 prefixEnd_1649304 94098410820346702690555 := by
  unfold tailWord_1649304
  simp only [CollatzResearch.WordTrace]
  refine ⟨30077529408430380771361483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40103372544573841028481977 30077529408430380771361483)
  ·
    refine ⟨45116294112645571157042225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30077529408430380771361483 45116294112645571157042225)
    ·
      refine ⟨33837220584484178367781669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45116294112645571157042225 33837220584484178367781669)
      ·
        refine ⟨6344478859590783443959063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33837220584484178367781669 6344478859590783443959063)
        ·
          refine ⟨9516718289386175165938595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6344478859590783443959063 9516718289386175165938595)
          ·
            refine ⟨14275077434079262748907893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9516718289386175165938595 14275077434079262748907893)
            ·
              refine ⟨1338288509444930882710115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14275077434079262748907893 1338288509444930882710115)
              ·
                refine ⟨2007432764167396324065173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1338288509444930882710115 2007432764167396324065173)
                ·
                  refine ⟨94098410820346702690555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2007432764167396324065173 94098410820346702690555)
                  ·
                    rfl

theorem cell23_1649304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 5, 1, 6].length) (baseStart_1649304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1649304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1649304 prefixEnd_1649304 := by exact prefixLift 1649304
  have htrace : WordTrace (prefixWord ++ tailWord_1649304) baseStart_1649304 baseEnd_1649304 := by
    simpa [prefixWord, tailWord_1649304, baseEnd_1649304] using wordTrace_append hprefix tailTrace_1649304
  have hstable : (prefixWord ++ tailWord_1649304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1649304).length < 2 ^ (prefixWord ++ tailWord_1649304).sum := by decide
  have hdescent : baseEnd_1649304 < baseStart_1649304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1649304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1649307 : List Nat := [1, 1, 1, 1, 1, 1, 2, 2, 2, 9, 2]
def baseStart_1649307 : Nat := 118140960795 + 1649307 * 2 ^ 59
def prefixEnd_1649307 : Nat := 4983230072969 + 3 ^ 40 * 1649307 * 2
def baseEnd_1649307 : Nat := 846887237825083812477481

theorem tailTrace_1649307 : CollatzResearch.WordTrace tailWord_1649307 prefixEnd_1649307 846887237825083812477481 := by
  unfold tailWord_1649307
  simp only [CollatzResearch.WordTrace]
  refine ⟨60155168235849893055082175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40103445490566595370054783 60155168235849893055082175)
  ·
    refine ⟨90232752353774839582623263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60155168235849893055082175 90232752353774839582623263)
    ·
      refine ⟨135349128530662259373934895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90232752353774839582623263 135349128530662259373934895)
      ·
        refine ⟨203023692795993389060902343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135349128530662259373934895 203023692795993389060902343)
        ·
          refine ⟨304535539193990083591353515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203023692795993389060902343 304535539193990083591353515)
          ·
            refine ⟨456803308790985125387030273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 304535539193990083591353515 456803308790985125387030273)
            ·
              refine ⟨342602481593238844040272705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 456803308790985125387030273 342602481593238844040272705)
              ·
                refine ⟨256951861194929133030204529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 342602481593238844040272705 256951861194929133030204529)
                ·
                  refine ⟨192713895896196849772653397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 256951861194929133030204529 192713895896196849772653397)
                  ·
                    refine ⟨1129182983766778416636641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 192713895896196849772653397 1129182983766778416636641)
                    ·
                      refine ⟨846887237825083812477481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1129182983766778416636641 846887237825083812477481)
                      ·
                        rfl

theorem cell23_1649307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 9, 2].length) (baseStart_1649307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1649307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1649307 prefixEnd_1649307 := by exact prefixLift 1649307
  have htrace : WordTrace (prefixWord ++ tailWord_1649307) baseStart_1649307 baseEnd_1649307 := by
    simpa [prefixWord, tailWord_1649307, baseEnd_1649307] using wordTrace_append hprefix tailTrace_1649307
  have hstable : (prefixWord ++ tailWord_1649307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1649307).length < 2 ^ (prefixWord ++ tailWord_1649307).sum := by decide
  have hdescent : baseEnd_1649307 < baseStart_1649307 := by decide
  rcases family_descends (prefixWord ++ tailWord_1649307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1649337 : List Nat := [1, 2, 1, 4, 1, 1, 1, 2, 5, 1, 4]
def baseStart_1649337 : Nat := 118140960795 + 1649337 * 2 ^ 59
def prefixEnd_1649337 : Nat := 4983230072969 + 3 ^ 40 * 1649337 * 2
def baseEnd_1649337 : Nat := 846902642244718695102343

theorem tailTrace_1649337 : CollatzResearch.WordTrace tailWord_1649337 prefixEnd_1649337 846902642244718695102343 := by
  unfold tailWord_1649337
  simp only [CollatzResearch.WordTrace]
  refine ⟨60156262425741208178674265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40104174950494138785782843 60156262425741208178674265)
  ·
    refine ⟨45117196819305906134005699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60156262425741208178674265 45117196819305906134005699)
    ·
      refine ⟨67675795228958859201008549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45117196819305906134005699 67675795228958859201008549)
      ·
        refine ⟨12689211605429786100189103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67675795228958859201008549 12689211605429786100189103)
        ·
          refine ⟨19033817408144679150283655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12689211605429786100189103 19033817408144679150283655)
          ·
            refine ⟨28550726112217018725425483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19033817408144679150283655 28550726112217018725425483)
            ·
              refine ⟨42826089168325528088138225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28550726112217018725425483 42826089168325528088138225)
              ·
                refine ⟨32119566876244146066103669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42826089168325528088138225 32119566876244146066103669)
                ·
                  refine ⟨3011209394647888693697219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32119566876244146066103669 3011209394647888693697219)
                  ·
                    refine ⟨4516814091971833040545829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3011209394647888693697219 4516814091971833040545829)
                    ·
                      refine ⟨846902642244718695102343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4516814091971833040545829 846902642244718695102343)
                      ·
                        rfl

theorem cell23_1649337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 5, 1, 4].length) (baseStart_1649337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1649337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1649337 prefixEnd_1649337 := by exact prefixLift 1649337
  have htrace : WordTrace (prefixWord ++ tailWord_1649337) baseStart_1649337 baseEnd_1649337 := by
    simpa [prefixWord, tailWord_1649337, baseEnd_1649337] using wordTrace_append hprefix tailTrace_1649337
  have hstable : (prefixWord ++ tailWord_1649337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1649337).length < 2 ^ (prefixWord ++ tailWord_1649337).sum := by decide
  have hdescent : baseEnd_1649337 < baseStart_1649337 := by decide
  rcases family_descends (prefixWord ++ tailWord_1649337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1649341 : List Nat := [1, 4, 1, 2, 1, 4, 1, 2, 2, 3, 2]
def baseStart_1649341 : Nat := 118140960795 + 1649341 * 2 ^ 59
def prefixEnd_1649341 : Nat := 4983230072969 + 3 ^ 40 * 1649341 * 2
def baseEnd_1649341 : Nat := 846904696167336679452325

theorem tailTrace_1649341 : CollatzResearch.WordTrace tailWord_1649341 prefixEnd_1649341 846904696167336679452325 := by
  unfold tailWord_1649341
  simp only [CollatzResearch.WordTrace]
  refine ⟨60156408317726716861819877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40104272211817811241213251 60156408317726716861819877)
  ·
    refine ⟨11279326559573759411591227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60156408317726716861819877 11279326559573759411591227)
    ·
      refine ⟨16918989839360639117386841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11279326559573759411591227 16918989839360639117386841)
      ·
        refine ⟨12689242379520479338040131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16918989839360639117386841 12689242379520479338040131)
        ·
          refine ⟨19033863569280719007060197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12689242379520479338040131 19033863569280719007060197)
          ·
            refine ⟨3568849419240134813823787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19033863569280719007060197 3568849419240134813823787)
            ·
              refine ⟨5353274128860202220735681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3568849419240134813823787 5353274128860202220735681)
              ·
                refine ⟨4014955596645151665551761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5353274128860202220735681 4014955596645151665551761)
                ·
                  refine ⟨3011216697483863749163821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4014955596645151665551761 3011216697483863749163821)
                  ·
                    refine ⟨1129206261556448905936433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3011216697483863749163821 1129206261556448905936433)
                    ·
                      refine ⟨846904696167336679452325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1129206261556448905936433 846904696167336679452325)
                      ·
                        rfl

theorem cell23_1649341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 2, 2, 3, 2].length) (baseStart_1649341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1649341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1649341 prefixEnd_1649341 := by exact prefixLift 1649341
  have htrace : WordTrace (prefixWord ++ tailWord_1649341) baseStart_1649341 baseEnd_1649341 := by
    simpa [prefixWord, tailWord_1649341, baseEnd_1649341] using wordTrace_append hprefix tailTrace_1649341
  have hstable : (prefixWord ++ tailWord_1649341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1649341).length < 2 ^ (prefixWord ++ tailWord_1649341).sum := by decide
  have hdescent : baseEnd_1649341 < baseStart_1649341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1649341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1649348 : List Nat := [2, 3, 3, 1, 1, 4, 1, 1, 3, 1, 3]
def baseStart_1649348 : Nat := 118140960795 + 1649348 * 2 ^ 59
def prefixEnd_1649348 : Nat := 4983230072969 + 3 ^ 40 * 1649348 * 2
def baseEnd_1649348 : Nat := 846908290531918152064793

theorem tailTrace_1649348 : CollatzResearch.WordTrace tailWord_1649348 prefixEnd_1649348 846908290531918152064793 := by
  unfold tailWord_1649348
  simp only [CollatzResearch.WordTrace]
  refine ⟨30078331814350678528662349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40104442419134238038216465 30078331814350678528662349)
  ·
    refine ⟨11279374430381504448248381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30078331814350678528662349 11279374430381504448248381)
    ·
      refine ⟨4229765411393064168093143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11279374430381504448248381 4229765411393064168093143)
      ·
        refine ⟨6344648117089596252139715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4229765411393064168093143 6344648117089596252139715)
        ·
          refine ⟨9516972175634394378209573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6344648117089596252139715 9516972175634394378209573)
          ·
            refine ⟨1784432282931448945914295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9516972175634394378209573 1784432282931448945914295)
            ·
              refine ⟨2676648424397173418871443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1784432282931448945914295 2676648424397173418871443)
              ·
                refine ⟨4014972636595760128307165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2676648424397173418871443 4014972636595760128307165)
                ·
                  refine ⟨1505614738723410048115187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4014972636595760128307165 1505614738723410048115187)
                  ·
                    refine ⟨2258422108085115072172781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1505614738723410048115187 2258422108085115072172781)
                    ·
                      refine ⟨846908290531918152064793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2258422108085115072172781 846908290531918152064793)
                      ·
                        rfl

theorem cell23_1649348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 1, 1, 3, 1, 3].length) (baseStart_1649348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1649348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1649348 prefixEnd_1649348 := by exact prefixLift 1649348
  have htrace : WordTrace (prefixWord ++ tailWord_1649348) baseStart_1649348 baseEnd_1649348 := by
    simpa [prefixWord, tailWord_1649348, baseEnd_1649348] using wordTrace_append hprefix tailTrace_1649348
  have hstable : (prefixWord ++ tailWord_1649348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1649348).length < 2 ^ (prefixWord ++ tailWord_1649348).sum := by decide
  have hdescent : baseEnd_1649348 < baseStart_1649348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1649348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1649367 : List Nat := [1, 1, 3, 2, 1, 4, 2, 1, 1, 1, 6]
def baseStart_1649367 : Nat := 118140960795 + 1649367 * 2 ^ 59
def prefixEnd_1649367 : Nat := 4983230072969 + 3 ^ 40 * 1649367 * 2
def baseEnd_1649367 : Nat := 846918046664353577727205

theorem tailTrace_1649367 : CollatzResearch.WordTrace tailWord_1649367 prefixEnd_1649367 846918046664353577727205 := by
  unfold tailWord_1649367
  simp only [CollatzResearch.WordTrace]
  refine ⟨60157356615632523302266355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40104904410421682201510903 60157356615632523302266355)
  ·
    refine ⟨90236034923448784953399533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60157356615632523302266355 90236034923448784953399533)
    ·
      refine ⟨33838513096293294357524825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90236034923448784953399533 33838513096293294357524825)
      ·
        refine ⟨25378884822219970768143619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33838513096293294357524825 25378884822219970768143619)
        ·
          refine ⟨38068327233329956152215429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25378884822219970768143619 38068327233329956152215429)
          ·
            refine ⟨7137811356249366778540393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38068327233329956152215429 7137811356249366778540393)
            ·
              refine ⟨5353358517187025083905295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7137811356249366778540393 5353358517187025083905295)
              ·
                refine ⟨8030037775780537625857943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5353358517187025083905295 8030037775780537625857943)
                ·
                  refine ⟨12045056663670806438786915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8030037775780537625857943 12045056663670806438786915)
                  ·
                    refine ⟨18067584995506209658180373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12045056663670806438786915 18067584995506209658180373)
                    ·
                      refine ⟨846918046664353577727205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18067584995506209658180373 846918046664353577727205)
                      ·
                        rfl

theorem cell23_1649367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 1, 1, 1, 6].length) (baseStart_1649367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1649367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1649367 prefixEnd_1649367 := by exact prefixLift 1649367
  have htrace : WordTrace (prefixWord ++ tailWord_1649367) baseStart_1649367 baseEnd_1649367 := by
    simpa [prefixWord, tailWord_1649367, baseEnd_1649367] using wordTrace_append hprefix tailTrace_1649367
  have hstable : (prefixWord ++ tailWord_1649367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1649367).length < 2 ^ (prefixWord ++ tailWord_1649367).sum := by decide
  have hdescent : baseEnd_1649367 < baseStart_1649367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1649367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1649377 : List Nat := [1, 2, 3, 1, 4, 1, 2, 9]
def baseStart_1649377 : Nat := 118140960795 + 1649377 * 2 ^ 59
def prefixEnd_1649377 : Nat := 4983230072969 + 3 ^ 40 * 1649377 * 2
def baseEnd_1649377 : Nat := 31367525239662908837117

theorem tailTrace_1649377 : CollatzResearch.WordTrace tailWord_1649377 prefixEnd_1649377 31367525239662908837117 := by
  unfold tailWord_1649377
  simp only [CollatzResearch.WordTrace]
  refine ⟨60157721345596295010130385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40105147563730863340086923 60157721345596295010130385)
  ·
    refine ⟨45118291009197221257597789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60157721345596295010130385 45118291009197221257597789)
    ·
      refine ⟨16919359128448957971599171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45118291009197221257597789 16919359128448957971599171)
      ·
        refine ⟨25379038692673436957398757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16919359128448957971599171 25379038692673436957398757)
        ·
          refine ⟨4758569754876269429512267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25379038692673436957398757 4758569754876269429512267)
          ·
            refine ⟨7137854632314404144268401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4758569754876269429512267 7137854632314404144268401)
            ·
              refine ⟨5353390974235803108201301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7137854632314404144268401 5353390974235803108201301)
              ·
                refine ⟨31367525239662908837117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5353390974235803108201301 31367525239662908837117)
                ·
                  rfl

theorem cell23_1649377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 9].length) (baseStart_1649377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1649377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1649377 prefixEnd_1649377 := by exact prefixLift 1649377
  have htrace : WordTrace (prefixWord ++ tailWord_1649377) baseStart_1649377 baseEnd_1649377 := by
    simpa [prefixWord, tailWord_1649377, baseEnd_1649377] using wordTrace_append hprefix tailTrace_1649377
  have hstable : (prefixWord ++ tailWord_1649377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1649377).length < 2 ^ (prefixWord ++ tailWord_1649377).sum := by decide
  have hdescent : baseEnd_1649377 < baseStart_1649377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1649377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1649388 : List Nat := [2, 2, 1, 1, 2, 2, 1, 7, 1, 2, 2]
def baseStart_1649388 : Nat := 118140960795 + 1649388 * 2 ^ 59
def prefixEnd_1649388 : Nat := 4983230072969 + 3 ^ 40 * 1649388 * 2
def baseEnd_1649388 : Nat := 846928829758097995564609

theorem tailTrace_1649388 : CollatzResearch.WordTrace tailWord_1649388 prefixEnd_1649388 846928829758097995564609 := by
  unfold tailWord_1649388
  simp only [CollatzResearch.WordTrace]
  refine ⟨30079061274278221944390409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40105415032370962592520545 30079061274278221944390409)
  ·
    refine ⟨22559295955708666458292807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30079061274278221944390409 22559295955708666458292807)
    ·
      refine ⟨33838943933562999687439211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22559295955708666458292807 33838943933562999687439211)
      ·
        refine ⟨50758415900344499531158817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33838943933562999687439211 50758415900344499531158817)
        ·
          refine ⟨38068811925258374648369113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50758415900344499531158817 38068811925258374648369113)
          ·
            refine ⟨28551608943943780986276835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38068811925258374648369113 28551608943943780986276835)
            ·
              refine ⟨42827413415915671479415253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28551608943943780986276835 42827413415915671479415253)
              ·
                refine ⟨1003767501935523550298795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 42827413415915671479415253 1003767501935523550298795)
                ·
                  refine ⟨1505651252903285325448193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1003767501935523550298795 1505651252903285325448193)
                  ·
                    refine ⟨1129238439677463994086145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1505651252903285325448193 1129238439677463994086145)
                    ·
                      refine ⟨846928829758097995564609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1129238439677463994086145 846928829758097995564609)
                      ·
                        rfl

theorem cell23_1649388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 7, 1, 2, 2].length) (baseStart_1649388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1649388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1649388 prefixEnd_1649388 := by exact prefixLift 1649388
  have htrace : WordTrace (prefixWord ++ tailWord_1649388) baseStart_1649388 baseEnd_1649388 := by
    simpa [prefixWord, tailWord_1649388, baseEnd_1649388] using wordTrace_append hprefix tailTrace_1649388
  have hstable : (prefixWord ++ tailWord_1649388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1649388).length < 2 ^ (prefixWord ++ tailWord_1649388).sum := by decide
  have hdescent : baseEnd_1649388 < baseStart_1649388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1649388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1649427 : List Nat := [1, 1, 1, 2, 1, 3, 3, 2, 2, 3, 4]
def baseStart_1649427 : Nat := 118140960795 + 1649427 * 2 ^ 59
def prefixEnd_1649427 : Nat := 4983230072969 + 3 ^ 40 * 1649427 * 2
def baseEnd_1649427 : Nat := 846948855503623342976929

theorem tailTrace_1649427 : CollatzResearch.WordTrace tailWord_1649427 prefixEnd_1649427 846948855503623342976929 := by
  unfold tailWord_1649427
  simp only [CollatzResearch.WordTrace]
  refine ⟨60159544995415153549450535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40106363330276769032967023 60159544995415153549450535)
  ·
    refine ⟨90239317493122730324175803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60159544995415153549450535 90239317493122730324175803)
    ·
      refine ⟨135358976239684095486263705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90239317493122730324175803 135358976239684095486263705)
      ·
        refine ⟨101519232179763071614697779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135358976239684095486263705 101519232179763071614697779)
        ·
          refine ⟨152278848269644607422046669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101519232179763071614697779 152278848269644607422046669)
          ·
            refine ⟨57104568101116727783267501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 152278848269644607422046669 57104568101116727783267501)
            ·
              refine ⟨21414213037918772918725313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57104568101116727783267501 21414213037918772918725313)
              ·
                refine ⟨16060659778439079689043985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21414213037918772918725313 16060659778439079689043985)
                ·
                  refine ⟨12045494833829309766782989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16060659778439079689043985 12045494833829309766782989)
                  ·
                    refine ⟨4517060562685991162543621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12045494833829309766782989 4517060562685991162543621)
                    ·
                      refine ⟨846948855503623342976929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4517060562685991162543621 846948855503623342976929)
                      ·
                        rfl

theorem cell23_1649427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 2, 2, 3, 4].length) (baseStart_1649427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1649427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1649427 prefixEnd_1649427 := by exact prefixLift 1649427
  have htrace : WordTrace (prefixWord ++ tailWord_1649427) baseStart_1649427 baseEnd_1649427 := by
    simpa [prefixWord, tailWord_1649427, baseEnd_1649427] using wordTrace_append hprefix tailTrace_1649427
  have hstable : (prefixWord ++ tailWord_1649427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1649427).length < 2 ^ (prefixWord ++ tailWord_1649427).sum := by decide
  have hdescent : baseEnd_1649427 < baseStart_1649427 := by decide
  rcases family_descends (prefixWord ++ tailWord_1649427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1649448 : List Nat := [2, 1, 5, 1, 1, 1, 3, 3, 1, 3, 2]
def baseStart_1649448 : Nat := 118140960795 + 1649448 * 2 ^ 59
def prefixEnd_1649448 : Nat := 4983230072969 + 3 ^ 40 * 1649448 * 2
def baseEnd_1649448 : Nat := 846959638597367760814333

theorem tailTrace_1649448 : CollatzResearch.WordTrace tailWord_1649448 prefixEnd_1649448 846959638597367760814333 := by
  unfold tailWord_1649448
  simp only [CollatzResearch.WordTrace]
  refine ⟨30080155464169537067982499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40106873952226049423976665 30080155464169537067982499)
  ·
    refine ⟨45120233196254305601973749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30080155464169537067982499 45120233196254305601973749)
    ·
      refine ⟨4230021862148841150185039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 45120233196254305601973749 4230021862148841150185039)
      ·
        refine ⟨6345032793223261725277559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4230021862148841150185039 6345032793223261725277559)
        ·
          refine ⟨9517549189834892587916339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6345032793223261725277559 9517549189834892587916339)
          ·
            refine ⟨14276323784752338881874509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9517549189834892587916339 14276323784752338881874509)
            ·
              refine ⟨5353621419282127080702941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14276323784752338881874509 5353621419282127080702941)
              ·
                refine ⟨2007608032230797655263603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5353621419282127080702941 2007608032230797655263603)
                ·
                  refine ⟨3011412048346196482895405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2007608032230797655263603 3011412048346196482895405)
                  ·
                    refine ⟨1129279518129823681085777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3011412048346196482895405 1129279518129823681085777)
                    ·
                      refine ⟨846959638597367760814333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1129279518129823681085777 846959638597367760814333)
                      ·
                        rfl

theorem cell23_1649448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 3, 1, 3, 2].length) (baseStart_1649448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1649448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1649448 prefixEnd_1649448 := by exact prefixLift 1649448
  have htrace : WordTrace (prefixWord ++ tailWord_1649448) baseStart_1649448 baseEnd_1649448 := by
    simpa [prefixWord, tailWord_1649448, baseEnd_1649448] using wordTrace_append hprefix tailTrace_1649448
  have hstable : (prefixWord ++ tailWord_1649448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1649448).length < 2 ^ (prefixWord ++ tailWord_1649448).sum := by decide
  have hdescent : baseEnd_1649448 < baseStart_1649448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1649448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1649484 : List Nat := [2, 2, 1, 3, 3, 1, 2, 2, 7]
def baseStart_1649484 : Nat := 118140960795 + 1649484 * 2 ^ 59
def prefixEnd_1649484 : Nat := 4983230072969 + 3 ^ 40 * 1649484 * 2
def baseEnd_1649484 : Nat := 94108680433436624440463

theorem tailTrace_1649484 : CollatzResearch.WordTrace tailWord_1649484 prefixEnd_1649484 94108680433436624440463 := by
  unfold tailWord_1649484
  simp only [CollatzResearch.WordTrace]
  refine ⟨30080811978104326142137753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40107749304139101522850337 30080811978104326142137753)
  ·
    refine ⟨22560608983578244606603315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30080811978104326142137753 22560608983578244606603315)
    ·
      refine ⟨33840913475367366909904973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22560608983578244606603315 33840913475367366909904973)
      ·
        refine ⟨12690342553262762591214365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33840913475367366909904973 12690342553262762591214365)
        ·
          refine ⟨4758878457473535971705387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12690342553262762591214365 4758878457473535971705387)
          ·
            refine ⟨7138317686210303957558081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4758878457473535971705387 7138317686210303957558081)
            ·
              refine ⟨5353738264657727968168561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7138317686210303957558081 5353738264657727968168561)
              ·
                refine ⟨4015303698493295976126421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5353738264657727968168561 4015303698493295976126421)
                ·
                  refine ⟨94108680433436624440463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4015303698493295976126421 94108680433436624440463)
                  ·
                    rfl

theorem cell23_1649484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 2, 7].length) (baseStart_1649484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1649484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1649484 prefixEnd_1649484 := by exact prefixLift 1649484
  have htrace : WordTrace (prefixWord ++ tailWord_1649484) baseStart_1649484 baseEnd_1649484 := by
    simpa [prefixWord, tailWord_1649484, baseEnd_1649484] using wordTrace_append hprefix tailTrace_1649484
  have hstable : (prefixWord ++ tailWord_1649484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1649484).length < 2 ^ (prefixWord ++ tailWord_1649484).sum := by decide
  have hdescent : baseEnd_1649484 < baseStart_1649484 := by decide
  rcases family_descends (prefixWord ++ tailWord_1649484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1649518 : List Nat := [4, 1, 2, 3, 2, 2, 1, 1, 7]
def baseStart_1649518 : Nat := 118140960795 + 1649518 * 2 ^ 59
def prefixEnd_1649518 : Nat := 4983230072969 + 3 ^ 40 * 1649518 * 2
def baseEnd_1649518 : Nat := 94110620249242498548779

theorem tailTrace_1649518 : CollatzResearch.WordTrace tailWord_1649518 prefixEnd_1649518 94110620249242498548779 := by
  unfold tailWord_1649518
  simp only [CollatzResearch.WordTrace]
  refine ⟨7520358004760684511376651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40108576025390317394008805 7520358004760684511376651)
  ·
    refine ⟨11280537007141026767064977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7520358004760684511376651 11280537007141026767064977)
    ·
      refine ⟨8460402755355770075298733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11280537007141026767064977 8460402755355770075298733)
      ·
        refine ⟨3172651033258413778237025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8460402755355770075298733 3172651033258413778237025)
        ·
          refine ⟨2379488274943810333677769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3172651033258413778237025 2379488274943810333677769)
          ·
            refine ⟨1784616206207857750258327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2379488274943810333677769 1784616206207857750258327)
            ·
              refine ⟨2676924309311786625387491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1784616206207857750258327 2676924309311786625387491)
              ·
                refine ⟨4015386463967679938081237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2676924309311786625387491 4015386463967679938081237)
                ·
                  refine ⟨94110620249242498548779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4015386463967679938081237 94110620249242498548779)
                  ·
                    rfl

theorem cell23_1649518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 1, 1, 7].length) (baseStart_1649518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1649518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1649518 prefixEnd_1649518 := by exact prefixLift 1649518
  have htrace : WordTrace (prefixWord ++ tailWord_1649518) baseStart_1649518 baseEnd_1649518 := by
    simpa [prefixWord, tailWord_1649518, baseEnd_1649518] using wordTrace_append hprefix tailTrace_1649518
  have hstable : (prefixWord ++ tailWord_1649518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1649518).length < 2 ^ (prefixWord ++ tailWord_1649518).sum := by decide
  have hdescent : baseEnd_1649518 < baseStart_1649518 := by decide
  rcases family_descends (prefixWord ++ tailWord_1649518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1649571 : List Nat := [1, 1, 1, 4, 1, 2, 4, 2, 2, 2, 3]
def baseStart_1649571 : Nat := 118140960795 + 1649571 * 2 ^ 59
def prefixEnd_1649571 : Nat := 4983230072969 + 3 ^ 40 * 1649571 * 2
def baseEnd_1649571 : Nat := 847022796717870779576267

theorem tailTrace_1649571 : CollatzResearch.WordTrace tailWord_1649571 prefixEnd_1649571 847022796717870779576267 := by
  unfold tailWord_1649571
  simp only [CollatzResearch.WordTrace]
  refine ⟨60164797106893466142692567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40109864737928977428461711 60164797106893466142692567)
  ·
    refine ⟨90247195660340199214038851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60164797106893466142692567 90247195660340199214038851)
    ·
      refine ⟨135370793490510298821058277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90247195660340199214038851 135370793490510298821058277)
      ·
        refine ⟨25382023779470681028948427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 135370793490510298821058277 25382023779470681028948427)
        ·
          refine ⟨38073035669206021543422641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25382023779470681028948427 38073035669206021543422641)
          ·
            refine ⟨28554776751904516157566981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38073035669206021543422641 28554776751904516157566981)
            ·
              refine ⟨5354020640982096779543809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28554776751904516157566981 5354020640982096779543809)
              ·
                refine ⟨4015515480736572584657857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5354020640982096779543809 4015515480736572584657857)
                ·
                  refine ⟨3011636610552429438493393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4015515480736572584657857 3011636610552429438493393)
                  ·
                    refine ⟨2258727457914322078870045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3011636610552429438493393 2258727457914322078870045)
                    ·
                      refine ⟨847022796717870779576267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2258727457914322078870045 847022796717870779576267)
                      ·
                        rfl

theorem cell23_1649571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 2, 2, 2, 3].length) (baseStart_1649571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1649571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1649571 prefixEnd_1649571 := by exact prefixLift 1649571
  have htrace : WordTrace (prefixWord ++ tailWord_1649571) baseStart_1649571 baseEnd_1649571 := by
    simpa [prefixWord, tailWord_1649571, baseEnd_1649571] using wordTrace_append hprefix tailTrace_1649571
  have hstable : (prefixWord ++ tailWord_1649571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1649571).length < 2 ^ (prefixWord ++ tailWord_1649571).sum := by decide
  have hdescent : baseEnd_1649571 < baseStart_1649571 := by decide
  rcases family_descends (prefixWord ++ tailWord_1649571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1649635 : List Nat := [1, 1, 1, 6, 1, 1, 1, 6, 1, 1, 3]
def baseStart_1649635 : Nat := 118140960795 + 1649635 * 2 ^ 59
def prefixEnd_1649635 : Nat := 4983230072969 + 3 ^ 40 * 1649635 * 2
def baseEnd_1649635 : Nat := 847055659479758529175973

theorem tailTrace_1649635 : CollatzResearch.WordTrace tailWord_1649635 prefixEnd_1649635 847055659479758529175973 := by
  unfold tailWord_1649635
  simp only [CollatzResearch.WordTrace]
  refine ⟨60167131378661605073022359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40111420919107736715348239 60167131378661605073022359)
  ·
    refine ⟨90250697067992407609533539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60167131378661605073022359 90250697067992407609533539)
    ·
      refine ⟨135376045601988611414300309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90250697067992407609533539 135376045601988611414300309)
      ·
        refine ⟨6345752137593216160045327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 135376045601988611414300309 6345752137593216160045327)
        ·
          refine ⟨9518628206389824240067991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6345752137593216160045327 9518628206389824240067991)
          ·
            refine ⟨14277942309584736360101987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9518628206389824240067991 14277942309584736360101987)
            ·
              refine ⟨21416913464377104540152981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14277942309584736360101987 21416913464377104540152981)
              ·
                refine ⟨1003917818642676775319671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 21416913464377104540152981 1003917818642676775319671)
                ·
                  refine ⟨1505876727964015162979507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1003917818642676775319671 1505876727964015162979507)
                  ·
                    refine ⟨2258815091946022744469261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1505876727964015162979507 2258815091946022744469261)
                    ·
                      refine ⟨847055659479758529175973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2258815091946022744469261 847055659479758529175973)
                      ·
                        rfl

theorem cell23_1649635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 6, 1, 1, 3].length) (baseStart_1649635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1649635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1649635 prefixEnd_1649635 := by exact prefixLift 1649635
  have htrace : WordTrace (prefixWord ++ tailWord_1649635) baseStart_1649635 baseEnd_1649635 := by
    simpa [prefixWord, tailWord_1649635, baseEnd_1649635] using wordTrace_append hprefix tailTrace_1649635
  have hstable : (prefixWord ++ tailWord_1649635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1649635).length < 2 ^ (prefixWord ++ tailWord_1649635).sum := by decide
  have hdescent : baseEnd_1649635 < baseStart_1649635 := by decide
  rcases family_descends (prefixWord ++ tailWord_1649635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1649671 : List Nat := [1, 1, 4, 3, 1, 1, 2, 1, 3, 2, 4]
def baseStart_1649671 : Nat := 118140960795 + 1649671 * 2 ^ 59
def prefixEnd_1649671 : Nat := 4983230072969 + 3 ^ 40 * 1649671 * 2
def baseEnd_1649671 : Nat := 847074144783320388325807

theorem tailTrace_1649671 : CollatzResearch.WordTrace tailWord_1649671 prefixEnd_1649671 847074144783320388325807 := by
  unfold tailWord_1649671
  simp only [CollatzResearch.WordTrace]
  refine ⟨60168444406531183221332867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40112296271020788814221911 60168444406531183221332867)
  ·
    refine ⟨90252666609796774831999301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60168444406531183221332867 90252666609796774831999301)
    ·
      refine ⟨16922374989336895280999869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90252666609796774831999301 16922374989336895280999869)
      ·
        refine ⟨6345890621001335730374951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16922374989336895280999869 6345890621001335730374951)
        ·
          refine ⟨9518835931502003595562427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6345890621001335730374951 9518835931502003595562427)
          ·
            refine ⟨14278253897253005393343641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9518835931502003595562427 14278253897253005393343641)
            ·
              refine ⟨10708690422939754045007731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14278253897253005393343641 10708690422939754045007731)
              ·
                refine ⟨16063035634409631067511597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10708690422939754045007731 16063035634409631067511597)
                ·
                  refine ⟨6023638362903611650316849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16063035634409631067511597 6023638362903611650316849)
                  ·
                    refine ⟨4517728772177708737737637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6023638362903611650316849 4517728772177708737737637)
                    ·
                      refine ⟨847074144783320388325807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4517728772177708737737637 847074144783320388325807)
                      ·
                        rfl

theorem cell23_1649671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_1649671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1649671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1649671 prefixEnd_1649671 := by exact prefixLift 1649671
  have htrace : WordTrace (prefixWord ++ tailWord_1649671) baseStart_1649671 baseEnd_1649671 := by
    simpa [prefixWord, tailWord_1649671, baseEnd_1649671] using wordTrace_append hprefix tailTrace_1649671
  have hstable : (prefixWord ++ tailWord_1649671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1649671).length < 2 ^ (prefixWord ++ tailWord_1649671).sum := by decide
  have hdescent : baseEnd_1649671 < baseStart_1649671 := by decide
  rcases family_descends (prefixWord ++ tailWord_1649671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
