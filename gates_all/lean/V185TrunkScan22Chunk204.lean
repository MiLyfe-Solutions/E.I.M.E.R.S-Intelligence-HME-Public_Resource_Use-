import V185TrunkScan22Chunk203

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1818839 : List Nat := [1, 1, 3, 2, 1, 2, 1, 1, 7, 3]
def baseStart_1818839 : Nat := 118140960795 + 1818839 * 2 ^ 59
def prefixEnd_1818839 : Nat := 4983230072969 + 3 ^ 40 * 1818839 * 2
def baseEnd_1818839 : Nat := 622625760095409678498545

theorem tailTrace_1818839 : CollatzResearch.WordTrace tailWord_1818839 prefixEnd_1818839 622625760095409678498545 := by
  unfold tailWord_1818839
  simp only [CollatzResearch.WordTrace]
  refine ⟨66338508257664410815555571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44225672171776273877037047 66338508257664410815555571)
  ·
    refine ⟨99507762386496616223333357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66338508257664410815555571 99507762386496616223333357)
    ·
      refine ⟨37315410894936231083750009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99507762386496616223333357 37315410894936231083750009)
      ·
        refine ⟨27986558171202173312812507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37315410894936231083750009 27986558171202173312812507)
        ·
          refine ⟨41979837256803259969218761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27986558171202173312812507 41979837256803259969218761)
          ·
            refine ⟨31484877942602444976914071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41979837256803259969218761 31484877942602444976914071)
            ·
              refine ⟨47227316913903667465371107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31484877942602444976914071 47227316913903667465371107)
              ·
                refine ⟨70840975370855501198056661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47227316913903667465371107 70840975370855501198056661)
                ·
                  refine ⟨1660335360254425809329453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 70840975370855501198056661 1660335360254425809329453)
                  ·
                    refine ⟨622625760095409678498545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1660335360254425809329453 622625760095409678498545)
                    ·
                      rfl

theorem cell22_1818839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 7, 3].length) (baseStart_1818839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1818839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1818839 prefixEnd_1818839 := by exact prefixLift 1818839
  have htrace : WordTrace (prefixWord ++ tailWord_1818839) baseStart_1818839 baseEnd_1818839 := by
    simpa [prefixWord, tailWord_1818839, baseEnd_1818839] using wordTrace_append hprefix tailTrace_1818839
  have hstable : (prefixWord ++ tailWord_1818839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1818839).length < 2 ^ (prefixWord ++ tailWord_1818839).sum := by decide
  have hdescent : baseEnd_1818839 < baseStart_1818839 := by decide
  rcases family_descends (prefixWord ++ tailWord_1818839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1818845 : List Nat := [1, 4, 3, 2, 1, 3, 1, 2, 2, 3]
def baseStart_1818845 : Nat := 118140960795 + 1818845 * 2 ^ 59
def prefixEnd_1818845 : Nat := 4983230072969 + 3 ^ 40 * 1818845 * 2
def baseEnd_1818845 : Nat := 622627814018027662848527

theorem tailTrace_1818845 : CollatzResearch.WordTrace tailWord_1818845 prefixEnd_1818845 622627814018027662848527 := by
  unfold tailWord_1818845
  simp only [CollatzResearch.WordTrace]
  refine ⟨66338727095642673840273989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44225818063761782560182659 66338727095642673840273989)
  ·
    refine ⟨12438511330433001345051373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66338727095642673840273989 12438511330433001345051373)
    ·
      refine ⟨4664441748912375504394265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12438511330433001345051373 4664441748912375504394265)
      ·
        refine ⟨3498331311684281628295699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4664441748912375504394265 3498331311684281628295699)
        ·
          refine ⟨5247496967526422442443549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3498331311684281628295699 5247496967526422442443549)
          ·
            refine ⟨1967811362822408415916331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5247496967526422442443549 1967811362822408415916331)
            ·
              refine ⟨2951717044233612623874497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1967811362822408415916331 2951717044233612623874497)
              ·
                refine ⟨2213787783175209467905873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2951717044233612623874497 2213787783175209467905873)
                ·
                  refine ⟨1660340837381407100929405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2213787783175209467905873 1660340837381407100929405)
                  ·
                    refine ⟨622627814018027662848527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1660340837381407100929405 622627814018027662848527)
                    ·
                      rfl

theorem cell22_1818845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 1, 2, 2, 3].length) (baseStart_1818845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1818845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1818845 prefixEnd_1818845 := by exact prefixLift 1818845
  have htrace : WordTrace (prefixWord ++ tailWord_1818845) baseStart_1818845 baseEnd_1818845 := by
    simpa [prefixWord, tailWord_1818845, baseEnd_1818845] using wordTrace_append hprefix tailTrace_1818845
  have hstable : (prefixWord ++ tailWord_1818845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1818845).length < 2 ^ (prefixWord ++ tailWord_1818845).sum := by decide
  have hdescent : baseEnd_1818845 < baseStart_1818845 := by decide
  rcases family_descends (prefixWord ++ tailWord_1818845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1818856 : List Nat := [2, 1, 4, 1, 2, 2, 1, 3, 3, 3]
def baseStart_1818856 : Nat := 118140960795 + 1818856 * 2 ^ 59
def prefixEnd_1818856 : Nat := 4983230072969 + 3 ^ 40 * 1818856 * 2
def baseEnd_1818856 : Nat := 622631579542827300823493

theorem tailTrace_1818856 : CollatzResearch.WordTrace tailWord_1818856 prefixEnd_1818856 622631579542827300823493 := by
  unfold tailWord_1818856
  simp only [CollatzResearch.WordTrace]
  refine ⟨33169564149301411359462211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44226085532401881812616281 33169564149301411359462211)
  ·
    refine ⟨49754346223952117039193317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33169564149301411359462211 49754346223952117039193317)
    ·
      refine ⟨9328939916991021944848747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49754346223952117039193317 9328939916991021944848747)
      ·
        refine ⟨13993409875486532917273121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9328939916991021944848747 13993409875486532917273121)
        ·
          refine ⟨10495057406614899687954841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13993409875486532917273121 10495057406614899687954841)
          ·
            refine ⟨7871293054961174765966131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10495057406614899687954841 7871293054961174765966131)
            ·
              refine ⟨11806939582441762148949197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7871293054961174765966131 11806939582441762148949197)
              ·
                refine ⟨4427602343415660805855949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11806939582441762148949197 4427602343415660805855949)
                ·
                  refine ⟨1660350878780872802195981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4427602343415660805855949 1660350878780872802195981)
                  ·
                    refine ⟨622631579542827300823493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1660350878780872802195981 622631579542827300823493)
                    ·
                      rfl

theorem cell22_1818856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 3, 3, 3].length) (baseStart_1818856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1818856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1818856 prefixEnd_1818856 := by exact prefixLift 1818856
  have htrace : WordTrace (prefixWord ++ tailWord_1818856) baseStart_1818856 baseEnd_1818856 := by
    simpa [prefixWord, tailWord_1818856, baseEnd_1818856] using wordTrace_append hprefix tailTrace_1818856
  have hstable : (prefixWord ++ tailWord_1818856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1818856).length < 2 ^ (prefixWord ++ tailWord_1818856).sum := by decide
  have hdescent : baseEnd_1818856 < baseStart_1818856 := by decide
  rcases family_descends (prefixWord ++ tailWord_1818856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1818920 : List Nat := [2, 1, 5, 1, 3, 2, 2, 1, 5]
def baseStart_1818920 : Nat := 118140960795 + 1818920 * 2 ^ 59
def prefixEnd_1818920 : Nat := 4983230072969 + 3 ^ 40 * 1818920 * 2
def baseEnd_1818920 : Nat := 207551162683584155741099

theorem tailTrace_1818920 : CollatzResearch.WordTrace tailWord_1818920 prefixEnd_1818920 207551162683584155741099 := by
  unfold tailWord_1818920
  simp only [CollatzResearch.WordTrace]
  refine ⟨33170731285185480824627107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44227641713580641099502809 33170731285185480824627107)
  ·
    refine ⟨49756096927778221236940661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33170731285185480824627107 49756096927778221236940661)
    ·
      refine ⟨4664634086979208240963187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 49756096927778221236940661 4664634086979208240963187)
      ·
        refine ⟨6996951130468812361444781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4664634086979208240963187 6996951130468812361444781)
        ·
          refine ⟨2623856673925804635541793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6996951130468812361444781 2623856673925804635541793)
          ·
            refine ⟨1967892505444353476656345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2623856673925804635541793 1967892505444353476656345)
            ·
              refine ⟨1475919379083265107492259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1967892505444353476656345 1475919379083265107492259)
              ·
                refine ⟨2213879068624897661238389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1475919379083265107492259 2213879068624897661238389)
                ·
                  refine ⟨207551162683584155741099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2213879068624897661238389 207551162683584155741099)
                  ·
                    rfl

theorem cell22_1818920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 2, 1, 5].length) (baseStart_1818920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1818920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1818920 prefixEnd_1818920 := by exact prefixLift 1818920
  have htrace : WordTrace (prefixWord ++ tailWord_1818920) baseStart_1818920 baseEnd_1818920 := by
    simpa [prefixWord, tailWord_1818920, baseEnd_1818920] using wordTrace_append hprefix tailTrace_1818920
  have hstable : (prefixWord ++ tailWord_1818920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1818920).length < 2 ^ (prefixWord ++ tailWord_1818920).sum := by decide
  have hdescent : baseEnd_1818920 < baseStart_1818920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1818920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1818961 : List Nat := [1, 2, 2, 1, 4, 2, 2, 2, 2, 4]
def baseStart_1818961 : Nat := 118140960795 + 1818961 * 2 ^ 59
def prefixEnd_1818961 : Nat := 4983230072969 + 3 ^ 40 * 1818961 * 2
def baseEnd_1818961 : Nat := 622667523188642026948171

theorem tailTrace_1818961 : CollatzResearch.WordTrace tailWord_1818961 prefixEnd_1818961 622667523188642026948171 := by
  unfold tailWord_1818961
  simp only [CollatzResearch.WordTrace]
  refine ⟨66342957963222425651496737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44228638642148283767664491 66342957963222425651496737)
  ·
    refine ⟨49757218472416819238622553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66342957963222425651496737 49757218472416819238622553)
    ·
      refine ⟨37317913854312614428966915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49757218472416819238622553 37317913854312614428966915)
      ·
        refine ⟨55976870781468921643450373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37317913854312614428966915 55976870781468921643450373)
        ·
          refine ⟨10495663271525422808146945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55976870781468921643450373 10495663271525422808146945)
          ·
            refine ⟨7871747453644067106110209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10495663271525422808146945 7871747453644067106110209)
            ·
              refine ⟨5903810590233050329582657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7871747453644067106110209 5903810590233050329582657)
              ·
                refine ⟨4427857942674787747186993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5903810590233050329582657 4427857942674787747186993)
                ·
                  refine ⟨3320893457006090810390245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4427857942674787747186993 3320893457006090810390245)
                  ·
                    refine ⟨622667523188642026948171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3320893457006090810390245 622667523188642026948171)
                    ·
                      rfl

theorem cell22_1818961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 2, 2, 4].length) (baseStart_1818961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1818961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1818961 prefixEnd_1818961 := by exact prefixLift 1818961
  have htrace : WordTrace (prefixWord ++ tailWord_1818961) baseStart_1818961 baseEnd_1818961 := by
    simpa [prefixWord, tailWord_1818961, baseEnd_1818961] using wordTrace_append hprefix tailTrace_1818961
  have hstable : (prefixWord ++ tailWord_1818961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1818961).length < 2 ^ (prefixWord ++ tailWord_1818961).sum := by decide
  have hdescent : baseEnd_1818961 < baseStart_1818961 := by decide
  rcases family_descends (prefixWord ++ tailWord_1818961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1819096 : List Nat := [2, 1, 2, 2, 2, 1, 1, 1, 6, 4]
def baseStart_1819096 : Nat := 118140960795 + 1819096 * 2 ^ 59
def prefixEnd_1819096 : Nat := 4983230072969 + 3 ^ 40 * 1819096 * 2
def baseEnd_1819096 : Nat := 622713736447546674822757

theorem tailTrace_1819096 : CollatzResearch.WordTrace tailWord_1819096 prefixEnd_1819096 622713736447546674822757 := by
  unfold tailWord_1819096
  simp only [CollatzResearch.WordTrace]
  refine ⟨33173940908866671853830571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44231921211822229138440761 33173940908866671853830571)
  ·
    refine ⟨49760911363300007780745857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33173940908866671853830571 49760911363300007780745857)
    ·
      refine ⟨37320683522475005835559393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49760911363300007780745857 37320683522475005835559393)
      ·
        refine ⟨27990512641856254376669545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37320683522475005835559393 27990512641856254376669545)
        ·
          refine ⟨20992884481392190782502159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27990512641856254376669545 20992884481392190782502159)
          ·
            refine ⟨31489326722088286173753239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20992884481392190782502159 31489326722088286173753239)
            ·
              refine ⟨47233990083132429260629859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31489326722088286173753239 47233990083132429260629859)
              ·
                refine ⟨70850985124698643890944789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47233990083132429260629859 70850985124698643890944789)
                ·
                  refine ⟨3321139927720248932388037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 70850985124698643890944789 3321139927720248932388037)
                  ·
                    refine ⟨622713736447546674822757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3321139927720248932388037 622713736447546674822757)
                    ·
                      rfl

theorem cell22_1819096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 6, 4].length) (baseStart_1819096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1819096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1819096 prefixEnd_1819096 := by exact prefixLift 1819096
  have htrace : WordTrace (prefixWord ++ tailWord_1819096) baseStart_1819096 baseEnd_1819096 := by
    simpa [prefixWord, tailWord_1819096, baseEnd_1819096] using wordTrace_append hprefix tailTrace_1819096
  have hstable : (prefixWord ++ tailWord_1819096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1819096).length < 2 ^ (prefixWord ++ tailWord_1819096).sum := by decide
  have hdescent : baseEnd_1819096 < baseStart_1819096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1819096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1819111 : List Nat := [1, 1, 5, 2, 1, 1, 1, 10]
def baseStart_1819111 : Nat := 118140960795 + 1819111 * 2 ^ 59
def prefixEnd_1819111 : Nat := 4983230072969 + 3 ^ 40 * 1819111 * 2
def baseEnd_1819111 : Nat := 69190985694899070633079

theorem tailTrace_1819111 : CollatzResearch.WordTrace tailWord_1819111 prefixEnd_1819111 69190985694899070633079 := by
  unfold tailWord_1819111
  simp only [CollatzResearch.WordTrace]
  refine ⟨66348428912679001269457187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44232285941786000846304791 66348428912679001269457187)
  ·
    refine ⟨99522643369018501904185781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66348428912679001269457187 99522643369018501904185781)
    ·
      refine ⟨9330247815845484553517417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 99522643369018501904185781 9330247815845484553517417)
      ·
        refine ⟨6997685861884113415138063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9330247815845484553517417 6997685861884113415138063)
        ·
          refine ⟨10496528792826170122707095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6997685861884113415138063 10496528792826170122707095)
          ·
            refine ⟨15744793189239255184060643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10496528792826170122707095 15744793189239255184060643)
            ·
              refine ⟨23617189783858882776090965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15744793189239255184060643 23617189783858882776090965)
              ·
                refine ⟨69190985694899070633079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 23617189783858882776090965 69190985694899070633079)
                ·
                  rfl

theorem cell22_1819111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 10].length) (baseStart_1819111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1819111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1819111 prefixEnd_1819111 := by exact prefixLift 1819111
  have htrace : WordTrace (prefixWord ++ tailWord_1819111) baseStart_1819111 baseEnd_1819111 := by
    simpa [prefixWord, tailWord_1819111, baseEnd_1819111] using wordTrace_append hprefix tailTrace_1819111
  have hstable : (prefixWord ++ tailWord_1819111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1819111).length < 2 ^ (prefixWord ++ tailWord_1819111).sum := by decide
  have hdescent : baseEnd_1819111 < baseStart_1819111 := by decide
  rcases family_descends (prefixWord ++ tailWord_1819111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1819141 : List Nat := [1, 3, 1, 1, 2, 2, 3, 1, 2, 6]
def baseStart_1819141 : Nat := 118140960795 + 1819141 * 2 ^ 59
def prefixEnd_1819141 : Nat := 4983230072969 + 3 ^ 40 * 1819141 * 2
def baseEnd_1819141 : Nat := 622729140867181557447619

theorem tailTrace_1819141 : CollatzResearch.WordTrace tailWord_1819141 prefixEnd_1819141 622729140867181557447619 := by
  unfold tailWord_1819141
  simp only [CollatzResearch.WordTrace]
  refine ⟨66349523102570316393049277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44233015401713544262032851 66349523102570316393049277)
  ·
    refine ⟨24881071163463868647393479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66349523102570316393049277 24881071163463868647393479)
    ·
      refine ⟨37321606745195802971090219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24881071163463868647393479 37321606745195802971090219)
      ·
        refine ⟨55982410117793704456635329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37321606745195802971090219 55982410117793704456635329)
        ·
          refine ⟨41986807588345278342476497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55982410117793704456635329 41986807588345278342476497)
          ·
            refine ⟨31490105691258958756857373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41986807588345278342476497 31490105691258958756857373)
            ·
              refine ⟨11808789634222109533821515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31490105691258958756857373 11808789634222109533821515)
              ·
                refine ⟨17713184451333164300732273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11808789634222109533821515 17713184451333164300732273)
                ·
                  refine ⟨13284888338499873225549205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17713184451333164300732273 13284888338499873225549205)
                  ·
                    refine ⟨622729140867181557447619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13284888338499873225549205 622729140867181557447619)
                    ·
                      rfl

theorem cell22_1819141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 1, 2, 6].length) (baseStart_1819141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1819141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1819141 prefixEnd_1819141 := by exact prefixLift 1819141
  have htrace : WordTrace (prefixWord ++ tailWord_1819141) baseStart_1819141 baseEnd_1819141 := by
    simpa [prefixWord, tailWord_1819141, baseEnd_1819141] using wordTrace_append hprefix tailTrace_1819141
  have hstable : (prefixWord ++ tailWord_1819141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1819141).length < 2 ^ (prefixWord ++ tailWord_1819141).sum := by decide
  have hdescent : baseEnd_1819141 < baseStart_1819141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1819141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1819149 : List Nat := [1, 7, 1, 1, 1, 1, 2, 3, 2, 3]
def baseStart_1819149 : Nat := 118140960795 + 1819149 * 2 ^ 59
def prefixEnd_1819149 : Nat := 4983230072969 + 3 ^ 40 * 1819149 * 2
def baseEnd_1819149 : Nat := 622731879430672203247595

theorem tailTrace_1819149 : CollatzResearch.WordTrace tailWord_1819149 prefixEnd_1819149 622731879430672203247595 := by
  unfold tailWord_1819149
  simp only [CollatzResearch.WordTrace]
  refine ⟨66349814886541333759340501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44233209924360889172893667 66349814886541333759340501)
  ·
    refine ⟨1555073786403312509984543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 66349814886541333759340501 1555073786403312509984543)
    ·
      refine ⟨2332610679604968764976815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1555073786403312509984543 2332610679604968764976815)
      ·
        refine ⟨3498916019407453147465223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2332610679604968764976815 3498916019407453147465223)
        ·
          refine ⟨5248374029111179721197835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3498916019407453147465223 5248374029111179721197835)
          ·
            refine ⟨7872561043666769581796753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5248374029111179721197835 7872561043666769581796753)
            ·
              refine ⟨5904420782750077186347565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7872561043666769581796753 5904420782750077186347565)
              ·
                refine ⟨2214157793531278944880337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5904420782750077186347565 2214157793531278944880337)
                ·
                  refine ⟨1660618345148459208660253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2214157793531278944880337 1660618345148459208660253)
                  ·
                    refine ⟨622731879430672203247595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1660618345148459208660253 622731879430672203247595)
                    ·
                      rfl

theorem cell22_1819149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_1819149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1819149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1819149 prefixEnd_1819149 := by exact prefixLift 1819149
  have htrace : WordTrace (prefixWord ++ tailWord_1819149) baseStart_1819149 baseEnd_1819149 := by
    simpa [prefixWord, tailWord_1819149, baseEnd_1819149] using wordTrace_append hprefix tailTrace_1819149
  have hstable : (prefixWord ++ tailWord_1819149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1819149).length < 2 ^ (prefixWord ++ tailWord_1819149).sum := by decide
  have hdescent : baseEnd_1819149 < baseStart_1819149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1819149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1819160 : List Nat := [2, 1, 2, 3, 3, 2, 1, 2, 3, 3]
def baseStart_1819160 : Nat := 118140960795 + 1819160 * 2 ^ 59
def prefixEnd_1819160 : Nat := 4983230072969 + 3 ^ 40 * 1819160 * 2
def baseEnd_1819160 : Nat := 622735644955471841222561

theorem tailTrace_1819160 : CollatzResearch.WordTrace tailWord_1819160 prefixEnd_1819160 622735644955471841222561 := by
  unfold tailWord_1819160
  simp only [CollatzResearch.WordTrace]
  refine ⟨33175108044750741318995467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44233477393000988425327289 33175108044750741318995467)
  ·
    refine ⟨49762662067126111978493201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33175108044750741318995467 49762662067126111978493201)
    ·
      refine ⟨37321996550344583983869901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49762662067126111978493201 37321996550344583983869901)
      ·
        refine ⟨13995748706379218993951213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37321996550344583983869901 13995748706379218993951213)
        ·
          refine ⟨5248405764892207122731705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13995748706379218993951213 5248405764892207122731705)
          ·
            refine ⟨3936304323669155342048779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5248405764892207122731705 3936304323669155342048779)
            ·
              refine ⟨5904456485503733013073169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3936304323669155342048779 5904456485503733013073169)
              ·
                refine ⟨4428342364127799759804877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5904456485503733013073169 4428342364127799759804877)
                ·
                  refine ⟨1660628386547924909926829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4428342364127799759804877 1660628386547924909926829)
                  ·
                    refine ⟨622735644955471841222561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1660628386547924909926829 622735644955471841222561)
                    ·
                      rfl

theorem cell22_1819160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 2, 3, 3].length) (baseStart_1819160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1819160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1819160 prefixEnd_1819160 := by exact prefixLift 1819160
  have htrace : WordTrace (prefixWord ++ tailWord_1819160) baseStart_1819160 baseEnd_1819160 := by
    simpa [prefixWord, tailWord_1819160, baseEnd_1819160] using wordTrace_append hprefix tailTrace_1819160
  have hstable : (prefixWord ++ tailWord_1819160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1819160).length < 2 ^ (prefixWord ++ tailWord_1819160).sum := by decide
  have hdescent : baseEnd_1819160 < baseStart_1819160 := by decide
  rcases family_descends (prefixWord ++ tailWord_1819160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1819190 : List Nat := [5, 1, 2, 1, 2, 2, 1, 1, 7]
def baseStart_1819190 : Nat := 118140960795 + 1819190 * 2 ^ 59
def prefixEnd_1819190 : Nat := 4983230072969 + 3 ^ 40 * 1819190 * 2
def baseEnd_1819190 : Nat := 207581971522853920990823

theorem tailTrace_1819190 : CollatzResearch.WordTrace tailWord_1819190 prefixEnd_1819190 207581971522853920990823 := by
  unfold tailWord_1819190
  simp only [CollatzResearch.WordTrace]
  refine ⟨4146956892462049860098939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44234206852928531841055349 4146956892462049860098939)
  ·
    refine ⟨6220435338693074790148409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4146956892462049860098939 6220435338693074790148409)
    ·
      refine ⟨4665326504019806092611307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6220435338693074790148409 4665326504019806092611307)
      ·
        refine ⟨6997989756029709138916961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4665326504019806092611307 6997989756029709138916961)
        ·
          refine ⟨5248492317022281854187721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6997989756029709138916961 5248492317022281854187721)
          ·
            refine ⟨3936369237766711390640791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5248492317022281854187721 3936369237766711390640791)
            ·
              refine ⟨5904553856650067085961187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3936369237766711390640791 5904553856650067085961187)
              ·
                refine ⟨8856830784975100628941781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5904553856650067085961187 8856830784975100628941781)
                ·
                  refine ⟨207581971522853920990823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8856830784975100628941781 207581971522853920990823)
                  ·
                    rfl

theorem cell22_1819190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 1, 7].length) (baseStart_1819190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1819190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1819190 prefixEnd_1819190 := by exact prefixLift 1819190
  have htrace : WordTrace (prefixWord ++ tailWord_1819190) baseStart_1819190 baseEnd_1819190 := by
    simpa [prefixWord, tailWord_1819190, baseEnd_1819190] using wordTrace_append hprefix tailTrace_1819190
  have hstable : (prefixWord ++ tailWord_1819190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1819190).length < 2 ^ (prefixWord ++ tailWord_1819190).sum := by decide
  have hdescent : baseEnd_1819190 < baseStart_1819190 := by decide
  rcases family_descends (prefixWord ++ tailWord_1819190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1819218 : List Nat := [3, 2, 2, 1, 2, 1, 1, 4, 6]
def baseStart_1819218 : Nat := 118140960795 + 1819218 * 2 ^ 59
def prefixEnd_1819218 : Nat := 4983230072969 + 3 ^ 40 * 1819218 * 2
def baseEnd_1819218 : Nat := 207585166513593007757461

theorem tailTrace_1819218 : CollatzResearch.WordTrace tailWord_1819218 prefixEnd_1819218 207585166513593007757461 := by
  unfold tailWord_1819218
  simp only [CollatzResearch.WordTrace]
  refine ⟨16588082880822839635900577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44234887682194239029068205 16588082880822839635900577)
  ·
    refine ⟨12441062160617129726925433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16588082880822839635900577 12441062160617129726925433)
    ·
      refine ⟨9330796620462847295194075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12441062160617129726925433 9330796620462847295194075)
      ·
        refine ⟨13996194930694270942791113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9330796620462847295194075 13996194930694270942791113)
        ·
          refine ⟨10497146198020703207093335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13996194930694270942791113 10497146198020703207093335)
          ·
            refine ⟨15745719297031054810640003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10497146198020703207093335 15745719297031054810640003)
            ·
              refine ⟨23618578945546582215960005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15745719297031054810640003 23618578945546582215960005)
              ·
                refine ⟨4428483552289984165492501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23618578945546582215960005 4428483552289984165492501)
                ·
                  refine ⟨207585166513593007757461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4428483552289984165492501 207585166513593007757461)
                  ·
                    rfl

theorem cell22_1819218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 4, 6].length) (baseStart_1819218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1819218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1819218 prefixEnd_1819218 := by exact prefixLift 1819218
  have htrace : WordTrace (prefixWord ++ tailWord_1819218) baseStart_1819218 baseEnd_1819218 := by
    simpa [prefixWord, tailWord_1819218, baseEnd_1819218] using wordTrace_append hprefix tailTrace_1819218
  have hstable : (prefixWord ++ tailWord_1819218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1819218).length < 2 ^ (prefixWord ++ tailWord_1819218).sum := by decide
  have hdescent : baseEnd_1819218 < baseStart_1819218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1819218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1819220 : List Nat := [2, 4, 1, 1, 1, 3, 1, 4, 1, 4]
def baseStart_1819220 : Nat := 118140960795 + 1819220 * 2 ^ 59
def prefixEnd_1819220 : Nat := 4983230072969 + 3 ^ 40 * 1819220 * 2
def baseEnd_1819220 : Nat := 622756184181651684722377

theorem tailTrace_1819220 : CollatzResearch.WordTrace tailWord_1819220 prefixEnd_1819220 622756184181651684722377 := by
  unfold tailWord_1819220
  simp only [CollatzResearch.WordTrace]
  refine ⟨33176202234642056442587557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44234936312856075256783409 33176202234642056442587557)
  ·
    refine ⟨6220537918995385582985167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33176202234642056442587557 6220537918995385582985167)
    ·
      refine ⟨9330806878493078374477751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6220537918995385582985167 9330806878493078374477751)
      ·
        refine ⟨13996210317739617561716627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9330806878493078374477751 13996210317739617561716627)
        ·
          refine ⟨20994315476609426342574941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13996210317739617561716627 20994315476609426342574941)
          ·
            refine ⟨7872868303728534878465603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20994315476609426342574941 7872868303728534878465603)
            ·
              refine ⟨11809302455592802317698405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7872868303728534878465603 11809302455592802317698405)
              ·
                refine ⟨2214244210423650434568451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11809302455592802317698405 2214244210423650434568451)
                ·
                  refine ⟨3321366315635475651852677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2214244210423650434568451 3321366315635475651852677)
                  ·
                    refine ⟨622756184181651684722377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3321366315635475651852677 622756184181651684722377)
                    ·
                      rfl

theorem cell22_1819220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 4, 1, 4].length) (baseStart_1819220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1819220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1819220 prefixEnd_1819220 := by exact prefixLift 1819220
  have htrace : WordTrace (prefixWord ++ tailWord_1819220) baseStart_1819220 baseEnd_1819220 := by
    simpa [prefixWord, tailWord_1819220, baseEnd_1819220] using wordTrace_append hprefix tailTrace_1819220
  have hstable : (prefixWord ++ tailWord_1819220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1819220).length < 2 ^ (prefixWord ++ tailWord_1819220).sum := by decide
  have hdescent : baseEnd_1819220 < baseStart_1819220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1819220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1819267 : List Nat := [1, 1, 1, 3, 3, 1, 6, 1, 2, 3]
def baseStart_1819267 : Nat := 118140960795 + 1819267 * 2 ^ 59
def prefixEnd_1819267 : Nat := 4983230072969 + 3 ^ 40 * 1819267 * 2
def baseEnd_1819267 : Nat := 622772273242159228797233

theorem tailTrace_1819267 : CollatzResearch.WordTrace tailWord_1819267 prefixEnd_1819267 622772273242159228797233 := by
  unfold tailWord_1819267
  simp only [CollatzResearch.WordTrace]
  refine ⟨66354118700113839912136055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44236079133409226608090703 66354118700113839912136055)
  ·
    refine ⟨99531178050170759868204083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66354118700113839912136055 99531178050170759868204083)
    ·
      refine ⟨149296767075256139802306125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99531178050170759868204083 149296767075256139802306125)
      ·
        refine ⟨55986287653221052425864797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149296767075256139802306125 55986287653221052425864797)
        ·
          refine ⟨20994857869957894659699299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55986287653221052425864797 20994857869957894659699299)
          ·
            refine ⟨31492286804936841989548949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20994857869957894659699299 31492286804936841989548949)
            ·
              refine ⟨1476200943981414468260107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 31492286804936841989548949 1476200943981414468260107)
              ·
                refine ⟨2214301415972121702390161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1476200943981414468260107 2214301415972121702390161)
                ·
                  refine ⟨1660726061979091276792621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2214301415972121702390161 1660726061979091276792621)
                  ·
                    refine ⟨622772273242159228797233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1660726061979091276792621 622772273242159228797233)
                    ·
                      rfl

theorem cell22_1819267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 6, 1, 2, 3].length) (baseStart_1819267 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1819267 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1819267 prefixEnd_1819267 := by exact prefixLift 1819267
  have htrace : WordTrace (prefixWord ++ tailWord_1819267) baseStart_1819267 baseEnd_1819267 := by
    simpa [prefixWord, tailWord_1819267, baseEnd_1819267] using wordTrace_append hprefix tailTrace_1819267
  have hstable : (prefixWord ++ tailWord_1819267).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1819267).length < 2 ^ (prefixWord ++ tailWord_1819267).sum := by decide
  have hdescent : baseEnd_1819267 < baseStart_1819267 := by decide
  rcases family_descends (prefixWord ++ tailWord_1819267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1819282 : List Nat := [3, 2, 3, 1, 2, 2, 2, 1, 2, 4]
def baseStart_1819282 : Nat := 118140960795 + 1819282 * 2 ^ 59
def prefixEnd_1819282 : Nat := 4983230072969 + 3 ^ 40 * 1819282 * 2
def baseEnd_1819282 : Nat := 622777408048704189672187

theorem tailTrace_1819282 : CollatzResearch.WordTrace tailWord_1819282 prefixEnd_1819282 622777408048704189672187 := by
  unfold tailWord_1819282
  simp only [CollatzResearch.WordTrace]
  refine ⟨16588666448764874368483025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44236443863372998315954733 16588666448764874368483025)
  ·
    refine ⟨12441499836573655776362269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16588666448764874368483025 12441499836573655776362269)
    ·
      refine ⟨4665562438715120916135851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12441499836573655776362269 4665562438715120916135851)
      ·
        refine ⟨6998343658072681374203777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4665562438715120916135851 6998343658072681374203777)
        ·
          refine ⟨5248757743554511030652833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6998343658072681374203777 5248757743554511030652833)
          ·
            refine ⟨3936568307665883272989625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5248757743554511030652833 3936568307665883272989625)
            ·
              refine ⟨2952426230749412454742219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3936568307665883272989625 2952426230749412454742219)
              ·
                refine ⟨4428639346124118682113329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2952426230749412454742219 4428639346124118682113329)
                ·
                  refine ⟨3321479509593089011584997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4428639346124118682113329 3321479509593089011584997)
                  ·
                    refine ⟨622777408048704189672187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3321479509593089011584997 622777408048704189672187)
                    ·
                      rfl

theorem cell22_1819282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_1819282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1819282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1819282 prefixEnd_1819282 := by exact prefixLift 1819282
  have htrace : WordTrace (prefixWord ++ tailWord_1819282) baseStart_1819282 baseEnd_1819282 := by
    simpa [prefixWord, tailWord_1819282, baseEnd_1819282] using wordTrace_append hprefix tailTrace_1819282
  have hstable : (prefixWord ++ tailWord_1819282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1819282).length < 2 ^ (prefixWord ++ tailWord_1819282).sum := by decide
  have hdescent : baseEnd_1819282 < baseStart_1819282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1819282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1819303 : List Nat := [1, 1, 6, 3, 2, 1, 2, 2, 4]
def baseStart_1819303 : Nat := 118140960795 + 1819303 * 2 ^ 59
def prefixEnd_1819303 : Nat := 4983230072969 + 3 ^ 40 * 1819303 * 2
def baseEnd_1819303 : Nat := 207594865592622378299041

theorem tailTrace_1819303 : CollatzResearch.WordTrace tailWord_1819303 prefixEnd_1819303 207594865592622378299041 := by
  unfold tailWord_1819303
  simp only [CollatzResearch.WordTrace]
  refine ⟨66355431727983418060446563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44236954485322278706964375 66355431727983418060446563)
  ·
    refine ⟨99533147591975127090669845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66355431727983418060446563 99533147591975127090669845)
    ·
      refine ⟨4665616293373834082375149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 99533147591975127090669845 4665616293373834082375149)
      ·
        refine ⟨1749606110015187780890681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4665616293373834082375149 1749606110015187780890681)
        ·
          refine ⟨1312204582511390835668011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1749606110015187780890681 1312204582511390835668011)
          ·
            refine ⟨1968306873767086253502017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1312204582511390835668011 1968306873767086253502017)
            ·
              refine ⟨1476230155325314690126513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1968306873767086253502017 1476230155325314690126513)
              ·
                refine ⟨1107172616493986017594885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1476230155325314690126513 1107172616493986017594885)
                ·
                  refine ⟨207594865592622378299041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1107172616493986017594885 207594865592622378299041)
                  ·
                    rfl

theorem cell22_1819303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 2, 2, 4].length) (baseStart_1819303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1819303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1819303 prefixEnd_1819303 := by exact prefixLift 1819303
  have htrace : WordTrace (prefixWord ++ tailWord_1819303) baseStart_1819303 baseEnd_1819303 := by
    simpa [prefixWord, tailWord_1819303, baseEnd_1819303] using wordTrace_append hprefix tailTrace_1819303
  have hstable : (prefixWord ++ tailWord_1819303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1819303).length < 2 ^ (prefixWord ++ tailWord_1819303).sum := by decide
  have hdescent : baseEnd_1819303 < baseStart_1819303 := by decide
  rcases family_descends (prefixWord ++ tailWord_1819303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1819325 : List Nat := [1, 4, 1, 2, 1, 3, 2, 3, 5]
def baseStart_1819325 : Nat := 118140960795 + 1819325 * 2 ^ 59
def prefixEnd_1819325 : Nat := 4983230072969 + 3 ^ 40 * 1819325 * 2
def baseEnd_1819325 : Nat := 207597375942488803615685

theorem tailTrace_1819325 : CollatzResearch.WordTrace tailWord_1819325 prefixEnd_1819325 207597375942488803615685 := by
  unfold tailWord_1819325
  simp only [CollatzResearch.WordTrace]
  refine ⟨66356234133903715817747429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44237489422602477211831619 66356234133903715817747429)
  ·
    refine ⟨12441793900106946715827643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66356234133903715817747429 12441793900106946715827643)
    ·
      refine ⟨18662690850160420073741465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12441793900106946715827643 18662690850160420073741465)
      ·
        refine ⟨13997018137620315055306099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18662690850160420073741465 13997018137620315055306099)
        ·
          refine ⟨20995527206430472582959149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13997018137620315055306099 20995527206430472582959149)
          ·
            refine ⟨7873322702411427218609681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20995527206430472582959149 7873322702411427218609681)
            ·
              refine ⟨5904992026808570413957261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7873322702411427218609681 5904992026808570413957261)
              ·
                refine ⟨2214372010053213905233973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5904992026808570413957261 2214372010053213905233973)
                ·
                  refine ⟨207597375942488803615685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2214372010053213905233973 207597375942488803615685)
                  ·
                    rfl

theorem cell22_1819325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 3, 5].length) (baseStart_1819325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1819325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1819325 prefixEnd_1819325 := by exact prefixLift 1819325
  have htrace : WordTrace (prefixWord ++ tailWord_1819325) baseStart_1819325 baseEnd_1819325 := by
    simpa [prefixWord, tailWord_1819325, baseEnd_1819325] using wordTrace_append hprefix tailTrace_1819325
  have hstable : (prefixWord ++ tailWord_1819325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1819325).length < 2 ^ (prefixWord ++ tailWord_1819325).sum := by decide
  have hdescent : baseEnd_1819325 < baseStart_1819325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1819325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1819346 : List Nat := [3, 2, 2, 2, 3, 1, 2, 3, 1, 3]
def baseStart_1819346 : Nat := 118140960795 + 1819346 * 2 ^ 59
def prefixEnd_1819346 : Nat := 4983230072969 + 3 ^ 40 * 1819346 * 2
def baseEnd_1819346 : Nat := 622799316556629356071991

theorem tailTrace_1819346 : CollatzResearch.WordTrace tailWord_1819346 prefixEnd_1819346 622799316556629356071991 := by
  unfold tailWord_1819346
  simp only [CollatzResearch.WordTrace]
  refine ⟨16589250016706909101065473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44238000044551757602841261 16589250016706909101065473)
  ·
    refine ⟨12441937512530181825799105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16589250016706909101065473 12441937512530181825799105)
    ·
      refine ⟨9331453134397636369349329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12441937512530181825799105 9331453134397636369349329)
      ·
        refine ⟨6998589850798227277011997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9331453134397636369349329 6998589850798227277011997)
        ·
          refine ⟨2624471194049335228879499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6998589850798227277011997 2624471194049335228879499)
          ·
            refine ⟨3936706791074002843319249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2624471194049335228879499 3936706791074002843319249)
            ·
              refine ⟨2952530093305502132489437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3936706791074002843319249 2952530093305502132489437)
              ·
                refine ⟨1107198784989563299683539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2952530093305502132489437 1107198784989563299683539)
                ·
                  refine ⟨1660798177484344949525309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1107198784989563299683539 1660798177484344949525309)
                  ·
                    refine ⟨622799316556629356071991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1660798177484344949525309 622799316556629356071991)
                    ·
                      rfl

theorem cell22_1819346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 2, 3, 1, 3].length) (baseStart_1819346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1819346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1819346 prefixEnd_1819346 := by exact prefixLift 1819346
  have htrace : WordTrace (prefixWord ++ tailWord_1819346) baseStart_1819346 baseEnd_1819346 := by
    simpa [prefixWord, tailWord_1819346, baseEnd_1819346] using wordTrace_append hprefix tailTrace_1819346
  have hstable : (prefixWord ++ tailWord_1819346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1819346).length < 2 ^ (prefixWord ++ tailWord_1819346).sum := by decide
  have hdescent : baseEnd_1819346 < baseStart_1819346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1819346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1819353 : List Nat := [1, 2, 1, 2, 3, 2, 1, 2, 8]
def baseStart_1819353 : Nat := 118140960795 + 1819353 * 2 ^ 59
def prefixEnd_1819353 : Nat := 4983230072969 + 3 ^ 40 * 1819353 * 2
def baseEnd_1819353 : Nat := 207600570933227890382323

theorem tailTrace_1819353 : CollatzResearch.WordTrace tailWord_1819353 prefixEnd_1819353 207600570933227890382323 := by
  unfold tailWord_1819353
  simp only [CollatzResearch.WordTrace]
  refine ⟨66357255377802276599766713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44238170251868184399844475 66357255377802276599766713)
  ·
    refine ⟨49767941533351707449825035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66357255377802276599766713 49767941533351707449825035)
    ·
      refine ⟨74651912300027561174737553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49767941533351707449825035 74651912300027561174737553)
      ·
        refine ⟨55988934225020670881053165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74651912300027561174737553 55988934225020670881053165)
        ·
          refine ⟨20995850334382751580394937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55988934225020670881053165 20995850334382751580394937)
          ·
            refine ⟨15746887750787063685296203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20995850334382751580394937 15746887750787063685296203)
            ·
              refine ⟨23620331626180595527944305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15746887750787063685296203 23620331626180595527944305)
              ·
                refine ⟨17715248719635446645958229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23620331626180595527944305 17715248719635446645958229)
                ·
                  refine ⟨207600570933227890382323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17715248719635446645958229 207600570933227890382323)
                  ·
                    rfl

theorem cell22_1819353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 2, 8].length) (baseStart_1819353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1819353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1819353 prefixEnd_1819353 := by exact prefixLift 1819353
  have htrace : WordTrace (prefixWord ++ tailWord_1819353) baseStart_1819353 baseEnd_1819353 := by
    simpa [prefixWord, tailWord_1819353, baseEnd_1819353] using wordTrace_append hprefix tailTrace_1819353
  have hstable : (prefixWord ++ tailWord_1819353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1819353).length < 2 ^ (prefixWord ++ tailWord_1819353).sum := by decide
  have hdescent : baseEnd_1819353 < baseStart_1819353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1819353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1819400 : List Nat := [2, 1, 3, 2, 2, 2, 2, 1, 1, 6]
def baseStart_1819400 : Nat := 118140960795 + 1819400 * 2 ^ 59
def prefixEnd_1819400 : Nat := 4983230072969 + 3 ^ 40 * 1819400 * 2
def baseEnd_1819400 : Nat := 622817801860191215221825

theorem tailTrace_1819400 : CollatzResearch.WordTrace tailWord_1819400 prefixEnd_1819400 622817801860191215221825 := by
  unfold tailWord_1819400
  simp only [CollatzResearch.WordTrace]
  refine ⟨33179484804316001813363827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44239313072421335751151769 33179484804316001813363827)
  ·
    refine ⟨49769227206474002720045741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33179484804316001813363827 49769227206474002720045741)
    ·
      refine ⟨18663460202427751020017153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49769227206474002720045741 18663460202427751020017153)
      ·
        refine ⟨13997595151820813265012865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18663460202427751020017153 13997595151820813265012865)
        ·
          refine ⟨10498196363865609948759649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13997595151820813265012865 10498196363865609948759649)
          ·
            refine ⟨7873647272899207461569737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10498196363865609948759649 7873647272899207461569737)
            ·
              refine ⟨5905235454674405596177303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7873647272899207461569737 5905235454674405596177303)
              ·
                refine ⟨8857853182011608394265955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5905235454674405596177303 8857853182011608394265955)
                ·
                  refine ⟨13286779773017412591398933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8857853182011608394265955 13286779773017412591398933)
                  ·
                    refine ⟨622817801860191215221825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13286779773017412591398933 622817801860191215221825)
                    ·
                      rfl

theorem cell22_1819400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 1, 1, 6].length) (baseStart_1819400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1819400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1819400 prefixEnd_1819400 := by exact prefixLift 1819400
  have htrace : WordTrace (prefixWord ++ tailWord_1819400) baseStart_1819400 baseEnd_1819400 := by
    simpa [prefixWord, tailWord_1819400, baseEnd_1819400] using wordTrace_append hprefix tailTrace_1819400
  have hstable : (prefixWord ++ tailWord_1819400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1819400).length < 2 ^ (prefixWord ++ tailWord_1819400).sum := by decide
  have hdescent : baseEnd_1819400 < baseStart_1819400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1819400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1819421 : List Nat := [1, 4, 2, 4, 2, 1, 1, 1, 6]
def baseStart_1819421 : Nat := 118140960795 + 1819421 * 2 ^ 59
def prefixEnd_1819421 : Nat := 4983230072969 + 3 ^ 40 * 1819421 * 2
def baseEnd_1819421 : Nat := 207608330196451386815587

theorem tailTrace_1819421 : CollatzResearch.WordTrace tailWord_1819421 prefixEnd_1819421 207608330196451386815587 := by
  unfold tailWord_1819421
  simp only [CollatzResearch.WordTrace]
  refine ⟨66359735541555924213242117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44239823694370616142161411 66359735541555924213242117)
  ·
    refine ⟨12442450414041735789982897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66359735541555924213242117 12442450414041735789982897)
    ·
      refine ⟨9331837810531301842487173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12442450414041735789982897 9331837810531301842487173)
      ·
        refine ⟨1749719589474619095466345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9331837810531301842487173 1749719589474619095466345)
        ·
          refine ⟨1312289692105964321599759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1749719589474619095466345 1312289692105964321599759)
          ·
            refine ⟨1968434538158946482399639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1312289692105964321599759 1968434538158946482399639)
            ·
              refine ⟨2952651807238419723599459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1968434538158946482399639 2952651807238419723599459)
              ·
                refine ⟨4428977710857629585399189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2952651807238419723599459 4428977710857629585399189)
                ·
                  refine ⟨207608330196451386815587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4428977710857629585399189 207608330196451386815587)
                  ·
                    rfl

theorem cell22_1819421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 1, 1, 6].length) (baseStart_1819421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1819421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1819421 prefixEnd_1819421 := by exact prefixLift 1819421
  have htrace : WordTrace (prefixWord ++ tailWord_1819421) baseStart_1819421 baseEnd_1819421 := by
    simpa [prefixWord, tailWord_1819421, baseEnd_1819421] using wordTrace_append hprefix tailTrace_1819421
  have hstable : (prefixWord ++ tailWord_1819421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1819421).length < 2 ^ (prefixWord ++ tailWord_1819421).sum := by decide
  have hdescent : baseEnd_1819421 < baseStart_1819421 := by decide
  rcases family_descends (prefixWord ++ tailWord_1819421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1819464 : List Nat := [2, 1, 3, 1, 1, 3, 2, 5, 1, 3]
def baseStart_1819464 : Nat := 118140960795 + 1819464 * 2 ^ 59
def prefixEnd_1819464 : Nat := 4983230072969 + 3 ^ 40 * 1819464 * 2
def baseEnd_1819464 : Nat := 622839710368116381621629

theorem tailTrace_1819464 : CollatzResearch.WordTrace tailWord_1819464 prefixEnd_1819464 622839710368116381621629 := by
  unfold tailWord_1819464
  simp only [CollatzResearch.WordTrace]
  refine ⟨33180651940200071278528723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44240869253600095038038297 33180651940200071278528723)
  ·
    refine ⟨49770977910300106917793085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33180651940200071278528723 49770977910300106917793085)
    ·
      refine ⟨18664116716362540094172407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49770977910300106917793085 18664116716362540094172407)
      ·
        refine ⟨27996175074543810141258611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18664116716362540094172407 27996175074543810141258611)
        ·
          refine ⟨41994262611815715211887917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27996175074543810141258611 41994262611815715211887917)
          ·
            refine ⟨15747848479430893204457969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41994262611815715211887917 15747848479430893204457969)
            ·
              refine ⟨11810886359573169903343477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15747848479430893204457969 11810886359573169903343477)
              ·
                refine ⟨1107270596209984678438451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11810886359573169903343477 1107270596209984678438451)
                ·
                  refine ⟨1660905894314977017657677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1107270596209984678438451 1660905894314977017657677)
                  ·
                    refine ⟨622839710368116381621629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1660905894314977017657677 622839710368116381621629)
                    ·
                      rfl

theorem cell22_1819464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 5, 1, 3].length) (baseStart_1819464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1819464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1819464 prefixEnd_1819464 := by exact prefixLift 1819464
  have htrace : WordTrace (prefixWord ++ tailWord_1819464) baseStart_1819464 baseEnd_1819464 := by
    simpa [prefixWord, tailWord_1819464, baseEnd_1819464] using wordTrace_append hprefix tailTrace_1819464
  have hstable : (prefixWord ++ tailWord_1819464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1819464).length < 2 ^ (prefixWord ++ tailWord_1819464).sum := by decide
  have hdescent : baseEnd_1819464 < baseStart_1819464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1819464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1819477 : List Nat := [1, 3, 2, 2, 2, 1, 4, 2, 5]
def baseStart_1819477 : Nat := 118140960795 + 1819477 * 2 ^ 59
def prefixEnd_1819477 : Nat := 4983230072969 + 3 ^ 40 * 1819477 * 2
def baseEnd_1819477 : Nat := 207614720177929560348863

theorem tailTrace_1819477 : CollatzResearch.WordTrace tailWord_1819477 prefixEnd_1819477 207614720177929560348863 := by
  unfold tailWord_1819477
  simp only [CollatzResearch.WordTrace]
  refine ⟨66361778029353045777280685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44241185352902030518187123 66361778029353045777280685)
  ·
    refine ⟨24885666761007392166480257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66361778029353045777280685 24885666761007392166480257)
    ·
      refine ⟨18664250070755544124860193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24885666761007392166480257 18664250070755544124860193)
      ·
        refine ⟨13998187553066658093645145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18664250070755544124860193 13998187553066658093645145)
        ·
          refine ⟨10498640664799993570233859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13998187553066658093645145 10498640664799993570233859)
          ·
            refine ⟨15747960997199990355350789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10498640664799993570233859 15747960997199990355350789)
            ·
              refine ⟨2952742686974998191628273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15747960997199990355350789 2952742686974998191628273)
              ·
                refine ⟨2214557015231248643721205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2952742686974998191628273 2214557015231248643721205)
                ·
                  refine ⟨207614720177929560348863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2214557015231248643721205 207614720177929560348863)
                  ·
                    rfl

theorem cell22_1819477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 4, 2, 5].length) (baseStart_1819477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1819477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1819477 prefixEnd_1819477 := by exact prefixLift 1819477
  have htrace : WordTrace (prefixWord ++ tailWord_1819477) baseStart_1819477 baseEnd_1819477 := by
    simpa [prefixWord, tailWord_1819477, baseEnd_1819477] using wordTrace_append hprefix tailTrace_1819477
  have hstable : (prefixWord ++ tailWord_1819477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1819477).length < 2 ^ (prefixWord ++ tailWord_1819477).sum := by decide
  have hdescent : baseEnd_1819477 < baseStart_1819477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1819477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1819481 : List Nat := [1, 2, 1, 2, 2, 4, 4, 2, 1, 3]
def baseStart_1819481 : Nat := 118140960795 + 1819481 * 2 ^ 59
def prefixEnd_1819481 : Nat := 4983230072969 + 3 ^ 40 * 1819481 * 2
def baseEnd_1819481 : Nat := 622845529815534003946577

theorem tailTrace_1819481 : CollatzResearch.WordTrace tailWord_1819481 prefixEnd_1819481 622845529815534003946577 := by
  unfold tailWord_1819481
  simp only [CollatzResearch.WordTrace]
  refine ⟨66361923921338554460426297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44241282614225702973617531 66361923921338554460426297)
  ·
    refine ⟨49771442941003915845319723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66361923921338554460426297 49771442941003915845319723)
    ·
      refine ⟨74657164411505873767979585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49771442941003915845319723 74657164411505873767979585)
      ·
        refine ⟨55992873308629405325984689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74657164411505873767979585 55992873308629405325984689)
        ·
          refine ⟨41994654981472053994488517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55992873308629405325984689 41994654981472053994488517)
          ·
            refine ⟨7873997809026010123966597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41994654981472053994488517 7873997809026010123966597)
            ·
              refine ⟨1476374589192376898243737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7873997809026010123966597 1476374589192376898243737)
              ·
                refine ⟨1107280941894282673682803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1476374589192376898243737 1107280941894282673682803)
                ·
                  refine ⟨1660921412841424010524205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1107280941894282673682803 1660921412841424010524205)
                  ·
                    refine ⟨622845529815534003946577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1660921412841424010524205 622845529815534003946577)
                    ·
                      rfl

theorem cell22_1819481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 4, 2, 1, 3].length) (baseStart_1819481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1819481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1819481 prefixEnd_1819481 := by exact prefixLift 1819481
  have htrace : WordTrace (prefixWord ++ tailWord_1819481) baseStart_1819481 baseEnd_1819481 := by
    simpa [prefixWord, tailWord_1819481, baseEnd_1819481] using wordTrace_append hprefix tailTrace_1819481
  have hstable : (prefixWord ++ tailWord_1819481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1819481).length < 2 ^ (prefixWord ++ tailWord_1819481).sum := by decide
  have hdescent : baseEnd_1819481 < baseStart_1819481 := by decide
  rcases family_descends (prefixWord ++ tailWord_1819481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1819492 : List Nat := [2, 3, 1, 1, 4, 2, 1, 1, 2, 5]
def baseStart_1819492 : Nat := 118140960795 + 1819492 * 2 ^ 59
def prefixEnd_1819492 : Nat := 4983230072969 + 3 ^ 40 * 1819492 * 2
def baseEnd_1819492 : Nat := 622849295340333641921543

theorem tailTrace_1819492 : CollatzResearch.WordTrace tailWord_1819492 prefixEnd_1819492 622849295340333641921543 := by
  unfold tailWord_1819492
  simp only [CollatzResearch.WordTrace]
  refine ⟨33181162562149351669538365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44241550082865802226051153 33181162562149351669538365)
  ·
    refine ⟨12442935960806006876076887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33181162562149351669538365 12442935960806006876076887)
    ·
      refine ⟨18664403941209010314115331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12442935960806006876076887 18664403941209010314115331)
      ·
        refine ⟨27996605911813515471172997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18664403941209010314115331 27996605911813515471172997)
        ·
          refine ⟨5249363608465034150844937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27996605911813515471172997 5249363608465034150844937)
          ·
            refine ⟨3937022706348775613133703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5249363608465034150844937 3937022706348775613133703)
            ·
              refine ⟨5905534059523163419700555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3937022706348775613133703 5905534059523163419700555)
              ·
                refine ⟨8858301089284745129550833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5905534059523163419700555 8858301089284745129550833)
                ·
                  refine ⟨6643725816963558847163125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8858301089284745129550833 6643725816963558847163125)
                  ·
                    refine ⟨622849295340333641921543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6643725816963558847163125 622849295340333641921543)
                    ·
                      rfl

theorem cell22_1819492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 1, 2, 5].length) (baseStart_1819492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1819492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1819492 prefixEnd_1819492 := by exact prefixLift 1819492
  have htrace : WordTrace (prefixWord ++ tailWord_1819492) baseStart_1819492 baseEnd_1819492 := by
    simpa [prefixWord, tailWord_1819492, baseEnd_1819492] using wordTrace_append hprefix tailTrace_1819492
  have hstable : (prefixWord ++ tailWord_1819492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1819492).length < 2 ^ (prefixWord ++ tailWord_1819492).sum := by decide
  have hdescent : baseEnd_1819492 < baseStart_1819492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1819492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1819505 : List Nat := [1, 2, 2, 2, 1, 4, 1, 1, 8]
def baseStart_1819505 : Nat := 118140960795 + 1819505 * 2 ^ 59
def prefixEnd_1819505 : Nat := 4983230072969 + 3 ^ 40 * 1819505 * 2
def baseEnd_1819505 : Nat := 207617915168668647115501

theorem tailTrace_1819505 : CollatzResearch.WordTrace tailWord_1819505 prefixEnd_1819505 207617915168668647115501 := by
  unfold tailWord_1819505
  simp only [CollatzResearch.WordTrace]
  refine ⟨66362799273251606559299969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44241866182167737706199979 66362799273251606559299969)
  ·
    refine ⟨49772099454938704919474977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66362799273251606559299969 49772099454938704919474977)
    ·
      refine ⟨37329074591204028689606233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49772099454938704919474977 37329074591204028689606233)
      ·
        refine ⟨27996805943403021517204675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37329074591204028689606233 27996805943403021517204675)
        ·
          refine ⟨41995208915104532275807013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27996805943403021517204675 41995208915104532275807013)
          ·
            refine ⟨7874101671582099801713815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41995208915104532275807013 7874101671582099801713815)
            ·
              refine ⟨11811152507373149702570723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7874101671582099801713815 11811152507373149702570723)
              ·
                refine ⟨17716728761059724553856085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11811152507373149702570723 17716728761059724553856085)
                ·
                  refine ⟨207617915168668647115501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17716728761059724553856085 207617915168668647115501)
                  ·
                    rfl

theorem cell22_1819505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 1, 8].length) (baseStart_1819505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1819505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1819505 prefixEnd_1819505 := by exact prefixLift 1819505
  have htrace : WordTrace (prefixWord ++ tailWord_1819505) baseStart_1819505 baseEnd_1819505 := by
    simpa [prefixWord, tailWord_1819505, baseEnd_1819505] using wordTrace_append hprefix tailTrace_1819505
  have hstable : (prefixWord ++ tailWord_1819505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1819505).length < 2 ^ (prefixWord ++ tailWord_1819505).sum := by decide
  have hdescent : baseEnd_1819505 < baseStart_1819505 := by decide
  rcases family_descends (prefixWord ++ tailWord_1819505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1819520 : List Nat := [2, 1, 1, 2, 1, 2, 2, 3, 3, 5]
def baseStart_1819520 : Nat := 118140960795 + 1819520 * 2 ^ 59
def prefixEnd_1819520 : Nat := 4983230072969 + 3 ^ 40 * 1819520 * 2
def baseEnd_1819520 : Nat := 622858880312550902221457

theorem tailTrace_1819520 : CollatzResearch.WordTrace tailWord_1819520 prefixEnd_1819520 622858880312550902221457 := by
  unfold tailWord_1819520
  simp only [CollatzResearch.WordTrace]
  refine ⟨33181673184098632060548007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44242230912131509414064009 33181673184098632060548007)
  ·
    refine ⟨49772509776147948090822011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33181673184098632060548007 49772509776147948090822011)
    ·
      refine ⟨74658764664221922136233017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49772509776147948090822011 74658764664221922136233017)
      ·
        refine ⟨55994073498166441602174763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74658764664221922136233017 55994073498166441602174763)
        ·
          refine ⟨83991110247249662403262145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55994073498166441602174763 83991110247249662403262145)
          ·
            refine ⟨62993332685437246802446609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83991110247249662403262145 62993332685437246802446609)
            ·
              refine ⟨47244999514077935101834957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62993332685437246802446609 47244999514077935101834957)
              ·
                refine ⟨17716874817779225663188109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47244999514077935101834957 17716874817779225663188109)
                ·
                  refine ⟨6643828056667209623695541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17716874817779225663188109 6643828056667209623695541)
                  ·
                    refine ⟨622858880312550902221457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6643828056667209623695541 622858880312550902221457)
                    ·
                      rfl

theorem cell22_1819520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 3, 3, 5].length) (baseStart_1819520 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1819520 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1819520 prefixEnd_1819520 := by exact prefixLift 1819520
  have htrace : WordTrace (prefixWord ++ tailWord_1819520) baseStart_1819520 baseEnd_1819520 := by
    simpa [prefixWord, tailWord_1819520, baseEnd_1819520] using wordTrace_append hprefix tailTrace_1819520
  have hstable : (prefixWord ++ tailWord_1819520).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1819520).length < 2 ^ (prefixWord ++ tailWord_1819520).sum := by decide
  have hdescent : baseEnd_1819520 < baseStart_1819520 := by decide
  rcases family_descends (prefixWord ++ tailWord_1819520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1819554 : List Nat := [3, 3, 1, 2, 2, 1, 3, 1, 1, 5]
def baseStart_1819554 : Nat := 118140960795 + 1819554 * 2 ^ 59
def prefixEnd_1819554 : Nat := 4983230072969 + 3 ^ 40 * 1819554 * 2
def baseEnd_1819554 : Nat := 622870519207386146871353

theorem tailTrace_1819554 : CollatzResearch.WordTrace tailWord_1819554 prefixEnd_1819554 622870519207386146871353 := by
  unfold tailWord_1819554
  simp only [CollatzResearch.WordTrace]
  refine ⟨16591146612518521981958429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44243057633382725285222477 16591146612518521981958429)
  ·
    refine ⟨6221679979694445743234411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16591146612518521981958429 6221679979694445743234411)
    ·
      refine ⟨9332519969541668614851617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6221679979694445743234411 9332519969541668614851617)
      ·
        refine ⟨6999389977156251461138713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9332519969541668614851617 6999389977156251461138713)
        ·
          refine ⟨5249542482867188595854035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6999389977156251461138713 5249542482867188595854035)
          ·
            refine ⟨7874313724300782893781053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5249542482867188595854035 7874313724300782893781053)
            ·
              refine ⟨2952867646612793585167895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7874313724300782893781053 2952867646612793585167895)
              ·
                refine ⟨4429301469919190377751843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2952867646612793585167895 4429301469919190377751843)
                ·
                  refine ⟨6643952204878785566627765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4429301469919190377751843 6643952204878785566627765)
                  ·
                    refine ⟨622870519207386146871353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6643952204878785566627765 622870519207386146871353)
                    ·
                      rfl

theorem cell22_1819554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 3, 1, 1, 5].length) (baseStart_1819554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1819554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1819554 prefixEnd_1819554 := by exact prefixLift 1819554
  have htrace : WordTrace (prefixWord ++ tailWord_1819554) baseStart_1819554 baseEnd_1819554 := by
    simpa [prefixWord, tailWord_1819554, baseEnd_1819554] using wordTrace_append hprefix tailTrace_1819554
  have hstable : (prefixWord ++ tailWord_1819554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1819554).length < 2 ^ (prefixWord ++ tailWord_1819554).sum := by decide
  have hdescent : baseEnd_1819554 < baseStart_1819554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1819554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1819599 : List Nat := [1, 1, 2, 1, 1, 6, 3, 1, 3, 3]
def baseStart_1819599 : Nat := 118140960795 + 1819599 * 2 ^ 59
def prefixEnd_1819599 : Nat := 4983230072969 + 3 ^ 40 * 1819599 * 2
def baseEnd_1819599 : Nat := 622885923627021029496215

theorem tailTrace_1819599 : CollatzResearch.WordTrace tailWord_1819599 prefixEnd_1819599 622885923627021029496215 := by
  unfold tailWord_1819599
  simp only [CollatzResearch.WordTrace]
  refine ⟨66366227734911060613221851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44244151823274040408814567 66366227734911060613221851)
  ·
    refine ⟨99549341602366590919832777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66366227734911060613221851 99549341602366590919832777)
    ·
      refine ⟨74662006201774943189874583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99549341602366590919832777 74662006201774943189874583)
      ·
        refine ⟨111993009302662414784811875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74662006201774943189874583 111993009302662414784811875)
        ·
          refine ⟨167989513953993622177217813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111993009302662414784811875 167989513953993622177217813)
          ·
            refine ⟨7874508466593451039557085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 167989513953993622177217813 7874508466593451039557085)
            ·
              refine ⟨2952940674972544139833907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7874508466593451039557085 2952940674972544139833907)
              ·
                refine ⟨4429411012458816209750861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2952940674972544139833907 4429411012458816209750861)
                ·
                  refine ⟨1661029129672056078656573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4429411012458816209750861 1661029129672056078656573)
                  ·
                    refine ⟨622885923627021029496215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1661029129672056078656573 622885923627021029496215)
                    ·
                      rfl

theorem cell22_1819599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 3, 1, 3, 3].length) (baseStart_1819599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1819599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1819599 prefixEnd_1819599 := by exact prefixLift 1819599
  have htrace : WordTrace (prefixWord ++ tailWord_1819599) baseStart_1819599 baseEnd_1819599 := by
    simpa [prefixWord, tailWord_1819599, baseEnd_1819599] using wordTrace_append hprefix tailTrace_1819599
  have hstable : (prefixWord ++ tailWord_1819599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1819599).length < 2 ^ (prefixWord ++ tailWord_1819599).sum := by decide
  have hdescent : baseEnd_1819599 < baseStart_1819599 := by decide
  rcases family_descends (prefixWord ++ tailWord_1819599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1819605 : List Nat := [1, 3, 2, 3, 4, 1, 2, 1, 2, 3]
def baseStart_1819605 : Nat := 118140960795 + 1819605 * 2 ^ 59
def prefixEnd_1819605 : Nat := 4983230072969 + 3 ^ 40 * 1819605 * 2
def baseEnd_1819605 : Nat := 622887977549639013846197

theorem tailTrace_1819605 : CollatzResearch.WordTrace tailWord_1819605 prefixEnd_1819605 622887977549639013846197 := by
  unfold tailWord_1819605
  simp only [CollatzResearch.WordTrace]
  refine ⟨66366446572889323637940269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44244297715259549091960179 66366446572889323637940269)
  ·
    refine ⟨24887417464833496364227601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66366446572889323637940269 24887417464833496364227601)
    ·
      refine ⟨18665563098625122273170701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24887417464833496364227601 18665563098625122273170701)
      ·
        refine ⟨6999586161984420852439013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18665563098625122273170701 6999586161984420852439013)
        ·
          refine ⟨1312422405372078909832315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6999586161984420852439013 1312422405372078909832315)
          ·
            refine ⟨1968633608058118364748473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1312422405372078909832315 1968633608058118364748473)
            ·
              refine ⟨1476475206043588773561355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1968633608058118364748473 1476475206043588773561355)
              ·
                refine ⟨2214712809065383160342033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1476475206043588773561355 2214712809065383160342033)
                ·
                  refine ⟨1661034606799037370256525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2214712809065383160342033 1661034606799037370256525)
                  ·
                    refine ⟨622887977549639013846197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1661034606799037370256525 622887977549639013846197)
                    ·
                      rfl

theorem cell22_1819605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 2, 1, 2, 3].length) (baseStart_1819605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1819605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1819605 prefixEnd_1819605 := by exact prefixLift 1819605
  have htrace : WordTrace (prefixWord ++ tailWord_1819605) baseStart_1819605 baseEnd_1819605 := by
    simpa [prefixWord, tailWord_1819605, baseEnd_1819605] using wordTrace_append hprefix tailTrace_1819605
  have hstable : (prefixWord ++ tailWord_1819605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1819605).length < 2 ^ (prefixWord ++ tailWord_1819605).sum := by decide
  have hdescent : baseEnd_1819605 < baseStart_1819605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1819605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1819706 : List Nat := [3, 1, 1, 1, 3, 1, 5, 2, 2, 3]
def baseStart_1819706 : Nat := 118140960795 + 1819706 * 2 ^ 59
def prefixEnd_1819706 : Nat := 4983230072969 + 3 ^ 40 * 1819706 * 2
def baseEnd_1819706 : Nat := 622922551913708417070887

theorem tailTrace_1819706 : CollatzResearch.WordTrace tailWord_1819706 prefixEnd_1819706 622922551913708417070887 := by
  unfold tailWord_1819706
  simp only [CollatzResearch.WordTrace]
  refine ⟨16592532586380854471841743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44246753563682278591577981 16592532586380854471841743)
  ·
    refine ⟨24888798879571281707762615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16592532586380854471841743 24888798879571281707762615)
    ·
      refine ⟨37333198319356922561643923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24888798879571281707762615 37333198319356922561643923)
      ·
        refine ⟨55999797479035383842465885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37333198319356922561643923 55999797479035383842465885)
        ·
          refine ⟨20999924054638268940924707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55999797479035383842465885 20999924054638268940924707)
          ·
            refine ⟨31499886081957403411387061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20999924054638268940924707 31499886081957403411387061)
            ·
              refine ⟨2953114320183506569817537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31499886081957403411387061 2953114320183506569817537)
              ·
                refine ⟨2214835740137629927363153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2953114320183506569817537 2214835740137629927363153)
                ·
                  refine ⟨1661126805103222445522365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2214835740137629927363153 1661126805103222445522365)
                  ·
                    refine ⟨622922551913708417070887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1661126805103222445522365 622922551913708417070887)
                    ·
                      rfl

theorem cell22_1819706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 5, 2, 2, 3].length) (baseStart_1819706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1819706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1819706 prefixEnd_1819706 := by exact prefixLift 1819706
  have htrace : WordTrace (prefixWord ++ tailWord_1819706) baseStart_1819706 baseEnd_1819706 := by
    simpa [prefixWord, tailWord_1819706, baseEnd_1819706] using wordTrace_append hprefix tailTrace_1819706
  have hstable : (prefixWord ++ tailWord_1819706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1819706).length < 2 ^ (prefixWord ++ tailWord_1819706).sum := by decide
  have hdescent : baseEnd_1819706 < baseStart_1819706 := by decide
  rcases family_descends (prefixWord ++ tailWord_1819706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1819742 : List Nat := [4, 4, 1, 1, 1, 3, 1, 3, 4]
def baseStart_1819742 : Nat := 118140960795 + 1819742 * 2 ^ 59
def prefixEnd_1819742 : Nat := 4983230072969 + 3 ^ 40 * 1819742 * 2
def baseEnd_1819742 : Nat := 207644958483138774390259

theorem tailTrace_1819742 : CollatzResearch.WordTrace tailWord_1819742 prefixEnd_1819742 207644958483138774390259 := by
  unfold tailWord_1819742
  simp only [CollatzResearch.WordTrace]
  refine ⟨8296430421674124504459685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44247628915595330690451653 8296430421674124504459685)
  ·
    refine ⟨1555580704063898344586191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8296430421674124504459685 1555580704063898344586191)
    ·
      refine ⟨2333371056095847516879287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1555580704063898344586191 2333371056095847516879287)
      ·
        refine ⟨3500056584143771275318931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2333371056095847516879287 3500056584143771275318931)
        ·
          refine ⟨5250084876215656912978397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3500056584143771275318931 5250084876215656912978397)
          ·
            refine ⟨1968781828580871342366899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5250084876215656912978397 1968781828580871342366899)
            ·
              refine ⟨2953172742871307013550349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1968781828580871342366899 2953172742871307013550349)
              ·
                refine ⟨1107439778576740130081381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2953172742871307013550349 1107439778576740130081381)
                ·
                  refine ⟨207644958483138774390259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1107439778576740130081381 207644958483138774390259)
                  ·
                    rfl

theorem cell22_1819742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_1819742 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1819742 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1819742 prefixEnd_1819742 := by exact prefixLift 1819742
  have htrace : WordTrace (prefixWord ++ tailWord_1819742) baseStart_1819742 baseEnd_1819742 := by
    simpa [prefixWord, tailWord_1819742, baseEnd_1819742] using wordTrace_append hprefix tailTrace_1819742
  have hstable : (prefixWord ++ tailWord_1819742).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1819742).length < 2 ^ (prefixWord ++ tailWord_1819742).sum := by decide
  have hdescent : baseEnd_1819742 < baseStart_1819742 := by decide
  rcases family_descends (prefixWord ++ tailWord_1819742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1819781 : List Nat := [1, 3, 1, 1, 6, 1, 1, 3, 5]
def baseStart_1819781 : Nat := 118140960795 + 1819781 * 2 ^ 59
def prefixEnd_1819781 : Nat := 4983230072969 + 3 ^ 40 * 1819781 * 2
def baseEnd_1819781 : Nat := 207649408648811073815219

theorem tailTrace_1819781 : CollatzResearch.WordTrace tailWord_1819781 prefixEnd_1819781 207649408648811073815219 := by
  unfold tailWord_1819781
  simp only [CollatzResearch.WordTrace]
  refine ⟨66372865820251705696347197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44248577213501137130898131 66372865820251705696347197)
  ·
    refine ⟨24889824682594389636130199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66372865820251705696347197 24889824682594389636130199)
    ·
      refine ⟨37334737023891584454195299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24889824682594389636130199 37334737023891584454195299)
      ·
        refine ⟨56002105535837376681292949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37334737023891584454195299 56002105535837376681292949)
        ·
          refine ⟨2625098696992377031935607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 56002105535837376681292949 2625098696992377031935607)
          ·
            refine ⟨3937648045488565547903411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2625098696992377031935607 3937648045488565547903411)
            ·
              refine ⟨5906472068232848321855117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3937648045488565547903411 5906472068232848321855117)
              ·
                refine ⟨2214927025587318120695669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5906472068232848321855117 2214927025587318120695669)
                ·
                  refine ⟨207649408648811073815219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2214927025587318120695669 207649408648811073815219)
                  ·
                    rfl

theorem cell22_1819781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 3, 5].length) (baseStart_1819781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1819781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1819781 prefixEnd_1819781 := by exact prefixLift 1819781
  have htrace : WordTrace (prefixWord ++ tailWord_1819781) baseStart_1819781 baseEnd_1819781 := by
    simpa [prefixWord, tailWord_1819781, baseEnd_1819781] using wordTrace_append hprefix tailTrace_1819781
  have hstable : (prefixWord ++ tailWord_1819781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1819781).length < 2 ^ (prefixWord ++ tailWord_1819781).sum := by decide
  have hdescent : baseEnd_1819781 < baseStart_1819781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1819781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1819830 : List Nat := [5, 1, 3, 2, 1, 1, 1, 1, 2, 5]
def baseStart_1819830 : Nat := 118140960795 + 1819830 * 2 ^ 59
def prefixEnd_1819830 : Nat := 4983230072969 + 3 ^ 40 * 1819830 * 2
def baseEnd_1819830 : Nat := 622964999647813426970507

theorem tailTrace_1819830 : CollatzResearch.WordTrace tailWord_1819830 prefixEnd_1819830 622964999647813426970507 := by
  unfold tailWord_1819830
  simp only [CollatzResearch.WordTrace]
  refine ⟨4148415812317136691555059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44249768664716124709920629 4148415812317136691555059)
  ·
    refine ⟨6222623718475705037332589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4148415812317136691555059 6222623718475705037332589)
    ·
      refine ⟨2333483894428389388999721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6222623718475705037332589 2333483894428389388999721)
      ·
        refine ⟨1750112920821292041749791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2333483894428389388999721 1750112920821292041749791)
        ·
          refine ⟨2625169381231938062624687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1750112920821292041749791 2625169381231938062624687)
          ·
            refine ⟨3937754071847907093937031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2625169381231938062624687 3937754071847907093937031)
            ·
              refine ⟨5906631107771860640905547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3937754071847907093937031 5906631107771860640905547)
              ·
                refine ⟨8859946661657790961358321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5906631107771860640905547 8859946661657790961358321)
                ·
                  refine ⟨6644959996243343221018741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8859946661657790961358321 6644959996243343221018741)
                  ·
                    refine ⟨622964999647813426970507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6644959996243343221018741 622964999647813426970507)
                    ·
                      rfl

theorem cell22_1819830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_1819830 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1819830 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1819830 prefixEnd_1819830 := by exact prefixLift 1819830
  have htrace : WordTrace (prefixWord ++ tailWord_1819830) baseStart_1819830 baseEnd_1819830 := by
    simpa [prefixWord, tailWord_1819830, baseEnd_1819830] using wordTrace_append hprefix tailTrace_1819830
  have hstable : (prefixWord ++ tailWord_1819830).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1819830).length < 2 ^ (prefixWord ++ tailWord_1819830).sum := by decide
  have hdescent : baseEnd_1819830 < baseStart_1819830 := by decide
  rcases family_descends (prefixWord ++ tailWord_1819830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1819839 : List Nat := [1, 1, 2, 2, 2, 2, 2, 2, 4, 4]
def baseStart_1819839 : Nat := 118140960795 + 1819839 * 2 ^ 59
def prefixEnd_1819839 : Nat := 4983230072969 + 3 ^ 40 * 1819839 * 2
def baseEnd_1819839 : Nat := 622968080531740403495479

theorem tailTrace_1819839 : CollatzResearch.WordTrace tailWord_1819839 prefixEnd_1819839 622968080531740403495479 := by
  unfold tailWord_1819839
  simp only [CollatzResearch.WordTrace]
  refine ⟨66374981254041581601958571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44249987502694387734639047 66374981254041581601958571)
  ·
    refine ⟨99562471881062372402937857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66374981254041581601958571 99562471881062372402937857)
    ·
      refine ⟨74671853910796779302203393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99562471881062372402937857 74671853910796779302203393)
      ·
        refine ⟨56003890433097584476652545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74671853910796779302203393 56003890433097584476652545)
        ·
          refine ⟨42002917824823188357489409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56003890433097584476652545 42002917824823188357489409)
          ·
            refine ⟨31502188368617391268117057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42002917824823188357489409 31502188368617391268117057)
            ·
              refine ⟨23626641276463043451087793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31502188368617391268117057 23626641276463043451087793)
              ·
                refine ⟨17719980957347282588315845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23626641276463043451087793 17719980957347282588315845)
                ·
                  refine ⟨3322496429502615485309221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17719980957347282588315845 3322496429502615485309221)
                  ·
                    refine ⟨622968080531740403495479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3322496429502615485309221 622968080531740403495479)
                    ·
                      rfl

theorem cell22_1819839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 4, 4].length) (baseStart_1819839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1819839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1819839 prefixEnd_1819839 := by exact prefixLift 1819839
  have htrace : WordTrace (prefixWord ++ tailWord_1819839) baseStart_1819839 baseEnd_1819839 := by
    simpa [prefixWord, tailWord_1819839, baseEnd_1819839] using wordTrace_append hprefix tailTrace_1819839
  have hstable : (prefixWord ++ tailWord_1819839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1819839).length < 2 ^ (prefixWord ++ tailWord_1819839).sum := by decide
  have hdescent : baseEnd_1819839 < baseStart_1819839 := by decide
  rcases family_descends (prefixWord ++ tailWord_1819839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1819980 : List Nat := [2, 2, 1, 3, 2, 3, 3, 1, 1, 4]
def baseStart_1819980 : Nat := 118140960795 + 1819980 * 2 ^ 59
def prefixEnd_1819980 : Nat := 4983230072969 + 3 ^ 40 * 1819980 * 2
def baseEnd_1819980 : Nat := 623016347713263035720047

theorem tailTrace_1819980 : CollatzResearch.WordTrace tailWord_1819980 prefixEnd_1819980 623016347713263035720047 := by
  unfold tailWord_1819980
  simp only [CollatzResearch.WordTrace]
  refine ⟨33190061973265381341420697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44253415964353841788560929 33190061973265381341420697)
  ·
    refine ⟨24892546479949036006065523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33190061973265381341420697 24892546479949036006065523)
    ·
      refine ⟨37338819719923554009098285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24892546479949036006065523 37338819719923554009098285)
      ·
        refine ⟨14002057394971332753411857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37338819719923554009098285 14002057394971332753411857)
        ·
          refine ⟨10501543046228499565058893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14002057394971332753411857 10501543046228499565058893)
          ·
            refine ⟨3938078642335687336897085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10501543046228499565058893 3938078642335687336897085)
            ·
              refine ⟨1476779490875882751336407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3938078642335687336897085 1476779490875882751336407)
              ·
                refine ⟨2215169236313824127004611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1476779490875882751336407 2215169236313824127004611)
                ·
                  refine ⟨3322753854470736190506917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2215169236313824127004611 3322753854470736190506917)
                  ·
                    refine ⟨623016347713263035720047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3322753854470736190506917 623016347713263035720047)
                    ·
                      rfl

theorem cell22_1819980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 3, 1, 1, 4].length) (baseStart_1819980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1819980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1819980 prefixEnd_1819980 := by exact prefixLift 1819980
  have htrace : WordTrace (prefixWord ++ tailWord_1819980) baseStart_1819980 baseEnd_1819980 := by
    simpa [prefixWord, tailWord_1819980, baseEnd_1819980] using wordTrace_append hprefix tailTrace_1819980
  have hstable : (prefixWord ++ tailWord_1819980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1819980).length < 2 ^ (prefixWord ++ tailWord_1819980).sum := by decide
  have hdescent : baseEnd_1819980 < baseStart_1819980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1819980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1819993 : List Nat := [1, 2, 1, 2, 2, 2, 3, 4, 2, 3]
def baseStart_1819993 : Nat := 118140960795 + 1819993 * 2 ^ 59
def prefixEnd_1819993 : Nat := 4983230072969 + 3 ^ 40 * 1819993 * 2
def baseEnd_1819993 : Nat := 623020797878935335145007

theorem tailTrace_1819993 : CollatzResearch.WordTrace tailWord_1819993 prefixEnd_1819993 623020797878935335145007 := by
  unfold tailWord_1819993
  simp only [CollatzResearch.WordTrace]
  refine ⟨66380598095483665903064633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44253732063655777268709755 66380598095483665903064633)
  ·
    refine ⟨49785448571612749427298475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66380598095483665903064633 49785448571612749427298475)
    ·
      refine ⟨74678172857419124140947713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49785448571612749427298475 74678172857419124140947713)
      ·
        refine ⟨56008629643064343105710785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74678172857419124140947713 56008629643064343105710785)
        ·
          refine ⟨42006472232298257329283089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56008629643064343105710785 42006472232298257329283089)
          ·
            refine ⟨31504854174223692996962317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42006472232298257329283089 31504854174223692996962317)
            ·
              refine ⟨11814320315333884873860869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31504854174223692996962317 11814320315333884873860869)
              ·
                refine ⟨2215185059125103413848913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11814320315333884873860869 2215185059125103413848913)
                ·
                  refine ⟨1661388794343827560386685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2215185059125103413848913 1661388794343827560386685)
                  ·
                    refine ⟨623020797878935335145007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1661388794343827560386685 623020797878935335145007)
                    ·
                      rfl

theorem cell22_1819993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 4, 2, 3].length) (baseStart_1819993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1819993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1819993 prefixEnd_1819993 := by exact prefixLift 1819993
  have htrace : WordTrace (prefixWord ++ tailWord_1819993) baseStart_1819993 baseEnd_1819993 := by
    simpa [prefixWord, tailWord_1819993, baseEnd_1819993] using wordTrace_append hprefix tailTrace_1819993
  have hstable : (prefixWord ++ tailWord_1819993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1819993).length < 2 ^ (prefixWord ++ tailWord_1819993).sum := by decide
  have hdescent : baseEnd_1819993 < baseStart_1819993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1819993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1820010 : List Nat := [3, 1, 3, 3, 2, 1, 2, 1, 1, 5]
def baseStart_1820010 : Nat := 118140960795 + 1820010 * 2 ^ 59
def prefixEnd_1820010 : Nat := 4983230072969 + 3 ^ 40 * 1820010 * 2
def baseEnd_1820010 : Nat := 623026617326352957469955

theorem tailTrace_1820010 : CollatzResearch.WordTrace tailWord_1820010 prefixEnd_1820010 623026617326352957469955 := by
  unfold tailWord_1820010
  simp only [CollatzResearch.WordTrace]
  refine ⟨16595304534105519451608371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44254145424281385204288989 16595304534105519451608371)
  ·
    refine ⟨24892956801158279177412557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16595304534105519451608371 24892956801158279177412557)
    ·
      refine ⟨9334858800434354691529709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24892956801158279177412557 9334858800434354691529709)
      ·
        refine ⟨3500572050162883009323641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9334858800434354691529709 3500572050162883009323641)
        ·
          refine ⟨2625429037622162256992731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3500572050162883009323641 2625429037622162256992731)
          ·
            refine ⟨3938143556433243385489097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2625429037622162256992731 3938143556433243385489097)
            ·
              refine ⟨2953607667324932539116823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3938143556433243385489097 2953607667324932539116823)
              ·
                refine ⟨4430411500987398808675235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2953607667324932539116823 4430411500987398808675235)
                ·
                  refine ⟨6645617251481098213012853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4430411500987398808675235 6645617251481098213012853)
                  ·
                    refine ⟨623026617326352957469955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6645617251481098213012853 623026617326352957469955)
                    ·
                      rfl

theorem cell22_1820010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 2, 1, 1, 5].length) (baseStart_1820010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1820010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1820010 prefixEnd_1820010 := by exact prefixLift 1820010
  have htrace : WordTrace (prefixWord ++ tailWord_1820010) baseStart_1820010 baseEnd_1820010 := by
    simpa [prefixWord, tailWord_1820010, baseEnd_1820010] using wordTrace_append hprefix tailTrace_1820010
  have hstable : (prefixWord ++ tailWord_1820010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1820010).length < 2 ^ (prefixWord ++ tailWord_1820010).sum := by decide
  have hdescent : baseEnd_1820010 < baseStart_1820010 := by decide
  rcases family_descends (prefixWord ++ tailWord_1820010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1820089 : List Nat := [1, 2, 1, 4, 4, 2, 1, 3, 1, 3]
def baseStart_1820089 : Nat := 118140960795 + 1820089 * 2 ^ 59
def prefixEnd_1820089 : Nat := 4983230072969 + 3 ^ 40 * 1820089 * 2
def baseEnd_1820089 : Nat := 623053660640823084744713

theorem tailTrace_1820089 : CollatzResearch.WordTrace tailWord_1820089 prefixEnd_1820089 623053660640823084744713 := by
  unfold tailWord_1820089
  simp only [CollatzResearch.WordTrace]
  refine ⟨66384099503135874298559321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44256066335423916199039547 66384099503135874298559321)
  ·
    refine ⟨49788074627351905723919491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66384099503135874298559321 49788074627351905723919491)
    ·
      refine ⟨74682111941027858585879237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49788074627351905723919491 74682111941027858585879237)
      ·
        refine ⟨14002895988942723484852357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74682111941027858585879237 14002895988942723484852357)
        ·
          refine ⟨2625542997926760653409817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14002895988942723484852357 2625542997926760653409817)
          ·
            refine ⟨1969157248445070490057363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2625542997926760653409817 1969157248445070490057363)
            ·
              refine ⟨2953735872667605735086045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1969157248445070490057363 2953735872667605735086045)
              ·
                refine ⟨1107650952250352150657267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2953735872667605735086045 1107650952250352150657267)
                ·
                  refine ⟨1661476428375528225985901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1107650952250352150657267 1661476428375528225985901)
                  ·
                    refine ⟨623053660640823084744713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1661476428375528225985901 623053660640823084744713)
                    ·
                      rfl

theorem cell22_1820089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 1, 3, 1, 3].length) (baseStart_1820089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1820089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1820089 prefixEnd_1820089 := by exact prefixLift 1820089
  have htrace : WordTrace (prefixWord ++ tailWord_1820089) baseStart_1820089 baseEnd_1820089 := by
    simpa [prefixWord, tailWord_1820089, baseEnd_1820089] using wordTrace_append hprefix tailTrace_1820089
  have hstable : (prefixWord ++ tailWord_1820089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1820089).length < 2 ^ (prefixWord ++ tailWord_1820089).sum := by decide
  have hdescent : baseEnd_1820089 < baseStart_1820089 := by decide
  rcases family_descends (prefixWord ++ tailWord_1820089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1820096 : List Nat := [2, 1, 1, 2, 3, 1, 2, 2, 8]
def baseStart_1820096 : Nat := 118140960795 + 1820096 * 2 ^ 59
def prefixEnd_1820096 : Nat := 4983230072969 + 3 ^ 40 * 1820096 * 2
def baseEnd_1820096 : Nat := 207685352294625799939897

theorem tailTrace_1820096 : CollatzResearch.WordTrace tailWord_1820096 prefixEnd_1820096 207685352294625799939897 := by
  unfold tailWord_1820096
  simp only [CollatzResearch.WordTrace]
  refine ⟨33192177407055257247032071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44256236542740342996042761 33192177407055257247032071)
  ·
    refine ⟨49788266110582885870548107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33192177407055257247032071 49788266110582885870548107)
    ·
      refine ⟨74682399165874328805822161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49788266110582885870548107 74682399165874328805822161)
      ·
        refine ⟨56011799374405746604366621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74682399165874328805822161 56011799374405746604366621)
        ·
          refine ⟨21004424765402154976637483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56011799374405746604366621 21004424765402154976637483)
          ·
            refine ⟨31506637148103232464956225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21004424765402154976637483 31506637148103232464956225)
            ·
              refine ⟨23629977861077424348717169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31506637148103232464956225 23629977861077424348717169)
              ·
                refine ⟨17722483395808068261537877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23629977861077424348717169 17722483395808068261537877)
                ·
                  refine ⟨207685352294625799939897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17722483395808068261537877 207685352294625799939897)
                  ·
                    rfl

theorem cell22_1820096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 2, 8].length) (baseStart_1820096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1820096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1820096 prefixEnd_1820096 := by exact prefixLift 1820096
  have htrace : WordTrace (prefixWord ++ tailWord_1820096) baseStart_1820096 baseEnd_1820096 := by
    simpa [prefixWord, tailWord_1820096, baseEnd_1820096] using wordTrace_append hprefix tailTrace_1820096
  have hstable : (prefixWord ++ tailWord_1820096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1820096).length < 2 ^ (prefixWord ++ tailWord_1820096).sum := by decide
  have hdescent : baseEnd_1820096 < baseStart_1820096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1820096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1820128 : List Nat := [2, 1, 1, 3, 1, 1, 2, 2, 6, 3]
def baseStart_1820128 : Nat := 118140960795 + 1820128 * 2 ^ 59
def prefixEnd_1820128 : Nat := 4983230072969 + 3 ^ 40 * 1820128 * 2
def baseEnd_1820128 : Nat := 623067011137839983019593

theorem tailTrace_1820128 : CollatzResearch.WordTrace tailWord_1820128 prefixEnd_1820128 623067011137839983019593 := by
  unfold tailWord_1820128
  simp only [CollatzResearch.WordTrace]
  refine ⟨33192760974997291979614519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44257014633329722639486025 33192760974997291979614519)
  ·
    refine ⟨49789141462495937969421779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33192760974997291979614519 49789141462495937969421779)
    ·
      refine ⟨74683712193743906954132669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49789141462495937969421779 74683712193743906954132669)
      ·
        refine ⟨28006392072653965107799751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74683712193743906954132669 28006392072653965107799751)
        ·
          refine ⟨42009588108980947661699627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28006392072653965107799751 42009588108980947661699627)
          ·
            refine ⟨63014382163471421492549441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42009588108980947661699627 63014382163471421492549441)
            ·
              refine ⟨47260786622603566119412081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63014382163471421492549441 47260786622603566119412081)
              ·
                refine ⟨35445589966952674589559061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47260786622603566119412081 35445589966952674589559061)
                ·
                  refine ⟨1661512029700906621385581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 35445589966952674589559061 1661512029700906621385581)
                  ·
                    refine ⟨623067011137839983019593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1661512029700906621385581 623067011137839983019593)
                    ·
                      rfl

theorem cell22_1820128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 6, 3].length) (baseStart_1820128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1820128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1820128 prefixEnd_1820128 := by exact prefixLift 1820128
  have htrace : WordTrace (prefixWord ++ tailWord_1820128) baseStart_1820128 baseEnd_1820128 := by
    simpa [prefixWord, tailWord_1820128, baseEnd_1820128] using wordTrace_append hprefix tailTrace_1820128
  have hstable : (prefixWord ++ tailWord_1820128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1820128).length < 2 ^ (prefixWord ++ tailWord_1820128).sum := by decide
  have hdescent : baseEnd_1820128 < baseStart_1820128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1820128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1820143 : List Nat := [1, 1, 2, 1, 4, 1, 3, 3, 2, 4]
def baseStart_1820143 : Nat := 118140960795 + 1820143 * 2 ^ 59
def prefixEnd_1820143 : Nat := 4983230072969 + 3 ^ 40 * 1820143 * 2
def baseEnd_1820143 : Nat := 623072145944384943894547

theorem tailTrace_1820143 : CollatzResearch.WordTrace tailWord_1820143 prefixEnd_1820143 623072145944384943894547 := by
  unfold tailWord_1820143
  simp only [CollatzResearch.WordTrace]
  refine ⟨66386069044940241521025083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44257379363293494347350055 66386069044940241521025083)
  ·
    refine ⟨99579103567410362281537625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66386069044940241521025083 99579103567410362281537625)
    ·
      refine ⟨74684327675557771711153219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99579103567410362281537625 74684327675557771711153219)
      ·
        refine ⟨112026491513336657566729829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74684327675557771711153219 112026491513336657566729829)
        ·
          refine ⟨21004967158750623293761843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112026491513336657566729829 21004967158750623293761843)
          ·
            refine ⟨31507450738125934940642765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21004967158750623293761843 31507450738125934940642765)
            ·
              refine ⟨11815294026797225602741037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31507450738125934940642765 11815294026797225602741037)
              ·
                refine ⟨4430735260048959601027889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11815294026797225602741037 4430735260048959601027889)
                ·
                  refine ⟨3323051445036719700770917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4430735260048959601027889 3323051445036719700770917)
                  ·
                    refine ⟨623072145944384943894547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3323051445036719700770917 623072145944384943894547)
                    ·
                      rfl

theorem cell22_1820143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 3, 2, 4].length) (baseStart_1820143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1820143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1820143 prefixEnd_1820143 := by exact prefixLift 1820143
  have htrace : WordTrace (prefixWord ++ tailWord_1820143) baseStart_1820143 baseEnd_1820143 := by
    simpa [prefixWord, tailWord_1820143, baseEnd_1820143] using wordTrace_append hprefix tailTrace_1820143
  have hstable : (prefixWord ++ tailWord_1820143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1820143).length < 2 ^ (prefixWord ++ tailWord_1820143).sum := by decide
  have hdescent : baseEnd_1820143 < baseStart_1820143 := by decide
  rcases family_descends (prefixWord ++ tailWord_1820143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1820149 : List Nat := [1, 3, 5, 1, 1, 2, 3, 1, 1, 4]
def baseStart_1820149 : Nat := 118140960795 + 1820149 * 2 ^ 59
def prefixEnd_1820149 : Nat := 4983230072969 + 3 ^ 40 * 1820149 * 2
def baseEnd_1820149 : Nat := 623074199867002928244529

theorem tailTrace_1820149 : CollatzResearch.WordTrace tailWord_1820149 prefixEnd_1820149 623074199867002928244529 := by
  unfold tailWord_1820149
  simp only [CollatzResearch.WordTrace]
  refine ⟨66386287882918504545743501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44257525255279003030495667 66386287882918504545743501)
  ·
    refine ⟨24894857956094439204653813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66386287882918504545743501 24894857956094439204653813)
    ·
      refine ⟨2333892933383853675436295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24894857956094439204653813 2333892933383853675436295)
      ·
        refine ⟨3500839400075780513154443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2333892933383853675436295 3500839400075780513154443)
        ·
          refine ⟨5251259100113670769731665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3500839400075780513154443 5251259100113670769731665)
          ·
            refine ⟨3938444325085253077298749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5251259100113670769731665 3938444325085253077298749)
            ·
              refine ⟨1476916621906969903987031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3938444325085253077298749 1476916621906969903987031)
              ·
                refine ⟨2215374932860454855980547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1476916621906969903987031 2215374932860454855980547)
                ·
                  refine ⟨3323062399290682283970821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2215374932860454855980547 3323062399290682283970821)
                  ·
                    refine ⟨623074199867002928244529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3323062399290682283970821 623074199867002928244529)
                    ·
                      rfl

theorem cell22_1820149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_1820149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1820149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1820149 prefixEnd_1820149 := by exact prefixLift 1820149
  have htrace : WordTrace (prefixWord ++ tailWord_1820149) baseStart_1820149 baseEnd_1820149 := by
    simpa [prefixWord, tailWord_1820149, baseEnd_1820149] using wordTrace_append hprefix tailTrace_1820149
  have hstable : (prefixWord ++ tailWord_1820149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1820149).length < 2 ^ (prefixWord ++ tailWord_1820149).sum := by decide
  have hdescent : baseEnd_1820149 < baseStart_1820149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1820149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1820188 : List Nat := [2, 2, 3, 1, 2, 1, 1, 2, 2, 6]
def baseStart_1820188 : Nat := 118140960795 + 1820188 * 2 ^ 59
def prefixEnd_1820188 : Nat := 4983230072969 + 3 ^ 40 * 1820188 * 2
def baseEnd_1820188 : Nat := 623087550364019826519409

theorem tailTrace_1820188 : CollatzResearch.WordTrace tailWord_1820188 prefixEnd_1820188 623087550364019826519409 := by
  unfold tailWord_1820188
  simp only [CollatzResearch.WordTrace]
  refine ⟨33193855164888607103206609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44258473553184809470942145 33193855164888607103206609)
  ·
    refine ⟨24895391373666455327404957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33193855164888607103206609 24895391373666455327404957)
    ·
      refine ⟨9335771765124920747776859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24895391373666455327404957 9335771765124920747776859)
      ·
        refine ⟨14003657647687381121665289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9335771765124920747776859 14003657647687381121665289)
        ·
          refine ⟨10502743235765535841248967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14003657647687381121665289 10502743235765535841248967)
          ·
            refine ⟨15754114853648303761873451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10502743235765535841248967 15754114853648303761873451)
            ·
              refine ⟨23631172280472455642810177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15754114853648303761873451 23631172280472455642810177)
              ·
                refine ⟨17723379210354341732107633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23631172280472455642810177 17723379210354341732107633)
                ·
                  refine ⟨13292534407765756299080725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17723379210354341732107633 13292534407765756299080725)
                  ·
                    refine ⟨623087550364019826519409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13292534407765756299080725 623087550364019826519409)
                    ·
                      rfl

theorem cell22_1820188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 2, 2, 6].length) (baseStart_1820188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1820188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1820188 prefixEnd_1820188 := by exact prefixLift 1820188
  have htrace : WordTrace (prefixWord ++ tailWord_1820188) baseStart_1820188 baseEnd_1820188 := by
    simpa [prefixWord, tailWord_1820188, baseEnd_1820188] using wordTrace_append hprefix tailTrace_1820188
  have hstable : (prefixWord ++ tailWord_1820188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1820188).length < 2 ^ (prefixWord ++ tailWord_1820188).sum := by decide
  have hdescent : baseEnd_1820188 < baseStart_1820188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1820188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1820218 : List Nat := [3, 1, 1, 1, 3, 2, 1, 1, 4, 5]
def baseStart_1820218 : Nat := 118140960795 + 1820218 * 2 ^ 59
def prefixEnd_1820218 : Nat := 4983230072969 + 3 ^ 40 * 1820218 * 2
def baseEnd_1820218 : Nat := 623097819977109748269317

theorem tailTrace_1820218 : CollatzResearch.WordTrace tailWord_1820218 prefixEnd_1820218 623097819977109748269317 := by
  unfold tailWord_1820218
  simp only [CollatzResearch.WordTrace]
  refine ⟨16597201129917132332501327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44259203013112352886670205 16597201129917132332501327)
  ·
    refine ⟨24895801694875698498751991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16597201129917132332501327 24895801694875698498751991)
    ·
      refine ⟨37343702542313547748127987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24895801694875698498751991 37343702542313547748127987)
      ·
        refine ⟨56015553813470321622191981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37343702542313547748127987 56015553813470321622191981)
        ·
          refine ⟨21005832680051370608321993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56015553813470321622191981 21005832680051370608321993)
          ·
            refine ⟨15754374510038527956241495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21005832680051370608321993 15754374510038527956241495)
            ·
              refine ⟨23631561765057791934362243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15754374510038527956241495 23631561765057791934362243)
              ·
                refine ⟨35447342647586687901543365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23631561765057791934362243 35447342647586687901543365)
                ·
                  refine ⟨6646376746422503981539381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35447342647586687901543365 6646376746422503981539381)
                  ·
                    refine ⟨623097819977109748269317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6646376746422503981539381 623097819977109748269317)
                    ·
                      rfl

theorem cell22_1820218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 4, 5].length) (baseStart_1820218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1820218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1820218 prefixEnd_1820218 := by exact prefixLift 1820218
  have htrace : WordTrace (prefixWord ++ tailWord_1820218) baseStart_1820218 baseEnd_1820218 := by
    simpa [prefixWord, tailWord_1820218, baseEnd_1820218] using wordTrace_append hprefix tailTrace_1820218
  have hstable : (prefixWord ++ tailWord_1820218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1820218).length < 2 ^ (prefixWord ++ tailWord_1820218).sum := by decide
  have hdescent : baseEnd_1820218 < baseStart_1820218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1820218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1820220 : List Nat := [2, 2, 2, 2, 4, 1, 1, 1, 7]
def baseStart_1820220 : Nat := 118140960795 + 1820220 * 2 ^ 59
def prefixEnd_1820220 : Nat := 4983230072969 + 3 ^ 40 * 1820220 * 2
def baseEnd_1820220 : Nat := 207699501539327469906437

theorem tailTrace_1820220 : CollatzResearch.WordTrace tailWord_1820220 prefixEnd_1820220 207699501539327469906437 := by
  unfold tailWord_1820220
  simp only [CollatzResearch.WordTrace]
  refine ⟨33194438732830641835789057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44259251643774189114385409 33194438732830641835789057)
  ·
    refine ⟨24895829049622981376841793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33194438732830641835789057 24895829049622981376841793)
    ·
      refine ⟨18671871787217236032631345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24895829049622981376841793 18671871787217236032631345)
      ·
        refine ⟨14003903840412927024473509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18671871787217236032631345 14003903840412927024473509)
        ·
          refine ⟨2625731970077423817088783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14003903840412927024473509 2625731970077423817088783)
          ·
            refine ⟨3938597955116135725633175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2625731970077423817088783 3938597955116135725633175)
            ·
              refine ⟨5907896932674203588449763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3938597955116135725633175 5907896932674203588449763)
              ·
                refine ⟨8861845399011305382674645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5907896932674203588449763 8861845399011305382674645)
                ·
                  refine ⟨207699501539327469906437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8861845399011305382674645 207699501539327469906437)
                  ·
                    rfl

theorem cell22_1820220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 1, 7].length) (baseStart_1820220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1820220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1820220 prefixEnd_1820220 := by exact prefixLift 1820220
  have htrace : WordTrace (prefixWord ++ tailWord_1820220) baseStart_1820220 baseEnd_1820220 := by
    simpa [prefixWord, tailWord_1820220, baseEnd_1820220] using wordTrace_append hprefix tailTrace_1820220
  have hstable : (prefixWord ++ tailWord_1820220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1820220).length < 2 ^ (prefixWord ++ tailWord_1820220).sum := by decide
  have hdescent : baseEnd_1820220 < baseStart_1820220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1820220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1820233 : List Nat := [1, 2, 1, 1, 2, 2, 1, 3, 5, 4]
def baseStart_1820233 : Nat := 118140960795 + 1820233 * 2 ^ 59
def prefixEnd_1820233 : Nat := 4983230072969 + 3 ^ 40 * 1820233 * 2
def baseEnd_1820233 : Nat := 623102954783654709144271

theorem tailTrace_1820233 : CollatzResearch.WordTrace tailWord_1820233 prefixEnd_1820233 623102954783654709144271 := by
  unfold tailWord_1820233
  simp only [CollatzResearch.WordTrace]
  refine ⟨66389351614614186891801353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44259567743076124594534235 66389351614614186891801353)
  ·
    refine ⟨49792013710960640168851015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66389351614614186891801353 49792013710960640168851015)
    ·
      refine ⟨74688020566440960253276523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49792013710960640168851015 74688020566440960253276523)
      ·
        refine ⟨112032030849661440379914785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74688020566440960253276523 112032030849661440379914785)
        ·
          refine ⟨84024023137246080284936089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112032030849661440379914785 84024023137246080284936089)
          ·
            refine ⟨63018017352934560213702067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84024023137246080284936089 63018017352934560213702067)
            ·
              refine ⟨94527026029401840320553101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63018017352934560213702067 94527026029401840320553101)
              ·
                refine ⟨35447634761025690120207413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94527026029401840320553101 35447634761025690120207413)
                ·
                  refine ⟨3323215758846158448769445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35447634761025690120207413 3323215758846158448769445)
                  ·
                    refine ⟨623102954783654709144271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3323215758846158448769445 623102954783654709144271)
                    ·
                      rfl

theorem cell22_1820233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 5, 4].length) (baseStart_1820233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1820233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1820233 prefixEnd_1820233 := by exact prefixLift 1820233
  have htrace : WordTrace (prefixWord ++ tailWord_1820233) baseStart_1820233 baseEnd_1820233 := by
    simpa [prefixWord, tailWord_1820233, baseEnd_1820233] using wordTrace_append hprefix tailTrace_1820233
  have hstable : (prefixWord ++ tailWord_1820233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1820233).length < 2 ^ (prefixWord ++ tailWord_1820233).sum := by decide
  have hdescent : baseEnd_1820233 < baseStart_1820233 := by decide
  rcases family_descends (prefixWord ++ tailWord_1820233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1820312 : List Nat := [2, 1, 2, 4, 1, 3, 2, 1, 2, 4]
def baseStart_1820312 : Nat := 118140960795 + 1820312 * 2 ^ 59
def prefixEnd_1820312 : Nat := 4983230072969 + 3 ^ 40 * 1820312 * 2
def baseEnd_1820312 : Nat := 623129998098124836419029

theorem tailTrace_1820312 : CollatzResearch.WordTrace tailWord_1820312 prefixEnd_1820312 623129998098124836419029 := by
  unfold tailWord_1820312
  simp only [CollatzResearch.WordTrace]
  refine ⟨33196116490663991691963595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44261488654218655589284793 33196116490663991691963595)
  ·
    refine ⟨49794174735995987537945393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33196116490663991691963595 49794174735995987537945393)
    ·
      refine ⟨37345631051996990653459045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49794174735995987537945393 37345631051996990653459045)
      ·
        refine ⟨7002305822249435747523571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37345631051996990653459045 7002305822249435747523571)
        ·
          refine ⟨10503458733374153621285357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7002305822249435747523571 10503458733374153621285357)
          ·
            refine ⟨3938797025015307607982009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10503458733374153621285357 3938797025015307607982009)
            ·
              refine ⟨2954097768761480705986507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3938797025015307607982009 2954097768761480705986507)
              ·
                refine ⟨4431146653142221058979761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2954097768761480705986507 4431146653142221058979761)
                ·
                  refine ⟨3323359989856665794234821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4431146653142221058979761 3323359989856665794234821)
                  ·
                    refine ⟨623129998098124836419029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3323359989856665794234821 623129998098124836419029)
                    ·
                      rfl

theorem cell22_1820312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 2, 1, 2, 4].length) (baseStart_1820312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1820312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1820312 prefixEnd_1820312 := by exact prefixLift 1820312
  have htrace : WordTrace (prefixWord ++ tailWord_1820312) baseStart_1820312 baseEnd_1820312 := by
    simpa [prefixWord, tailWord_1820312, baseEnd_1820312] using wordTrace_append hprefix tailTrace_1820312
  have hstable : (prefixWord ++ tailWord_1820312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1820312).length < 2 ^ (prefixWord ++ tailWord_1820312).sum := by decide
  have hdescent : baseEnd_1820312 < baseStart_1820312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1820312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1820447 : List Nat := [1, 1, 2, 4, 2, 1, 3, 2, 2, 4]
def baseStart_1820447 : Nat := 118140960795 + 1820447 * 2 ^ 59
def prefixEnd_1820447 : Nat := 4983230072969 + 3 ^ 40 * 1820447 * 2
def baseEnd_1820447 : Nat := 623176211357029484293615

theorem tailTrace_1820447 : CollatzResearch.WordTrace tailWord_1820447 prefixEnd_1820447 623176211357029484293615 := by
  unfold tailWord_1820447
  simp only [CollatzResearch.WordTrace]
  refine ⟨66397156835838901440091595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44264771223892600960061063 66397156835838901440091595)
  ·
    refine ⟨99595735253758352160137393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66397156835838901440091595 99595735253758352160137393)
    ·
      refine ⟨74696801440318764120103045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99595735253758352160137393 74696801440318764120103045)
      ·
        refine ⟨14005650270059768272519321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74696801440318764120103045 14005650270059768272519321)
        ·
          refine ⟨10504237702544826204389491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14005650270059768272519321 10504237702544826204389491)
          ·
            refine ⟨15756356553817239306584237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10504237702544826204389491 15756356553817239306584237)
            ·
              refine ⟨5908633707681464739969089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15756356553817239306584237 5908633707681464739969089)
              ·
                refine ⟨4431475280761098554976817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5908633707681464739969089 4431475280761098554976817)
                ·
                  refine ⟨3323606460570823916232613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4431475280761098554976817 3323606460570823916232613)
                  ·
                    refine ⟨623176211357029484293615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3323606460570823916232613 623176211357029484293615)
                    ·
                      rfl

theorem cell22_1820447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 2, 2, 4].length) (baseStart_1820447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1820447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1820447 prefixEnd_1820447 := by exact prefixLift 1820447
  have htrace : WordTrace (prefixWord ++ tailWord_1820447) baseStart_1820447 baseEnd_1820447 := by
    simpa [prefixWord, tailWord_1820447, baseEnd_1820447] using wordTrace_append hprefix tailTrace_1820447
  have hstable : (prefixWord ++ tailWord_1820447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1820447).length < 2 ^ (prefixWord ++ tailWord_1820447).sum := by decide
  have hdescent : baseEnd_1820447 < baseStart_1820447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1820447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1820466 : List Nat := [3, 2, 1, 1, 3, 2, 4, 1, 2, 3]
def baseStart_1820466 : Nat := 118140960795 + 1820466 * 2 ^ 59
def prefixEnd_1820466 : Nat := 4983230072969 + 3 ^ 40 * 1820466 * 2
def baseEnd_1820466 : Nat := 623182715445319768068557

theorem tailTrace_1820466 : CollatzResearch.WordTrace tailWord_1820466 prefixEnd_1820466 623182715445319768068557 := by
  unfold tailWord_1820466
  simp only [CollatzResearch.WordTrace]
  refine ⟨16599462455692516921258313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44265233215180045123355501 16599462455692516921258313)
  ·
    refine ⟨12449596841769387690943735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16599462455692516921258313 12449596841769387690943735)
    ·
      refine ⟨18674395262654081536415603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12449596841769387690943735 18674395262654081536415603)
      ·
        refine ⟨28011592893981122304623405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18674395262654081536415603 28011592893981122304623405)
        ·
          refine ⟨10504347335242920864233777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28011592893981122304623405 10504347335242920864233777)
          ·
            refine ⟨7878260501432190648175333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10504347335242920864233777 7878260501432190648175333)
            ·
              refine ⟨1477173844018535746532875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7878260501432190648175333 1477173844018535746532875)
              ·
                refine ⟨2215760766027803619799313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1477173844018535746532875 2215760766027803619799313)
                ·
                  refine ⟨1661820574520852714849485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2215760766027803619799313 1661820574520852714849485)
                  ·
                    refine ⟨623182715445319768068557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1661820574520852714849485 623182715445319768068557)
                    ·
                      rfl

theorem cell22_1820466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 4, 1, 2, 3].length) (baseStart_1820466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1820466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1820466 prefixEnd_1820466 := by exact prefixLift 1820466
  have htrace : WordTrace (prefixWord ++ tailWord_1820466) baseStart_1820466 baseEnd_1820466 := by
    simpa [prefixWord, tailWord_1820466, baseEnd_1820466] using wordTrace_append hprefix tailTrace_1820466
  have hstable : (prefixWord ++ tailWord_1820466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1820466).length < 2 ^ (prefixWord ++ tailWord_1820466).sum := by decide
  have hdescent : baseEnd_1820466 < baseStart_1820466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1820466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1820511 : List Nat := [1, 1, 2, 3, 1, 5, 1, 4, 1, 3]
def baseStart_1820511 : Nat := 118140960795 + 1820511 * 2 ^ 59
def prefixEnd_1820511 : Nat := 4983230072969 + 3 ^ 40 * 1820511 * 2
def baseEnd_1820511 : Nat := 623198119864954650693419

theorem tailTrace_1820511 : CollatzResearch.WordTrace tailWord_1820511 prefixEnd_1820511 623198119864954650693419 := by
  unfold tailWord_1820511
  simp only [CollatzResearch.WordTrace]
  refine ⟨66399491107607040370421387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44266327405071360246947591 66399491107607040370421387)
  ·
    refine ⟨99599236661410560555632081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66399491107607040370421387 99599236661410560555632081)
    ·
      refine ⟨74699427496057920416724061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99599236661410560555632081 74699427496057920416724061)
      ·
        refine ⟨28012285311021720156271523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74699427496057920416724061 28012285311021720156271523)
        ·
          refine ⟨42018427966532580234407285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28012285311021720156271523 42018427966532580234407285)
          ·
            refine ⟨3939227621862429396975683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42018427966532580234407285 3939227621862429396975683)
            ·
              refine ⟨5908841432793644095463525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3939227621862429396975683 5908841432793644095463525)
              ·
                refine ⟨1107907768648808267899411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5908841432793644095463525 1107907768648808267899411)
                ·
                  refine ⟨1661861652973212401849117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1107907768648808267899411 1661861652973212401849117)
                  ·
                    refine ⟨623198119864954650693419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1661861652973212401849117 623198119864954650693419)
                    ·
                      rfl

theorem cell22_1820511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 4, 1, 3].length) (baseStart_1820511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1820511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1820511 prefixEnd_1820511 := by exact prefixLift 1820511
  have htrace : WordTrace (prefixWord ++ tailWord_1820511) baseStart_1820511 baseEnd_1820511 := by
    simpa [prefixWord, tailWord_1820511, baseEnd_1820511] using wordTrace_append hprefix tailTrace_1820511
  have hstable : (prefixWord ++ tailWord_1820511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1820511).length < 2 ^ (prefixWord ++ tailWord_1820511).sum := by decide
  have hdescent : baseEnd_1820511 < baseStart_1820511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1820511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1820537 : List Nat := [1, 2, 1, 3, 2, 2, 1, 3, 3, 4]
def baseStart_1820537 : Nat := 118140960795 + 1820537 * 2 ^ 59
def prefixEnd_1820537 : Nat := 4983230072969 + 3 ^ 40 * 1820537 * 2
def baseEnd_1820537 : Nat := 623207020196299249543339

theorem tailTrace_1820537 : CollatzResearch.WordTrace tailWord_1820537 prefixEnd_1820537 623207020196299249543339 := by
  unfold tailWord_1820537
  simp only [CollatzResearch.WordTrace]
  refine ⟨66400439405512846810867865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44266959603675231207245243 66400439405512846810867865)
  ·
    refine ⟨49800329554134635108150899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66400439405512846810867865 49800329554134635108150899)
    ·
      refine ⟨74700494331201952662226349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49800329554134635108150899 74700494331201952662226349)
      ·
        refine ⟨28012685374200732248334881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74700494331201952662226349 28012685374200732248334881)
        ·
          refine ⟨21009514030650549186251161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28012685374200732248334881 21009514030650549186251161)
          ·
            refine ⟨15757135522987911889688371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21009514030650549186251161 15757135522987911889688371)
            ·
              refine ⟨23635703284481867834532557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15757135522987911889688371 23635703284481867834532557)
              ·
                refine ⟨8863388731680700437949709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23635703284481867834532557 8863388731680700437949709)
                ·
                  refine ⟨3323770774380262664231141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8863388731680700437949709 3323770774380262664231141)
                  ·
                    refine ⟨623207020196299249543339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3323770774380262664231141 623207020196299249543339)
                    ·
                      rfl

theorem cell22_1820537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 3, 3, 4].length) (baseStart_1820537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1820537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1820537 prefixEnd_1820537 := by exact prefixLift 1820537
  have htrace : WordTrace (prefixWord ++ tailWord_1820537) baseStart_1820537 baseEnd_1820537 := by
    simpa [prefixWord, tailWord_1820537, baseEnd_1820537] using wordTrace_append hprefix tailTrace_1820537
  have hstable : (prefixWord ++ tailWord_1820537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1820537).length < 2 ^ (prefixWord ++ tailWord_1820537).sum := by decide
  have hdescent : baseEnd_1820537 < baseStart_1820537 := by decide
  rcases family_descends (prefixWord ++ tailWord_1820537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1820545 : List Nat := [1, 2, 4, 4, 1, 1, 2, 3, 1, 3]
def baseStart_1820545 : Nat := 118140960795 + 1820545 * 2 ^ 59
def prefixEnd_1820545 : Nat := 4983230072969 + 3 ^ 40 * 1820545 * 2
def baseEnd_1820545 : Nat := 623209758759789895343315

theorem tailTrace_1820545 : CollatzResearch.WordTrace tailWord_1820545 prefixEnd_1820545 623209758759789895343315 := by
  unfold tailWord_1820545
  simp only [CollatzResearch.WordTrace]
  refine ⟨66400731189483864177159089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44267154126322576118106059 66400731189483864177159089)
  ·
    refine ⟨49800548392112898132869317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66400731189483864177159089 49800548392112898132869317)
    ·
      refine ⟨9337602823521168399912997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49800548392112898132869317 9337602823521168399912997)
      ·
        refine ⟨1750800529410219074983687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9337602823521168399912997 1750800529410219074983687)
        ·
          refine ⟨2626200794115328612475531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1750800529410219074983687 2626200794115328612475531)
          ·
            refine ⟨3939301191172992918713297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2626200794115328612475531 3939301191172992918713297)
            ·
              refine ⟨2954475893379744689034973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3939301191172992918713297 2954475893379744689034973)
              ·
                refine ⟨1107928460017404258388115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2954475893379744689034973 1107928460017404258388115)
                ·
                  refine ⟨1661892690026106387582173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1107928460017404258388115 1661892690026106387582173)
                  ·
                    refine ⟨623209758759789895343315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1661892690026106387582173 623209758759789895343315)
                    ·
                      rfl

theorem cell22_1820545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 2, 3, 1, 3].length) (baseStart_1820545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1820545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1820545 prefixEnd_1820545 := by exact prefixLift 1820545
  have htrace : WordTrace (prefixWord ++ tailWord_1820545) baseStart_1820545 baseEnd_1820545 := by
    simpa [prefixWord, tailWord_1820545, baseEnd_1820545] using wordTrace_append hprefix tailTrace_1820545
  have hstable : (prefixWord ++ tailWord_1820545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1820545).length < 2 ^ (prefixWord ++ tailWord_1820545).sum := by decide
  have hdescent : baseEnd_1820545 < baseStart_1820545 := by decide
  rcases family_descends (prefixWord ++ tailWord_1820545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1820558 : List Nat := [4, 1, 1, 5, 1, 2, 1, 2, 5]
def baseStart_1820558 : Nat := 118140960795 + 1820558 * 2 ^ 59
def prefixEnd_1820558 : Nat := 4983230072969 + 3 ^ 40 * 1820558 * 2
def baseEnd_1820558 : Nat := 207738069641820731589425

theorem tailTrace_1820558 : CollatzResearch.WordTrace tailWord_1820558 prefixEnd_1820558 207738069641820731589425 := by
  unfold tailWord_1820558
  simp only [CollatzResearch.WordTrace]
  refine ⟨8300150667304595924672791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44267470225624511598254885 8300150667304595924672791)
  ·
    refine ⟨12450226000956893887009187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8300150667304595924672791 12450226000956893887009187)
    ·
      refine ⟨18675339001435340830513781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12450226000956893887009187 18675339001435340830513781)
      ·
        refine ⟨1750813031384563202860667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18675339001435340830513781 1750813031384563202860667)
        ·
          refine ⟨2626219547076844804291001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1750813031384563202860667 2626219547076844804291001)
          ·
            refine ⟨1969664660307633603218251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2626219547076844804291001 1969664660307633603218251)
            ·
              refine ⟨2954496990461450404827377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1969664660307633603218251 2954496990461450404827377)
              ·
                refine ⟨2215872742846087803620533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2954496990461450404827377 2215872742846087803620533)
                ·
                  refine ⟨207738069641820731589425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2215872742846087803620533 207738069641820731589425)
                  ·
                    rfl

theorem cell22_1820558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 1, 2, 5].length) (baseStart_1820558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1820558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1820558 prefixEnd_1820558 := by exact prefixLift 1820558
  have htrace : WordTrace (prefixWord ++ tailWord_1820558) baseStart_1820558 baseEnd_1820558 := by
    simpa [prefixWord, tailWord_1820558, baseEnd_1820558] using wordTrace_append hprefix tailTrace_1820558
  have hstable : (prefixWord ++ tailWord_1820558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1820558).length < 2 ^ (prefixWord ++ tailWord_1820558).sum := by decide
  have hdescent : baseEnd_1820558 < baseStart_1820558 := by decide
  rcases family_descends (prefixWord ++ tailWord_1820558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1820569 : List Nat := [1, 2, 1, 2, 1, 3, 4, 4, 4]
def baseStart_1820569 : Nat := 118140960795 + 1820569 * 2 ^ 59
def prefixEnd_1820569 : Nat := 4983230072969 + 3 ^ 40 * 1820569 * 2
def baseEnd_1820569 : Nat := 207739324816753944247747

theorem tailTrace_1820569 : CollatzResearch.WordTrace tailWord_1820569 prefixEnd_1820569 207739324816753944247747 := by
  unfold tailWord_1820569
  simp only [CollatzResearch.WordTrace]
  refine ⟨66401606541396916276032761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44267737694264610850688507 66401606541396916276032761)
  ·
    refine ⟨49801204906047687207024571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66401606541396916276032761 49801204906047687207024571)
    ·
      refine ⟨74701807359071530810536857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49801204906047687207024571 74701807359071530810536857)
      ·
        refine ⟨56026355519303648107902643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74701807359071530810536857 56026355519303648107902643)
        ·
          refine ⟨84039533278955472161853965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56026355519303648107902643 84039533278955472161853965)
          ·
            refine ⟨31514824979608302060695237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84039533278955472161853965 31514824979608302060695237)
            ·
              refine ⟨5909029683676556636380357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31514824979608302060695237 5909029683676556636380357)
              ·
                refine ⟨1107943065689354369321317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5909029683676556636380357 1107943065689354369321317)
                ·
                  refine ⟨207739324816753944247747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1107943065689354369321317 207739324816753944247747)
                  ·
                    rfl

theorem cell22_1820569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 4, 4].length) (baseStart_1820569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1820569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1820569 prefixEnd_1820569 := by exact prefixLift 1820569
  have htrace : WordTrace (prefixWord ++ tailWord_1820569) baseStart_1820569 baseEnd_1820569 := by
    simpa [prefixWord, tailWord_1820569, baseEnd_1820569] using wordTrace_append hprefix tailTrace_1820569
  have hstable : (prefixWord ++ tailWord_1820569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1820569).length < 2 ^ (prefixWord ++ tailWord_1820569).sum := by decide
  have hdescent : baseEnd_1820569 < baseStart_1820569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1820569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1820706 : List Nat := [3, 3, 1, 1, 1, 2, 2, 4, 1, 4]
def baseStart_1820706 : Nat := 118140960795 + 1820706 * 2 ^ 59
def prefixEnd_1820706 : Nat := 4983230072969 + 3 ^ 40 * 1820706 * 2
def baseEnd_1820706 : Nat := 623264872350039142067821

theorem tailTrace_1820706 : CollatzResearch.WordTrace tailWord_1820706 prefixEnd_1820706 623264872350039142067821 := by
  unfold tailWord_1820706
  simp only [CollatzResearch.WordTrace]
  refine ⟨16601650835475147168442493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44271068894600392449179981 16601650835475147168442493)
  ·
    refine ⟨6225619063303180188165935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16601650835475147168442493 6225619063303180188165935)
    ·
      refine ⟨9338428594954770282248903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6225619063303180188165935 9338428594954770282248903)
      ·
        refine ⟨14007642892432155423373355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9338428594954770282248903 14007642892432155423373355)
        ·
          refine ⟨21011464338648233135060033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14007642892432155423373355 21011464338648233135060033)
          ·
            refine ⟨15758598253986174851295025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21011464338648233135060033 15758598253986174851295025)
            ·
              refine ⟨11818948690489631138471269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15758598253986174851295025 11818948690489631138471269)
              ·
                refine ⟨2216052879466805838463363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11818948690489631138471269 2216052879466805838463363)
                ·
                  refine ⟨3324079319200208757695045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2216052879466805838463363 3324079319200208757695045)
                  ·
                    refine ⟨623264872350039142067821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3324079319200208757695045 623264872350039142067821)
                    ·
                      rfl

theorem cell22_1820706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 4, 1, 4].length) (baseStart_1820706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1820706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1820706 prefixEnd_1820706 := by exact prefixLift 1820706
  have htrace : WordTrace (prefixWord ++ tailWord_1820706) baseStart_1820706 baseEnd_1820706 := by
    simpa [prefixWord, tailWord_1820706, baseEnd_1820706] using wordTrace_append hprefix tailTrace_1820706
  have hstable : (prefixWord ++ tailWord_1820706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1820706).length < 2 ^ (prefixWord ++ tailWord_1820706).sum := by decide
  have hdescent : baseEnd_1820706 < baseStart_1820706 := by decide
  rcases family_descends (prefixWord ++ tailWord_1820706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1820721 : List Nat := [1, 2, 2, 3, 1, 3, 1, 5, 4]
def baseStart_1820721 : Nat := 118140960795 + 1820721 * 2 ^ 59
def prefixEnd_1820721 : Nat := 4983230072969 + 3 ^ 40 * 1820721 * 2
def baseEnd_1820721 : Nat := 207756669052194700980925

theorem tailTrace_1820721 : CollatzResearch.WordTrace tailWord_1820721 prefixEnd_1820721 207756669052194700980925 := by
  unfold tailWord_1820721
  simp only [CollatzResearch.WordTrace]
  refine ⟨66407150436846246235566017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44271433624564164157044011 66407150436846246235566017)
  ·
    refine ⟨49805362827634684676674513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66407150436846246235566017 49805362827634684676674513)
    ·
      refine ⟨37354022120726013507505885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49805362827634684676674513 37354022120726013507505885)
      ·
        refine ⟨14007758295272255065314707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37354022120726013507505885 14007758295272255065314707)
        ·
          refine ⟨21011637442908382597972061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14007758295272255065314707 21011637442908382597972061)
          ·
            refine ⟨7879364041090643474239523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21011637442908382597972061 7879364041090643474239523)
            ·
              refine ⟨11819046061635965211359285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7879364041090643474239523 11819046061635965211359285)
              ·
                refine ⟨1108035568278371738564933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11819046061635965211359285 1108035568278371738564933)
                ·
                  refine ⟨207756669052194700980925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1108035568278371738564933 207756669052194700980925)
                  ·
                    rfl

theorem cell22_1820721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 5, 4].length) (baseStart_1820721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1820721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1820721 prefixEnd_1820721 := by exact prefixLift 1820721
  have htrace : WordTrace (prefixWord ++ tailWord_1820721) baseStart_1820721 baseEnd_1820721 := by
    simpa [prefixWord, tailWord_1820721, baseEnd_1820721] using wordTrace_append hprefix tailTrace_1820721
  have hstable : (prefixWord ++ tailWord_1820721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1820721).length < 2 ^ (prefixWord ++ tailWord_1820721).sum := by decide
  have hdescent : baseEnd_1820721 < baseStart_1820721 := by decide
  rcases family_descends (prefixWord ++ tailWord_1820721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1820736 : List Nat := [2, 1, 1, 2, 2, 5, 1, 1, 4, 3]
def baseStart_1820736 : Nat := 118140960795 + 1820736 * 2 ^ 59
def prefixEnd_1820736 : Nat := 4983230072969 + 3 ^ 40 * 1820736 * 2
def baseEnd_1820736 : Nat := 623275141963129063817729

theorem tailTrace_1820736 : CollatzResearch.WordTrace tailWord_1820736 prefixEnd_1820736 623275141963129063817729 := by
  unfold tailWord_1820736
  simp only [CollatzResearch.WordTrace]
  refine ⟨33203848765895951898681031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44271798354527935864908041 33203848765895951898681031)
  ·
    refine ⟨49805773148843927848021547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33203848765895951898681031 49805773148843927848021547)
    ·
      refine ⟨74708659723265891772032321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49805773148843927848021547 74708659723265891772032321)
      ·
        refine ⟨56031494792449418829024241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74708659723265891772032321 56031494792449418829024241)
        ·
          refine ⟨42023621094337064121768181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56031494792449418829024241 42023621094337064121768181)
          ·
            refine ⟨3939714477594099761415767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42023621094337064121768181 3939714477594099761415767)
            ·
              refine ⟨5909571716391149642123651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3939714477594099761415767 5909571716391149642123651)
              ·
                refine ⟨8864357574586724463185477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5909571716391149642123651 8864357574586724463185477)
                ·
                  refine ⟨1662067045235010836847277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8864357574586724463185477 1662067045235010836847277)
                  ·
                    refine ⟨623275141963129063817729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1662067045235010836847277 623275141963129063817729)
                    ·
                      rfl

theorem cell22_1820736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 1, 4, 3].length) (baseStart_1820736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1820736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1820736 prefixEnd_1820736 := by exact prefixLift 1820736
  have htrace : WordTrace (prefixWord ++ tailWord_1820736) baseStart_1820736 baseEnd_1820736 := by
    simpa [prefixWord, tailWord_1820736, baseEnd_1820736] using wordTrace_append hprefix tailTrace_1820736
  have hstable : (prefixWord ++ tailWord_1820736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1820736).length < 2 ^ (prefixWord ++ tailWord_1820736).sum := by decide
  have hdescent : baseEnd_1820736 < baseStart_1820736 := by decide
  rcases family_descends (prefixWord ++ tailWord_1820736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1820809 : List Nat := [1, 2, 1, 1, 4, 2, 2, 1, 1, 7]
def baseStart_1820809 : Nat := 118140960795 + 1820809 * 2 ^ 59
def prefixEnd_1820809 : Nat := 4983230072969 + 3 ^ 40 * 1820809 * 2
def baseEnd_1820809 : Nat := 623300131354981206742505

theorem tailTrace_1820809 : CollatzResearch.WordTrace tailWord_1820809 prefixEnd_1820809 623300131354981206742505 := by
  unfold tailWord_1820809
  simp only [CollatzResearch.WordTrace]
  refine ⟨66410360060527437264769481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44273573373684958176512987 66410360060527437264769481)
  ·
    refine ⟨49807770045395577948577111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66410360060527437264769481 49807770045395577948577111)
    ·
      refine ⟨74711655068093366922865667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49807770045395577948577111 74711655068093366922865667)
      ·
        refine ⟨112067482602140050384298501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74711655068093366922865667 112067482602140050384298501)
        ·
          refine ⟨21012652987901259447055969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112067482602140050384298501 21012652987901259447055969)
          ·
            refine ⟨15759489740925944585291977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21012652987901259447055969 15759489740925944585291977)
            ·
              refine ⟨11819617305694458438968983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15759489740925944585291977 11819617305694458438968983)
              ·
                refine ⟨17729425958541687658453475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11819617305694458438968983 17729425958541687658453475)
                ·
                  refine ⟨26594138937812531487680213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17729425958541687658453475 26594138937812531487680213)
                  ·
                    refine ⟨623300131354981206742505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26594138937812531487680213 623300131354981206742505)
                    ·
                      rfl

theorem cell22_1820809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 1, 1, 7].length) (baseStart_1820809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1820809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1820809 prefixEnd_1820809 := by exact prefixLift 1820809
  have htrace : WordTrace (prefixWord ++ tailWord_1820809) baseStart_1820809 baseEnd_1820809 := by
    simpa [prefixWord, tailWord_1820809, baseEnd_1820809] using wordTrace_append hprefix tailTrace_1820809
  have hstable : (prefixWord ++ tailWord_1820809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1820809).length < 2 ^ (prefixWord ++ tailWord_1820809).sum := by decide
  have hdescent : baseEnd_1820809 < baseStart_1820809 := by decide
  rcases family_descends (prefixWord ++ tailWord_1820809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1820849 : List Nat := [1, 2, 2, 5, 2, 2, 2, 2, 1, 3]
def baseStart_1820849 : Nat := 118140960795 + 1820849 * 2 ^ 59
def prefixEnd_1820849 : Nat := 4983230072969 + 3 ^ 40 * 1820849 * 2
def baseEnd_1820849 : Nat := 623313824172434435742383

theorem tailTrace_1820849 : CollatzResearch.WordTrace tailWord_1820849 prefixEnd_1820849 623313824172434435742383 := by
  unfold tailWord_1820849
  simp only [CollatzResearch.WordTrace]
  refine ⟨66411818980382524096225601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44274545986921682730817067 66411818980382524096225601)
  ·
    refine ⟨49808864235286893072169201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66411818980382524096225601 49808864235286893072169201)
    ·
      refine ⟨37356648176465169804126901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49808864235286893072169201 37356648176465169804126901)
      ·
        refine ⟨3502185766543609669136897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37356648176465169804126901 3502185766543609669136897)
        ·
          refine ⟨2626639324907707251852673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3502185766543609669136897 2626639324907707251852673)
          ·
            refine ⟨1969979493680780438889505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2626639324907707251852673 1969979493680780438889505)
            ·
              refine ⟨1477484620260585329167129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1969979493680780438889505 1477484620260585329167129)
              ·
                refine ⟨1108113465195438996875347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1477484620260585329167129 1108113465195438996875347)
                ·
                  refine ⟨1662170197793158495313021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1108113465195438996875347 1662170197793158495313021)
                  ·
                    refine ⟨623313824172434435742383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1662170197793158495313021 623313824172434435742383)
                    ·
                      rfl

theorem cell22_1820849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 2, 2, 1, 3].length) (baseStart_1820849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1820849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1820849 prefixEnd_1820849 := by exact prefixLift 1820849
  have htrace : WordTrace (prefixWord ++ tailWord_1820849) baseStart_1820849 baseEnd_1820849 := by
    simpa [prefixWord, tailWord_1820849, baseEnd_1820849] using wordTrace_append hprefix tailTrace_1820849
  have hstable : (prefixWord ++ tailWord_1820849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1820849).length < 2 ^ (prefixWord ++ tailWord_1820849).sum := by decide
  have hdescent : baseEnd_1820849 < baseStart_1820849 := by decide
  rcases family_descends (prefixWord ++ tailWord_1820849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1820871 : List Nat := [1, 1, 4, 1, 1, 1, 1, 1, 8, 3]
def baseStart_1820871 : Nat := 118140960795 + 1820871 * 2 ^ 59
def prefixEnd_1820871 : Nat := 4983230072969 + 3 ^ 40 * 1820871 * 2
def baseEnd_1820871 : Nat := 623321355222033711692315

theorem tailTrace_1820871 : CollatzResearch.WordTrace tailWord_1820871 prefixEnd_1820871 623321355222033711692315 := by
  unfold tailWord_1820871
  simp only [CollatzResearch.WordTrace]
  refine ⟨66412621386302821853526467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44275080924201881235684311 66412621386302821853526467)
  ·
    refine ⟨99618932079454232780289701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66412621386302821853526467 99618932079454232780289701)
    ·
      refine ⟨18678549764897668646304319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99618932079454232780289701 18678549764897668646304319)
      ·
        refine ⟨28017824647346502969456479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18678549764897668646304319 28017824647346502969456479)
        ·
          refine ⟨42026736971019754454184719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28017824647346502969456479 42026736971019754454184719)
          ·
            refine ⟨63040105456529631681277079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42026736971019754454184719 63040105456529631681277079)
            ·
              refine ⟨94560158184794447521915619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63040105456529631681277079 94560158184794447521915619)
              ·
                refine ⟨141840237277191671282873429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94560158184794447521915619 141840237277191671282873429)
                ·
                  refine ⟨1662190280592089897846173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 141840237277191671282873429 1662190280592089897846173)
                  ·
                    refine ⟨623321355222033711692315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1662190280592089897846173 623321355222033711692315)
                    ·
                      rfl

theorem cell22_1820871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 8, 3].length) (baseStart_1820871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1820871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1820871 prefixEnd_1820871 := by exact prefixLift 1820871
  have htrace : WordTrace (prefixWord ++ tailWord_1820871) baseStart_1820871 baseEnd_1820871 := by
    simpa [prefixWord, tailWord_1820871, baseEnd_1820871] using wordTrace_append hprefix tailTrace_1820871
  have hstable : (prefixWord ++ tailWord_1820871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1820871).length < 2 ^ (prefixWord ++ tailWord_1820871).sum := by decide
  have hdescent : baseEnd_1820871 < baseStart_1820871 := by decide
  rcases family_descends (prefixWord ++ tailWord_1820871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1820892 : List Nat := [2, 2, 5, 2, 1, 1, 1, 3, 1, 4]
def baseStart_1820892 : Nat := 118140960795 + 1820892 * 2 ^ 59
def prefixEnd_1820892 : Nat := 4983230072969 + 3 ^ 40 * 1820892 * 2
def baseEnd_1820892 : Nat := 623328543951196656917251

theorem tailTrace_1820892 : CollatzResearch.WordTrace tailWord_1820892 prefixEnd_1820892 623328543951196656917251 := by
  unfold tailWord_1820892
  simp only [CollatzResearch.WordTrace]
  refine ⟨33206693659613371220020465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44275591546151161626693953 33206693659613371220020465)
  ·
    refine ⟨24905020244710028415015349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33206693659613371220020465 24905020244710028415015349)
    ·
      refine ⟨2334845647941565163907689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24905020244710028415015349 2334845647941565163907689)
      ·
        refine ⟨1751134235956173872930767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2334845647941565163907689 1751134235956173872930767)
        ·
          refine ⟨2626701353934260809396151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1751134235956173872930767 2626701353934260809396151)
          ·
            refine ⟨3940052030901391214094227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2626701353934260809396151 3940052030901391214094227)
            ·
              refine ⟨5910078046352086821141341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3940052030901391214094227 5910078046352086821141341)
              ·
                refine ⟨2216279267382032557928003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5910078046352086821141341 2216279267382032557928003)
                ·
                  refine ⟨3324418901073048836892005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2216279267382032557928003 3324418901073048836892005)
                  ·
                    refine ⟨623328543951196656917251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3324418901073048836892005 623328543951196656917251)
                    ·
                      rfl

theorem cell22_1820892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_1820892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1820892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1820892 prefixEnd_1820892 := by exact prefixLift 1820892
  have htrace : WordTrace (prefixWord ++ tailWord_1820892) baseStart_1820892 baseEnd_1820892 := by
    simpa [prefixWord, tailWord_1820892, baseEnd_1820892] using wordTrace_append hprefix tailTrace_1820892
  have hstable : (prefixWord ++ tailWord_1820892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1820892).length < 2 ^ (prefixWord ++ tailWord_1820892).sum := by decide
  have hdescent : baseEnd_1820892 < baseStart_1820892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1820892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1820901 : List Nat := [1, 3, 1, 4, 2, 2, 9]
def baseStart_1820901 : Nat := 118140960795 + 1820901 * 2 ^ 59
def prefixEnd_1820901 : Nat := 4983230072969 + 3 ^ 40 * 1820901 * 2
def baseEnd_1820901 : Nat := 23086356475374949386749

theorem tailTrace_1820901 : CollatzResearch.WordTrace tailWord_1820901 prefixEnd_1820901 23086356475374949386749 := by
  unfold tailWord_1820901
  simp only [CollatzResearch.WordTrace]
  refine ⟨66413715576194136977118557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44275810384129424651412371 66413715576194136977118557)
  ·
    refine ⟨24905143341072801366419459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66413715576194136977118557 24905143341072801366419459)
    ·
      refine ⟨37357715011609202049629189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24905143341072801366419459 37357715011609202049629189)
      ·
        refine ⟨7004571564676725384305473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37357715011609202049629189 7004571564676725384305473)
        ·
          refine ⟨5253428673507544038229105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7004571564676725384305473 5253428673507544038229105)
          ·
            refine ⟨3940071505130658028671829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5253428673507544038229105 3940071505130658028671829)
            ·
              refine ⟨23086356475374949386749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3940071505130658028671829 23086356475374949386749)
              ·
                rfl

theorem cell22_1820901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 9].length) (baseStart_1820901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1820901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1820901 prefixEnd_1820901 := by exact prefixLift 1820901
  have htrace : WordTrace (prefixWord ++ tailWord_1820901) baseStart_1820901 baseEnd_1820901 := by
    simpa [prefixWord, tailWord_1820901, baseEnd_1820901] using wordTrace_append hprefix tailTrace_1820901
  have hstable : (prefixWord ++ tailWord_1820901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1820901).length < 2 ^ (prefixWord ++ tailWord_1820901).sum := by decide
  have hdescent : baseEnd_1820901 < baseStart_1820901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1820901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1820961 : List Nat := [1, 2, 3, 2, 1, 1, 2, 1, 4, 5]
def baseStart_1820961 : Nat := 118140960795 + 1820961 * 2 ^ 59
def prefixEnd_1820961 : Nat := 4983230072969 + 3 ^ 40 * 1820961 * 2
def baseEnd_1820961 : Nat := 623352164061303476942039

theorem tailTrace_1820961 : CollatzResearch.WordTrace tailWord_1820961 prefixEnd_1820961 623352164061303476942039 := by
  unfold tailWord_1820961
  simp only [CollatzResearch.WordTrace]
  refine ⟨66415903955976767224302737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44277269303984511482868491 66415903955976767224302737)
  ·
    refine ⟨49811927966982575418227053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66415903955976767224302737 49811927966982575418227053)
    ·
      refine ⟨18679472987618465781835145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49811927966982575418227053 18679472987618465781835145)
      ·
        refine ⟨14009604740713849336376359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18679472987618465781835145 14009604740713849336376359)
        ·
          refine ⟨21014407111070774004564539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14009604740713849336376359 21014407111070774004564539)
          ·
            refine ⟨31521610666606161006846809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21014407111070774004564539 31521610666606161006846809)
            ·
              refine ⟨23641207999954620755135107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31521610666606161006846809 23641207999954620755135107)
              ·
                refine ⟨35461811999931931132702661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23641207999954620755135107 35461811999931931132702661)
                ·
                  refine ⟨6649089749987237087381749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35461811999931931132702661 6649089749987237087381749)
                  ·
                    refine ⟨623352164061303476942039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6649089749987237087381749 623352164061303476942039)
                    ·
                      rfl

theorem cell22_1820961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 4, 5].length) (baseStart_1820961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1820961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1820961 prefixEnd_1820961 := by exact prefixLift 1820961
  have htrace : WordTrace (prefixWord ++ tailWord_1820961) baseStart_1820961 baseEnd_1820961 := by
    simpa [prefixWord, tailWord_1820961, baseEnd_1820961] using wordTrace_append hprefix tailTrace_1820961
  have hstable : (prefixWord ++ tailWord_1820961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1820961).length < 2 ^ (prefixWord ++ tailWord_1820961).sum := by decide
  have hdescent : baseEnd_1820961 < baseStart_1820961 := by decide
  rcases family_descends (prefixWord ++ tailWord_1820961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1820980 : List Nat := [2, 5, 1, 1, 1, 3, 1, 3, 5]
def baseStart_1820980 : Nat := 118140960795 + 1820980 * 2 ^ 59
def prefixEnd_1820980 : Nat := 4983230072969 + 3 ^ 40 * 1820980 * 2
def baseEnd_1820980 : Nat := 207786222716531253572327

theorem tailTrace_1820980 : CollatzResearch.WordTrace tailWord_1820980 prefixEnd_1820980 207786222716531253572327 := by
  unfold tailWord_1820980
  simp only [CollatzResearch.WordTrace]
  refine ⟨33208298471453966734622197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44277731295271955646162929 33208298471453966734622197)
  ·
    refine ⟨3113277981698809381370831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33208298471453966734622197 3113277981698809381370831)
    ·
      refine ⟨4669916972548214072056247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3113277981698809381370831 4669916972548214072056247)
      ·
        refine ⟨7004875458822321108084371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4669916972548214072056247 7004875458822321108084371)
        ·
          refine ⟨10507313188233481662126557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7004875458822321108084371 10507313188233481662126557)
          ·
            refine ⟨3940242445587555623297459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10507313188233481662126557 3940242445587555623297459)
            ·
              refine ⟨5910363668381333434946189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3940242445587555623297459 5910363668381333434946189)
              ·
                refine ⟨2216386375643000038104821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5910363668381333434946189 2216386375643000038104821)
                ·
                  refine ⟨207786222716531253572327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2216386375643000038104821 207786222716531253572327)
                  ·
                    rfl

theorem cell22_1820980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 3, 5].length) (baseStart_1820980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1820980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1820980 prefixEnd_1820980 := by exact prefixLift 1820980
  have htrace : WordTrace (prefixWord ++ tailWord_1820980) baseStart_1820980 baseEnd_1820980 := by
    simpa [prefixWord, tailWord_1820980, baseEnd_1820980] using wordTrace_append hprefix tailTrace_1820980
  have hstable : (prefixWord ++ tailWord_1820980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1820980).length < 2 ^ (prefixWord ++ tailWord_1820980).sum := by decide
  have hdescent : baseEnd_1820980 < baseStart_1820980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1820980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1820991 : List Nat := [1, 1, 2, 2, 4, 1, 2, 1, 8]
def baseStart_1820991 : Nat := 118140960795 + 1820991 * 2 ^ 59
def prefixEnd_1820991 : Nat := 4983230072969 + 3 ^ 40 * 1820991 * 2
def baseEnd_1820991 : Nat := 207787477891464466230649

theorem tailTrace_1820991 : CollatzResearch.WordTrace tailWord_1820991 prefixEnd_1820991 207787477891464466230649 := by
  unfold tailWord_1820991
  simp only [CollatzResearch.WordTrace]
  refine ⟨66416998145868082347894827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44277998763912054898596551 66416998145868082347894827)
  ·
    refine ⟨99625497218802123521842241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66416998145868082347894827 99625497218802123521842241)
    ·
      refine ⟨74719122914101592641381681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99625497218802123521842241 74719122914101592641381681)
      ·
        refine ⟨56039342185576194481036261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74719122914101592641381681 56039342185576194481036261)
        ·
          refine ⟨10507376659795536465194299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56039342185576194481036261 10507376659795536465194299)
          ·
            refine ⟨15761064989693304697791449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10507376659795536465194299 15761064989693304697791449)
            ·
              refine ⟨11820798742269978523343587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15761064989693304697791449 11820798742269978523343587)
              ·
                refine ⟨17731198113404967785015381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11820798742269978523343587 17731198113404967785015381)
                ·
                  refine ⟨207787477891464466230649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17731198113404967785015381 207787477891464466230649)
                  ·
                    rfl

theorem cell22_1820991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 1, 8].length) (baseStart_1820991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1820991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1820991 prefixEnd_1820991 := by exact prefixLift 1820991
  have htrace : WordTrace (prefixWord ++ tailWord_1820991) baseStart_1820991 baseEnd_1820991 := by
    simpa [prefixWord, tailWord_1820991, baseEnd_1820991] using wordTrace_append hprefix tailTrace_1820991
  have hstable : (prefixWord ++ tailWord_1820991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1820991).length < 2 ^ (prefixWord ++ tailWord_1820991).sum := by decide
  have hdescent : baseEnd_1820991 < baseStart_1820991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1820991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1821023 : List Nat := [1, 1, 2, 3, 1, 2, 2, 3, 4, 3]
def baseStart_1821023 : Nat := 118140960795 + 1821023 * 2 ^ 59
def prefixEnd_1821023 : Nat := 4983230072969 + 3 ^ 40 * 1821023 * 2
def baseEnd_1821023 : Nat := 623373387928355981891849

theorem tailTrace_1821023 : CollatzResearch.WordTrace tailWord_1821023 prefixEnd_1821023 623373387928355981891849 := by
  unfold tailWord_1821023
  simp only [CollatzResearch.WordTrace]
  refine ⟨66418165281752151813059723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44278776854501434542039815 66418165281752151813059723)
  ·
    refine ⟨99627247922628227719589585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66418165281752151813059723 99627247922628227719589585)
    ·
      refine ⟨74720435941971170789692189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99627247922628227719589585 74720435941971170789692189)
      ·
        refine ⟨28020163478239189046134571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74720435941971170789692189 28020163478239189046134571)
        ·
          refine ⟨42030245217358783569201857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28020163478239189046134571 42030245217358783569201857)
          ·
            refine ⟨31522683913019087676901393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42030245217358783569201857 31522683913019087676901393)
            ·
              refine ⟨23642012934764315757676045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31522683913019087676901393 23642012934764315757676045)
              ·
                refine ⟨8865754850536618409128517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23642012934764315757676045 8865754850536618409128517)
                ·
                  refine ⟨1662329034475615951711597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8865754850536618409128517 1662329034475615951711597)
                  ·
                    refine ⟨623373387928355981891849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1662329034475615951711597 623373387928355981891849)
                    ·
                      rfl

theorem cell22_1821023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 3, 4, 3].length) (baseStart_1821023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1821023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1821023 prefixEnd_1821023 := by exact prefixLift 1821023
  have htrace : WordTrace (prefixWord ++ tailWord_1821023) baseStart_1821023 baseEnd_1821023 := by
    simpa [prefixWord, tailWord_1821023, baseEnd_1821023] using wordTrace_append hprefix tailTrace_1821023
  have hstable : (prefixWord ++ tailWord_1821023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1821023).length < 2 ^ (prefixWord ++ tailWord_1821023).sum := by decide
  have hdescent : baseEnd_1821023 < baseStart_1821023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1821023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1821040 : List Nat := [2, 1, 1, 1, 4, 3, 2, 3, 2, 3]
def baseStart_1821040 : Nat := 118140960795 + 1821040 * 2 ^ 59
def prefixEnd_1821040 : Nat := 4983230072969 + 3 ^ 40 * 1821040 * 2
def baseEnd_1821040 : Nat := 623379207375773604216797

theorem tailTrace_1821040 : CollatzResearch.WordTrace tailWord_1821040 prefixEnd_1821040 623379207375773604216797 := by
  unfold tailWord_1821040
  simp only [CollatzResearch.WordTrace]
  refine ⟨33209392661345281858214287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44279190215127042477619049 33209392661345281858214287)
  ·
    refine ⟨49814088992017922787321431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33209392661345281858214287 49814088992017922787321431)
    ·
      refine ⟨74721133488026884180982147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49814088992017922787321431 74721133488026884180982147)
      ·
        refine ⟨112081700232040326271473221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74721133488026884180982147 112081700232040326271473221)
        ·
          refine ⟨21015318793507561175901229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112081700232040326271473221 21015318793507561175901229)
          ·
            refine ⟨7880744547565335440962961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21015318793507561175901229 7880744547565335440962961)
            ·
              refine ⟨5910558410674001580722221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7880744547565335440962961 5910558410674001580722221)
              ·
                refine ⟨2216459404002750592770833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5910558410674001580722221 2216459404002750592770833)
                ·
                  refine ⟨1662344553002062944578125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2216459404002750592770833 1662344553002062944578125)
                  ·
                    refine ⟨623379207375773604216797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1662344553002062944578125 623379207375773604216797)
                    ·
                      rfl

theorem cell22_1821040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 3, 2, 3].length) (baseStart_1821040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1821040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1821040 prefixEnd_1821040 := by exact prefixLift 1821040
  have htrace : WordTrace (prefixWord ++ tailWord_1821040) baseStart_1821040 baseEnd_1821040 := by
    simpa [prefixWord, tailWord_1821040, baseEnd_1821040] using wordTrace_append hprefix tailTrace_1821040
  have hstable : (prefixWord ++ tailWord_1821040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1821040).length < 2 ^ (prefixWord ++ tailWord_1821040).sum := by decide
  have hdescent : baseEnd_1821040 < baseStart_1821040 := by decide
  rcases family_descends (prefixWord ++ tailWord_1821040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1821162 : List Nat := [3, 1, 3, 1, 3, 1, 3, 2, 1, 4]
def baseStart_1821162 : Nat := 118140960795 + 1821162 * 2 ^ 59
def prefixEnd_1821162 : Nat := 4983230072969 + 3 ^ 40 * 1821162 * 2
def baseEnd_1821162 : Nat := 623420970469005952666423

theorem tailTrace_1821162 : CollatzResearch.WordTrace tailWord_1821162 prefixEnd_1821162 623420970469005952666423 := by
  unfold tailWord_1821162
  simp only [CollatzResearch.WordTrace]
  refine ⟨16605808757062144638092435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44282156685499052368246493 16605808757062144638092435)
  ·
    refine ⟨24908713135593216957138653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16605808757062144638092435 24908713135593216957138653)
    ·
      refine ⟨9340767425847456358926995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24908713135593216957138653 9340767425847456358926995)
      ·
        refine ⟨14011151138771184538390493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9340767425847456358926995 14011151138771184538390493)
        ·
          refine ⟨5254181677039194201896435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14011151138771184538390493 5254181677039194201896435)
          ·
            refine ⟨7881272515558791302844653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5254181677039194201896435 7881272515558791302844653)
            ·
              refine ⟨2955477193334546738566745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7881272515558791302844653 2955477193334546738566745)
              ·
                refine ⟨2216607895000910053925059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2955477193334546738566745 2216607895000910053925059)
                ·
                  refine ⟨3324911842501365080887589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2216607895000910053925059 3324911842501365080887589)
                  ·
                    refine ⟨623420970469005952666423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3324911842501365080887589 623420970469005952666423)
                    ·
                      rfl

theorem cell22_1821162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 3, 2, 1, 4].length) (baseStart_1821162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1821162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1821162 prefixEnd_1821162 := by exact prefixLift 1821162
  have htrace : WordTrace (prefixWord ++ tailWord_1821162) baseStart_1821162 baseEnd_1821162 := by
    simpa [prefixWord, tailWord_1821162, baseEnd_1821162] using wordTrace_append hprefix tailTrace_1821162
  have hstable : (prefixWord ++ tailWord_1821162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1821162).length < 2 ^ (prefixWord ++ tailWord_1821162).sum := by decide
  have hdescent : baseEnd_1821162 < baseStart_1821162 := by decide
  rcases family_descends (prefixWord ++ tailWord_1821162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1821224 : List Nat := [2, 1, 5, 2, 1, 3, 1, 1, 2, 4]
def baseStart_1821224 : Nat := 118140960795 + 1821224 * 2 ^ 59
def prefixEnd_1821224 : Nat := 4983230072969 + 3 ^ 40 * 1821224 * 2
def baseEnd_1821224 : Nat := 623442194336058457616233

theorem tailTrace_1821224 : CollatzResearch.WordTrace tailWord_1821224 prefixEnd_1821224 623442194336058457616233 := by
  unfold tailWord_1821224
  simp only [CollatzResearch.WordTrace]
  refine ⟨33212748177011981570563363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44283664236015975427417817 33212748177011981570563363)
  ·
    refine ⟨49819122265517972355845045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33212748177011981570563363 49819122265517972355845045)
    ·
      refine ⟨4670542712392309908360473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 49819122265517972355845045 4670542712392309908360473)
      ·
        refine ⟨3502907034294232431270355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4670542712392309908360473 3502907034294232431270355)
        ·
          refine ⟨5254360551441348646905533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3502907034294232431270355 5254360551441348646905533)
          ·
            refine ⟨1970385206790505742589575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5254360551441348646905533 1970385206790505742589575)
            ·
              refine ⟨2955577810185758613884363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1970385206790505742589575 2955577810185758613884363)
              ·
                refine ⟨4433366715278637920826545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2955577810185758613884363 4433366715278637920826545)
                ·
                  refine ⟨3325025036458978440619909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4433366715278637920826545 3325025036458978440619909)
                  ·
                    refine ⟨623442194336058457616233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3325025036458978440619909 623442194336058457616233)
                    ·
                      rfl

theorem cell22_1821224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 1, 1, 2, 4].length) (baseStart_1821224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1821224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1821224 prefixEnd_1821224 := by exact prefixLift 1821224
  have htrace : WordTrace (prefixWord ++ tailWord_1821224) baseStart_1821224 baseEnd_1821224 := by
    simpa [prefixWord, tailWord_1821224, baseEnd_1821224] using wordTrace_append hprefix tailTrace_1821224
  have hstable : (prefixWord ++ tailWord_1821224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1821224).length < 2 ^ (prefixWord ++ tailWord_1821224).sum := by decide
  have hdescent : baseEnd_1821224 < baseStart_1821224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1821224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1821265 : List Nat := [1, 2, 2, 1, 3, 3, 2, 1, 2, 5]
def baseStart_1821265 : Nat := 118140960795 + 1821265 * 2 ^ 59
def prefixEnd_1821265 : Nat := 4983230072969 + 3 ^ 40 * 1821265 * 2
def baseEnd_1821265 : Nat := 623456229473948017341107

theorem tailTrace_1821265 : CollatzResearch.WordTrace tailWord_1821265 prefixEnd_1821265 623456229473948017341107 := by
  unfold tailWord_1821265
  simp only [CollatzResearch.WordTrace]
  refine ⟨66426991746875427143369249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44284661164583618095579499 66426991746875427143369249)
  ·
    refine ⟨49820243810156570357526937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66426991746875427143369249 49820243810156570357526937)
    ·
      refine ⟨37365182857617427768145203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49820243810156570357526937 37365182857617427768145203)
      ·
        refine ⟨56047774286426141652217805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37365182857617427768145203 56047774286426141652217805)
        ·
          refine ⟨21017915357409803119581677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56047774286426141652217805 21017915357409803119581677)
          ·
            refine ⟨7881718259028676169843129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21017915357409803119581677 7881718259028676169843129)
            ·
              refine ⟨5911288694271507127382347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7881718259028676169843129 5911288694271507127382347)
              ·
                refine ⟨8866933041407260691073521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5911288694271507127382347 8866933041407260691073521)
                ·
                  refine ⟨6650199781055445518305141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8866933041407260691073521 6650199781055445518305141)
                  ·
                    refine ⟨623456229473948017341107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6650199781055445518305141 623456229473948017341107)
                    ·
                      rfl

theorem cell22_1821265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 1, 2, 5].length) (baseStart_1821265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1821265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1821265 prefixEnd_1821265 := by exact prefixLift 1821265
  have htrace : WordTrace (prefixWord ++ tailWord_1821265) baseStart_1821265 baseEnd_1821265 := by
    simpa [prefixWord, tailWord_1821265, baseEnd_1821265] using wordTrace_append hprefix tailTrace_1821265
  have hstable : (prefixWord ++ tailWord_1821265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1821265).length < 2 ^ (prefixWord ++ tailWord_1821265).sum := by decide
  have hdescent : baseEnd_1821265 < baseStart_1821265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1821265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1821280 : List Nat := [2, 1, 1, 3, 2, 1, 2, 3, 3, 4]
def baseStart_1821280 : Nat := 118140960795 + 1821280 * 2 ^ 59
def prefixEnd_1821280 : Nat := 4983230072969 + 3 ^ 40 * 1821280 * 2
def baseEnd_1821280 : Nat := 623461364280492978216061

theorem tailTrace_1821280 : CollatzResearch.WordTrace tailWord_1821280 prefixEnd_1821280 623461364280492978216061 := by
  unfold tailWord_1821280
  simp only [CollatzResearch.WordTrace]
  refine ⟨33213769420910542352582647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44285025894547389803443529 33213769420910542352582647)
  ·
    refine ⟨49820654131365813528873971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33213769420910542352582647 49820654131365813528873971)
    ·
      refine ⟨74730981197048720293310957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49820654131365813528873971 74730981197048720293310957)
      ·
        refine ⟨28024117948893270109991609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74730981197048720293310957 28024117948893270109991609)
        ·
          refine ⟨21018088461669952582493707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28024117948893270109991609 21018088461669952582493707)
          ·
            refine ⟨31527132692504928873740561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21018088461669952582493707 31527132692504928873740561)
            ·
              refine ⟨23645349519378696655305421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31527132692504928873740561 23645349519378696655305421)
              ·
                refine ⟨8867006069767011245739533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23645349519378696655305421 8867006069767011245739533)
                ·
                  refine ⟨3325127276162629217152325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8867006069767011245739533 3325127276162629217152325)
                  ·
                    refine ⟨623461364280492978216061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3325127276162629217152325 623461364280492978216061)
                    ·
                      rfl

theorem cell22_1821280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 3, 3, 4].length) (baseStart_1821280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1821280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1821280 prefixEnd_1821280 := by exact prefixLift 1821280
  have htrace : WordTrace (prefixWord ++ tailWord_1821280) baseStart_1821280 baseEnd_1821280 := by
    simpa [prefixWord, tailWord_1821280, baseEnd_1821280] using wordTrace_append hprefix tailTrace_1821280
  have hstable : (prefixWord ++ tailWord_1821280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1821280).length < 2 ^ (prefixWord ++ tailWord_1821280).sum := by decide
  have hdescent : baseEnd_1821280 < baseStart_1821280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1821280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1821288 : List Nat := [2, 1, 4, 3, 2, 2, 1, 3, 1, 3]
def baseStart_1821288 : Nat := 118140960795 + 1821288 * 2 ^ 59
def prefixEnd_1821288 : Nat := 4983230072969 + 3 ^ 40 * 1821288 * 2
def baseEnd_1821288 : Nat := 623464102843983624016037

theorem tailTrace_1821288 : CollatzResearch.WordTrace tailWord_1821288 prefixEnd_1821288 623464102843983624016037 := by
  unfold tailWord_1821288
  simp only [CollatzResearch.WordTrace]
  refine ⟨33213915312896051035728259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44285220417194734714304345 33213915312896051035728259)
  ·
    refine ⟨49820872969344076553592389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33213915312896051035728259 49820872969344076553592389)
    ·
      refine ⟨9341413681752014353798573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49820872969344076553592389 9341413681752014353798573)
      ·
        refine ⟨3503030130657005382674465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9341413681752014353798573 3503030130657005382674465)
        ·
          refine ⟨2627272597992754037005849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3503030130657005382674465 2627272597992754037005849)
          ·
            refine ⟨1970454448494565527754387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2627272597992754037005849 1970454448494565527754387)
            ·
              refine ⟨2955681672741848291631581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1970454448494565527754387 2955681672741848291631581)
              ·
                refine ⟨1108380627278193109361843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2955681672741848291631581 1108380627278193109361843)
                ·
                  refine ⟨1662570940917289664042765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1108380627278193109361843 1662570940917289664042765)
                  ·
                    refine ⟨623464102843983624016037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1662570940917289664042765 623464102843983624016037)
                    ·
                      rfl

theorem cell22_1821288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 1, 3, 1, 3].length) (baseStart_1821288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1821288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1821288 prefixEnd_1821288 := by exact prefixLift 1821288
  have htrace : WordTrace (prefixWord ++ tailWord_1821288) baseStart_1821288 baseEnd_1821288 := by
    simpa [prefixWord, tailWord_1821288, baseEnd_1821288] using wordTrace_append hprefix tailTrace_1821288
  have hstable : (prefixWord ++ tailWord_1821288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1821288).length < 2 ^ (prefixWord ++ tailWord_1821288).sum := by decide
  have hdescent : baseEnd_1821288 < baseStart_1821288 := by decide
  rcases family_descends (prefixWord ++ tailWord_1821288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1821312 : List Nat := [2, 1, 1, 2, 1, 7, 1, 1, 6]
def baseStart_1821312 : Nat := 118140960795 + 1821312 * 2 ^ 59
def prefixEnd_1821312 : Nat := 4983230072969 + 3 ^ 40 * 1821312 * 2
def baseEnd_1821312 : Nat := 207824106178151853805321

theorem tailTrace_1821312 : CollatzResearch.WordTrace tailWord_1821312 prefixEnd_1821312 207824106178151853805321 := by
  unfold tailWord_1821312
  simp only [CollatzResearch.WordTrace]
  refine ⟨33214352988852577085165095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44285803985136769446886793 33214352988852577085165095)
  ·
    refine ⟨49821529483278865627747643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33214352988852577085165095 49821529483278865627747643)
    ·
      refine ⟨74732294224918298441621465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49821529483278865627747643 74732294224918298441621465)
      ·
        refine ⟨56049220668688723831216099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74732294224918298441621465 56049220668688723831216099)
        ·
          refine ⟨84073831003033085746824149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56049220668688723831216099 84073831003033085746824149)
          ·
            refine ⟨1970480414133587947191191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 84073831003033085746824149 1970480414133587947191191)
            ·
              refine ⟨2955720621200381920786787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1970480414133587947191191 2955720621200381920786787)
              ·
                refine ⟨4433580931800572881180181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2955720621200381920786787 4433580931800572881180181)
                ·
                  refine ⟨207824106178151853805321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4433580931800572881180181 207824106178151853805321)
                  ·
                    rfl

theorem cell22_1821312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 1, 1, 6].length) (baseStart_1821312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1821312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1821312 prefixEnd_1821312 := by exact prefixLift 1821312
  have htrace : WordTrace (prefixWord ++ tailWord_1821312) baseStart_1821312 baseEnd_1821312 := by
    simpa [prefixWord, tailWord_1821312, baseEnd_1821312] using wordTrace_append hprefix tailTrace_1821312
  have hstable : (prefixWord ++ tailWord_1821312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1821312).length < 2 ^ (prefixWord ++ tailWord_1821312).sum := by decide
  have hdescent : baseEnd_1821312 < baseStart_1821312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1821312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1821327 : List Nat := [1, 1, 2, 1, 1, 1, 1, 9, 2, 3]
def baseStart_1821327 : Nat := 118140960795 + 1821327 * 2 ^ 59
def prefixEnd_1821327 : Nat := 4983230072969 + 3 ^ 40 * 1821327 * 2
def baseEnd_1821327 : Nat := 623477453341000522290917

theorem tailTrace_1821327 : CollatzResearch.WordTrace tailWord_1821327 prefixEnd_1821327 623477453341000522290917 := by
  unfold tailWord_1821327
  simp only [CollatzResearch.WordTrace]
  refine ⟨66429253072650811732126235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44286168715100541154750823 66429253072650811732126235)
  ·
    refine ⟨99643879608976217598189353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66429253072650811732126235 99643879608976217598189353)
    ·
      refine ⟨74732909706732163198642015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99643879608976217598189353 74732909706732163198642015)
      ·
        refine ⟨112099364560098244797963023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74732909706732163198642015 112099364560098244797963023)
        ·
          refine ⟨168149046840147367196944535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112099364560098244797963023 168149046840147367196944535)
          ·
            refine ⟨252223570260221050795416803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168149046840147367196944535 252223570260221050795416803)
            ·
              refine ⟨378335355390331576193125205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 252223570260221050795416803 378335355390331576193125205)
              ·
                refine ⟨2216808722990224079256593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 378335355390331576193125205 2216808722990224079256593)
                ·
                  refine ⟨1662606542242668059442445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2216808722990224079256593 1662606542242668059442445)
                  ·
                    refine ⟨623477453341000522290917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1662606542242668059442445 623477453341000522290917)
                    ·
                      rfl

theorem cell22_1821327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 9, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 9, 2, 3].length) (baseStart_1821327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1821327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1821327 prefixEnd_1821327 := by exact prefixLift 1821327
  have htrace : WordTrace (prefixWord ++ tailWord_1821327) baseStart_1821327 baseEnd_1821327 := by
    simpa [prefixWord, tailWord_1821327, baseEnd_1821327] using wordTrace_append hprefix tailTrace_1821327
  have hstable : (prefixWord ++ tailWord_1821327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1821327).length < 2 ^ (prefixWord ++ tailWord_1821327).sum := by decide
  have hdescent : baseEnd_1821327 < baseStart_1821327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1821327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1821370 : List Nat := [3, 1, 1, 1, 2, 3, 1, 1, 1, 8]
def baseStart_1821370 : Nat := 118140960795 + 1821370 * 2 ^ 59
def prefixEnd_1821370 : Nat := 4983230072969 + 3 ^ 40 * 1821370 * 2
def baseEnd_1821370 : Nat := 623492173119762743465785

theorem tailTrace_1821370 : CollatzResearch.WordTrace tailWord_1821370 prefixEnd_1821370 623492173119762743465785 := by
  unfold tailWord_1821370
  simp only [CollatzResearch.WordTrace]
  refine ⟨16607705352873757518985391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44287214274330020050627709 16607705352873757518985391)
  ·
    refine ⟨24911558029310636278478087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16607705352873757518985391 24911558029310636278478087)
    ·
      refine ⟨37367337043965954417717131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24911558029310636278478087 37367337043965954417717131)
      ·
        refine ⟨56051005565948931626575697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37367337043965954417717131 56051005565948931626575697)
        ·
          refine ⟨42038254174461698719931773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56051005565948931626575697 42038254174461698719931773)
          ·
            refine ⟨15764345315423137019974415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42038254174461698719931773 15764345315423137019974415)
            ·
              refine ⟨23646517973134705529961623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15764345315423137019974415 23646517973134705529961623)
              ·
                refine ⟨35469776959702058294942435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23646517973134705529961623 35469776959702058294942435)
                ·
                  refine ⟨53204665439553087442413653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35469776959702058294942435 53204665439553087442413653)
                  ·
                    refine ⟨623492173119762743465785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 53204665439553087442413653 623492173119762743465785)
                    ·
                      rfl

theorem cell22_1821370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 1, 8].length) (baseStart_1821370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1821370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1821370 prefixEnd_1821370 := by exact prefixLift 1821370
  have htrace : WordTrace (prefixWord ++ tailWord_1821370) baseStart_1821370 baseEnd_1821370 := by
    simpa [prefixWord, tailWord_1821370, baseEnd_1821370] using wordTrace_append hprefix tailTrace_1821370
  have hstable : (prefixWord ++ tailWord_1821370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1821370).length < 2 ^ (prefixWord ++ tailWord_1821370).sum := by decide
  have hdescent : baseEnd_1821370 < baseStart_1821370 := by decide
  rcases family_descends (prefixWord ++ tailWord_1821370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1821552 : List Nat := [2, 1, 1, 1, 4, 1, 3, 1, 1, 7]
def baseStart_1821552 : Nat := 118140960795 + 1821552 * 2 ^ 59
def prefixEnd_1821552 : Nat := 4983230072969 + 3 ^ 40 * 1821552 * 2
def baseEnd_1821552 : Nat := 623554475439174935415227

theorem tailTrace_1821552 : CollatzResearch.WordTrace tailWord_1821552 prefixEnd_1821552 623554475439174935415227 := by
  unfold tailWord_1821552
  simp only [CollatzResearch.WordTrace]
  refine ⟨33218729748417837579533455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44291639664557116772711273 33218729748417837579533455)
  ·
    refine ⟨49828094622626756369300183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33218729748417837579533455 49828094622626756369300183)
    ·
      refine ⟨74742141933940134553950275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49828094622626756369300183 74742141933940134553950275)
      ·
        refine ⟨112113212900910201830925413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74742141933940134553950275 112113212900910201830925413)
        ·
          refine ⟨21021227418920662843298515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112113212900910201830925413 21021227418920662843298515)
          ·
            refine ⟨31531841128380994264947773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21021227418920662843298515 31531841128380994264947773)
            ·
              refine ⟨11824440423142872849355415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31531841128380994264947773 11824440423142872849355415)
              ·
                refine ⟨17736660634714309274033123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11824440423142872849355415 17736660634714309274033123)
                ·
                  refine ⟨26604990952071463911049685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17736660634714309274033123 26604990952071463911049685)
                  ·
                    refine ⟨623554475439174935415227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26604990952071463911049685 623554475439174935415227)
                    ·
                      rfl

theorem cell22_1821552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 1, 1, 7].length) (baseStart_1821552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1821552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1821552 prefixEnd_1821552 := by exact prefixLift 1821552
  have htrace : WordTrace (prefixWord ++ tailWord_1821552) baseStart_1821552 baseEnd_1821552 := by
    simpa [prefixWord, tailWord_1821552, baseEnd_1821552] using wordTrace_append hprefix tailTrace_1821552
  have hstable : (prefixWord ++ tailWord_1821552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1821552).length < 2 ^ (prefixWord ++ tailWord_1821552).sum := by decide
  have hdescent : baseEnd_1821552 < baseStart_1821552 := by decide
  rcases family_descends (prefixWord ++ tailWord_1821552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1821554 : List Nat := [3, 2, 1, 2, 1, 1, 4, 3, 5]
def baseStart_1821554 : Nat := 118140960795 + 1821554 * 2 ^ 59
def prefixEnd_1821554 : Nat := 4983230072969 + 3 ^ 40 * 1821554 * 2
def baseEnd_1821554 : Nat := 207851720026682532288407

theorem tailTrace_1821554 : CollatzResearch.WordTrace tailWord_1821554 prefixEnd_1821554 207851720026682532288407 := by
  unfold tailWord_1821554
  simp only [CollatzResearch.WordTrace]
  refine ⟨16609383110707107375159929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44291688295218953000426477 16609383110707107375159929)
  ·
    refine ⟨12457037333030330531369947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16609383110707107375159929 12457037333030330531369947)
    ·
      refine ⟨18685555999545495797054921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12457037333030330531369947 18685555999545495797054921)
      ·
        refine ⟨14014166999659121847791191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18685555999545495797054921 14014166999659121847791191)
        ·
          refine ⟨21021250499488682771686787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14014166999659121847791191 21021250499488682771686787)
          ·
            refine ⟨31531875749233024157530181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21021250499488682771686787 31531875749233024157530181)
            ·
              refine ⟨5912226702981192029536909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31531875749233024157530181 5912226702981192029536909)
              ·
                refine ⟨2217085013617947011076341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5912226702981192029536909 2217085013617947011076341)
                ·
                  refine ⟨207851720026682532288407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2217085013617947011076341 207851720026682532288407)
                  ·
                    rfl

theorem cell22_1821554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 3, 5].length) (baseStart_1821554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1821554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1821554 prefixEnd_1821554 := by exact prefixLift 1821554
  have htrace : WordTrace (prefixWord ++ tailWord_1821554) baseStart_1821554 baseEnd_1821554 := by
    simpa [prefixWord, tailWord_1821554, baseEnd_1821554] using wordTrace_append hprefix tailTrace_1821554
  have hstable : (prefixWord ++ tailWord_1821554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1821554).length < 2 ^ (prefixWord ++ tailWord_1821554).sum := by decide
  have hdescent : baseEnd_1821554 < baseStart_1821554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1821554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1821558 : List Nat := [5, 1, 1, 3, 1, 2, 1, 2, 3, 3]
def baseStart_1821558 : Nat := 118140960795 + 1821558 * 2 ^ 59
def prefixEnd_1821558 : Nat := 4983230072969 + 3 ^ 40 * 1821558 * 2
def baseEnd_1821558 : Nat := 623556529361792919765209

theorem tailTrace_1821558 : CollatzResearch.WordTrace tailWord_1821558 prefixEnd_1821558 623556529361792919765209 := by
  unfold tailWord_1821558
  simp only [CollatzResearch.WordTrace]
  refine ⟨4152354895925871136486583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44291785556542625455856885 4152354895925871136486583)
  ·
    refine ⟨6228532343888806704729875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4152354895925871136486583 6228532343888806704729875)
    ·
      refine ⟨9342798515833210057094813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6228532343888806704729875 9342798515833210057094813)
      ·
        refine ⟨3503549443437453771410555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9342798515833210057094813 3503549443437453771410555)
        ·
          refine ⟨5255324165156180657115833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3503549443437453771410555 5255324165156180657115833)
          ·
            refine ⟨3941493123867135492836875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5255324165156180657115833 3941493123867135492836875)
            ·
              refine ⟨5912239685800703239255313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3941493123867135492836875 5912239685800703239255313)
              ·
                refine ⟨4434179764350527429441485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5912239685800703239255313 4434179764350527429441485)
                ·
                  refine ⟨1662817411631447786040557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4434179764350527429441485 1662817411631447786040557)
                  ·
                    refine ⟨623556529361792919765209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1662817411631447786040557 623556529361792919765209)
                    ·
                      rfl

theorem cell22_1821558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 2, 3, 3].length) (baseStart_1821558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1821558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1821558 prefixEnd_1821558 := by exact prefixLift 1821558
  have htrace : WordTrace (prefixWord ++ tailWord_1821558) baseStart_1821558 baseEnd_1821558 := by
    simpa [prefixWord, tailWord_1821558, baseEnd_1821558] using wordTrace_append hprefix tailTrace_1821558
  have hstable : (prefixWord ++ tailWord_1821558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1821558).length < 2 ^ (prefixWord ++ tailWord_1821558).sum := by decide
  have hdescent : baseEnd_1821558 < baseStart_1821558 := by decide
  rcases family_descends (prefixWord ++ tailWord_1821558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1821599 : List Nat := [1, 1, 2, 5, 2, 1, 1, 3, 6]
def baseStart_1821599 : Nat := 118140960795 + 1821599 * 2 ^ 59
def prefixEnd_1821599 : Nat := 4983230072969 + 3 ^ 40 * 1821599 * 2
def baseEnd_1821599 : Nat := 207856854833227493163361

theorem tailTrace_1821599 : CollatzResearch.WordTrace tailWord_1821599 prefixEnd_1821599 207856854833227493163361 := by
  unfold tailWord_1821599
  simp only [CollatzResearch.WordTrace]
  refine ⟨66439173727665402186027851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44292782485110268124018567 66439173727665402186027851)
  ·
    refine ⟨99658760591498103279041777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66439173727665402186027851 99658760591498103279041777)
    ·
      refine ⟨74744070443623577459281333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99658760591498103279041777 74744070443623577459281333)
      ·
        refine ⟨7007256604089710386807625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 74744070443623577459281333 7007256604089710386807625)
        ·
          refine ⟨5255442453067282790105719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7007256604089710386807625 5255442453067282790105719)
          ·
            refine ⟨7883163679600924185158579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5255442453067282790105719 7883163679600924185158579)
            ·
              refine ⟨11824745519401386277737869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7883163679600924185158579 11824745519401386277737869)
              ·
                refine ⟨4434279569775519854151701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11824745519401386277737869 4434279569775519854151701)
                ·
                  refine ⟨207856854833227493163361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4434279569775519854151701 207856854833227493163361)
                  ·
                    rfl

theorem cell22_1821599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 3, 6].length) (baseStart_1821599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1821599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1821599 prefixEnd_1821599 := by exact prefixLift 1821599
  have htrace : WordTrace (prefixWord ++ tailWord_1821599) baseStart_1821599 baseEnd_1821599 := by
    simpa [prefixWord, tailWord_1821599, baseEnd_1821599] using wordTrace_append hprefix tailTrace_1821599
  have hstable : (prefixWord ++ tailWord_1821599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1821599).length < 2 ^ (prefixWord ++ tailWord_1821599).sum := by decide
  have hdescent : baseEnd_1821599 < baseStart_1821599 := by decide
  rcases family_descends (prefixWord ++ tailWord_1821599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1821646 : List Nat := [4, 1, 1, 1, 2, 4, 1, 2, 2, 4]
def baseStart_1821646 : Nat := 118140960795 + 1821646 * 2 ^ 59
def prefixEnd_1821646 : Nat := 4983230072969 + 3 ^ 40 * 1821646 * 2
def baseEnd_1821646 : Nat := 623586653560190023564939

theorem tailTrace_1821646 : CollatzResearch.WordTrace tailWord_1821646 prefixEnd_1821646 623586653560190023564939 := by
  unfold tailWord_1821646
  simp only [CollatzResearch.WordTrace]
  refine ⟨8305110994811891151623599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44293925305663419475325861 8305110994811891151623599)
  ·
    refine ⟨12457666492217836727435399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8305110994811891151623599 12457666492217836727435399)
    ·
      refine ⟨18686499738326755091153099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12457666492217836727435399 18686499738326755091153099)
      ·
        refine ⟨28029749607490132636729649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18686499738326755091153099 28029749607490132636729649)
        ·
          refine ⟨21022312205617599477547237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28029749607490132636729649 21022312205617599477547237)
          ·
            refine ⟨3941683538553299902040107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21022312205617599477547237 3941683538553299902040107)
            ·
              refine ⟨5912525307829949853060161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3941683538553299902040107 5912525307829949853060161)
              ·
                refine ⟨4434393980872462389795121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5912525307829949853060161 4434393980872462389795121)
                ·
                  refine ⟨3325795485654346792346341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4434393980872462389795121 3325795485654346792346341)
                  ·
                    refine ⟨623586653560190023564939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3325795485654346792346341 623586653560190023564939)
                    ·
                      rfl

theorem cell22_1821646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 2, 2, 4].length) (baseStart_1821646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1821646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1821646 prefixEnd_1821646 := by exact prefixLift 1821646
  have htrace : WordTrace (prefixWord ++ tailWord_1821646) baseStart_1821646 baseEnd_1821646 := by
    simpa [prefixWord, tailWord_1821646, baseEnd_1821646] using wordTrace_append hprefix tailTrace_1821646
  have hstable : (prefixWord ++ tailWord_1821646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1821646).length < 2 ^ (prefixWord ++ tailWord_1821646).sum := by decide
  have hdescent : baseEnd_1821646 < baseStart_1821646 := by decide
  rcases family_descends (prefixWord ++ tailWord_1821646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1821650 : List Nat := [3, 2, 2, 3, 1, 2, 3, 2, 4]
def baseStart_1821650 : Nat := 118140960795 + 1821650 * 2 ^ 59
def prefixEnd_1821650 : Nat := 4983230072969 + 3 ^ 40 * 1821650 * 2
def baseEnd_1821650 : Nat := 207862674280645115488309

theorem tailTrace_1821650 : CollatzResearch.WordTrace tailWord_1821650 prefixEnd_1821650 207862674280645115488309 := by
  unfold tailWord_1821650
  simp only [CollatzResearch.WordTrace]
  refine ⟨16610258462620159474033601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44294022566987091930756269 16610258462620159474033601)
  ·
    refine ⟨12457693846965119605525201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16610258462620159474033601 12457693846965119605525201)
    ·
      refine ⟨9343270385223839704143901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12457693846965119605525201 9343270385223839704143901)
      ·
        refine ⟨3503726394458939889053963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9343270385223839704143901 3503726394458939889053963)
        ·
          refine ⟨5255589591688409833580945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3503726394458939889053963 5255589591688409833580945)
          ·
            refine ⟨3941692193766307375185709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5255589591688409833580945 3941692193766307375185709)
            ·
              refine ⟨1478134572662365265694641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3941692193766307375185709 1478134572662365265694641)
              ·
                refine ⟨1108600929496773949270981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1478134572662365265694641 1108600929496773949270981)
                ·
                  refine ⟨207862674280645115488309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1108600929496773949270981 207862674280645115488309)
                  ·
                    rfl

theorem cell22_1821650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 3, 2, 4].length) (baseStart_1821650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1821650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1821650 prefixEnd_1821650 := by exact prefixLift 1821650
  have htrace : WordTrace (prefixWord ++ tailWord_1821650) baseStart_1821650 baseEnd_1821650 := by
    simpa [prefixWord, tailWord_1821650, baseEnd_1821650] using wordTrace_append hprefix tailTrace_1821650
  have hstable : (prefixWord ++ tailWord_1821650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1821650).length < 2 ^ (prefixWord ++ tailWord_1821650).sum := by decide
  have hdescent : baseEnd_1821650 < baseStart_1821650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1821650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1821661 : List Nat := [1, 4, 3, 1, 2, 2, 2, 7]
def baseStart_1821661 : Nat := 118140960795 + 1821661 * 2 ^ 59
def prefixEnd_1821661 : Nat := 4983230072969 + 3 ^ 40 * 1821661 * 2
def baseEnd_1821661 : Nat := 69287976485192776048877

theorem tailTrace_1821661 : CollatzResearch.WordTrace tailWord_1821661 prefixEnd_1821661 69287976485192776048877 := by
  unfold tailWord_1821661
  simp only [CollatzResearch.WordTrace]
  refine ⟨66441435053440786774784837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44294290035627191183189891 66441435053440786774784837)
  ·
    refine ⟨12457769072520147520272157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66441435053440786774784837 12457769072520147520272157)
    ·
      refine ⟨4671663402195055320102059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12457769072520147520272157 4671663402195055320102059)
      ·
        refine ⟨7007495103292582980153089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4671663402195055320102059 7007495103292582980153089)
        ·
          refine ⟨5255621327469437235114817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7007495103292582980153089 5255621327469437235114817)
          ·
            refine ⟨3941715995602077926336113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5255621327469437235114817 3941715995602077926336113)
            ·
              refine ⟨2956286996701558444752085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3941715995602077926336113 2956286996701558444752085)
              ·
                refine ⟨69287976485192776048877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2956286996701558444752085 69287976485192776048877)
                ·
                  rfl

theorem cell22_1821661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 2, 7].length) (baseStart_1821661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1821661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1821661 prefixEnd_1821661 := by exact prefixLift 1821661
  have htrace : WordTrace (prefixWord ++ tailWord_1821661) baseStart_1821661 baseEnd_1821661 := by
    simpa [prefixWord, tailWord_1821661, baseEnd_1821661] using wordTrace_append hprefix tailTrace_1821661
  have hstable : (prefixWord ++ tailWord_1821661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1821661).length < 2 ^ (prefixWord ++ tailWord_1821661).sum := by decide
  have hdescent : baseEnd_1821661 < baseStart_1821661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1821661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1821693 : List Nat := [1, 4, 1, 1, 1, 2, 1, 7, 1, 3]
def baseStart_1821693 : Nat := 118140960795 + 1821693 * 2 ^ 59
def prefixEnd_1821693 : Nat := 4983230072969 + 3 ^ 40 * 1821693 * 2
def baseEnd_1821693 : Nat := 623602742620697567639795

theorem tailTrace_1821693 : CollatzResearch.WordTrace tailWord_1821693 prefixEnd_1821693 623602742620697567639795 := by
  unfold tailWord_1821693
  simp only [CollatzResearch.WordTrace]
  refine ⟨66442602189324856239949733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44295068126216570826633155 66442602189324856239949733)
  ·
    refine ⟨12457987910498410544990575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66442602189324856239949733 12457987910498410544990575)
    ·
      refine ⟨18686981865747615817485863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12457987910498410544990575 18686981865747615817485863)
      ·
        refine ⟨28030472798621423726228795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18686981865747615817485863 28030472798621423726228795)
        ·
          refine ⟨42045709197932135589343193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28030472798621423726228795 42045709197932135589343193)
          ·
            refine ⟨31534281898449101692007395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42045709197932135589343193 31534281898449101692007395)
            ·
              refine ⟨47301422847673652538011093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31534281898449101692007395 47301422847673652538011093)
              ·
                refine ⟨1108627097992351231359635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 47301422847673652538011093 1108627097992351231359635)
                ·
                  refine ⟨1662940646988526847039453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1108627097992351231359635 1662940646988526847039453)
                  ·
                    refine ⟨623602742620697567639795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1662940646988526847039453 623602742620697567639795)
                    ·
                      rfl

theorem cell22_1821693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 7, 1, 3].length) (baseStart_1821693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1821693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1821693 prefixEnd_1821693 := by exact prefixLift 1821693
  have htrace : WordTrace (prefixWord ++ tailWord_1821693) baseStart_1821693 baseEnd_1821693 := by
    simpa [prefixWord, tailWord_1821693, baseEnd_1821693] using wordTrace_append hprefix tailTrace_1821693
  have hstable : (prefixWord ++ tailWord_1821693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1821693).length < 2 ^ (prefixWord ++ tailWord_1821693).sum := by decide
  have hdescent : baseEnd_1821693 < baseStart_1821693 := by decide
  rcases family_descends (prefixWord ++ tailWord_1821693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1821706 : List Nat := [3, 1, 2, 2, 3, 1, 1, 4, 5]
def baseStart_1821706 : Nat := 118140960795 + 1821706 * 2 ^ 59
def prefixEnd_1821706 : Nat := 4983230072969 + 3 ^ 40 * 1821706 * 2
def baseEnd_1821706 : Nat := 207869064262123289021585

theorem tailTrace_1821706 : CollatzResearch.WordTrace tailWord_1821706 prefixEnd_1821706 207869064262123289021585 := by
  unfold tailWord_1821706
  simp only [CollatzResearch.WordTrace]
  refine ⟨16610769084569439865043243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44295384225518506306781981 16610769084569439865043243)
  ·
    refine ⟨24916153626854159797564865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16610769084569439865043243 24916153626854159797564865)
    ·
      refine ⟨18687115220140619848173649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24916153626854159797564865 18687115220140619848173649)
      ·
        refine ⟨14015336415105464886130237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18687115220140619848173649 14015336415105464886130237)
        ·
          refine ⟨5255751155664549332298839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14015336415105464886130237 5255751155664549332298839)
          ·
            refine ⟨7883626733496823998448259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5255751155664549332298839 7883626733496823998448259)
            ·
              refine ⟨11825440100245235997672389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7883626733496823998448259 11825440100245235997672389)
              ·
                refine ⟨2217270018795981749563573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11825440100245235997672389 2217270018795981749563573)
                ·
                  refine ⟨207869064262123289021585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2217270018795981749563573 207869064262123289021585)
                  ·
                    rfl

theorem cell22_1821706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 4, 5].length) (baseStart_1821706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1821706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1821706 prefixEnd_1821706 := by exact prefixLift 1821706
  have htrace : WordTrace (prefixWord ++ tailWord_1821706) baseStart_1821706 baseEnd_1821706 := by
    simpa [prefixWord, tailWord_1821706, baseEnd_1821706] using wordTrace_append hprefix tailTrace_1821706
  have hstable : (prefixWord ++ tailWord_1821706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1821706).length < 2 ^ (prefixWord ++ tailWord_1821706).sum := by decide
  have hdescent : baseEnd_1821706 < baseStart_1821706 := by decide
  rcases family_descends (prefixWord ++ tailWord_1821706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1821710 : List Nat := [4, 1, 1, 2, 2, 3, 1, 4, 1, 3]
def baseStart_1821710 : Nat := 118140960795 + 1821710 * 2 ^ 59
def prefixEnd_1821710 : Nat := 4983230072969 + 3 ^ 40 * 1821710 * 2
def baseEnd_1821710 : Nat := 623608562068115189964743

theorem tailTrace_1821710 : CollatzResearch.WordTrace tailWord_1821710 prefixEnd_1821710 623608562068115189964743 := by
  unfold tailWord_1821710
  simp only [CollatzResearch.WordTrace]
  refine ⟨8305402778782908517914823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44295481486842178762212389 8305402778782908517914823)
  ·
    refine ⟨12458104168174362776872235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8305402778782908517914823 12458104168174362776872235)
    ·
      refine ⟨18687156252261544165308353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12458104168174362776872235 18687156252261544165308353)
      ·
        refine ⟨14015367189196158123981265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18687156252261544165308353 14015367189196158123981265)
        ·
          refine ⟨10511525391897118592985949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14015367189196158123981265 10511525391897118592985949)
          ·
            refine ⟨3941822021961419472369731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10511525391897118592985949 3941822021961419472369731)
            ·
              refine ⟨5912733032942129208554597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3941822021961419472369731 5912733032942129208554597)
              ·
                refine ⟨1108637443676649226603987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5912733032942129208554597 1108637443676649226603987)
                ·
                  refine ⟨1662956165514973839905981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1108637443676649226603987 1662956165514973839905981)
                  ·
                    refine ⟨623608562068115189964743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1662956165514973839905981 623608562068115189964743)
                    ·
                      rfl

theorem cell22_1821710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 4, 1, 3].length) (baseStart_1821710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1821710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1821710 prefixEnd_1821710 := by exact prefixLift 1821710
  have htrace : WordTrace (prefixWord ++ tailWord_1821710) baseStart_1821710 baseEnd_1821710 := by
    simpa [prefixWord, tailWord_1821710, baseEnd_1821710] using wordTrace_append hprefix tailTrace_1821710
  have hstable : (prefixWord ++ tailWord_1821710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1821710).length < 2 ^ (prefixWord ++ tailWord_1821710).sum := by decide
  have hdescent : baseEnd_1821710 < baseStart_1821710 := by decide
  rcases family_descends (prefixWord ++ tailWord_1821710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1821753 : List Nat := [1, 2, 1, 5, 2, 2, 1, 3, 1, 4]
def baseStart_1821753 : Nat := 118140960795 + 1821753 * 2 ^ 59
def prefixEnd_1821753 : Nat := 4983230072969 + 3 ^ 40 * 1821753 * 2
def baseEnd_1821753 : Nat := 623623281846877411139611

theorem tailTrace_1821753 : CollatzResearch.WordTrace tailWord_1821753 prefixEnd_1821753 623623281846877411139611 := by
  unfold tailWord_1821753
  simp only [CollatzResearch.WordTrace]
  refine ⟨66444790569107486487133913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44296527046071657658089275 66444790569107486487133913)
  ·
    refine ⟨49833592926830614865350435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66444790569107486487133913 49833592926830614865350435)
    ·
      refine ⟨74750389390245922298025653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49833592926830614865350435 74750389390245922298025653)
      ·
        refine ⟨7007849005335555215439905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 74750389390245922298025653 7007849005335555215439905)
        ·
          refine ⟨5255886754001666411579929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7007849005335555215439905 5255886754001666411579929)
          ·
            refine ⟨3941915065501249808684947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5255886754001666411579929 3941915065501249808684947)
            ·
              refine ⟨5912872598251874713027421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3941915065501249808684947 5912872598251874713027421)
              ·
                refine ⟨2217327224344453017385283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5912872598251874713027421 2217327224344453017385283)
                ·
                  refine ⟨3325990836516679526077925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2217327224344453017385283 3325990836516679526077925)
                  ·
                    refine ⟨623623281846877411139611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3325990836516679526077925 623623281846877411139611)
                    ·
                      rfl

theorem cell22_1821753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 3, 1, 4].length) (baseStart_1821753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1821753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1821753 prefixEnd_1821753 := by exact prefixLift 1821753
  have htrace : WordTrace (prefixWord ++ tailWord_1821753) baseStart_1821753 baseEnd_1821753 := by
    simpa [prefixWord, tailWord_1821753, baseEnd_1821753] using wordTrace_append hprefix tailTrace_1821753
  have hstable : (prefixWord ++ tailWord_1821753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1821753).length < 2 ^ (prefixWord ++ tailWord_1821753).sum := by decide
  have hdescent : baseEnd_1821753 < baseStart_1821753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1821753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1821920 : List Nat := [2, 1, 1, 3, 1, 5, 2, 3, 4]
def baseStart_1821920 : Nat := 118140960795 + 1821920 * 2 ^ 59
def prefixEnd_1821920 : Nat := 4983230072969 + 3 ^ 40 * 1821920 * 2
def baseEnd_1821920 : Nat := 207893483119914880738033

theorem tailTrace_1821920 : CollatzResearch.WordTrace tailWord_1821920 prefixEnd_1821920 207893483119914880738033 := by
  unfold tailWord_1821920
  simp only [CollatzResearch.WordTrace]
  refine ⟨33225440779751237004231607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44300587706334982672308809 33225440779751237004231607)
  ·
    refine ⟨49838161169626855506347411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33225440779751237004231607 49838161169626855506347411)
    ·
      refine ⟨74757241754440283259521117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49838161169626855506347411 74757241754440283259521117)
      ·
        refine ⟨28033965657915106222320419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74757241754440283259521117 28033965657915106222320419)
        ·
          refine ⟨42050948486872659333480629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28033965657915106222320419 42050948486872659333480629)
          ·
            refine ⟨3942276420644311812513809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42050948486872659333480629 3942276420644311812513809)
            ·
              refine ⟨2956707315483233859385357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3942276420644311812513809 2956707315483233859385357)
              ·
                refine ⟨1108765243306212697269509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2956707315483233859385357 1108765243306212697269509)
                ·
                  refine ⟨207893483119914880738033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1108765243306212697269509 207893483119914880738033)
                  ·
                    rfl

theorem cell22_1821920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 2, 3, 4].length) (baseStart_1821920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1821920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1821920 prefixEnd_1821920 := by exact prefixLift 1821920
  have htrace : WordTrace (prefixWord ++ tailWord_1821920) baseStart_1821920 baseEnd_1821920 := by
    simpa [prefixWord, tailWord_1821920, baseEnd_1821920] using wordTrace_append hprefix tailTrace_1821920
  have hstable : (prefixWord ++ tailWord_1821920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1821920).length < 2 ^ (prefixWord ++ tailWord_1821920).sum := by decide
  have hdescent : baseEnd_1821920 < baseStart_1821920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1821920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1821931 : List Nat := [1, 1, 1, 1, 2, 7, 9]
def baseStart_1821931 : Nat := 118140960795 + 1821931 * 2 ^ 59
def prefixEnd_1821931 : Nat := 4983230072969 + 3 ^ 40 * 1821931 * 2
def baseEnd_1821931 : Nat := 23099415366094232599595

theorem tailTrace_1821931 : CollatzResearch.WordTrace tailWord_1821931 prefixEnd_1821931 23099415366094232599595 := by
  unfold tailWord_1821931
  simp only [CollatzResearch.WordTrace]
  refine ⟨66451282762462622887113647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44300855174975081924742431 66451282762462622887113647)
  ·
    refine ⟨99676924143693934330670471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66451282762462622887113647 99676924143693934330670471)
    ·
      refine ⟨149515386215540901496005707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99676924143693934330670471 149515386215540901496005707)
      ·
        refine ⟨224273079323311352244008561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149515386215540901496005707 224273079323311352244008561)
        ·
          refine ⟨168204809492483514183006421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224273079323311352244008561 168204809492483514183006421)
          ·
            refine ⟨3942300222480082363664213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 168204809492483514183006421 3942300222480082363664213)
            ·
              refine ⟨23099415366094232599595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3942300222480082363664213 23099415366094232599595)
              ·
                rfl

theorem cell22_1821931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 9].length) (baseStart_1821931 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1821931 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1821931 prefixEnd_1821931 := by exact prefixLift 1821931
  have htrace : WordTrace (prefixWord ++ tailWord_1821931) baseStart_1821931 baseEnd_1821931 := by
    simpa [prefixWord, tailWord_1821931, baseEnd_1821931] using wordTrace_append hprefix tailTrace_1821931
  have hstable : (prefixWord ++ tailWord_1821931).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1821931).length < 2 ^ (prefixWord ++ tailWord_1821931).sum := by decide
  have hdescent : baseEnd_1821931 < baseStart_1821931 := by decide
  rcases family_descends (prefixWord ++ tailWord_1821931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1821935 : List Nat := [1, 1, 2, 1, 7, 1, 1, 1, 4, 3]
def baseStart_1821935 : Nat := 118140960795 + 1821935 * 2 ^ 59
def prefixEnd_1821935 : Nat := 4983230072969 + 3 ^ 40 * 1821935 * 2
def baseEnd_1821935 : Nat := 623685584166289603089053

theorem tailTrace_1821935 : CollatzResearch.WordTrace tailWord_1821935 prefixEnd_1821935 623685584166289603089053 := by
  unfold tailWord_1821935
  simp only [CollatzResearch.WordTrace]
  refine ⟨66451428654448131570259259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44300952436298754380172839 66451428654448131570259259)
  ·
    refine ⟨99677142981672197355388889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66451428654448131570259259 99677142981672197355388889)
    ·
      refine ⟨74757857236254148016541667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99677142981672197355388889 74757857236254148016541667)
      ·
        refine ⟨112136785854381222024812501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74757857236254148016541667 112136785854381222024812501)
        ·
          refine ⟨2628205918462059891206543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 112136785854381222024812501 2628205918462059891206543)
          ·
            refine ⟨3942308877693089836809815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2628205918462059891206543 3942308877693089836809815)
            ·
              refine ⟨5913463316539634755214723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3942308877693089836809815 5913463316539634755214723)
              ·
                refine ⟨8870194974809452132822085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5913463316539634755214723 8870194974809452132822085)
                ·
                  refine ⟨1663161557776772274904141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8870194974809452132822085 1663161557776772274904141)
                  ·
                    refine ⟨623685584166289603089053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1663161557776772274904141 623685584166289603089053)
                    ·
                      rfl

theorem cell22_1821935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 1, 4, 3].length) (baseStart_1821935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1821935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1821935 prefixEnd_1821935 := by exact prefixLift 1821935
  have htrace : WordTrace (prefixWord ++ tailWord_1821935) baseStart_1821935 baseEnd_1821935 := by
    simpa [prefixWord, tailWord_1821935, baseEnd_1821935] using wordTrace_append hprefix tailTrace_1821935
  have hstable : (prefixWord ++ tailWord_1821935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1821935).length < 2 ^ (prefixWord ++ tailWord_1821935).sum := by decide
  have hdescent : baseEnd_1821935 < baseStart_1821935 := by decide
  rcases family_descends (prefixWord ++ tailWord_1821935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1821982 : List Nat := [4, 3, 2, 1, 2, 2, 8]
def baseStart_1821982 : Nat := 118140960795 + 1821982 * 2 ^ 59
def prefixEnd_1821982 : Nat := 4983230072969 + 3 ^ 40 * 1821982 * 2
def baseEnd_1821982 : Nat := 23100061971362857302367

theorem tailTrace_1821982 : CollatzResearch.WordTrace tailWord_1821982 prefixEnd_1821982 23100061971362857302367 := by
  unfold tailWord_1821982
  simp only [CollatzResearch.WordTrace]
  refine ⟨8306642860659732324652525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44302095256851905731480133 8306642860659732324652525)
  ·
    refine ⟨3114991072747399621744697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8306642860659732324652525 3114991072747399621744697)
    ·
      refine ⟨2336243304560549716308523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3114991072747399621744697 2336243304560549716308523)
      ·
        refine ⟨3504364956840824574462785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2336243304560549716308523 3504364956840824574462785)
        ·
          refine ⟨2628273717630618430847089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3504364956840824574462785 2628273717630618430847089)
          ·
            refine ⟨1971205288222963823135317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2628273717630618430847089 1971205288222963823135317)
            ·
              refine ⟨23100061971362857302367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1971205288222963823135317 23100061971362857302367)
              ·
                rfl

theorem cell22_1821982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 8].length) (baseStart_1821982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1821982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1821982 prefixEnd_1821982 := by exact prefixLift 1821982
  have htrace : WordTrace (prefixWord ++ tailWord_1821982) baseStart_1821982 baseEnd_1821982 := by
    simpa [prefixWord, tailWord_1821982, baseEnd_1821982] using wordTrace_append hprefix tailTrace_1821982
  have hstable : (prefixWord ++ tailWord_1821982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1821982).length < 2 ^ (prefixWord ++ tailWord_1821982).sum := by decide
  have hdescent : baseEnd_1821982 < baseStart_1821982 := by decide
  rcases family_descends (prefixWord ++ tailWord_1821982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1822053 : List Nat := [1, 3, 1, 3, 1, 2, 1, 2, 3, 5]
def baseStart_1822053 : Nat := 118140960795 + 1822053 * 2 ^ 59
def prefixEnd_1822053 : Nat := 4983230072969 + 3 ^ 40 * 1822053 * 2
def baseEnd_1822053 : Nat := 623725977977776628638691

theorem tailTrace_1822053 : CollatzResearch.WordTrace tailWord_1822053 prefixEnd_1822053 623725977977776628638691 := by
  unfold tailWord_1822053
  simp only [CollatzResearch.WordTrace]
  refine ⟨66455732468020637723054813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44303821645347091815369875 66455732468020637723054813)
  ·
    refine ⟨24920899675507739146145555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66455732468020637723054813 24920899675507739146145555)
    ·
      refine ⟨37381349513261608719218333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24920899675507739146145555 37381349513261608719218333)
      ·
        refine ⟨14018006067473103269706875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37381349513261608719218333 14018006067473103269706875)
        ·
          refine ⟨21027009101209654904560313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14018006067473103269706875 21027009101209654904560313)
          ·
            refine ⟨15770256825907241178420235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21027009101209654904560313 15770256825907241178420235)
            ·
              refine ⟨23655385238860861767630353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15770256825907241178420235 23655385238860861767630353)
              ·
                refine ⟨17741538929145646325722765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23655385238860861767630353 17741538929145646325722765)
                ·
                  refine ⟨6653077098429617372146037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17741538929145646325722765 6653077098429617372146037)
                  ·
                    refine ⟨623725977977776628638691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6653077098429617372146037 623725977977776628638691)
                    ·
                      rfl

theorem cell22_1822053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 2, 3, 5].length) (baseStart_1822053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1822053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1822053 prefixEnd_1822053 := by exact prefixLift 1822053
  have htrace : WordTrace (prefixWord ++ tailWord_1822053) baseStart_1822053 baseEnd_1822053 := by
    simpa [prefixWord, tailWord_1822053, baseEnd_1822053] using wordTrace_append hprefix tailTrace_1822053
  have hstable : (prefixWord ++ tailWord_1822053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1822053).length < 2 ^ (prefixWord ++ tailWord_1822053).sum := by decide
  have hdescent : baseEnd_1822053 < baseStart_1822053 := by decide
  rcases family_descends (prefixWord ++ tailWord_1822053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1822085 : List Nat := [1, 3, 1, 1, 3, 1, 5, 1, 2, 4]
def baseStart_1822085 : Nat := 118140960795 + 1822085 * 2 ^ 59
def prefixEnd_1822085 : Nat := 4983230072969 + 3 ^ 40 * 1822085 * 2
def baseEnd_1822085 : Nat := 623736932231739211838593

theorem tailTrace_1822085 : CollatzResearch.WordTrace tailWord_1822085 prefixEnd_1822085 623736932231739211838593 := by
  unfold tailWord_1822085
  simp only [CollatzResearch.WordTrace]
  refine ⟨66456899603904707188219709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44304599735936471458813139 66456899603904707188219709)
  ·
    refine ⟨24921337351464265195582391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66456899603904707188219709 24921337351464265195582391)
    ·
      refine ⟨37382006027196397793373587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24921337351464265195582391 37382006027196397793373587)
      ·
        refine ⟨56073009040794596690060381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37382006027196397793373587 56073009040794596690060381)
        ·
          refine ⟨21027378390297973758772643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56073009040794596690060381 21027378390297973758772643)
          ·
            refine ⟨31541067585446960638158965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21027378390297973758772643 31541067585446960638158965)
            ·
              refine ⟨2956975086135652559827403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31541067585446960638158965 2956975086135652559827403)
              ·
                refine ⟨4435462629203478839741105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2956975086135652559827403 4435462629203478839741105)
                ·
                  refine ⟨3326596971902609129805829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4435462629203478839741105 3326596971902609129805829)
                  ·
                    refine ⟨623736932231739211838593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3326596971902609129805829 623736932231739211838593)
                    ·
                      rfl

theorem cell22_1822085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 5, 1, 2, 4].length) (baseStart_1822085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1822085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1822085 prefixEnd_1822085 := by exact prefixLift 1822085
  have htrace : WordTrace (prefixWord ++ tailWord_1822085) baseStart_1822085 baseEnd_1822085 := by
    simpa [prefixWord, tailWord_1822085, baseEnd_1822085] using wordTrace_append hprefix tailTrace_1822085
  have hstable : (prefixWord ++ tailWord_1822085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1822085).length < 2 ^ (prefixWord ++ tailWord_1822085).sum := by decide
  have hdescent : baseEnd_1822085 < baseStart_1822085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1822085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1822100 : List Nat := [2, 4, 2, 1, 2, 2, 9]
def baseStart_1822100 : Nat := 118140960795 + 1822100 * 2 ^ 59
def prefixEnd_1822100 : Nat := 4983230072969 + 3 ^ 40 * 1822100 * 2
def baseEnd_1822100 : Nat := 23101558038454969359761

theorem tailTrace_1822100 : CollatzResearch.WordTrace tailWord_1822100 prefixEnd_1822100 23101558038454969359761 := by
  unfold tailWord_1822100
  simp only [CollatzResearch.WordTrace]
  refine ⟨33228723349425182375007877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44304964465900243166677169 33228723349425182375007877)
  ·
    refine ⟨6230385628017221695313977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33228723349425182375007877 6230385628017221695313977)
    ·
      refine ⟨4672789221012916271485483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6230385628017221695313977 4672789221012916271485483)
      ·
        refine ⟨7009183831519374407228225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4672789221012916271485483 7009183831519374407228225)
        ·
          refine ⟨5256887873639530805421169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7009183831519374407228225 5256887873639530805421169)
          ·
            refine ⟨3942665905229648104065877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5256887873639530805421169 3942665905229648104065877)
            ·
              refine ⟨23101558038454969359761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3942665905229648104065877 23101558038454969359761)
              ·
                rfl

theorem cell22_1822100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 9].length) (baseStart_1822100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1822100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1822100 prefixEnd_1822100 := by exact prefixLift 1822100
  have htrace : WordTrace (prefixWord ++ tailWord_1822100) baseStart_1822100 baseEnd_1822100 := by
    simpa [prefixWord, tailWord_1822100, baseEnd_1822100] using wordTrace_append hprefix tailTrace_1822100
  have hstable : (prefixWord ++ tailWord_1822100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1822100).length < 2 ^ (prefixWord ++ tailWord_1822100).sum := by decide
  have hdescent : baseEnd_1822100 < baseStart_1822100 := by decide
  rcases family_descends (prefixWord ++ tailWord_1822100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1822143 : List Nat := [1, 1, 2, 2, 2, 1, 1, 4, 1, 7]
def baseStart_1822143 : Nat := 118140960795 + 1822143 * 2 ^ 59
def prefixEnd_1822143 : Nat := 4983230072969 + 3 ^ 40 * 1822143 * 2
def baseEnd_1822143 : Nat := 623756786817046393888415

theorem tailTrace_1822143 : CollatzResearch.WordTrace tailWord_1822143 prefixEnd_1822143 623756786817046393888415 := by
  unfold tailWord_1822143
  simp only [CollatzResearch.WordTrace]
  refine ⟨66459015037694583093831083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44306010025129722062554055 66459015037694583093831083)
  ·
    refine ⟨99688522556541874640746625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66459015037694583093831083 99688522556541874640746625)
    ·
      refine ⟨74766391917406405980559969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99688522556541874640746625 74766391917406405980559969)
      ·
        refine ⟨56074793938054804485419977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74766391917406405980559969 56074793938054804485419977)
        ·
          refine ⟨42056095453541103364064983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56074793938054804485419977 42056095453541103364064983)
          ·
            refine ⟨63084143180311655046097475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42056095453541103364064983 63084143180311655046097475)
            ·
              refine ⟨94626214770467482569146213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63084143180311655046097475 94626214770467482569146213)
              ·
                refine ⟨17742415269462652981714915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94626214770467482569146213 17742415269462652981714915)
                ·
                  refine ⟨26613622904193979472572373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17742415269462652981714915 26613622904193979472572373)
                  ·
                    refine ⟨623756786817046393888415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26613622904193979472572373 623756786817046393888415)
                    ·
                      rfl

theorem cell22_1822143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 4, 1, 7].length) (baseStart_1822143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1822143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1822143 prefixEnd_1822143 := by exact prefixLift 1822143
  have htrace : WordTrace (prefixWord ++ tailWord_1822143) baseStart_1822143 baseEnd_1822143 := by
    simpa [prefixWord, tailWord_1822143, baseEnd_1822143] using wordTrace_append hprefix tailTrace_1822143
  have hstable : (prefixWord ++ tailWord_1822143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1822143).length < 2 ^ (prefixWord ++ tailWord_1822143).sum := by decide
  have hdescent : baseEnd_1822143 < baseStart_1822143 := by decide
  rcases family_descends (prefixWord ++ tailWord_1822143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1822166 : List Nat := [5, 2, 1, 1, 1, 4, 1, 1, 3, 3]
def baseStart_1822166 : Nat := 118140960795 + 1822166 * 2 ^ 59
def prefixEnd_1822166 : Nat := 4983230072969 + 3 ^ 40 * 1822166 * 2
def baseEnd_1822166 : Nat := 623764660187082000563345

theorem tailTrace_1822166 : CollatzResearch.WordTrace tailWord_1822166 prefixEnd_1822166 623764660187082000563345 := by
  unfold tailWord_1822166
  simp only [CollatzResearch.WordTrace]
  refine ⟨4153740869788203626369897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44306569277740838681278901 4153740869788203626369897)
  ·
    refine ⟨3115305652341152719777423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4153740869788203626369897 3115305652341152719777423)
    ·
      refine ⟨4672958478511729079666135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3115305652341152719777423 4672958478511729079666135)
      ·
        refine ⟨7009437717767593619499203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4672958478511729079666135 7009437717767593619499203)
        ·
          refine ⟨10514156576651390429248805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7009437717767593619499203 10514156576651390429248805)
          ·
            refine ⟨1971404358122135705484151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10514156576651390429248805 1971404358122135705484151)
            ·
              refine ⟨2957106537183203558226227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1971404358122135705484151 2957106537183203558226227)
              ·
                refine ⟨4435659805774805337339341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2957106537183203558226227 4435659805774805337339341)
                ·
                  refine ⟨1663372427165552001502253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4435659805774805337339341 1663372427165552001502253)
                  ·
                    refine ⟨623764660187082000563345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1663372427165552001502253 623764660187082000563345)
                    ·
                      rfl

theorem cell22_1822166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 1, 1, 3, 3].length) (baseStart_1822166 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1822166 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1822166 prefixEnd_1822166 := by exact prefixLift 1822166
  have htrace : WordTrace (prefixWord ++ tailWord_1822166) baseStart_1822166 baseEnd_1822166 := by
    simpa [prefixWord, tailWord_1822166, baseEnd_1822166] using wordTrace_append hprefix tailTrace_1822166
  have hstable : (prefixWord ++ tailWord_1822166).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1822166).length < 2 ^ (prefixWord ++ tailWord_1822166).sum := by decide
  have hdescent : baseEnd_1822166 < baseStart_1822166 := by decide
  rcases family_descends (prefixWord ++ tailWord_1822166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1822175 : List Nat := [1, 1, 2, 3, 3, 1, 2, 2, 3, 4]
def baseStart_1822175 : Nat := 118140960795 + 1822175 * 2 ^ 59
def prefixEnd_1822175 : Nat := 4983230072969 + 3 ^ 40 * 1822175 * 2
def baseEnd_1822175 : Nat := 623767741071008977088317

theorem tailTrace_1822175 : CollatzResearch.WordTrace tailWord_1822175 prefixEnd_1822175 623767741071008977088317 := by
  unfold tailWord_1822175
  simp only [CollatzResearch.WordTrace]
  refine ⟨66460182173578652558995979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44306788115719101705997319 66460182173578652558995979)
  ·
    refine ⟨99690273260367978838493969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66460182173578652558995979 99690273260367978838493969)
    ·
      refine ⟨74767704945275984128870477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99690273260367978838493969 74767704945275984128870477)
      ·
        refine ⟨28037889354478494048326429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74767704945275984128870477 28037889354478494048326429)
        ·
          refine ⟨10514208507929435268122411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28037889354478494048326429 10514208507929435268122411)
          ·
            refine ⟨15771312761894152902183617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10514208507929435268122411 15771312761894152902183617)
            ·
              refine ⟨11828484571420614676637713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15771312761894152902183617 11828484571420614676637713)
              ·
                refine ⟨8871363428565461007478285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11828484571420614676637713 8871363428565461007478285)
                ·
                  refine ⟨3326761285712047877804357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8871363428565461007478285 3326761285712047877804357)
                  ·
                    refine ⟨623767741071008977088317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3326761285712047877804357 623767741071008977088317)
                    ·
                      rfl

theorem cell22_1822175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 2, 3, 4].length) (baseStart_1822175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1822175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1822175 prefixEnd_1822175 := by exact prefixLift 1822175
  have htrace : WordTrace (prefixWord ++ tailWord_1822175) baseStart_1822175 baseEnd_1822175 := by
    simpa [prefixWord, tailWord_1822175, baseEnd_1822175] using wordTrace_append hprefix tailTrace_1822175
  have hstable : (prefixWord ++ tailWord_1822175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1822175).length < 2 ^ (prefixWord ++ tailWord_1822175).sum := by decide
  have hdescent : baseEnd_1822175 < baseStart_1822175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1822175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1822179 : List Nat := [1, 1, 1, 6, 2, 3, 2, 1, 5]
def baseStart_1822179 : Nat := 118140960795 + 1822179 * 2 ^ 59
def prefixEnd_1822179 : Nat := 4983230072969 + 3 ^ 40 * 1822179 * 2
def baseEnd_1822179 : Nat := 207923036784251433329435

theorem tailTrace_1822179 : CollatzResearch.WordTrace tailWord_1822179 prefixEnd_1822179 207923036784251433329435 := by
  unfold tailWord_1822179
  simp only [CollatzResearch.WordTrace]
  refine ⟨66460328065564161242141591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44306885377042774161427727 66460328065564161242141591)
  ·
    refine ⟨99690492098346241863212387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66460328065564161242141591 99690492098346241863212387)
    ·
      refine ⟨149535738147519362794818581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99690492098346241863212387 149535738147519362794818581)
      ·
        refine ⟨7009487725664970131007121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 149535738147519362794818581 7009487725664970131007121)
        ·
          refine ⟨5257115794248727598255341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7009487725664970131007121 5257115794248727598255341)
          ·
            refine ⟨1971418422843272849345753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5257115794248727598255341 1971418422843272849345753)
            ·
              refine ⟨1478563817132454637009315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1971418422843272849345753 1478563817132454637009315)
              ·
                refine ⟨2217845725698681955513973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1478563817132454637009315 2217845725698681955513973)
                ·
                  refine ⟨207923036784251433329435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2217845725698681955513973 207923036784251433329435)
                  ·
                    rfl

theorem cell22_1822179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 2, 1, 5].length) (baseStart_1822179 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1822179 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1822179 prefixEnd_1822179 := by exact prefixLift 1822179
  have htrace : WordTrace (prefixWord ++ tailWord_1822179) baseStart_1822179 baseEnd_1822179 := by
    simpa [prefixWord, tailWord_1822179, baseEnd_1822179] using wordTrace_append hprefix tailTrace_1822179
  have hstable : (prefixWord ++ tailWord_1822179).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1822179).length < 2 ^ (prefixWord ++ tailWord_1822179).sum := by decide
  have hdescent : baseEnd_1822179 < baseStart_1822179 := by decide
  rcases family_descends (prefixWord ++ tailWord_1822179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1822190 : List Nat := [4, 1, 2, 1, 2, 1, 2, 1, 8]
def baseStart_1822190 : Nat := 118140960795 + 1822190 * 2 ^ 59
def prefixEnd_1822190 : Nat := 4983230072969 + 3 ^ 40 * 1822190 * 2
def baseEnd_1822190 : Nat := 207924291959184645987757

theorem tailTrace_1822190 : CollatzResearch.WordTrace tailWord_1822190 prefixEnd_1822190 207924291959184645987757 := by
  unfold tailWord_1822190
  simp only [CollatzResearch.WordTrace]
  refine ⟨8307591158565538765099003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44307152845682873413861349 8307591158565538765099003)
  ·
    refine ⟨12461386737848308147648505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8307591158565538765099003 12461386737848308147648505)
    ·
      refine ⟨9346040053386231110736379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12461386737848308147648505 9346040053386231110736379)
      ·
        refine ⟨14019060080079346666104569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9346040053386231110736379 14019060080079346666104569)
        ·
          refine ⟨10514295060059509999578427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14019060080079346666104569 10514295060059509999578427)
          ·
            refine ⟨15771442590089264999367641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10514295060059509999578427 15771442590089264999367641)
            ·
              refine ⟨11828581942566948749525731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15771442590089264999367641 11828581942566948749525731)
              ·
                refine ⟨17742872913850423124288597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11828581942566948749525731 17742872913850423124288597)
                ·
                  refine ⟨207924291959184645987757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17742872913850423124288597 207924291959184645987757)
                  ·
                    rfl

theorem cell22_1822190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 1, 8].length) (baseStart_1822190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1822190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1822190 prefixEnd_1822190 := by exact prefixLift 1822190
  have htrace : WordTrace (prefixWord ++ tailWord_1822190) baseStart_1822190 baseEnd_1822190 := by
    simpa [prefixWord, tailWord_1822190, baseEnd_1822190] using wordTrace_append hprefix tailTrace_1822190
  have hstable : (prefixWord ++ tailWord_1822190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1822190).length < 2 ^ (prefixWord ++ tailWord_1822190).sum := by decide
  have hdescent : baseEnd_1822190 < baseStart_1822190 := by decide
  rcases family_descends (prefixWord ++ tailWord_1822190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1822192 : List Nat := [2, 1, 1, 1, 3, 4, 3, 2, 1, 4]
def baseStart_1822192 : Nat := 118140960795 + 1822192 * 2 ^ 59
def prefixEnd_1822192 : Nat := 4983230072969 + 3 ^ 40 * 1822192 * 2
def baseEnd_1822192 : Nat := 623773560518426599413265

theorem tailTrace_1822192 : CollatzResearch.WordTrace tailWord_1822192 prefixEnd_1822192 623773560518426599413265 := by
  unfold tailWord_1822192
  simp only [CollatzResearch.WordTrace]
  refine ⟨33230401107258532231182415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44307201476344709641576553 33230401107258532231182415)
  ·
    refine ⟨49845601660887798346773623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33230401107258532231182415 49845601660887798346773623)
    ·
      refine ⟨74768402491331697520160435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49845601660887798346773623 74768402491331697520160435)
      ·
        refine ⟨112152603736997546280240653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74768402491331697520160435 112152603736997546280240653)
        ·
          refine ⟨42057226401374079855090245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112152603736997546280240653 42057226401374079855090245)
          ·
            refine ⟨7885729950257639972829421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42057226401374079855090245 7885729950257639972829421)
            ·
              refine ⟨2957148731346614989811033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7885729950257639972829421 2957148731346614989811033)
              ·
                refine ⟨2217861548509961242358275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2957148731346614989811033 2217861548509961242358275)
                ·
                  refine ⟨3326792322764941863537413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2217861548509961242358275 3326792322764941863537413)
                  ·
                    refine ⟨623773560518426599413265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3326792322764941863537413 623773560518426599413265)
                    ·
                      rfl

theorem cell22_1822192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 3, 2, 1, 4].length) (baseStart_1822192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1822192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1822192 prefixEnd_1822192 := by exact prefixLift 1822192
  have htrace : WordTrace (prefixWord ++ tailWord_1822192) baseStart_1822192 baseEnd_1822192 := by
    simpa [prefixWord, tailWord_1822192, baseEnd_1822192] using wordTrace_append hprefix tailTrace_1822192
  have hstable : (prefixWord ++ tailWord_1822192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1822192).length < 2 ^ (prefixWord ++ tailWord_1822192).sum := by decide
  have hdescent : baseEnd_1822192 < baseStart_1822192 := by decide
  rcases family_descends (prefixWord ++ tailWord_1822192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1822205 : List Nat := [1, 4, 1, 1, 1, 4, 1, 1, 3, 5]
def baseStart_1822205 : Nat := 118140960795 + 1822205 * 2 ^ 59
def prefixEnd_1822205 : Nat := 4983230072969 + 3 ^ 40 * 1822205 * 2
def baseEnd_1822205 : Nat := 623778010684098898838225

theorem tailTrace_1822205 : CollatzResearch.WordTrace tailWord_1822205 prefixEnd_1822205 623778010684098898838225 := by
  unfold tailWord_1822205
  simp only [CollatzResearch.WordTrace]
  refine ⟨66461276363469967682588069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44307517575646645121725379 66461276363469967682588069)
  ·
    refine ⟨12461489318150618940485263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66461276363469967682588069 12461489318150618940485263)
    ·
      refine ⟨18692233977225928410727895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12461489318150618940485263 18692233977225928410727895)
      ·
        refine ⟨28038350965838892616091843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18692233977225928410727895 28038350965838892616091843)
        ·
          refine ⟨42057526448758338924137765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28038350965838892616091843 42057526448758338924137765)
          ·
            refine ⟨7885786209142188548275831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42057526448758338924137765 7885786209142188548275831)
            ·
              refine ⟨11828679313713282822413747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7885786209142188548275831 11828679313713282822413747)
              ·
                refine ⟨17743018970569924233620621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11828679313713282822413747 17743018970569924233620621)
                ·
                  refine ⟨6653632113963721587607733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17743018970569924233620621 6653632113963721587607733)
                  ·
                    refine ⟨623778010684098898838225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6653632113963721587607733 623778010684098898838225)
                    ·
                      rfl

theorem cell22_1822205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 1, 3, 5].length) (baseStart_1822205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1822205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1822205 prefixEnd_1822205 := by exact prefixLift 1822205
  have htrace : WordTrace (prefixWord ++ tailWord_1822205) baseStart_1822205 baseEnd_1822205 := by
    simpa [prefixWord, tailWord_1822205, baseEnd_1822205] using wordTrace_append hprefix tailTrace_1822205
  have hstable : (prefixWord ++ tailWord_1822205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1822205).length < 2 ^ (prefixWord ++ tailWord_1822205).sum := by decide
  have hdescent : baseEnd_1822205 < baseStart_1822205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1822205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1822254 : List Nat := [4, 1, 3, 1, 2, 1, 3, 1, 2, 4]
def baseStart_1822254 : Nat := 118140960795 + 1822254 * 2 ^ 59
def prefixEnd_1822254 : Nat := 4983230072969 + 3 ^ 40 * 1822254 * 2
def baseEnd_1822254 : Nat := 623794784385479104363075

theorem tailTrace_1822254 : CollatzResearch.WordTrace tailWord_1822254 prefixEnd_1822254 623794784385479104363075 := by
  unfold tailWord_1822254
  simp only [CollatzResearch.WordTrace]
  refine ⟨8307882942536556131390227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44308709026861632700747877 8307882942536556131390227)
  ·
    refine ⟨12461824413804834197085341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8307882942536556131390227 12461824413804834197085341)
    ·
      refine ⟨4673184155176812823907003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12461824413804834197085341 4673184155176812823907003)
      ·
        refine ⟨7009776232765219235860505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4673184155176812823907003 7009776232765219235860505)
        ·
          refine ⟨5257332174573914426895379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7009776232765219235860505 5257332174573914426895379)
          ·
            refine ⟨7885998261860871640343069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5257332174573914426895379 7885998261860871640343069)
            ·
              refine ⟨2957249348197826865128651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7885998261860871640343069 2957249348197826865128651)
              ·
                refine ⟨4435874022296740297692977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2957249348197826865128651 4435874022296740297692977)
                ·
                  refine ⟨3326905516722555223269733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4435874022296740297692977 3326905516722555223269733)
                  ·
                    refine ⟨623794784385479104363075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3326905516722555223269733 623794784385479104363075)
                    ·
                      rfl

theorem cell22_1822254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_1822254 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1822254 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1822254 prefixEnd_1822254 := by exact prefixLift 1822254
  have htrace : WordTrace (prefixWord ++ tailWord_1822254) baseStart_1822254 baseEnd_1822254 := by
    simpa [prefixWord, tailWord_1822254, baseEnd_1822254] using wordTrace_append hprefix tailTrace_1822254
  have hstable : (prefixWord ++ tailWord_1822254).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1822254).length < 2 ^ (prefixWord ++ tailWord_1822254).sum := by decide
  have hdescent : baseEnd_1822254 < baseStart_1822254 := by decide
  rcases family_descends (prefixWord ++ tailWord_1822254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1822284 : List Nat := [2, 2, 1, 3, 1, 4, 2, 1, 3, 3]
def baseStart_1822284 : Nat := 118140960795 + 1822284 * 2 ^ 59
def prefixEnd_1822284 : Nat := 4983230072969 + 3 ^ 40 * 1822284 * 2
def baseEnd_1822284 : Nat := 623805053998569026112983

theorem tailTrace_1822284 : CollatzResearch.WordTrace tailWord_1822284 prefixEnd_1822284 623805053998569026112983 := by
  unfold tailWord_1822284
  simp only [CollatzResearch.WordTrace]
  refine ⟨33232078865091882087356953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44309438486789176116475937 33232078865091882087356953)
  ·
    refine ⟨24924059148818911565517715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33232078865091882087356953 24924059148818911565517715)
    ·
      refine ⟨37386088723228367348276573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24924059148818911565517715 37386088723228367348276573)
      ·
        refine ⟨14019783271210637755603715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37386088723228367348276573 14019783271210637755603715)
        ·
          refine ⟨21029674906815956633405573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14019783271210637755603715 21029674906815956633405573)
          ·
            refine ⟨3943064045027991868763545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21029674906815956633405573 3943064045027991868763545)
            ·
              refine ⟨2957298033770993901572659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3943064045027991868763545 2957298033770993901572659)
              ·
                refine ⟨4435947050656490852358989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2957298033770993901572659 4435947050656490852358989)
                ·
                  refine ⟨1663480143996184069634621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4435947050656490852358989 1663480143996184069634621)
                  ·
                    refine ⟨623805053998569026112983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1663480143996184069634621 623805053998569026112983)
                    ·
                      rfl

theorem cell22_1822284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 2, 1, 3, 3].length) (baseStart_1822284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1822284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1822284 prefixEnd_1822284 := by exact prefixLift 1822284
  have htrace : WordTrace (prefixWord ++ tailWord_1822284) baseStart_1822284 baseEnd_1822284 := by
    simpa [prefixWord, tailWord_1822284, baseEnd_1822284] using wordTrace_append hprefix tailTrace_1822284
  have hstable : (prefixWord ++ tailWord_1822284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1822284).length < 2 ^ (prefixWord ++ tailWord_1822284).sum := by decide
  have hdescent : baseEnd_1822284 < baseStart_1822284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1822284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1822391 : List Nat := [1, 1, 3, 1, 5, 2, 2, 2, 2, 3]
def baseStart_1822391 : Nat := 118140960795 + 1822391 * 2 ^ 59
def prefixEnd_1822391 : Nat := 4983230072969 + 3 ^ 40 * 1822391 * 2
def baseEnd_1822391 : Nat := 623841682285256413687655

theorem tailTrace_1822391 : CollatzResearch.WordTrace tailWord_1822391 prefixEnd_1822391 623841682285256413687655 := by
  unfold tailWord_1822391
  simp only [CollatzResearch.WordTrace]
  refine ⟨66468060340796121448859027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44312040227197414299239351 66468060340796121448859027)
  ·
    refine ⟨99702090511194182173288541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66468060340796121448859027 99702090511194182173288541)
    ·
      refine ⟨37388283941697818314983203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99702090511194182173288541 37388283941697818314983203)
      ·
        refine ⟨56082425912546727472474805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37388283941697818314983203 56082425912546727472474805)
        ·
          refine ⟨5257727429301255700544513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56082425912546727472474805 5257727429301255700544513)
          ·
            refine ⟨3943295571975941775408385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5257727429301255700544513 3943295571975941775408385)
            ·
              refine ⟨2957471678981956331556289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3943295571975941775408385 2957471678981956331556289)
              ·
                refine ⟨2218103759236467248667217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2957471678981956331556289 2218103759236467248667217)
                ·
                  refine ⟨1663577819427350436500413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2218103759236467248667217 1663577819427350436500413)
                  ·
                    refine ⟨623841682285256413687655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1663577819427350436500413 623841682285256413687655)
                    ·
                      rfl

theorem cell22_1822391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 2, 2, 2, 3].length) (baseStart_1822391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1822391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1822391 prefixEnd_1822391 := by exact prefixLift 1822391
  have htrace : WordTrace (prefixWord ++ tailWord_1822391) baseStart_1822391 baseEnd_1822391 := by
    simpa [prefixWord, tailWord_1822391, baseEnd_1822391] using wordTrace_append hprefix tailTrace_1822391
  have hstable : (prefixWord ++ tailWord_1822391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1822391).length < 2 ^ (prefixWord ++ tailWord_1822391).sum := by decide
  have hdescent : baseEnd_1822391 < baseStart_1822391 := by decide
  rcases family_descends (prefixWord ++ tailWord_1822391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1822447 : List Nat := [1, 1, 2, 1, 5, 1, 1, 1, 4, 5]
def baseStart_1822447 : Nat := 118140960795 + 1822447 * 2 ^ 59
def prefixEnd_1822447 : Nat := 4983230072969 + 3 ^ 40 * 1822447 * 2
def baseEnd_1822447 : Nat := 623860852229690934287483

theorem tailTrace_1822447 : CollatzResearch.WordTrace tailWord_1822447 prefixEnd_1822447 623860852229690934287483 := by
  unfold tailWord_1822447
  simp only [CollatzResearch.WordTrace]
  refine ⟨66470102828593243012897595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44313401885728828675265063 66470102828593243012897595)
  ·
    refine ⟨99705154242889864519346393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66470102828593243012897595 99705154242889864519346393)
    ·
      refine ⟨74778865682167398389509795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99705154242889864519346393 74778865682167398389509795)
      ·
        refine ⟨112168298523251097584264693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74778865682167398389509795 112168298523251097584264693)
        ·
          refine ⟨10515777986554790398524815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 112168298523251097584264693 10515777986554790398524815)
          ·
            refine ⟨15773666979832185597787223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10515777986554790398524815 15773666979832185597787223)
            ·
              refine ⟨23660500469748278396680835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15773666979832185597787223 23660500469748278396680835)
              ·
                refine ⟨35490750704622417595021253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23660500469748278396680835 35490750704622417595021253)
                ·
                  refine ⟨6654515757116703299066485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35490750704622417595021253 6654515757116703299066485)
                  ·
                    refine ⟨623860852229690934287483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6654515757116703299066485 623860852229690934287483)
                    ·
                      rfl

theorem cell22_1822447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 4, 5].length) (baseStart_1822447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1822447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1822447 prefixEnd_1822447 := by exact prefixLift 1822447
  have htrace : WordTrace (prefixWord ++ tailWord_1822447) baseStart_1822447 baseEnd_1822447 := by
    simpa [prefixWord, tailWord_1822447, baseEnd_1822447] using wordTrace_append hprefix tailTrace_1822447
  have hstable : (prefixWord ++ tailWord_1822447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1822447).length < 2 ^ (prefixWord ++ tailWord_1822447).sum := by decide
  have hdescent : baseEnd_1822447 < baseStart_1822447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1822447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1822449 : List Nat := [1, 2, 2, 2, 2, 3, 3, 2, 5]
def baseStart_1822449 : Nat := 118140960795 + 1822449 * 2 ^ 59
def prefixEnd_1822449 : Nat := 4983230072969 + 3 ^ 40 * 1822449 * 2
def baseEnd_1822449 : Nat := 207953845623521198579159

theorem tailTrace_1822449 : CollatzResearch.WordTrace tailWord_1822449 prefixEnd_1822449 207953845623521198579159 := by
  unfold tailWord_1822449
  simp only [CollatzResearch.WordTrace]
  refine ⟨66470175774585997354470401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44313450516390664902980267 66470175774585997354470401)
  ·
    refine ⟨49852631830939498015852801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66470175774585997354470401 49852631830939498015852801)
    ·
      refine ⟨37389473873204623511889601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49852631830939498015852801 37389473873204623511889601)
      ·
        refine ⟨28042105404903467633917201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37389473873204623511889601 28042105404903467633917201)
        ·
          refine ⟨21031579053677600725437901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28042105404903467633917201 21031579053677600725437901)
          ·
            refine ⟨7886842145129100272039213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21031579053677600725437901 7886842145129100272039213)
            ·
              refine ⟨2957565804423412602014705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7886842145129100272039213 2957565804423412602014705)
              ·
                refine ⟨2218174353317559451511029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2957565804423412602014705 2218174353317559451511029)
                ·
                  refine ⟨207953845623521198579159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2218174353317559451511029 207953845623521198579159)
                  ·
                    rfl

theorem cell22_1822449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 3, 2, 5].length) (baseStart_1822449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1822449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1822449 prefixEnd_1822449 := by exact prefixLift 1822449
  have htrace : WordTrace (prefixWord ++ tailWord_1822449) baseStart_1822449 baseEnd_1822449 := by
    simpa [prefixWord, tailWord_1822449, baseEnd_1822449] using wordTrace_append hprefix tailTrace_1822449
  have hstable : (prefixWord ++ tailWord_1822449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1822449).length < 2 ^ (prefixWord ++ tailWord_1822449).sum := by decide
  have hdescent : baseEnd_1822449 < baseStart_1822449 := by decide
  rcases family_descends (prefixWord ++ tailWord_1822449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1822556 : List Nat := [2, 2, 4, 2, 3, 9]
def baseStart_1822556 : Nat := 118140960795 + 1822556 * 2 ^ 59
def prefixEnd_1822556 : Nat := 4983230072969 + 3 ^ 40 * 1822556 * 2
def baseEnd_1822556 : Nat := 7702446483422851645829

theorem tailTrace_1822556 : CollatzResearch.WordTrace tailWord_1822556 prefixEnd_1822556 7702446483422851645829 := by
  unfold tailWord_1822556
  simp only [CollatzResearch.WordTrace]
  refine ⟨33237039192599177314307761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44316052256798903085743681 33237039192599177314307761)
  ·
    refine ⟨24927779394449382985730821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33237039192599177314307761 24927779394449382985730821)
    ·
      refine ⟨4673958636459259309824529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24927779394449382985730821 4673958636459259309824529)
      ·
        refine ⟨3505468977344444482368397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4673958636459259309824529 3505468977344444482368397)
        ·
          refine ⟨1314550866504166680888149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3505468977344444482368397 1314550866504166680888149)
          ·
            refine ⟨7702446483422851645829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1314550866504166680888149 7702446483422851645829)
            ·
              rfl

theorem cell22_1822556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 9].length) (baseStart_1822556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1822556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1822556 prefixEnd_1822556 := by exact prefixLift 1822556
  have htrace : WordTrace (prefixWord ++ tailWord_1822556) baseStart_1822556 baseEnd_1822556 := by
    simpa [prefixWord, tailWord_1822556, baseEnd_1822556] using wordTrace_append hprefix tailTrace_1822556
  have hstable : (prefixWord ++ tailWord_1822556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1822556).length < 2 ^ (prefixWord ++ tailWord_1822556).sum := by decide
  have hdescent : baseEnd_1822556 < baseStart_1822556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1822556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1822618 : List Nat := [3, 1, 1, 4, 2, 3, 1, 2, 5]
def baseStart_1822618 : Nat := 118140960795 + 1822618 * 2 ^ 59
def prefixEnd_1822618 : Nat := 4983230072969 + 3 ^ 40 * 1822618 * 2
def baseEnd_1822618 : Nat := 207973129674767829420653

theorem tailTrace_1822618 : CollatzResearch.WordTrace tailWord_1822618 prefixEnd_1822618 207973129674767829420653 := by
  unfold tailWord_1822618
  simp only [CollatzResearch.WordTrace]
  refine ⟨16619084927743434804343127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44317559807315826144915005 16619084927743434804343127)
  ·
    refine ⟨24928627391615152206514691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16619084927743434804343127 24928627391615152206514691)
    ·
      refine ⟨37392941087422728309772037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24928627391615152206514691 37392941087422728309772037)
      ·
        refine ⟨7011176453891761558082257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37392941087422728309772037 7011176453891761558082257)
        ·
          refine ⟨5258382340418821168561693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7011176453891761558082257 5258382340418821168561693)
          ·
            refine ⟨1971893377657057938210635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5258382340418821168561693 1971893377657057938210635)
            ·
              refine ⟨2957840066485586907315953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1971893377657057938210635 2957840066485586907315953)
              ·
                refine ⟨2218380049864190180486965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2957840066485586907315953 2218380049864190180486965)
                ·
                  refine ⟨207973129674767829420653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2218380049864190180486965 207973129674767829420653)
                  ·
                    rfl

theorem cell22_1822618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 1, 2, 5].length) (baseStart_1822618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1822618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1822618 prefixEnd_1822618 := by exact prefixLift 1822618
  have htrace : WordTrace (prefixWord ++ tailWord_1822618) baseStart_1822618 baseEnd_1822618 := by
    simpa [prefixWord, tailWord_1822618, baseEnd_1822618] using wordTrace_append hprefix tailTrace_1822618
  have hstable : (prefixWord ++ tailWord_1822618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1822618).length < 2 ^ (prefixWord ++ tailWord_1822618).sum := by decide
  have hdescent : baseEnd_1822618 < baseStart_1822618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1822618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1822622 : List Nat := [4, 3, 1, 3, 1, 1, 2, 1, 3, 3]
def baseStart_1822622 : Nat := 118140960795 + 1822622 * 2 ^ 59
def prefixEnd_1822622 : Nat := 4983230072969 + 3 ^ 40 * 1822622 * 2
def baseEnd_1822622 : Nat := 623920758306048811161947

theorem tailTrace_1822622 : CollatzResearch.WordTrace tailWord_1822622 prefixEnd_1822622 623920758306048811161947 := by
  unfold tailWord_1822622
  simp only [CollatzResearch.WordTrace]
  refine ⟨8309560700369905987564765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44317657068639498600345413 8309560700369905987564765)
  ·
    refine ⟨3116085262638714745336787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8309560700369905987564765 3116085262638714745336787)
    ·
      refine ⟨4674127893958072118005181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3116085262638714745336787 4674127893958072118005181)
      ·
        refine ⟨1752797960234277044251943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4674127893958072118005181 1752797960234277044251943)
        ·
          refine ⟨2629196940351415566377915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1752797960234277044251943 2629196940351415566377915)
          ·
            refine ⟨3943795410527123349566873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2629196940351415566377915 3943795410527123349566873)
            ·
              refine ⟨2957846557895342512175155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3943795410527123349566873 2957846557895342512175155)
              ·
                refine ⟨4436769836843013768262733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2957846557895342512175155 4436769836843013768262733)
                ·
                  refine ⟨1663788688816130163098525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4436769836843013768262733 1663788688816130163098525)
                  ·
                    refine ⟨623920758306048811161947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1663788688816130163098525 623920758306048811161947)
                    ·
                      rfl

theorem cell22_1822622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 2, 1, 3, 3].length) (baseStart_1822622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1822622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1822622 prefixEnd_1822622 := by exact prefixLift 1822622
  have htrace : WordTrace (prefixWord ++ tailWord_1822622) baseStart_1822622 baseEnd_1822622 := by
    simpa [prefixWord, tailWord_1822622, baseEnd_1822622] using wordTrace_append hprefix tailTrace_1822622
  have hstable : (prefixWord ++ tailWord_1822622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1822622).length < 2 ^ (prefixWord ++ tailWord_1822622).sum := by decide
  have hdescent : baseEnd_1822622 < baseStart_1822622 := by decide
  rcases family_descends (prefixWord ++ tailWord_1822622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1822691 : List Nat := [1, 1, 1, 6, 1, 3, 2, 7]
def baseStart_1822691 : Nat := 118140960795 + 1822691 * 2 ^ 59
def prefixEnd_1822691 : Nat := 4983230072969 + 3 ^ 40 * 1822691 * 2
def baseEnd_1822691 : Nat := 69327153157350625687415

theorem tailTrace_1822691 : CollatzResearch.WordTrace tailWord_1822691 prefixEnd_1822691 69327153157350625687415 := by
  unfold tailWord_1822691
  simp only [CollatzResearch.WordTrace]
  refine ⟨66479002239709272684779927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44319334826472848456519951 66479002239709272684779927)
  ·
    refine ⟨99718503359563909027169891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66479002239709272684779927 99718503359563909027169891)
    ·
      refine ⟨149577755039345863540754837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99718503359563909027169891 149577755039345863540754837)
      ·
        refine ⟨7011457267469337353472883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 149577755039345863540754837 7011457267469337353472883)
        ·
          refine ⟨10517185901204006030209325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7011457267469337353472883 10517185901204006030209325)
          ·
            refine ⟨3943944712951502261328497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10517185901204006030209325 3943944712951502261328497)
            ·
              refine ⟨2957958534713626695996373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3943944712951502261328497 2957958534713626695996373)
              ·
                refine ⟨69327153157350625687415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2957958534713626695996373 69327153157350625687415)
                ·
                  rfl

theorem cell22_1822691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 2, 7].length) (baseStart_1822691 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1822691 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1822691 prefixEnd_1822691 := by exact prefixLift 1822691
  have htrace : WordTrace (prefixWord ++ tailWord_1822691) baseStart_1822691 baseEnd_1822691 := by
    simpa [prefixWord, tailWord_1822691, baseEnd_1822691] using wordTrace_append hprefix tailTrace_1822691
  have hstable : (prefixWord ++ tailWord_1822691).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1822691).length < 2 ^ (prefixWord ++ tailWord_1822691).sum := by decide
  have hdescent : baseEnd_1822691 < baseStart_1822691 := by decide
  rcases family_descends (prefixWord ++ tailWord_1822691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1822695 : List Nat := [1, 1, 5, 2, 3, 1, 1, 3, 2, 3]
def baseStart_1822695 : Nat := 118140960795 + 1822695 * 2 ^ 59
def prefixEnd_1822695 : Nat := 4983230072969 + 3 ^ 40 * 1822695 * 2
def baseEnd_1822695 : Nat := 623945747697900954086723

theorem tailTrace_1822695 : CollatzResearch.WordTrace tailWord_1822695 prefixEnd_1822695 623945747697900954086723 := by
  unfold tailWord_1822695
  simp only [CollatzResearch.WordTrace]
  refine ⟨66479148131694781367925539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44319432087796520911950359 66479148131694781367925539)
  ·
    refine ⟨99718722197542172051888309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66479148131694781367925539 99718722197542172051888309)
    ·
      refine ⟨9348630206019578629864529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 99718722197542172051888309 9348630206019578629864529)
      ·
        refine ⟨7011472654514683972398397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9348630206019578629864529 7011472654514683972398397)
        ·
          refine ⟨2629302245443006489649399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7011472654514683972398397 2629302245443006489649399)
          ·
            refine ⟨3943953368164509734474099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2629302245443006489649399 3943953368164509734474099)
            ·
              refine ⟨5915930052246764601711149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3943953368164509734474099 5915930052246764601711149)
              ·
                refine ⟨2218473769592536725641681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5915930052246764601711149 2218473769592536725641681)
                ·
                  refine ⟨1663855327194402544231261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2218473769592536725641681 1663855327194402544231261)
                  ·
                    refine ⟨623945747697900954086723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1663855327194402544231261 623945747697900954086723)
                    ·
                      rfl

theorem cell22_1822695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 3, 2, 3].length) (baseStart_1822695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1822695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1822695 prefixEnd_1822695 := by exact prefixLift 1822695
  have htrace : WordTrace (prefixWord ++ tailWord_1822695) baseStart_1822695 baseEnd_1822695 := by
    simpa [prefixWord, tailWord_1822695, baseEnd_1822695] using wordTrace_append hprefix tailTrace_1822695
  have hstable : (prefixWord ++ tailWord_1822695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1822695).length < 2 ^ (prefixWord ++ tailWord_1822695).sum := by decide
  have hdescent : baseEnd_1822695 < baseStart_1822695 := by decide
  rcases family_descends (prefixWord ++ tailWord_1822695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1822710 : List Nat := [5, 1, 1, 1, 4, 1, 2, 1, 2, 4]
def baseStart_1822710 : Nat := 118140960795 + 1822710 * 2 ^ 59
def prefixEnd_1822710 : Nat := 4983230072969 + 3 ^ 40 * 1822710 * 2
def baseEnd_1822710 : Nat := 623950882504445914961677

theorem tailTrace_1822710 : CollatzResearch.WordTrace tailWord_1822710 prefixEnd_1822710 623950882504445914961677 := by
  unfold tailWord_1822710
  simp only [CollatzResearch.WordTrace]
  refine ⟨4154980951665027433107599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44319796817760292619814389 4154980951665027433107599)
  ·
    refine ⟨6232471427497541149661399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4154980951665027433107599 6232471427497541149661399)
    ·
      refine ⟨9348707141246311724492099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6232471427497541149661399 9348707141246311724492099)
      ·
        refine ⟨14023060711869467586738149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9348707141246311724492099 14023060711869467586738149)
        ·
          refine ⟨2629323883475525172513403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14023060711869467586738149 2629323883475525172513403)
          ·
            refine ⟨3943985825213287758770105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2629323883475525172513403 3943985825213287758770105)
            ·
              refine ⟨2957989368909965819077579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3943985825213287758770105 2957989368909965819077579)
              ·
                refine ⟨4436984053364948728616369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2957989368909965819077579 4436984053364948728616369)
                ·
                  refine ⟨3327738040023711546462277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4436984053364948728616369 3327738040023711546462277)
                  ·
                    refine ⟨623950882504445914961677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3327738040023711546462277 623950882504445914961677)
                    ·
                      rfl

theorem cell22_1822710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 2, 1, 2, 4].length) (baseStart_1822710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1822710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1822710 prefixEnd_1822710 := by exact prefixLift 1822710
  have htrace : WordTrace (prefixWord ++ tailWord_1822710) baseStart_1822710 baseEnd_1822710 := by
    simpa [prefixWord, tailWord_1822710, baseEnd_1822710] using wordTrace_append hprefix tailTrace_1822710
  have hstable : (prefixWord ++ tailWord_1822710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1822710).length < 2 ^ (prefixWord ++ tailWord_1822710).sum := by decide
  have hdescent : baseEnd_1822710 < baseStart_1822710 := by decide
  rcases family_descends (prefixWord ++ tailWord_1822710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1822719 : List Nat := [1, 1, 2, 2, 1, 2, 1, 3, 9]
def baseStart_1822719 : Nat := 118140960795 + 1822719 * 2 ^ 59
def prefixEnd_1822719 : Nat := 4983230072969 + 3 ^ 40 * 1822719 * 2
def baseEnd_1822719 : Nat := 207984654462790963828883

theorem tailTrace_1822719 : CollatzResearch.WordTrace tailWord_1822719 prefixEnd_1822719 207984654462790963828883 := by
  unfold tailWord_1822719
  simp only [CollatzResearch.WordTrace]
  refine ⟨66480023483607833466799211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44320015655738555644532807 66480023483607833466799211)
  ·
    refine ⟨99720035225411750200198817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66480023483607833466799211 99720035225411750200198817)
    ·
      refine ⟨74790026419058812650149113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99720035225411750200198817 74790026419058812650149113)
      ·
        refine ⟨56092519814294109487611835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74790026419058812650149113 56092519814294109487611835)
        ·
          refine ⟨84138779721441164231417753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56092519814294109487611835 84138779721441164231417753)
          ·
            refine ⟨63104084791080873173563315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84138779721441164231417753 63104084791080873173563315)
            ·
              refine ⟨94656127186621309760344973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63104084791080873173563315 94656127186621309760344973)
              ·
                refine ⟨35496047694982991160129365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94656127186621309760344973 35496047694982991160129365)
                ·
                  refine ⟨207984654462790963828883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 35496047694982991160129365 207984654462790963828883)
                  ·
                    rfl

theorem cell22_1822719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 9].length) (baseStart_1822719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1822719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1822719 prefixEnd_1822719 := by exact prefixLift 1822719
  have htrace : WordTrace (prefixWord ++ tailWord_1822719) baseStart_1822719 baseEnd_1822719 := by
    simpa [prefixWord, tailWord_1822719, baseEnd_1822719] using wordTrace_append hprefix tailTrace_1822719
  have hstable : (prefixWord ++ tailWord_1822719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1822719).length < 2 ^ (prefixWord ++ tailWord_1822719).sum := by decide
  have hdescent : baseEnd_1822719 < baseStart_1822719 := by decide
  rcases family_descends (prefixWord ++ tailWord_1822719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1822751 : List Nat := [1, 1, 2, 4, 1, 2, 3, 1, 2, 5]
def baseStart_1822751 : Nat := 118140960795 + 1822751 * 2 ^ 59
def prefixEnd_1822751 : Nat := 4983230072969 + 3 ^ 40 * 1822751 * 2
def baseEnd_1822751 : Nat := 623964917642335474686551

theorem tailTrace_1822751 : CollatzResearch.WordTrace tailWord_1822751 prefixEnd_1822751 623964917642335474686551 := by
  unfold tailWord_1822751
  simp only [CollatzResearch.WordTrace]
  refine ⟨66481190619491902931964107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44320793746327935287976071 66481190619491902931964107)
  ·
    refine ⟨99721785929237854397946161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66481190619491902931964107 99721785929237854397946161)
    ·
      refine ⟨74791339446928390798459621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99721785929237854397946161 74791339446928390798459621)
      ·
        refine ⟨14023376146299073274711179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74791339446928390798459621 14023376146299073274711179)
        ·
          refine ⟨21035064219448609912066769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14023376146299073274711179 21035064219448609912066769)
          ·
            refine ⟨15776298164586457434050077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21035064219448609912066769 15776298164586457434050077)
            ·
              refine ⟨5916111811719921537768779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15776298164586457434050077 5916111811719921537768779)
              ·
                refine ⟨8874167717579882306653169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5916111811719921537768779 8874167717579882306653169)
                ·
                  refine ⟨6655625788184911729989877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8874167717579882306653169 6655625788184911729989877)
                  ·
                    refine ⟨623964917642335474686551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6655625788184911729989877 623964917642335474686551)
                    ·
                      rfl

theorem cell22_1822751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 1, 2, 5].length) (baseStart_1822751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1822751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1822751 prefixEnd_1822751 := by exact prefixLift 1822751
  have htrace : WordTrace (prefixWord ++ tailWord_1822751) baseStart_1822751 baseEnd_1822751 := by
    simpa [prefixWord, tailWord_1822751, baseEnd_1822751] using wordTrace_append hprefix tailTrace_1822751
  have hstable : (prefixWord ++ tailWord_1822751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1822751).length < 2 ^ (prefixWord ++ tailWord_1822751).sum := by decide
  have hdescent : baseEnd_1822751 < baseStart_1822751 := by decide
  rcases family_descends (prefixWord ++ tailWord_1822751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1822781 : List Nat := [1, 4, 1, 3, 1, 1, 1, 2, 8]
def baseStart_1822781 : Nat := 118140960795 + 1822781 * 2 ^ 59
def prefixEnd_1822781 : Nat := 4983230072969 + 3 ^ 40 * 1822781 * 2
def baseEnd_1822781 : Nat := 207991729085141798812153

theorem tailTrace_1822781 : CollatzResearch.WordTrace tailWord_1822781 prefixEnd_1822781 207991729085141798812153 := by
  unfold tailWord_1822781
  simp only [CollatzResearch.WordTrace]
  refine ⟨66482284809383218055556197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44321523206255478703704131 66482284809383218055556197)
  ·
    refine ⟨12465428401759353385416787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66482284809383218055556197 12465428401759353385416787)
    ·
      refine ⟨18698142602639030078125181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12465428401759353385416787 18698142602639030078125181)
      ·
        refine ⟨7011803475989636279296943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18698142602639030078125181 7011803475989636279296943)
        ·
          refine ⟨10517705213984454418945415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7011803475989636279296943 10517705213984454418945415)
          ·
            refine ⟨15776557820976681628418123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10517705213984454418945415 15776557820976681628418123)
            ·
              refine ⟨23664836731465022442627185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15776557820976681628418123 23664836731465022442627185)
              ·
                refine ⟨17748627548598766831970389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23664836731465022442627185 17748627548598766831970389)
                ·
                  refine ⟨207991729085141798812153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17748627548598766831970389 207991729085141798812153)
                  ·
                    rfl

theorem cell22_1822781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 2, 8].length) (baseStart_1822781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1822781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1822781 prefixEnd_1822781 := by exact prefixLift 1822781
  have htrace : WordTrace (prefixWord ++ tailWord_1822781) baseStart_1822781 baseEnd_1822781 := by
    simpa [prefixWord, tailWord_1822781, baseEnd_1822781] using wordTrace_append hprefix tailTrace_1822781
  have hstable : (prefixWord ++ tailWord_1822781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1822781).length < 2 ^ (prefixWord ++ tailWord_1822781).sum := by decide
  have hdescent : baseEnd_1822781 < baseStart_1822781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1822781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1822796 : List Nat := [2, 2, 1, 3, 1, 1, 2, 2, 3, 5]
def baseStart_1822796 : Nat := 118140960795 + 1822796 * 2 ^ 59
def prefixEnd_1822796 : Nat := 4983230072969 + 3 ^ 40 * 1822796 * 2
def baseEnd_1822796 : Nat := 623980322061970357311413

theorem tailTrace_1822796 : CollatzResearch.WordTrace tailWord_1822796 prefixEnd_1822796 623980322061970357311413 := by
  unfold tailWord_1822796
  simp only [CollatzResearch.WordTrace]
  refine ⟨33241415952164437808676121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44321887936219250411568161 33241415952164437808676121)
  ·
    refine ⟨24931061964123328356507091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33241415952164437808676121 24931061964123328356507091)
    ·
      refine ⟨37396592946184992534760637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24931061964123328356507091 37396592946184992534760637)
      ·
        refine ⟨14023722354819372200535239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37396592946184992534760637 14023722354819372200535239)
        ·
          refine ⟨21035583532229058300802859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14023722354819372200535239 21035583532229058300802859)
          ·
            refine ⟨31553375298343587451204289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21035583532229058300802859 31553375298343587451204289)
            ·
              refine ⟨23665031473757690588403217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31553375298343587451204289 23665031473757690588403217)
              ·
                refine ⟨17748773605318267941302413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23665031473757690588403217 17748773605318267941302413)
                ·
                  refine ⟨6655790101994350477988405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17748773605318267941302413 6655790101994350477988405)
                  ·
                    refine ⟨623980322061970357311413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6655790101994350477988405 623980322061970357311413)
                    ·
                      rfl

theorem cell22_1822796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 2, 3, 5].length) (baseStart_1822796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1822796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1822796 prefixEnd_1822796 := by exact prefixLift 1822796
  have htrace : WordTrace (prefixWord ++ tailWord_1822796) baseStart_1822796 baseEnd_1822796 := by
    simpa [prefixWord, tailWord_1822796, baseEnd_1822796] using wordTrace_append hprefix tailTrace_1822796
  have hstable : (prefixWord ++ tailWord_1822796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1822796).length < 2 ^ (prefixWord ++ tailWord_1822796).sum := by decide
  have hdescent : baseEnd_1822796 < baseStart_1822796 := by decide
  rcases family_descends (prefixWord ++ tailWord_1822796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1822798 : List Nat := [4, 1, 1, 1, 1, 5, 2, 1, 6]
def baseStart_1822798 : Nat := 118140960795 + 1822798 * 2 ^ 59
def prefixEnd_1822798 : Nat := 4983230072969 + 3 ^ 40 * 1822798 * 2
def baseEnd_1822798 : Nat := 207993668900947672920469

theorem tailTrace_1822798 : CollatzResearch.WordTrace tailWord_1822798 prefixEnd_1822798 207993668900947672920469 := by
  unfold tailWord_1822798
  simp only [CollatzResearch.WordTrace]
  refine ⟨8310363106290203744865631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44321936566881086639283365 8310363106290203744865631)
  ·
    refine ⟨12465544659435305617298447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8310363106290203744865631 12465544659435305617298447)
    ·
      refine ⟨18698316989152958425947671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12465544659435305617298447 18698316989152958425947671)
      ·
        refine ⟨28047475483729437638921507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18698316989152958425947671 28047475483729437638921507)
        ·
          refine ⟨42071213225594156458382261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28047475483729437638921507 42071213225594156458382261)
          ·
            refine ⟨3944176239899452167973337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42071213225594156458382261 3944176239899452167973337)
            ·
              refine ⟨2958132179924589125980003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3944176239899452167973337 2958132179924589125980003)
              ·
                refine ⟨4437198269886883688970005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2958132179924589125980003 4437198269886883688970005)
                ·
                  refine ⟨207993668900947672920469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4437198269886883688970005 207993668900947672920469)
                  ·
                    rfl

theorem cell22_1822798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 2, 1, 6].length) (baseStart_1822798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1822798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1822798 prefixEnd_1822798 := by exact prefixLift 1822798
  have htrace : WordTrace (prefixWord ++ tailWord_1822798) baseStart_1822798 baseEnd_1822798 := by
    simpa [prefixWord, tailWord_1822798, baseEnd_1822798] using wordTrace_append hprefix tailTrace_1822798
  have hstable : (prefixWord ++ tailWord_1822798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1822798).length < 2 ^ (prefixWord ++ tailWord_1822798).sum := by decide
  have hdescent : baseEnd_1822798 < baseStart_1822798 := by decide
  rcases family_descends (prefixWord ++ tailWord_1822798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1822900 : List Nat := [2, 5, 3, 1, 2, 1, 2, 2, 4]
def baseStart_1822900 : Nat := 118140960795 + 1822900 * 2 ^ 59
def prefixEnd_1822900 : Nat := 4983230072969 + 3 ^ 40 * 1822900 * 2
def baseEnd_1822900 : Nat := 208005307795782917570365

theorem tailTrace_1822900 : CollatzResearch.WordTrace tailWord_1822900 prefixEnd_1822900 208005307795782917570365 := by
  unfold tailWord_1822900
  simp only [CollatzResearch.WordTrace]
  refine ⟨33243312547976050689569077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44324416730634734252758769 33243312547976050689569077)
  ·
    refine ⟨3116560551372754752147101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33243312547976050689569077 3116560551372754752147101)
    ·
      refine ⟨1168710206764783032055163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3116560551372754752147101 1168710206764783032055163)
      ·
        refine ⟨1753065310147174548082745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1168710206764783032055163 1753065310147174548082745)
        ·
          refine ⟨1314798982610380911062059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1753065310147174548082745 1314798982610380911062059)
          ·
            refine ⟨1972198473915571366593089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1314798982610380911062059 1972198473915571366593089)
            ·
              refine ⟨1479148855436678524944817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1972198473915571366593089 1479148855436678524944817)
              ·
                refine ⟨1109361641577508893708613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1479148855436678524944817 1109361641577508893708613)
                ·
                  refine ⟨208005307795782917570365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1109361641577508893708613 208005307795782917570365)
                  ·
                    rfl

theorem cell22_1822900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 2, 2, 4].length) (baseStart_1822900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1822900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1822900 prefixEnd_1822900 := by exact prefixLift 1822900
  have htrace : WordTrace (prefixWord ++ tailWord_1822900) baseStart_1822900 baseEnd_1822900 := by
    simpa [prefixWord, tailWord_1822900, baseEnd_1822900] using wordTrace_append hprefix tailTrace_1822900
  have hstable : (prefixWord ++ tailWord_1822900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1822900).length < 2 ^ (prefixWord ++ tailWord_1822900).sum := by decide
  have hdescent : baseEnd_1822900 < baseStart_1822900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1822900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1822952 : List Nat := [2, 1, 4, 1, 2, 2, 4, 1, 1, 4]
def baseStart_1822952 : Nat := 118140960795 + 1822952 * 2 ^ 59
def prefixEnd_1822952 : Nat := 4983230072969 + 3 ^ 40 * 1822952 * 2
def baseEnd_1822952 : Nat := 624033724050037950410935

theorem tailTrace_1822952 : CollatzResearch.WordTrace tailWord_1822952 prefixEnd_1822952 624033724050037950410935 := by
  unfold tailWord_1822952
  simp only [CollatzResearch.WordTrace]
  refine ⟨33244260845881857130015555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44325681127842476173354073 33244260845881857130015555)
  ·
    refine ⟨49866391268822785695023333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33244260845881857130015555 49866391268822785695023333)
    ·
      refine ⟨9349948362904272317816875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49866391268822785695023333 9349948362904272317816875)
      ·
        refine ⟨14024922544356408476725313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9349948362904272317816875 14024922544356408476725313)
        ·
          refine ⟨10518691908267306357543985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14024922544356408476725313 10518691908267306357543985)
          ·
            refine ⟨7889018931200479768157989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10518691908267306357543985 7889018931200479768157989)
            ·
              refine ⟨1479191049600089956529623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7889018931200479768157989 1479191049600089956529623)
              ·
                refine ⟨2218786574400134934794435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1479191049600089956529623 2218786574400134934794435)
                ·
                  refine ⟨3328179861600202402191653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2218786574400134934794435 3328179861600202402191653)
                  ·
                    refine ⟨624033724050037950410935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3328179861600202402191653 624033724050037950410935)
                    ·
                      rfl

theorem cell22_1822952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 4, 1, 1, 4].length) (baseStart_1822952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1822952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1822952 prefixEnd_1822952 := by exact prefixLift 1822952
  have htrace : WordTrace (prefixWord ++ tailWord_1822952) baseStart_1822952 baseEnd_1822952 := by
    simpa [prefixWord, tailWord_1822952, baseEnd_1822952] using wordTrace_append hprefix tailTrace_1822952
  have hstable : (prefixWord ++ tailWord_1822952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1822952).length < 2 ^ (prefixWord ++ tailWord_1822952).sum := by decide
  have hdescent : baseEnd_1822952 < baseStart_1822952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1822952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1822963 : List Nat := [1, 1, 1, 2, 2, 4, 2, 1, 4, 4]
def baseStart_1822963 : Nat := 118140960795 + 1822963 * 2 ^ 59
def prefixEnd_1822963 : Nat := 4983230072969 + 3 ^ 40 * 1822963 * 2
def baseEnd_1822963 : Nat := 624037489574837588385901

theorem tailTrace_1822963 : CollatzResearch.WordTrace tailWord_1822963 prefixEnd_1822963 624037489574837588385901 := by
  unfold tailWord_1822963
  simp only [CollatzResearch.WordTrace]
  refine ⟨66488922894723863138681543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44325948596482575425787695 66488922894723863138681543)
  ·
    refine ⟨99733384342085794708022315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66488922894723863138681543 99733384342085794708022315)
    ·
      refine ⟨149600076513128692062033473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99733384342085794708022315 149600076513128692062033473)
      ·
        refine ⟨112200057384846519046525105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149600076513128692062033473 112200057384846519046525105)
        ·
          refine ⟨84150043038634889284893829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112200057384846519046525105 84150043038634889284893829)
          ·
            refine ⟨15778133069744041740917593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84150043038634889284893829 15778133069744041740917593)
            ·
              refine ⟨11833599802308031305688195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15778133069744041740917593 11833599802308031305688195)
              ·
                refine ⟨17750399703462046958532293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11833599802308031305688195 17750399703462046958532293)
                ·
                  refine ⟨3328199944399133804724805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17750399703462046958532293 3328199944399133804724805)
                  ·
                    refine ⟨624037489574837588385901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3328199944399133804724805 624037489574837588385901)
                    ·
                      rfl

theorem cell22_1822963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 1, 4, 4].length) (baseStart_1822963 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1822963 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1822963 prefixEnd_1822963 := by exact prefixLift 1822963
  have htrace : WordTrace (prefixWord ++ tailWord_1822963) baseStart_1822963 baseEnd_1822963 := by
    simpa [prefixWord, tailWord_1822963, baseEnd_1822963] using wordTrace_append hprefix tailTrace_1822963
  have hstable : (prefixWord ++ tailWord_1822963).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1822963).length < 2 ^ (prefixWord ++ tailWord_1822963).sum := by decide
  have hdescent : baseEnd_1822963 < baseStart_1822963 := by decide
  rcases family_descends (prefixWord ++ tailWord_1822963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1823023 : List Nat := [1, 1, 2, 1, 2, 1, 6, 1, 7]
def baseStart_1823023 : Nat := 118140960795 + 1823023 * 2 ^ 59
def prefixEnd_1823023 : Nat := 4983230072969 + 3 ^ 40 * 1823023 * 2
def baseEnd_1823023 : Nat := 208019342933672477295239

theorem tailTrace_1823023 : CollatzResearch.WordTrace tailWord_1823023 prefixEnd_1823023 208019342933672477295239 := by
  unfold tailWord_1823023
  simp only [CollatzResearch.WordTrace]
  refine ⟨66491111274506493385865723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44327407516337662257243815 66491111274506493385865723)
  ·
    refine ⟨99736666911759740078798585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66491111274506493385865723 99736666911759740078798585)
    ·
      refine ⟨74802500183819805059098939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99736666911759740078798585 74802500183819805059098939)
      ·
        refine ⟨112203750275729707588648409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74802500183819805059098939 112203750275729707588648409)
        ·
          refine ⟨84152812706797280691486307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112203750275729707588648409 84152812706797280691486307)
          ·
            refine ⟨126229219060195921037229461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84152812706797280691486307 126229219060195921037229461)
            ·
              refine ⟨5916994643446683798620131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 126229219060195921037229461 5916994643446683798620131)
              ·
                refine ⟨8875491965170025697930197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5916994643446683798620131 8875491965170025697930197)
                ·
                  refine ⟨208019342933672477295239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8875491965170025697930197 208019342933672477295239)
                  ·
                    rfl

theorem cell22_1823023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 1, 7].length) (baseStart_1823023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1823023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1823023 prefixEnd_1823023 := by exact prefixLift 1823023
  have htrace : WordTrace (prefixWord ++ tailWord_1823023) baseStart_1823023 baseEnd_1823023 := by
    simpa [prefixWord, tailWord_1823023, baseEnd_1823023] using wordTrace_append hprefix tailTrace_1823023
  have hstable : (prefixWord ++ tailWord_1823023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1823023).length < 2 ^ (prefixWord ++ tailWord_1823023).sum := by decide
  have hdescent : baseEnd_1823023 < baseStart_1823023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1823023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1823085 : List Nat := [1, 5, 1, 1, 1, 2, 2, 3, 6]
def baseStart_1823085 : Nat := 118140960795 + 1823085 * 2 ^ 59
def prefixEnd_1823085 : Nat := 4983230072969 + 3 ^ 40 * 1823085 * 2
def baseEnd_1823085 : Nat := 208026417556023312278509

theorem tailTrace_1823085 : CollatzResearch.WordTrace tailWord_1823085 prefixEnd_1823085 208026417556023312278509 := by
  unfold tailWord_1823085
  simp only [CollatzResearch.WordTrace]
  refine ⟨66493372600281877974622709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44328915066854585316415139 66493372600281877974622709)
  ·
    refine ⟨6233753681276426060120879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 66493372600281877974622709 6233753681276426060120879)
    ·
      refine ⟨9350630521914639090181319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6233753681276426060120879 9350630521914639090181319)
      ·
        refine ⟨14025945782871958635271979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9350630521914639090181319 14025945782871958635271979)
        ·
          refine ⟨21038918674307937952907969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14025945782871958635271979 21038918674307937952907969)
          ·
            refine ⟨15779189005730953464680977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21038918674307937952907969 15779189005730953464680977)
            ·
              refine ⟨11834391754298215098510733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15779189005730953464680977 11834391754298215098510733)
              ·
                refine ⟨4437896907861830661941525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11834391754298215098510733 4437896907861830661941525)
                ·
                  refine ⟨208026417556023312278509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4437896907861830661941525 208026417556023312278509)
                  ·
                    rfl

theorem cell22_1823085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 3, 6].length) (baseStart_1823085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1823085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1823085 prefixEnd_1823085 := by exact prefixLift 1823085
  have htrace : WordTrace (prefixWord ++ tailWord_1823085) baseStart_1823085 baseEnd_1823085 := by
    simpa [prefixWord, tailWord_1823085, baseEnd_1823085] using wordTrace_append hprefix tailTrace_1823085
  have hstable : (prefixWord ++ tailWord_1823085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1823085).length < 2 ^ (prefixWord ++ tailWord_1823085).sum := by decide
  have hdescent : baseEnd_1823085 < baseStart_1823085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1823085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1823115 : List Nat := [1, 1, 1, 1, 4, 5, 1, 1, 1, 6]
def baseStart_1823115 : Nat := 118140960795 + 1823115 * 2 ^ 59
def prefixEnd_1823115 : Nat := 4983230072969 + 3 ^ 40 * 1823115 * 2
def baseEnd_1823115 : Nat := 624089522281159858585435

theorem tailTrace_1823115 : CollatzResearch.WordTrace tailWord_1823115 prefixEnd_1823115 624089522281159858585435 := by
  unfold tailWord_1823115
  simp only [CollatzResearch.WordTrace]
  refine ⟨66494466790173193098214799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44329644526782128732143199 66494466790173193098214799)
  ·
    refine ⟨99741700185259789647322199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66494466790173193098214799 99741700185259789647322199)
    ·
      refine ⟨149612550277889684470983299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99741700185259789647322199 149612550277889684470983299)
      ·
        refine ⟨224418825416834526706474949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149612550277889684470983299 224418825416834526706474949)
        ·
          refine ⟨42078529765656473757464053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 224418825416834526706474949 42078529765656473757464053)
          ·
            refine ⟨3944862165530294414762255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42078529765656473757464053 3944862165530294414762255)
            ·
              refine ⟨5917293248295441622143383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3944862165530294414762255 5917293248295441622143383)
              ·
                refine ⟨8875939872443162433215075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5917293248295441622143383 8875939872443162433215075)
                ·
                  refine ⟨13313909808664743649822613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8875939872443162433215075 13313909808664743649822613)
                  ·
                    refine ⟨624089522281159858585435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13313909808664743649822613 624089522281159858585435)
                    ·
                      rfl

theorem cell22_1823115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 1, 1, 6].length) (baseStart_1823115 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1823115 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1823115 prefixEnd_1823115 := by exact prefixLift 1823115
  have htrace : WordTrace (prefixWord ++ tailWord_1823115) baseStart_1823115 baseEnd_1823115 := by
    simpa [prefixWord, tailWord_1823115, baseEnd_1823115] using wordTrace_append hprefix tailTrace_1823115
  have hstable : (prefixWord ++ tailWord_1823115).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1823115).length < 2 ^ (prefixWord ++ tailWord_1823115).sum := by decide
  have hdescent : baseEnd_1823115 < baseStart_1823115 := by decide
  rcases family_descends (prefixWord ++ tailWord_1823115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1823130 : List Nat := [3, 1, 1, 4, 1, 3, 9]
def baseStart_1823130 : Nat := 118140960795 + 1823130 * 2 ^ 59
def prefixEnd_1823130 : Nat := 4983230072969 + 3 ^ 40 * 1823130 * 2
def baseEnd_1823130 : Nat := 23114616929174252572607

theorem tailTrace_1823130 : CollatzResearch.WordTrace tailWord_1823130 prefixEnd_1823130 23114616929174252572607 := by
  unfold tailWord_1823130
  simp only [CollatzResearch.WordTrace]
  refine ⟨16623753471279712665002711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44330009256745900440007229 16623753471279712665002711)
  ·
    refine ⟨24935630206919568997504067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16623753471279712665002711 24935630206919568997504067)
    ·
      refine ⟨37403445310379353496256101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24935630206919568997504067 37403445310379353496256101)
      ·
        refine ⟨7013145995696128780548019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37403445310379353496256101 7013145995696128780548019)
        ·
          refine ⟨10519718993544193170822029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7013145995696128780548019 10519718993544193170822029)
          ·
            refine ⟨3944894622579072439058261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10519718993544193170822029 3944894622579072439058261)
            ·
              refine ⟨23114616929174252572607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3944894622579072439058261 23114616929174252572607)
              ·
                rfl

theorem cell22_1823130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 9].length) (baseStart_1823130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1823130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1823130 prefixEnd_1823130 := by exact prefixLift 1823130
  have htrace : WordTrace (prefixWord ++ tailWord_1823130) baseStart_1823130 baseEnd_1823130 := by
    simpa [prefixWord, tailWord_1823130, baseEnd_1823130] using wordTrace_append hprefix tailTrace_1823130
  have hstable : (prefixWord ++ tailWord_1823130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1823130).length < 2 ^ (prefixWord ++ tailWord_1823130).sum := by decide
  have hdescent : baseEnd_1823130 < baseStart_1823130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1823130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1823164 : List Nat := [2, 2, 2, 4, 1, 3, 2, 6]
def baseStart_1823164 : Nat := 118140960795 + 1823164 * 2 ^ 59
def prefixEnd_1823164 : Nat := 4983230072969 + 3 ^ 40 * 1823164 * 2
def baseEnd_1823164 : Nat := 69345143998060007123365

theorem tailTrace_1823164 : CollatzResearch.WordTrace tailWord_1823164 prefixEnd_1823164 69345143998060007123365 := by
  unfold tailWord_1823164
  simp only [CollatzResearch.WordTrace]
  refine ⟨33248126983497837233374273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44330835977997116311165697 33248126983497837233374273)
  ·
    refine ⟨24936095237623377925030705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33248126983497837233374273 24936095237623377925030705)
    ·
      refine ⟨18702071428217533443773029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24936095237623377925030705 18702071428217533443773029)
      ·
        refine ⟨3506638392790787520707443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18702071428217533443773029 3506638392790787520707443)
        ·
          refine ⟨5259957589186181281061165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3506638392790787520707443 5259957589186181281061165)
          ·
            refine ⟨1972484095944817980397937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5259957589186181281061165 1972484095944817980397937)
            ·
              refine ⟨1479363071958613485298453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1972484095944817980397937 1479363071958613485298453)
              ·
                refine ⟨69345143998060007123365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1479363071958613485298453 69345143998060007123365)
                ·
                  rfl

theorem cell22_1823164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 2, 6].length) (baseStart_1823164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1823164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1823164 prefixEnd_1823164 := by exact prefixLift 1823164
  have htrace : WordTrace (prefixWord ++ tailWord_1823164) baseStart_1823164 baseEnd_1823164 := by
    simpa [prefixWord, tailWord_1823164, baseEnd_1823164] using wordTrace_append hprefix tailTrace_1823164
  have hstable : (prefixWord ++ tailWord_1823164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1823164).length < 2 ^ (prefixWord ++ tailWord_1823164).sum := by decide
  have hdescent : baseEnd_1823164 < baseStart_1823164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1823164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1823175 : List Nat := [1, 1, 4, 1, 1, 4, 1, 2, 7]
def baseStart_1823175 : Nat := 118140960795 + 1823175 * 2 ^ 59
def prefixEnd_1823175 : Nat := 4983230072969 + 3 ^ 40 * 1823175 * 2
def baseEnd_1823175 : Nat := 208036687169113234028417

theorem tailTrace_1823175 : CollatzResearch.WordTrace tailWord_1823175 prefixEnd_1823175 208036687169113234028417 := by
  unfold tailWord_1823175
  simp only [CollatzResearch.WordTrace]
  refine ⟨66496655169955823345398979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44331103446637215563599319 66496655169955823345398979)
  ·
    refine ⟨99744982754933735018098469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66496655169955823345398979 99744982754933735018098469)
    ·
      refine ⟨18702184266550075315893463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99744982754933735018098469 18702184266550075315893463)
      ·
        refine ⟨28053276399825112973840195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18702184266550075315893463 28053276399825112973840195)
        ·
          refine ⟨42079914599737669460760293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28053276399825112973840195 42079914599737669460760293)
          ·
            refine ⟨7889983987450813023892555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42079914599737669460760293 7889983987450813023892555)
            ·
              refine ⟨11834975981176219535838833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7889983987450813023892555 11834975981176219535838833)
              ·
                refine ⟨8876231985882164651879125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11834975981176219535838833 8876231985882164651879125)
                ·
                  refine ⟨208036687169113234028417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8876231985882164651879125 208036687169113234028417)
                  ·
                    rfl

theorem cell22_1823175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 2, 7].length) (baseStart_1823175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1823175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1823175 prefixEnd_1823175 := by exact prefixLift 1823175
  have htrace : WordTrace (prefixWord ++ tailWord_1823175) baseStart_1823175 baseEnd_1823175 := by
    simpa [prefixWord, tailWord_1823175, baseEnd_1823175] using wordTrace_append hprefix tailTrace_1823175
  have hstable : (prefixWord ++ tailWord_1823175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1823175).length < 2 ^ (prefixWord ++ tailWord_1823175).sum := by decide
  have hdescent : baseEnd_1823175 < baseStart_1823175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1823175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1823202 : List Nat := [3, 3, 3, 2, 2, 1, 2, 1, 2, 3]
def baseStart_1823202 : Nat := 118140960795 + 1823202 * 2 ^ 59
def prefixEnd_1823202 : Nat := 4983230072969 + 3 ^ 40 * 1823202 * 2
def baseEnd_1823202 : Nat := 624119304159120631660169

theorem tailTrace_1823202 : CollatzResearch.WordTrace tailWord_1823202 prefixEnd_1823202 624119304159120631660169 := by
  unfold tailWord_1823202
  simp only [CollatzResearch.WordTrace]
  refine ⟨16624409985214501739157965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44331759960572004637754573 16624409985214501739157965)
  ·
    refine ⟨6234153744455438152184237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16624409985214501739157965 6234153744455438152184237)
    ·
      refine ⟨2337807654170789307069089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6234153744455438152184237 2337807654170789307069089)
      ·
        refine ⟨1753355740628091980301817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2337807654170789307069089 1753355740628091980301817)
        ·
          refine ⟨1315016805471068985226363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1753355740628091980301817 1315016805471068985226363)
          ·
            refine ⟨1972525208206603477839545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1315016805471068985226363 1972525208206603477839545)
            ·
              refine ⟨1479393906154952608379659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1972525208206603477839545 1479393906154952608379659)
              ·
                refine ⟨2219090859232428912569489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1479393906154952608379659 2219090859232428912569489)
                ·
                  refine ⟨1664318144424321684427117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2219090859232428912569489 1664318144424321684427117)
                  ·
                    refine ⟨624119304159120631660169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1664318144424321684427117 624119304159120631660169)
                    ·
                      rfl

theorem cell22_1823202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_1823202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1823202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1823202 prefixEnd_1823202 := by exact prefixLift 1823202
  have htrace : WordTrace (prefixWord ++ tailWord_1823202) baseStart_1823202 baseEnd_1823202 := by
    simpa [prefixWord, tailWord_1823202, baseEnd_1823202] using wordTrace_append hprefix tailTrace_1823202
  have hstable : (prefixWord ++ tailWord_1823202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1823202).length < 2 ^ (prefixWord ++ tailWord_1823202).sum := by decide
  have hdescent : baseEnd_1823202 < baseStart_1823202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1823202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1823269 : List Nat := [1, 3, 1, 2, 2, 1, 4, 3, 2, 3]
def baseStart_1823269 : Nat := 118140960795 + 1823269 * 2 ^ 59
def prefixEnd_1823269 : Nat := 4983230072969 + 3 ^ 40 * 1823269 * 2
def baseEnd_1823269 : Nat := 624142239628354790234963

theorem tailTrace_1823269 : CollatzResearch.WordTrace tailWord_1823269 prefixEnd_1823269 624142239628354790234963 := by
  unfold tailWord_1823269
  simp only [CollatzResearch.WordTrace]
  refine ⟨66500083631615277399320861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44333389087743518266213907 66500083631615277399320861)
  ·
    refine ⟨24937531361855729024745323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66500083631615277399320861 24937531361855729024745323)
    ·
      refine ⟨37406297042783593537117985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24937531361855729024745323 37406297042783593537117985)
      ·
        refine ⟨28054722782087695152838489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37406297042783593537117985 28054722782087695152838489)
        ·
          refine ⟨21041042086565771364628867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28054722782087695152838489 21041042086565771364628867)
          ·
            refine ⟨31561563129848657046943301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21041042086565771364628867 31561563129848657046943301)
            ·
              refine ⟨5917793086846623196301869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31561563129848657046943301 5917793086846623196301869)
              ·
                refine ⟨2219172407567483698613201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5917793086846623196301869 2219172407567483698613201)
                ·
                  refine ⟨1664379305675612773959901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2219172407567483698613201 1664379305675612773959901)
                  ·
                    refine ⟨624142239628354790234963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1664379305675612773959901 624142239628354790234963)
                    ·
                      rfl

theorem cell22_1823269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 3, 2, 3].length) (baseStart_1823269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1823269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1823269 prefixEnd_1823269 := by exact prefixLift 1823269
  have htrace : WordTrace (prefixWord ++ tailWord_1823269) baseStart_1823269 baseEnd_1823269 := by
    simpa [prefixWord, tailWord_1823269, baseEnd_1823269] using wordTrace_append hprefix tailTrace_1823269
  have hstable : (prefixWord ++ tailWord_1823269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1823269).length < 2 ^ (prefixWord ++ tailWord_1823269).sum := by decide
  have hdescent : baseEnd_1823269 < baseStart_1823269 := by decide
  rcases family_descends (prefixWord ++ tailWord_1823269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1823271 : List Nat := [1, 1, 7, 2, 1, 1, 1, 2, 6]
def baseStart_1823271 : Nat := 118140960795 + 1823271 * 2 ^ 59
def prefixEnd_1823271 : Nat := 4983230072969 + 3 ^ 40 * 1823271 * 2
def baseEnd_1823271 : Nat := 208047641423075817228319

theorem tailTrace_1823271 : CollatzResearch.WordTrace tailWord_1823271 prefixEnd_1823271 208047641423075817228319 := by
  unfold tailWord_1823271
  simp only [CollatzResearch.WordTrace]
  refine ⟨66500156577608031740893667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44333437718405354493929111 66500156577608031740893667)
  ·
    refine ⟨99750234866412047611340501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66500156577608031740893667 99750234866412047611340501)
    ·
      refine ⟨2337896129681532365890793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 99750234866412047611340501 2337896129681532365890793)
      ·
        refine ⟨1753422097261149274418095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2337896129681532365890793 1753422097261149274418095)
        ·
          refine ⟨2630133145891723911627143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1753422097261149274418095 2630133145891723911627143)
          ·
            refine ⟨3945199718837585867440715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2630133145891723911627143 3945199718837585867440715)
            ·
              refine ⟨5917799578256378801161073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3945199718837585867440715 5917799578256378801161073)
              ·
                refine ⟨4438349683692284100870805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5917799578256378801161073 4438349683692284100870805)
                ·
                  refine ⟨208047641423075817228319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4438349683692284100870805 208047641423075817228319)
                  ·
                    rfl

theorem cell22_1823271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 2, 6].length) (baseStart_1823271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1823271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1823271 prefixEnd_1823271 := by exact prefixLift 1823271
  have htrace : WordTrace (prefixWord ++ tailWord_1823271) baseStart_1823271 baseEnd_1823271 := by
    simpa [prefixWord, tailWord_1823271, baseEnd_1823271] using wordTrace_append hprefix tailTrace_1823271
  have hstable : (prefixWord ++ tailWord_1823271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1823271).length < 2 ^ (prefixWord ++ tailWord_1823271).sum := by decide
  have hdescent : baseEnd_1823271 < baseStart_1823271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1823271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1823327 : List Nat := [1, 1, 2, 3, 1, 1, 1, 7, 5]
def baseStart_1823327 : Nat := 118140960795 + 1823327 * 2 ^ 59
def prefixEnd_1823327 : Nat := 4983230072969 + 3 ^ 40 * 1823327 * 2
def baseEnd_1823327 : Nat := 208054031404553990761595

theorem tailTrace_1823327 : CollatzResearch.WordTrace tailWord_1823327 prefixEnd_1823327 208054031404553990761595 := by
  unfold tailWord_1823327
  simp only [CollatzResearch.WordTrace]
  refine ⟨66502199065405153304932235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44334799376936768869954823 66502199065405153304932235)
  ·
    refine ⟨99753298598107729957398353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66502199065405153304932235 99753298598107729957398353)
    ·
      refine ⟨74814973948580797468048765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99753298598107729957398353 74814973948580797468048765)
      ·
        refine ⟨28055615230717799050518287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74814973948580797468048765 28055615230717799050518287)
        ·
          refine ⟨42083422846076698575777431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28055615230717799050518287 42083422846076698575777431)
          ·
            refine ⟨63125134269115047863666147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42083422846076698575777431 63125134269115047863666147)
            ·
              refine ⟨94687701403672571795499221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63125134269115047863666147 94687701403672571795499221)
              ·
                refine ⟨2219243001648575901457013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 94687701403672571795499221 2219243001648575901457013)
                ·
                  refine ⟨208054031404553990761595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2219243001648575901457013 208054031404553990761595)
                  ·
                    rfl

theorem cell22_1823327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 7, 5].length) (baseStart_1823327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1823327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1823327 prefixEnd_1823327 := by exact prefixLift 1823327
  have htrace : WordTrace (prefixWord ++ tailWord_1823327) baseStart_1823327 baseEnd_1823327 := by
    simpa [prefixWord, tailWord_1823327, baseEnd_1823327] using wordTrace_append hprefix tailTrace_1823327
  have hstable : (prefixWord ++ tailWord_1823327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1823327).length < 2 ^ (prefixWord ++ tailWord_1823327).sum := by decide
  have hdescent : baseEnd_1823327 < baseStart_1823327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1823327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1823372 : List Nat := [2, 2, 1, 2, 1, 1, 2, 5, 6]
def baseStart_1823372 : Nat := 118140960795 + 1823372 * 2 ^ 59
def prefixEnd_1823372 : Nat := 4983230072969 + 3 ^ 40 * 1823372 * 2
def baseEnd_1823372 : Nat := 208059166211098951636549

theorem tailTrace_1823372 : CollatzResearch.WordTrace tailWord_1823372 prefixEnd_1823372 208059166211098951636549 := by
  unfold tailWord_1823372
  simp only [CollatzResearch.WordTrace]
  refine ⟨33251920175121062995160185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44335893566828083993546913 33251920175121062995160185)
  ·
    refine ⟨24938940131340797246370139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33251920175121062995160185 24938940131340797246370139)
    ·
      refine ⟨37408410197011195869555209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24938940131340797246370139 37408410197011195869555209)
      ·
        refine ⟨28056307647758396902166407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37408410197011195869555209 28056307647758396902166407)
        ·
          refine ⟨42084461471637595353249611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28056307647758396902166407 42084461471637595353249611)
          ·
            refine ⟨63126692207456393029874417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42084461471637595353249611 63126692207456393029874417)
            ·
              refine ⟨47345019155592294772405813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63126692207456393029874417 47345019155592294772405813)
              ·
                refine ⟨4438595545836777634913045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47345019155592294772405813 4438595545836777634913045)
                ·
                  refine ⟨208059166211098951636549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4438595545836777634913045 208059166211098951636549)
                  ·
                    rfl

theorem cell22_1823372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 5, 6].length) (baseStart_1823372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1823372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1823372 prefixEnd_1823372 := by exact prefixLift 1823372
  have htrace : WordTrace (prefixWord ++ tailWord_1823372) baseStart_1823372 baseEnd_1823372 := by
    simpa [prefixWord, tailWord_1823372, baseEnd_1823372] using wordTrace_append hprefix tailTrace_1823372
  have hstable : (prefixWord ++ tailWord_1823372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1823372).length < 2 ^ (prefixWord ++ tailWord_1823372).sum := by decide
  have hdescent : baseEnd_1823372 < baseStart_1823372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1823372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1823374 : List Nat := [4, 1, 1, 3, 1, 1, 2, 2, 3, 4]
def baseStart_1823374 : Nat := 118140960795 + 1823374 * 2 ^ 59
def prefixEnd_1823374 : Nat := 4983230072969 + 3 ^ 40 * 1823374 * 2
def baseEnd_1823374 : Nat := 624178183274169516359641

theorem tailTrace_1823374 : CollatzResearch.WordTrace tailWord_1823374 prefixEnd_1823374 624178183274169516359641 := by
  unfold tailWord_1823374
  simp only [CollatzResearch.WordTrace]
  refine ⟨8312989162029360041486647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44335942197489920221262117 8312989162029360041486647)
  ·
    refine ⟨12469483743044040062229971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8312989162029360041486647 12469483743044040062229971)
    ·
      refine ⟨18704225614566060093344957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12469483743044040062229971 18704225614566060093344957)
      ·
        refine ⟨7014084605462272535004359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18704225614566060093344957 7014084605462272535004359)
        ·
          refine ⟨10521126908193408802506539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7014084605462272535004359 10521126908193408802506539)
          ·
            refine ⟨15781690362290113203759809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10521126908193408802506539 15781690362290113203759809)
            ·
              refine ⟨11836267771717584902819857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15781690362290113203759809 11836267771717584902819857)
              ·
                refine ⟨8877200828788188677114893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11836267771717584902819857 8877200828788188677114893)
                ·
                  refine ⟨3328950310795570753918085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8877200828788188677114893 3328950310795570753918085)
                  ·
                    refine ⟨624178183274169516359641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3328950310795570753918085 624178183274169516359641)
                    ·
                      rfl

theorem cell22_1823374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 2, 3, 4].length) (baseStart_1823374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1823374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1823374 prefixEnd_1823374 := by exact prefixLift 1823374
  have htrace : WordTrace (prefixWord ++ tailWord_1823374) baseStart_1823374 baseEnd_1823374 := by
    simpa [prefixWord, tailWord_1823374, baseEnd_1823374] using wordTrace_append hprefix tailTrace_1823374
  have hstable : (prefixWord ++ tailWord_1823374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1823374).length < 2 ^ (prefixWord ++ tailWord_1823374).sum := by decide
  have hdescent : baseEnd_1823374 < baseStart_1823374 := by decide
  rcases family_descends (prefixWord ++ tailWord_1823374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1823378 : List Nat := [3, 2, 3, 1, 2, 3, 2, 1, 5]
def baseStart_1823378 : Nat := 118140960795 + 1823378 * 2 ^ 59
def prefixEnd_1823378 : Nat := 4983230072969 + 3 ^ 40 * 1823378 * 2
def baseEnd_1823378 : Nat := 208059850851971613086543

theorem tailTrace_1823378 : CollatzResearch.WordTrace tailWord_1823378 prefixEnd_1823378 208059850851971613086543 := by
  unfold tailWord_1823378
  simp only [CollatzResearch.WordTrace]
  refine ⟨16626014797055097253759697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44336039458813592676692525 16626014797055097253759697)
  ·
    refine ⟨12469511097791322940319773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16626014797055097253759697 12469511097791322940319773)
    ·
      refine ⟨4676066661671746102619915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12469511097791322940319773 4676066661671746102619915)
      ·
        refine ⟨7014099992507619153929873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4676066661671746102619915 7014099992507619153929873)
        ·
          refine ⟨5260574994380714365447405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7014099992507619153929873 5260574994380714365447405)
          ·
            refine ⟨1972715622892767887042777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5260574994380714365447405 1972715622892767887042777)
            ·
              refine ⟨1479536717169575915282083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1972715622892767887042777 1479536717169575915282083)
              ·
                refine ⟨2219305075754363872923125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1479536717169575915282083 2219305075754363872923125)
                ·
                  refine ⟨208059850851971613086543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2219305075754363872923125 208059850851971613086543)
                  ·
                    rfl

theorem cell22_1823378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 2, 1, 5].length) (baseStart_1823378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1823378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1823378 prefixEnd_1823378 := by exact prefixLift 1823378
  have htrace : WordTrace (prefixWord ++ tailWord_1823378) baseStart_1823378 baseEnd_1823378 := by
    simpa [prefixWord, tailWord_1823378, baseEnd_1823378] using wordTrace_append hprefix tailTrace_1823378
  have hstable : (prefixWord ++ tailWord_1823378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1823378).length < 2 ^ (prefixWord ++ tailWord_1823378).sum := by decide
  have hdescent : baseEnd_1823378 < baseStart_1823378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1823378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1823421 : List Nat := [1, 4, 1, 2, 1, 3, 1, 4, 2, 3]
def baseStart_1823421 : Nat := 118140960795 + 1823421 * 2 ^ 59
def prefixEnd_1823421 : Nat := 4983230072969 + 3 ^ 40 * 1823421 * 2
def baseEnd_1823421 : Nat := 624194272334677060434497

theorem tailTrace_1823421 : CollatzResearch.WordTrace tailWord_1823421 prefixEnd_1823421 624194272334677060434497 := by
  unfold tailWord_1823421
  simp only [CollatzResearch.WordTrace]
  refine ⟨66505627527064607358854117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44337085018043071572569411 66505627527064607358854117)
  ·
    refine ⟨12469805161324613879785147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66505627527064607358854117 12469805161324613879785147)
    ·
      refine ⟨18704707741986920819677721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12469805161324613879785147 18704707741986920819677721)
      ·
        refine ⟨14028530806490190614758291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18704707741986920819677721 14028530806490190614758291)
        ·
          refine ⟨21042796209735285922137437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14028530806490190614758291 21042796209735285922137437)
          ·
            refine ⟨7891048578650732220801539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21042796209735285922137437 7891048578650732220801539)
            ·
              refine ⟨11836572867976098331202309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7891048578650732220801539 11836572867976098331202309)
              ·
                refine ⟨2219357412745518437100433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11836572867976098331202309 2219357412745518437100433)
                ·
                  refine ⟨1664518059559138827825325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2219357412745518437100433 1664518059559138827825325)
                  ·
                    refine ⟨624194272334677060434497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1664518059559138827825325 624194272334677060434497)
                    ·
                      rfl

theorem cell22_1823421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 4, 2, 3].length) (baseStart_1823421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1823421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1823421 prefixEnd_1823421 := by exact prefixLift 1823421
  have htrace : WordTrace (prefixWord ++ tailWord_1823421) baseStart_1823421 baseEnd_1823421 := by
    simpa [prefixWord, tailWord_1823421, baseEnd_1823421] using wordTrace_append hprefix tailTrace_1823421
  have hstable : (prefixWord ++ tailWord_1823421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1823421).length < 2 ^ (prefixWord ++ tailWord_1823421).sum := by decide
  have hdescent : baseEnd_1823421 < baseStart_1823421 := by decide
  rcases family_descends (prefixWord ++ tailWord_1823421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1823423 : List Nat := [1, 1, 2, 2, 2, 6, 2, 2, 4]
def baseStart_1823423 : Nat := 118140960795 + 1823423 * 2 ^ 59
def prefixEnd_1823423 : Nat := 4983230072969 + 3 ^ 40 * 1823423 * 2
def baseEnd_1823423 : Nat := 208064985658516573961497

theorem tailTrace_1823423 : CollatzResearch.WordTrace tailWord_1823423 prefixEnd_1823423 208064985658516573961497 := by
  unfold tailWord_1823423
  simp only [CollatzResearch.WordTrace]
  refine ⟨66505700473057361700426923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44337133648704907800284615 66505700473057361700426923)
  ·
    refine ⟨99758550709586042550640385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66505700473057361700426923 99758550709586042550640385)
    ·
      refine ⟨74818913032189531912980289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99758550709586042550640385 74818913032189531912980289)
      ·
        refine ⟨56114184774142148934735217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74818913032189531912980289 56114184774142148934735217)
        ·
          refine ⟨42085638580606611701051413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56114184774142148934735217 42085638580606611701051413)
          ·
            refine ⟨1972764308465934923486785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 42085638580606611701051413 1972764308465934923486785)
            ·
              refine ⟨1479573231349451192615089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1972764308465934923486785 1479573231349451192615089)
              ·
                refine ⟨1109679923512088394461317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1479573231349451192615089 1109679923512088394461317)
                ·
                  refine ⟨208064985658516573961497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1109679923512088394461317 208064985658516573961497)
                  ·
                    rfl

theorem cell22_1823423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 2, 2, 4].length) (baseStart_1823423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1823423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1823423 prefixEnd_1823423 := by exact prefixLift 1823423
  have htrace : WordTrace (prefixWord ++ tailWord_1823423) baseStart_1823423 baseEnd_1823423 := by
    simpa [prefixWord, tailWord_1823423, baseEnd_1823423] using wordTrace_append hprefix tailTrace_1823423
  have hstable : (prefixWord ++ tailWord_1823423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1823423).length < 2 ^ (prefixWord ++ tailWord_1823423).sum := by decide
  have hdescent : baseEnd_1823423 < baseStart_1823423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1823423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1823434 : List Nat := [3, 1, 2, 1, 4, 1, 3, 7]
def baseStart_1823434 : Nat := 118140960795 + 1823434 * 2 ^ 59
def prefixEnd_1823434 : Nat := 4983230072969 + 3 ^ 40 * 1823434 * 2
def baseEnd_1823434 : Nat := 69355413611149928873273

theorem tailTrace_1823434 : CollatzResearch.WordTrace tailWord_1823434 prefixEnd_1823434 69355413611149928873273 := by
  unfold tailWord_1823434
  simp only [CollatzResearch.WordTrace]
  refine ⟨16626525419004377644769339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44337401117345007052718237 16626525419004377644769339)
  ·
    refine ⟨24939788128506566467154009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16626525419004377644769339 24939788128506566467154009)
    ·
      refine ⟨18704841096379924850365507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24939788128506566467154009 18704841096379924850365507)
      ·
        refine ⟨28057261644569887275548261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18704841096379924850365507 28057261644569887275548261)
        ·
          refine ⟨5260736558356853864165299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28057261644569887275548261 5260736558356853864165299)
          ·
            refine ⟨7891104837535280796247949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5260736558356853864165299 7891104837535280796247949)
            ·
              refine ⟨2959164314075730298592981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7891104837535280796247949 2959164314075730298592981)
              ·
                refine ⟨69355413611149928873273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2959164314075730298592981 69355413611149928873273)
                ·
                  rfl

theorem cell22_1823434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 3, 7].length) (baseStart_1823434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1823434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1823434 prefixEnd_1823434 := by exact prefixLift 1823434
  have htrace : WordTrace (prefixWord ++ tailWord_1823434) baseStart_1823434 baseEnd_1823434 := by
    simpa [prefixWord, tailWord_1823434, baseEnd_1823434] using wordTrace_append hprefix tailTrace_1823434
  have hstable : (prefixWord ++ tailWord_1823434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1823434).length < 2 ^ (prefixWord ++ tailWord_1823434).sum := by decide
  have hdescent : baseEnd_1823434 < baseStart_1823434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1823434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1823541 : List Nat := [1, 3, 3, 1, 3, 1, 3, 1, 6]
def baseStart_1823541 : Nat := 118140960795 + 1823541 * 2 ^ 59
def prefixEnd_1823541 : Nat := 4983230072969 + 3 ^ 40 * 1823541 * 2
def baseEnd_1823541 : Nat := 208078450262345582478043

theorem tailTrace_1823541 : CollatzResearch.WordTrace tailWord_1823541 prefixEnd_1823541 208078450262345582478043 := by
  unfold tailWord_1823541
  simp only [CollatzResearch.WordTrace]
  refine ⟨66510004286629867853222477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44340002857753245235481651 66510004286629867853222477)
  ·
    refine ⟨24941251607486200444958429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66510004286629867853222477 24941251607486200444958429)
    ·
      refine ⟨9352969352807325166859411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24941251607486200444958429 9352969352807325166859411)
      ·
        refine ⟨14029454029210987750289117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9352969352807325166859411 14029454029210987750289117)
        ·
          refine ⟨5261045260954120406358419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14029454029210987750289117 5261045260954120406358419)
          ·
            refine ⟨7891567891431180609537629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5261045260954120406358419 7891567891431180609537629)
            ·
              refine ⟨2959337959286692728576611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7891567891431180609537629 2959337959286692728576611)
              ·
                refine ⟨4439006938930039092864917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2959337959286692728576611 4439006938930039092864917)
                ·
                  refine ⟨208078450262345582478043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4439006938930039092864917 208078450262345582478043)
                  ·
                    rfl

theorem cell22_1823541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 3, 1, 6].length) (baseStart_1823541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1823541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1823541 prefixEnd_1823541 := by exact prefixLift 1823541
  have htrace : WordTrace (prefixWord ++ tailWord_1823541) baseStart_1823541 baseEnd_1823541 := by
    simpa [prefixWord, tailWord_1823541, baseEnd_1823541] using wordTrace_append hprefix tailTrace_1823541
  have hstable : (prefixWord ++ tailWord_1823541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1823541).length < 2 ^ (prefixWord ++ tailWord_1823541).sum := by decide
  have hdescent : baseEnd_1823541 < baseStart_1823541 := by decide
  rcases family_descends (prefixWord ++ tailWord_1823541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1823586 : List Nat := [3, 3, 2, 1, 3, 10]
def baseStart_1823586 : Nat := 118140960795 + 1823586 * 2 ^ 59
def prefixEnd_1823586 : Nat := 4983230072969 + 3 ^ 40 * 1823586 * 2
def baseEnd_1823586 : Nat := 7706799446995946050111

theorem tailTrace_1823586 : CollatzResearch.WordTrace tailWord_1823586 prefixEnd_1823586 7706799446995946050111 := by
  unfold tailWord_1823586
  simp only [CollatzResearch.WordTrace]
  refine ⟨16627911392866710134652653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44341097047644560359073741 16627911392866710134652653)
  ·
    refine ⟨6235466772325016300494745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16627911392866710134652653 6235466772325016300494745)
    ·
      refine ⟨4676600079243762225371059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6235466772325016300494745 4676600079243762225371059)
      ·
        refine ⟨7014900118865643338056589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4676600079243762225371059 7014900118865643338056589)
        ·
          refine ⟨2630587544574616251771221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7014900118865643338056589 2630587544574616251771221)
          ·
            refine ⟨7706799446995946050111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2630587544574616251771221 7706799446995946050111)
            ·
              rfl

theorem cell22_1823586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 10].length) (baseStart_1823586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1823586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1823586 prefixEnd_1823586 := by exact prefixLift 1823586
  have htrace : WordTrace (prefixWord ++ tailWord_1823586) baseStart_1823586 baseEnd_1823586 := by
    simpa [prefixWord, tailWord_1823586, baseEnd_1823586] using wordTrace_append hprefix tailTrace_1823586
  have hstable : (prefixWord ++ tailWord_1823586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1823586).length < 2 ^ (prefixWord ++ tailWord_1823586).sum := by decide
  have hdescent : baseEnd_1823586 < baseStart_1823586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1823586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1823659 : List Nat := [1, 1, 1, 1, 2, 1, 1, 4, 10]
def baseStart_1823659 : Nat := 118140960795 + 1823659 * 2 ^ 59
def prefixEnd_1823659 : Nat := 4983230072969 + 3 ^ 40 * 1823659 * 2
def baseEnd_1823659 : Nat := 208091914866174590994589

theorem tailTrace_1823659 : CollatzResearch.WordTrace tailWord_1823659 prefixEnd_1823659 208091914866174590994589 := by
  unfold tailWord_1823659
  simp only [CollatzResearch.WordTrace]
  refine ⟨66514308100202374006018031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44342872066801582670678687 66514308100202374006018031)
  ·
    refine ⟨99771462150303561009027047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66514308100202374006018031 99771462150303561009027047)
    ·
      refine ⟨149657193225455341513540571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99771462150303561009027047 149657193225455341513540571)
      ·
        refine ⟨224485789838183012270310857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149657193225455341513540571 224485789838183012270310857)
        ·
          refine ⟨168364342378637259202733143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224485789838183012270310857 168364342378637259202733143)
          ·
            refine ⟨252546513567955888804099715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168364342378637259202733143 252546513567955888804099715)
            ·
              refine ⟨378819770351933833206149573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 252546513567955888804099715 378819770351933833206149573)
              ·
                refine ⟨71028706940987593726153045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 378819770351933833206149573 71028706940987593726153045)
                ·
                  refine ⟨208091914866174590994589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 71028706940987593726153045 208091914866174590994589)
                  ·
                    rfl

theorem cell22_1823659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 10].length) (baseStart_1823659 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1823659 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1823659 prefixEnd_1823659 := by exact prefixLift 1823659
  have htrace : WordTrace (prefixWord ++ tailWord_1823659) baseStart_1823659 baseEnd_1823659 := by
    simpa [prefixWord, tailWord_1823659, baseEnd_1823659] using wordTrace_append hprefix tailTrace_1823659
  have hstable : (prefixWord ++ tailWord_1823659).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1823659).length < 2 ^ (prefixWord ++ tailWord_1823659).sum := by decide
  have hdescent : baseEnd_1823659 < baseStart_1823659 := by decide
  rcases family_descends (prefixWord ++ tailWord_1823659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1823665 : List Nat := [1, 2, 2, 4, 3, 1, 3, 1, 5]
def baseStart_1823665 : Nat := 118140960795 + 1823665 * 2 ^ 59
def prefixEnd_1823665 : Nat := 4983230072969 + 3 ^ 40 * 1823665 * 2
def baseEnd_1823665 : Nat := 208092599507047252444583

theorem tailTrace_1823665 : CollatzResearch.WordTrace tailWord_1823665 prefixEnd_1823665 208092599507047252444583 := by
  unfold tailWord_1823665
  simp only [CollatzResearch.WordTrace]
  refine ⟨66514526938180637030736449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44343017958787091353824299 66514526938180637030736449)
  ·
    refine ⟨49885895203635477773052337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66514526938180637030736449 49885895203635477773052337)
    ·
      refine ⟨37414421402726608329789253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49885895203635477773052337 37414421402726608329789253)
      ·
        refine ⟨7015204013011239061835485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37414421402726608329789253 7015204013011239061835485)
        ·
          refine ⟨2630701504879214648188307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7015204013011239061835485 2630701504879214648188307)
          ·
            refine ⟨3946052257318821972282461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2630701504879214648188307 3946052257318821972282461)
            ·
              refine ⟨1479769596494558239605923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3946052257318821972282461 1479769596494558239605923)
              ·
                refine ⟨2219654394741837359408885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1479769596494558239605923 2219654394741837359408885)
                ·
                  refine ⟨208092599507047252444583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2219654394741837359408885 208092599507047252444583)
                  ·
                    rfl

theorem cell22_1823665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 3, 1, 5].length) (baseStart_1823665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1823665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1823665 prefixEnd_1823665 := by exact prefixLift 1823665
  have htrace : WordTrace (prefixWord ++ tailWord_1823665) baseStart_1823665 baseEnd_1823665 := by
    simpa [prefixWord, tailWord_1823665, baseEnd_1823665] using wordTrace_append hprefix tailTrace_1823665
  have hstable : (prefixWord ++ tailWord_1823665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1823665).length < 2 ^ (prefixWord ++ tailWord_1823665).sum := by decide
  have hdescent : baseEnd_1823665 < baseStart_1823665 := by decide
  rcases family_descends (prefixWord ++ tailWord_1823665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1823811 : List Nat := [1, 1, 1, 3, 1, 2, 3, 2, 8]
def baseStart_1823811 : Nat := 118140960795 + 1823811 * 2 ^ 59
def prefixEnd_1823811 : Nat := 4983230072969 + 3 ^ 40 * 1823811 * 2
def baseEnd_1823811 : Nat := 208109259101615347727767

theorem tailTrace_1823811 : CollatzResearch.WordTrace tailWord_1823811 prefixEnd_1823811 208109259101615347727767 := by
  unfold tailWord_1823811
  simp only [CollatzResearch.WordTrace]
  refine ⟨66519851995651703965551287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44346567997101135977034191 66519851995651703965551287)
  ·
    refine ⟨99779777993477555948326931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66519851995651703965551287 99779777993477555948326931)
    ·
      refine ⟨149669666990216333922490397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99779777993477555948326931 149669666990216333922490397)
      ·
        refine ⟨56126125121331125220933899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149669666990216333922490397 56126125121331125220933899)
        ·
          refine ⟨84189187681996687831400849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56126125121331125220933899 84189187681996687831400849)
          ·
            refine ⟨63141890761497515873550637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84189187681996687831400849 63141890761497515873550637)
            ·
              refine ⟨23678209035561568452581489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63141890761497515873550637 23678209035561568452581489)
              ·
                refine ⟨17758656776671176339436117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23678209035561568452581489 17758656776671176339436117)
                ·
                  refine ⟨208109259101615347727767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17758656776671176339436117 208109259101615347727767)
                  ·
                    rfl

theorem cell22_1823811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 2, 8].length) (baseStart_1823811 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1823811 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1823811 prefixEnd_1823811 := by exact prefixLift 1823811
  have htrace : WordTrace (prefixWord ++ tailWord_1823811) baseStart_1823811 baseEnd_1823811 := by
    simpa [prefixWord, tailWord_1823811, baseEnd_1823811] using wordTrace_append hprefix tailTrace_1823811
  have hstable : (prefixWord ++ tailWord_1823811).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1823811).length < 2 ^ (prefixWord ++ tailWord_1823811).sum := by decide
  have hdescent : baseEnd_1823811 < baseStart_1823811 := by decide
  rcases family_descends (prefixWord ++ tailWord_1823811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1823828 : List Nat := [2, 4, 1, 1, 1, 1, 3, 3, 6]
def baseStart_1823828 : Nat := 118140960795 + 1823828 * 2 ^ 59
def prefixEnd_1823828 : Nat := 4983230072969 + 3 ^ 40 * 1823828 * 2
def baseEnd_1823828 : Nat := 208111198917421221836083

theorem tailTrace_1823828 : CollatzResearch.WordTrace tailWord_1823828 prefixEnd_1823828 208111198917421221836083 := by
  unfold tailWord_1823828
  simp only [CollatzResearch.WordTrace]
  refine ⟨33260236018295057934460069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44346981357726743912613425 33260236018295057934460069)
  ·
    refine ⟨6236294253430323362711263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33260236018295057934460069 6236294253430323362711263)
    ·
      refine ⟨9354441380145485044066895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6236294253430323362711263 9354441380145485044066895)
      ·
        refine ⟨14031662070218227566100343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9354441380145485044066895 14031662070218227566100343)
        ·
          refine ⟨21047493105327341349150515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14031662070218227566100343 21047493105327341349150515)
          ·
            refine ⟨31571239657991012023725773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21047493105327341349150515 31571239657991012023725773)
            ·
              refine ⟨11839214871746629508897165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31571239657991012023725773 11839214871746629508897165)
              ·
                refine ⟨4439705576904986065836437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11839214871746629508897165 4439705576904986065836437)
                ·
                  refine ⟨208111198917421221836083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4439705576904986065836437 208111198917421221836083)
                  ·
                    rfl

theorem cell22_1823828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 3, 6].length) (baseStart_1823828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1823828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1823828 prefixEnd_1823828 := by exact prefixLift 1823828
  have htrace : WordTrace (prefixWord ++ tailWord_1823828) baseStart_1823828 baseEnd_1823828 := by
    simpa [prefixWord, tailWord_1823828, baseEnd_1823828] using wordTrace_append hprefix tailTrace_1823828
  have hstable : (prefixWord ++ tailWord_1823828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1823828).length < 2 ^ (prefixWord ++ tailWord_1823828).sum := by decide
  have hdescent : baseEnd_1823828 < baseStart_1823828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1823828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1823858 : List Nat := [3, 2, 1, 2, 2, 1, 1, 3, 1, 6]
def baseStart_1823858 : Nat := 118140960795 + 1823858 * 2 ^ 59
def prefixEnd_1823858 : Nat := 4983230072969 + 3 ^ 40 * 1823858 * 2
def baseEnd_1823858 : Nat := 624343866365353587258157

theorem tailTrace_1823858 : CollatzResearch.WordTrace tailWord_1823858 prefixEnd_1823858 624343866365353587258157 := by
  unfold tailWord_1823858
  simp only [CollatzResearch.WordTrace]
  refine ⟨16630391556620357748128057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44347710817654287328341485 16630391556620357748128057)
  ·
    refine ⟨12472793667465268311096043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16630391556620357748128057 12472793667465268311096043)
    ·
      refine ⟨18709190501197902466644065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12472793667465268311096043 18709190501197902466644065)
      ·
        refine ⟨14031892875898426849983049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18709190501197902466644065 14031892875898426849983049)
        ·
          refine ⟨10523919656923820137487287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14031892875898426849983049 10523919656923820137487287)
          ·
            refine ⟨15785879485385730206230931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10523919656923820137487287 15785879485385730206230931)
            ·
              refine ⟨23678819228078595309346397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15785879485385730206230931 23678819228078595309346397)
              ·
                refine ⟨8879557210529473241004899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23678819228078595309346397 8879557210529473241004899)
                ·
                  refine ⟨13319335815794209861507349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8879557210529473241004899 13319335815794209861507349)
                  ·
                    refine ⟨624343866365353587258157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13319335815794209861507349 624343866365353587258157)
                    ·
                      rfl

theorem cell22_1823858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 3, 1, 6].length) (baseStart_1823858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1823858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1823858 prefixEnd_1823858 := by exact prefixLift 1823858
  have htrace : WordTrace (prefixWord ++ tailWord_1823858) baseStart_1823858 baseEnd_1823858 := by
    simpa [prefixWord, tailWord_1823858, baseEnd_1823858] using wordTrace_append hprefix tailTrace_1823858
  have hstable : (prefixWord ++ tailWord_1823858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1823858).length < 2 ^ (prefixWord ++ tailWord_1823858).sum := by decide
  have hdescent : baseEnd_1823858 < baseStart_1823858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1823858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1823873 : List Nat := [1, 2, 4, 2, 2, 1, 10]
def baseStart_1823873 : Nat := 118140960795 + 1823873 * 2 ^ 59
def prefixEnd_1823873 : Nat := 4983230072969 + 3 ^ 40 * 1823873 * 2
def baseEnd_1823873 : Nat := 23124037080440686967893

theorem tailTrace_1823873 : CollatzResearch.WordTrace tailWord_1823873 prefixEnd_1823873 23124037080440686967893 := by
  unfold tailWord_1823873
  simp only [CollatzResearch.WordTrace]
  refine ⟨66522113321427088554308273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44348075547618059036205515 66522113321427088554308273)
  ·
    refine ⟨49891584991070316415731205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66522113321427088554308273 49891584991070316415731205)
    ·
      refine ⟨9354672185825684327949601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49891584991070316415731205 9354672185825684327949601)
      ·
        refine ⟨7016004139369263245962201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9354672185825684327949601 7016004139369263245962201)
        ·
          refine ⟨5262003104526947434471651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7016004139369263245962201 5262003104526947434471651)
          ·
            refine ⟨7893004656790421151707477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5262003104526947434471651 7893004656790421151707477)
            ·
              refine ⟨23124037080440686967893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 7893004656790421151707477 23124037080440686967893)
              ·
                rfl

theorem cell22_1823873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 10].length) (baseStart_1823873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1823873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1823873 prefixEnd_1823873 := by exact prefixLift 1823873
  have htrace : WordTrace (prefixWord ++ tailWord_1823873) baseStart_1823873 baseEnd_1823873 := by
    simpa [prefixWord, tailWord_1823873, baseEnd_1823873] using wordTrace_append hprefix tailTrace_1823873
  have hstable : (prefixWord ++ tailWord_1823873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1823873).length < 2 ^ (prefixWord ++ tailWord_1823873).sum := by decide
  have hdescent : baseEnd_1823873 < baseStart_1823873 := by decide
  rcases family_descends (prefixWord ++ tailWord_1823873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1823890 : List Nat := [3, 2, 3, 1, 1, 3, 2, 7]
def baseStart_1823890 : Nat := 118140960795 + 1823890 * 2 ^ 59
def prefixEnd_1823890 : Nat := 4983230072969 + 3 ^ 40 * 1823890 * 2
def baseEnd_1823890 : Nat := 69372757846590685606451

theorem tailTrace_1823890 : CollatzResearch.WordTrace tailWord_1823890 prefixEnd_1823890 69372757846590685606451 := by
  unfold tailWord_1823890
  simp only [CollatzResearch.WordTrace]
  refine ⟨16630683340591375114419281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44348488908243666971784749 16630683340591375114419281)
  ·
    refine ⟨12473012505443531335814461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16630683340591375114419281 12473012505443531335814461)
    ·
      refine ⟨4677379689541324250930423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12473012505443531335814461 4677379689541324250930423)
      ·
        refine ⟨7016069534311986376395635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4677379689541324250930423 7016069534311986376395635)
        ·
          refine ⟨10524104301467979564593453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7016069534311986376395635 10524104301467979564593453)
          ·
            refine ⟨3946539113050492336722545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10524104301467979564593453 3946539113050492336722545)
            ·
              refine ⟨2959904334787869252541909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3946539113050492336722545 2959904334787869252541909)
              ·
                refine ⟨69372757846590685606451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2959904334787869252541909 69372757846590685606451)
                ·
                  rfl

theorem cell22_1823890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 2, 7].length) (baseStart_1823890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1823890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1823890 prefixEnd_1823890 := by exact prefixLift 1823890
  have htrace : WordTrace (prefixWord ++ tailWord_1823890) baseStart_1823890 baseEnd_1823890 := by
    simpa [prefixWord, tailWord_1823890, baseEnd_1823890] using wordTrace_append hprefix tailTrace_1823890
  have hstable : (prefixWord ++ tailWord_1823890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1823890).length < 2 ^ (prefixWord ++ tailWord_1823890).sum := by decide
  have hdescent : baseEnd_1823890 < baseStart_1823890 := by decide
  rcases family_descends (prefixWord ++ tailWord_1823890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1823905 : List Nat := [1, 2, 3, 3, 1, 1, 2, 1, 5, 3]
def baseStart_1823905 : Nat := 118140960795 + 1823905 * 2 ^ 59
def prefixEnd_1823905 : Nat := 4983230072969 + 3 ^ 40 * 1823905 * 2
def baseEnd_1823905 : Nat := 624359955425861131333013

theorem tailTrace_1823905 : CollatzResearch.WordTrace tailWord_1823905 prefixEnd_1823905 624359955425861131333013 := by
  unfold tailWord_1823905
  simp only [CollatzResearch.WordTrace]
  refine ⟨66523280457311158019473169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44348853638207438679648779 66523280457311158019473169)
  ·
    refine ⟨49892460342983368514604877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66523280457311158019473169 49892460342983368514604877)
    ·
      refine ⟨18709672628618763192976829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49892460342983368514604877 18709672628618763192976829)
      ·
        refine ⟨7016127235732036197366311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18709672628618763192976829 7016127235732036197366311)
        ·
          refine ⟨10524190853598054296049467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7016127235732036197366311 10524190853598054296049467)
          ·
            refine ⟨15786286280397081444074201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10524190853598054296049467 15786286280397081444074201)
            ·
              refine ⟨11839714710297811083055651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15786286280397081444074201 11839714710297811083055651)
              ·
                refine ⟨17759572065446716624583477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11839714710297811083055651 17759572065446716624583477)
                ·
                  refine ⟨1664959881135629683554701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17759572065446716624583477 1664959881135629683554701)
                  ·
                    refine ⟨624359955425861131333013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1664959881135629683554701 624359955425861131333013)
                    ·
                      rfl

theorem cell22_1823905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 1, 5, 3].length) (baseStart_1823905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1823905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1823905 prefixEnd_1823905 := by exact prefixLift 1823905
  have htrace : WordTrace (prefixWord ++ tailWord_1823905) baseStart_1823905 baseEnd_1823905 := by
    simpa [prefixWord, tailWord_1823905, baseEnd_1823905] using wordTrace_append hprefix tailTrace_1823905
  have hstable : (prefixWord ++ tailWord_1823905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1823905).length < 2 ^ (prefixWord ++ tailWord_1823905).sum := by decide
  have hdescent : baseEnd_1823905 < baseStart_1823905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1823905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824012 : List Nat := [2, 2, 1, 2, 2, 5, 1, 1, 1, 5]
def baseStart_1824012 : Nat := 118140960795 + 1824012 * 2 ^ 59
def prefixEnd_1824012 : Nat := 4983230072969 + 3 ^ 40 * 1824012 * 2
def baseEnd_1824012 : Nat := 624396583712548518907685

theorem tailTrace_1824012 : CollatzResearch.WordTrace tailWord_1824012 prefixEnd_1824012 624396583712548518907685 := by
  unfold tailWord_1824012
  simp only [CollatzResearch.WordTrace]
  refine ⟨33263591533961757646809145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44351455378615676862412193 33263591533961757646809145)
  ·
    refine ⟨24947693650471318235106859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33263591533961757646809145 24947693650471318235106859)
    ·
      refine ⟨37421540475706977352660289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24947693650471318235106859 37421540475706977352660289)
      ·
        refine ⟨28066155356780233014495217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37421540475706977352660289 28066155356780233014495217)
        ·
          refine ⟨21049616517585174760871413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28066155356780233014495217 21049616517585174760871413)
          ·
            refine ⟨1973401548523610133831695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21049616517585174760871413 1973401548523610133831695)
            ·
              refine ⟨2960102322785415200747543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1973401548523610133831695 2960102322785415200747543)
              ·
                refine ⟨4440153484178122801121315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2960102322785415200747543 4440153484178122801121315)
                ·
                  refine ⟨6660230226267184201681973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4440153484178122801121315 6660230226267184201681973)
                  ·
                    refine ⟨624396583712548518907685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6660230226267184201681973 624396583712548518907685)
                    ·
                      rfl

theorem cell22_1824012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 1, 1, 1, 5].length) (baseStart_1824012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1824012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1824012 prefixEnd_1824012 := by exact prefixLift 1824012
  have htrace : WordTrace (prefixWord ++ tailWord_1824012) baseStart_1824012 baseEnd_1824012 := by
    simpa [prefixWord, tailWord_1824012, baseEnd_1824012] using wordTrace_append hprefix tailTrace_1824012
  have hstable : (prefixWord ++ tailWord_1824012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824012).length < 2 ^ (prefixWord ++ tailWord_1824012).sum := by decide
  have hdescent : baseEnd_1824012 < baseStart_1824012 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824031 : List Nat := [1, 1, 2, 4, 5, 1, 1, 3, 4]
def baseStart_1824031 : Nat := 118140960795 + 1824031 * 2 ^ 59
def prefixEnd_1824031 : Nat := 4983230072969 + 3 ^ 40 * 1824031 * 2
def baseEnd_1824031 : Nat := 208134362600279600894209

theorem tailTrace_1824031 : CollatzResearch.WordTrace tailWord_1824031 prefixEnd_1824031 208134362600279600894209 := by
  unfold tailWord_1824031
  simp only [CollatzResearch.WordTrace]
  refine ⟨66527876054854681538559947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44351917369903121025706631 66527876054854681538559947)
  ·
    refine ⟨99791814082282022307839921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66527876054854681538559947 99791814082282022307839921)
    ·
      refine ⟨74843860561711516730879941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99791814082282022307839921 74843860561711516730879941)
      ·
        refine ⟨14033223855320909387039989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74843860561711516730879941 14033223855320909387039989)
        ·
          refine ⟨1315614736436335255034999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14033223855320909387039989 1315614736436335255034999)
          ·
            refine ⟨1973422104654502882552499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1315614736436335255034999 1973422104654502882552499)
            ·
              refine ⟨2960133156981754323828749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1973422104654502882552499 2960133156981754323828749)
              ·
                refine ⟨1110049933868157871435781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2960133156981754323828749 1110049933868157871435781)
                ·
                  refine ⟨208134362600279600894209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1110049933868157871435781 208134362600279600894209)
                  ·
                    rfl

theorem cell22_1824031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 1, 3, 4].length) (baseStart_1824031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1824031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1824031 prefixEnd_1824031 := by exact prefixLift 1824031
  have htrace : WordTrace (prefixWord ++ tailWord_1824031) baseStart_1824031 baseEnd_1824031 := by
    simpa [prefixWord, tailWord_1824031, baseEnd_1824031] using wordTrace_append hprefix tailTrace_1824031
  have hstable : (prefixWord ++ tailWord_1824031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824031).length < 2 ^ (prefixWord ++ tailWord_1824031).sum := by decide
  have hdescent : baseEnd_1824031 < baseStart_1824031 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824042 : List Nat := [3, 1, 4, 2, 1, 3, 8]
def baseStart_1824042 : Nat := 118140960795 + 1824042 * 2 ^ 59
def prefixEnd_1824042 : Nat := 4983230072969 + 3 ^ 40 * 1824042 * 2
def baseEnd_1824042 : Nat := 23126179752801423728059

theorem tailTrace_1824042 : CollatzResearch.WordTrace tailWord_1824042 prefixEnd_1824042 23126179752801423728059 := by
  unfold tailWord_1824042
  simp only [CollatzResearch.WordTrace]
  refine ⟨16632069314453707604302595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44352184838543220278140253 16632069314453707604302595)
  ·
    refine ⟨24948103971680561406453893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16632069314453707604302595 24948103971680561406453893)
    ·
      refine ⟨4677769494690105263710105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24948103971680561406453893 4677769494690105263710105)
      ·
        refine ⟨3508327121017578947782579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4677769494690105263710105 3508327121017578947782579)
        ·
          refine ⟨5262490681526368421673869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3508327121017578947782579 5262490681526368421673869)
          ·
            refine ⟨1973434005572388158127701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5262490681526368421673869 1973434005572388158127701)
            ·
              refine ⟨23126179752801423728059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1973434005572388158127701 23126179752801423728059)
              ·
                rfl

theorem cell22_1824042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 8].length) (baseStart_1824042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1824042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1824042 prefixEnd_1824042 := by exact prefixLift 1824042
  have htrace : WordTrace (prefixWord ++ tailWord_1824042) baseStart_1824042 baseEnd_1824042 := by
    simpa [prefixWord, tailWord_1824042, baseEnd_1824042] using wordTrace_append hprefix tailTrace_1824042
  have hstable : (prefixWord ++ tailWord_1824042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824042).length < 2 ^ (prefixWord ++ tailWord_1824042).sum := by decide
  have hdescent : baseEnd_1824042 < baseStart_1824042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824104 : List Nat := [2, 1, 4, 2, 3, 1, 2, 2, 5]
def baseStart_1824104 : Nat := 118140960795 + 1824104 * 2 ^ 59
def prefixEnd_1824104 : Nat := 4983230072969 + 3 ^ 40 * 1824104 * 2
def baseEnd_1824104 : Nat := 208142692397563648535801

theorem tailTrace_1824104 : CollatzResearch.WordTrace tailWord_1824104 prefixEnd_1824104 208142692397563648535801 := by
  unfold tailWord_1824104
  simp only [CollatzResearch.WordTrace]
  refine ⟨33265269291795107502983683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44353692389060143337311577 33265269291795107502983683)
  ·
    refine ⟨49897903937692661254475525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33265269291795107502983683 49897903937692661254475525)
    ·
      refine ⟨9355856988317373985214161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49897903937692661254475525 9355856988317373985214161)
      ·
        refine ⟨7016892741238030488910621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9355856988317373985214161 7016892741238030488910621)
        ·
          refine ⟨2631334777964261433341483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7016892741238030488910621 2631334777964261433341483)
          ·
            refine ⟨3947002166946392150012225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2631334777964261433341483 3947002166946392150012225)
            ·
              refine ⟨2960251625209794112509169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3947002166946392150012225 2960251625209794112509169)
              ·
                refine ⟨2220188718907345584381877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2960251625209794112509169 2220188718907345584381877)
                ·
                  refine ⟨208142692397563648535801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2220188718907345584381877 208142692397563648535801)
                  ·
                    rfl

theorem cell22_1824104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 2, 2, 5].length) (baseStart_1824104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1824104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1824104 prefixEnd_1824104 := by exact prefixLift 1824104
  have htrace : WordTrace (prefixWord ++ tailWord_1824104) baseStart_1824104 baseEnd_1824104 := by
    simpa [prefixWord, tailWord_1824104, baseEnd_1824104] using wordTrace_append hprefix tailTrace_1824104
  have hstable : (prefixWord ++ tailWord_1824104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824104).length < 2 ^ (prefixWord ++ tailWord_1824104).sum := by decide
  have hdescent : baseEnd_1824104 < baseStart_1824104 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824108 : List Nat := [2, 2, 1, 1, 5, 3, 2, 2, 1, 3]
def baseStart_1824108 : Nat := 118140960795 + 1824108 * 2 ^ 59
def prefixEnd_1824108 : Nat := 4983230072969 + 3 ^ 40 * 1824108 * 2
def baseEnd_1824108 : Nat := 624429446474436268507391

theorem tailTrace_1824108 : CollatzResearch.WordTrace tailWord_1824108 prefixEnd_1824108 624429446474436268507391 := by
  unfold tailWord_1824108
  simp only [CollatzResearch.WordTrace]
  refine ⟨33265342237787861844556489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44353789650383815792741985 33265342237787861844556489)
  ·
    refine ⟨24949006678340896383417367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33265342237787861844556489 24949006678340896383417367)
    ·
      refine ⟨37423510017511344575126051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24949006678340896383417367 37423510017511344575126051)
      ·
        refine ⟨56135265026267016862689077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37423510017511344575126051 56135265026267016862689077)
        ·
          refine ⟨5262681096212532830877101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56135265026267016862689077 5262681096212532830877101)
          ·
            refine ⟨1973505411079699811578913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5262681096212532830877101 1973505411079699811578913)
            ·
              refine ⟨1480129058309774858684185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1973505411079699811578913 1480129058309774858684185)
              ·
                refine ⟨1110096793732331144013139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1480129058309774858684185 1110096793732331144013139)
                ·
                  refine ⟨1665145190598496716019709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1110096793732331144013139 1665145190598496716019709)
                  ·
                    refine ⟨624429446474436268507391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1665145190598496716019709 624429446474436268507391)
                    ·
                      rfl

theorem cell22_1824108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 2, 2, 1, 3].length) (baseStart_1824108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1824108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1824108 prefixEnd_1824108 := by exact prefixLift 1824108
  have htrace : WordTrace (prefixWord ++ tailWord_1824108) baseStart_1824108 baseEnd_1824108 := by
    simpa [prefixWord, tailWord_1824108, baseEnd_1824108] using wordTrace_append hprefix tailTrace_1824108
  have hstable : (prefixWord ++ tailWord_1824108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824108).length < 2 ^ (prefixWord ++ tailWord_1824108).sum := by decide
  have hdescent : baseEnd_1824108 < baseStart_1824108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824132 : List Nat := [2, 3, 2, 1, 1, 4, 1, 2, 6]
def baseStart_1824132 : Nat := 118140960795 + 1824132 * 2 ^ 59
def prefixEnd_1824132 : Nat := 4983230072969 + 3 ^ 40 * 1824132 * 2
def baseEnd_1824132 : Nat := 208145887388302735302439

theorem tailTrace_1824132 : CollatzResearch.WordTrace tailWord_1824132 prefixEnd_1824132 208145887388302735302439 := by
  unfold tailWord_1824132
  simp only [CollatzResearch.WordTrace]
  refine ⟨33265779913744387893993325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44354373218325850525324433 33265779913744387893993325)
  ·
    refine ⟨12474667467654145460247497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33265779913744387893993325 12474667467654145460247497)
    ·
      refine ⟨9356000600740609095185623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12474667467654145460247497 9356000600740609095185623)
      ·
        refine ⟨14034000901110913642778435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9356000600740609095185623 14034000901110913642778435)
        ·
          refine ⟨21051001351666370464167653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14034000901110913642778435 21051001351666370464167653)
          ·
            refine ⟨3947062753437444462031435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21051001351666370464167653 3947062753437444462031435)
            ·
              refine ⟨5920594130156166693047153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3947062753437444462031435 5920594130156166693047153)
              ·
                refine ⟨4440445597617125019785365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5920594130156166693047153 4440445597617125019785365)
                ·
                  refine ⟨208145887388302735302439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4440445597617125019785365 208145887388302735302439)
                  ·
                    rfl

theorem cell22_1824132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 2, 6].length) (baseStart_1824132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1824132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1824132 prefixEnd_1824132 := by exact prefixLift 1824132
  have htrace : WordTrace (prefixWord ++ tailWord_1824132) baseStart_1824132 baseEnd_1824132 := by
    simpa [prefixWord, tailWord_1824132, baseEnd_1824132] using wordTrace_append hprefix tailTrace_1824132
  have hstable : (prefixWord ++ tailWord_1824132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824132).length < 2 ^ (prefixWord ++ tailWord_1824132).sum := by decide
  have hdescent : baseEnd_1824132 < baseStart_1824132 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824145 : List Nat := [1, 2, 2, 1, 1, 1, 2, 5, 1, 6]
def baseStart_1824145 : Nat := 118140960795 + 1824145 * 2 ^ 59
def prefixEnd_1824145 : Nat := 4983230072969 + 3 ^ 40 * 1824145 * 2
def baseEnd_1824145 : Nat := 624442112330580505332277

theorem tailTrace_1824145 : CollatzResearch.WordTrace tailWord_1824145 prefixEnd_1824145 624442112330580505332277 := by
  unfold tailWord_1824145
  simp only [CollatzResearch.WordTrace]
  refine ⟨66532033976441679008209889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44354689317627786005473259 66532033976441679008209889)
  ·
    refine ⟨49899025482331259256157417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66532033976441679008209889 49899025482331259256157417)
    ·
      refine ⟨37424269111748444442118063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49899025482331259256157417 37424269111748444442118063)
      ·
        refine ⟨56136403667622666663177095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37424269111748444442118063 56136403667622666663177095)
        ·
          refine ⟨84204605501433999994765643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56136403667622666663177095 84204605501433999994765643)
          ·
            refine ⟨126306908252150999992148465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84204605501433999994765643 126306908252150999992148465)
            ·
              refine ⟨94730181189113249994111349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126306908252150999992148465 94730181189113249994111349)
              ·
                refine ⟨8880954486479367186947939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 94730181189113249994111349 8880954486479367186947939)
                ·
                  refine ⟨13321431729719050780421909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8880954486479367186947939 13321431729719050780421909)
                  ·
                    refine ⟨624442112330580505332277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13321431729719050780421909 624442112330580505332277)
                    ·
                      rfl

theorem cell22_1824145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 6].length) (baseStart_1824145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1824145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1824145 prefixEnd_1824145 := by exact prefixLift 1824145
  have htrace : WordTrace (prefixWord ++ tailWord_1824145) baseStart_1824145 baseEnd_1824145 := by
    simpa [prefixWord, tailWord_1824145, baseEnd_1824145] using wordTrace_append hprefix tailTrace_1824145
  have hstable : (prefixWord ++ tailWord_1824145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824145).length < 2 ^ (prefixWord ++ tailWord_1824145).sum := by decide
  have hdescent : baseEnd_1824145 < baseStart_1824145 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824160 : List Nat := [2, 1, 1, 4, 1, 2, 11]
def baseStart_1824160 : Nat := 118140960795 + 1824160 * 2 ^ 59
def prefixEnd_1824160 : Nat := 4983230072969 + 3 ^ 40 * 1824160 * 2
def baseEnd_1824160 : Nat := 23127675819893535785453

theorem tailTrace_1824160 : CollatzResearch.WordTrace tailWord_1824160 prefixEnd_1824160 23127675819893535785453 := by
  unfold tailWord_1824160
  simp only [CollatzResearch.WordTrace]
  refine ⟨33266290535693668285002967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44355054047591557713337289 33266290535693668285002967)
  ·
    refine ⟨49899435803540502427504451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33266290535693668285002967 49899435803540502427504451)
    ·
      refine ⟨74849153705310753641256677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49899435803540502427504451 74849153705310753641256677)
      ·
        refine ⟨14034216319745766307735627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74849153705310753641256677 14034216319745766307735627)
        ·
          refine ⟨21051324479618649461603441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14034216319745766307735627 21051324479618649461603441)
          ·
            refine ⟨15788493359713987096202581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21051324479618649461603441 15788493359713987096202581)
            ·
              refine ⟨23127675819893535785453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 15788493359713987096202581 23127675819893535785453)
              ·
                rfl

theorem cell22_1824160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 11].length) (baseStart_1824160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1824160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1824160 prefixEnd_1824160 := by exact prefixLift 1824160
  have htrace : WordTrace (prefixWord ++ tailWord_1824160) baseStart_1824160 baseEnd_1824160 := by
    simpa [prefixWord, tailWord_1824160, baseEnd_1824160] using wordTrace_append hprefix tailTrace_1824160
  have hstable : (prefixWord ++ tailWord_1824160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824160).length < 2 ^ (prefixWord ++ tailWord_1824160).sum := by decide
  have hdescent : baseEnd_1824160 < baseStart_1824160 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824239 : List Nat := [1, 1, 2, 1, 4, 1, 6, 1, 5]
def baseStart_1824239 : Nat := 118140960795 + 1824239 * 2 ^ 59
def prefixEnd_1824239 : Nat := 4983230072969 + 3 ^ 40 * 1824239 * 2
def baseEnd_1824239 : Nat := 208158096817198531160663

theorem tailTrace_1824239 : CollatzResearch.WordTrace tailWord_1824239 prefixEnd_1824239 208158096817198531160663 := by
  unfold tailWord_1824239
  simp only [CollatzResearch.WordTrace]
  refine ⟨66535462438101133062131771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44356974958734088708087847 66535462438101133062131771)
  ·
    refine ⟨99803193657151699593197657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66535462438101133062131771 99803193657151699593197657)
    ·
      refine ⟨74852395242863774694898243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99803193657151699593197657 74852395242863774694898243)
      ·
        refine ⟨112278592864295662042347365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74852395242863774694898243 112278592864295662042347365)
        ·
          refine ⟨21052236162055436632940131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112278592864295662042347365 21052236162055436632940131)
          ·
            refine ⟨31578354243083154949410197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21052236162055436632940131 31578354243083154949410197)
            ·
              refine ⟨1480235355144522888253603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 31578354243083154949410197 1480235355144522888253603)
              ·
                refine ⟨2220353032716784332380405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1480235355144522888253603 2220353032716784332380405)
                ·
                  refine ⟨208158096817198531160663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2220353032716784332380405 208158096817198531160663)
                  ·
                    rfl

theorem cell22_1824239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 6, 1, 5].length) (baseStart_1824239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1824239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1824239 prefixEnd_1824239 := by exact prefixLift 1824239
  have htrace : WordTrace (prefixWord ++ tailWord_1824239) baseStart_1824239 baseEnd_1824239 := by
    simpa [prefixWord, tailWord_1824239, baseEnd_1824239] using wordTrace_append hprefix tailTrace_1824239
  have hstable : (prefixWord ++ tailWord_1824239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824239).length < 2 ^ (prefixWord ++ tailWord_1824239).sum := by decide
  have hdescent : baseEnd_1824239 < baseStart_1824239 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824282 : List Nat := [3, 1, 1, 3, 1, 1, 1, 1, 5, 5]
def baseStart_1824282 : Nat := 118140960795 + 1824282 * 2 ^ 59
def prefixEnd_1824282 : Nat := 4983230072969 + 3 ^ 40 * 1824282 * 2
def baseEnd_1824282 : Nat := 624489010230357814656857

theorem tailTrace_1824282 : CollatzResearch.WordTrace tailWord_1824282 prefixEnd_1824282 624489010230357814656857 := by
  unfold tailWord_1824282
  simp only [CollatzResearch.WordTrace]
  refine ⟨16634257694236337851486775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44358020517963567603964733 16634257694236337851486775)
  ·
    refine ⟨24951386541354506777230163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16634257694236337851486775 24951386541354506777230163)
    ·
      refine ⟨37427079812031760165845245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24951386541354506777230163 37427079812031760165845245)
      ·
        refine ⟨14035154929511910062191967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37427079812031760165845245 14035154929511910062191967)
        ·
          refine ⟨21052732394267865093287951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14035154929511910062191967 21052732394267865093287951)
          ·
            refine ⟨31579098591401797639931927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21052732394267865093287951 31579098591401797639931927)
            ·
              refine ⟨47368647887102696459897891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31579098591401797639931927 47368647887102696459897891)
              ·
                refine ⟨71052971830654044689846837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47368647887102696459897891 71052971830654044689846837)
                ·
                  refine ⟨6661216109123816689673141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71052971830654044689846837 6661216109123816689673141)
                  ·
                    refine ⟨624489010230357814656857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6661216109123816689673141 624489010230357814656857)
                    ·
                      rfl

theorem cell22_1824282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 5, 5].length) (baseStart_1824282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1824282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1824282 prefixEnd_1824282 := by exact prefixLift 1824282
  have htrace : WordTrace (prefixWord ++ tailWord_1824282) baseStart_1824282 baseEnd_1824282 := by
    simpa [prefixWord, tailWord_1824282, baseEnd_1824282] using wordTrace_append hprefix tailTrace_1824282
  have hstable : (prefixWord ++ tailWord_1824282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824282).length < 2 ^ (prefixWord ++ tailWord_1824282).sum := by decide
  have hdescent : baseEnd_1824282 < baseStart_1824282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824333 : List Nat := [1, 6, 1, 1, 3, 1, 1, 1, 4, 3]
def baseStart_1824333 : Nat := 118140960795 + 1824333 * 2 ^ 59
def prefixEnd_1824333 : Nat := 4983230072969 + 3 ^ 40 * 1824333 * 2
def baseEnd_1824333 : Nat := 624506468572610681631701

theorem tailTrace_1824333 : CollatzResearch.WordTrace tailWord_1824333 prefixEnd_1824333 624506468572610681631701 := by
  unfold tailWord_1824333
  simp only [CollatzResearch.WordTrace]
  refine ⟨66538890899760587116053653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44359260599840391410702435 66538890899760587116053653)
  ·
    refine ⟨3119010510926277521065015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 66538890899760587116053653 3119010510926277521065015)
    ·
      refine ⟨4678515766389416281597523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3119010510926277521065015 4678515766389416281597523)
      ·
        refine ⟨7017773649584124422396285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4678515766389416281597523 7017773649584124422396285)
        ·
          refine ⟨2631665118594046658398607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7017773649584124422396285 2631665118594046658398607)
          ·
            refine ⟨3947497677891069987597911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2631665118594046658398607 3947497677891069987597911)
            ·
              refine ⟨5921246516836604981396867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3947497677891069987597911 5921246516836604981396867)
              ·
                refine ⟨8881869775254907472095301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5921246516836604981396867 8881869775254907472095301)
                ·
                  refine ⟨1665350582860295151017869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8881869775254907472095301 1665350582860295151017869)
                  ·
                    refine ⟨624506468572610681631701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1665350582860295151017869 624506468572610681631701)
                    ·
                      rfl

theorem cell22_1824333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 1, 4, 3].length) (baseStart_1824333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1824333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1824333 prefixEnd_1824333 := by exact prefixLift 1824333
  have htrace : WordTrace (prefixWord ++ tailWord_1824333) baseStart_1824333 baseEnd_1824333 := by
    simpa [prefixWord, tailWord_1824333, baseEnd_1824333] using wordTrace_append hprefix tailTrace_1824333
  have hstable : (prefixWord ++ tailWord_1824333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824333).length < 2 ^ (prefixWord ++ tailWord_1824333).sum := by decide
  have hdescent : baseEnd_1824333 < baseStart_1824333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824408 : List Nat := [2, 1, 2, 4, 1, 4, 2, 1, 5]
def baseStart_1824408 : Nat := 118140960795 + 1824408 * 2 ^ 59
def prefixEnd_1824408 : Nat := 4983230072969 + 3 ^ 40 * 1824408 * 2
def baseEnd_1824408 : Nat := 208177380868445162002157

theorem tailTrace_1824408 : CollatzResearch.WordTrace tailWord_1824408 prefixEnd_1824408 208177380868445162002157 := by
  unfold tailWord_1824408
  simp only [CollatzResearch.WordTrace]
  refine ⟨33270813187244437462516939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44361084249659249950022585 33270813187244437462516939)
  ·
    refine ⟨49906219780866656193775409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33270813187244437462516939 49906219780866656193775409)
    ·
      refine ⟨37429664835649992145331557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49906219780866656193775409 37429664835649992145331557)
      ·
        refine ⟨7018062156684373527249667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37429664835649992145331557 7018062156684373527249667)
        ·
          refine ⟨10527093235026560290874501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7018062156684373527249667 10527093235026560290874501)
          ·
            refine ⟨1973829981567480054538969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10527093235026560290874501 1973829981567480054538969)
            ·
              refine ⟨1480372486175610040904227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1973829981567480054538969 1480372486175610040904227)
              ·
                refine ⟨2220558729263415061356341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1480372486175610040904227 2220558729263415061356341)
                ·
                  refine ⟨208177380868445162002157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2220558729263415061356341 208177380868445162002157)
                  ·
                    rfl

theorem cell22_1824408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 2, 1, 5].length) (baseStart_1824408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1824408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1824408 prefixEnd_1824408 := by exact prefixLift 1824408
  have htrace : WordTrace (prefixWord ++ tailWord_1824408) baseStart_1824408 baseEnd_1824408 := by
    simpa [prefixWord, tailWord_1824408, baseEnd_1824408] using wordTrace_append hprefix tailTrace_1824408
  have hstable : (prefixWord ++ tailWord_1824408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824408).length < 2 ^ (prefixWord ++ tailWord_1824408).sum := by decide
  have hdescent : baseEnd_1824408 < baseStart_1824408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824421 : List Nat := [1, 3, 1, 2, 1, 2, 5, 2, 1, 4]
def baseStart_1824421 : Nat := 118140960795 + 1824421 * 2 ^ 59
def prefixEnd_1824421 : Nat := 4983230072969 + 3 ^ 40 * 1824421 * 2
def baseEnd_1824421 : Nat := 624536592771007785431431

theorem tailTrace_1824421 : CollatzResearch.WordTrace tailWord_1824421 prefixEnd_1824421 624536592771007785431431 := by
  unfold tailWord_1824421
  simp only [CollatzResearch.WordTrace]
  refine ⟨66542100523441778145257117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44361400348961185430171411 66542100523441778145257117)
  ·
    refine ⟨24953287696290666804471419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66542100523441778145257117 24953287696290666804471419)
    ·
      refine ⟨37429931544436000206707129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24953287696290666804471419 37429931544436000206707129)
      ·
        refine ⟨28072448658327000155030347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37429931544436000206707129 28072448658327000155030347)
        ·
          refine ⟨42108672987490500232545521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28072448658327000155030347 42108672987490500232545521)
          ·
            refine ⟨31581504740617875174409141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42108672987490500232545521 31581504740617875174409141)
            ·
              refine ⟨2960766069432925797600857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31581504740617875174409141 2960766069432925797600857)
              ·
                refine ⟨2220574552074694348200643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2960766069432925797600857 2220574552074694348200643)
                ·
                  refine ⟨3330861828112041522300965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2220574552074694348200643 3330861828112041522300965)
                  ·
                    refine ⟨624536592771007785431431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3330861828112041522300965 624536592771007785431431)
                    ·
                      rfl

theorem cell22_1824421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 5, 2, 1, 4].length) (baseStart_1824421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1824421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1824421 prefixEnd_1824421 := by exact prefixLift 1824421
  have htrace : WordTrace (prefixWord ++ tailWord_1824421) baseStart_1824421 baseEnd_1824421 := by
    simpa [prefixWord, tailWord_1824421, baseEnd_1824421] using wordTrace_append hprefix tailTrace_1824421
  have hstable : (prefixWord ++ tailWord_1824421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824421).length < 2 ^ (prefixWord ++ tailWord_1824421).sum := by decide
  have hdescent : baseEnd_1824421 < baseStart_1824421 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824434 : List Nat := [3, 2, 1, 1, 1, 2, 3, 1, 3, 5]
def baseStart_1824434 : Nat := 118140960795 + 1824434 * 2 ^ 59
def prefixEnd_1824434 : Nat := 4983230072969 + 3 ^ 40 * 1824434 * 2
def baseEnd_1824434 : Nat := 624541042936680084856391

theorem tailTrace_1824434 : CollatzResearch.WordTrace tailWord_1824434 prefixEnd_1824434 624541042936680084856391 := by
  unfold tailWord_1824434
  simp only [CollatzResearch.WordTrace]
  refine ⟨16635643668098670341370089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44361716448263120910320237 16635643668098670341370089)
  ·
    refine ⟨12476732751074002756027567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16635643668098670341370089 12476732751074002756027567)
    ·
      refine ⟨18715099126611004134041351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12476732751074002756027567 18715099126611004134041351)
      ·
        refine ⟨28072648689916506201062027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18715099126611004134041351 28072648689916506201062027)
        ·
          refine ⟨42108973034874759301593041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28072648689916506201062027 42108973034874759301593041)
          ·
            refine ⟨31581729776156069476194781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42108973034874759301593041 31581729776156069476194781)
            ·
              refine ⟨11843148666058526053573043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31581729776156069476194781 11843148666058526053573043)
              ·
                refine ⟨17764722999087789080359565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11843148666058526053573043 17764722999087789080359565)
                ·
                  refine ⟨6661771124657920905134837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17764722999087789080359565 6661771124657920905134837)
                  ·
                    refine ⟨624541042936680084856391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6661771124657920905134837 624541042936680084856391)
                    ·
                      rfl

theorem cell22_1824434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 1, 3, 5].length) (baseStart_1824434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1824434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1824434 prefixEnd_1824434 := by exact prefixLift 1824434
  have htrace : WordTrace (prefixWord ++ tailWord_1824434) baseStart_1824434 baseEnd_1824434 := by
    simpa [prefixWord, tailWord_1824434, baseEnd_1824434] using wordTrace_append hprefix tailTrace_1824434
  have hstable : (prefixWord ++ tailWord_1824434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824434).length < 2 ^ (prefixWord ++ tailWord_1824434).sum := by decide
  have hdescent : baseEnd_1824434 < baseStart_1824434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824468 : List Nat := [2, 4, 1, 3, 1, 2, 2, 1, 1, 5]
def baseStart_1824468 : Nat := 118140960795 + 1824468 * 2 ^ 59
def prefixEnd_1824468 : Nat := 4983230072969 + 3 ^ 40 * 1824468 * 2
def baseEnd_1824468 : Nat := 624552681831515329506287

theorem tailTrace_1824468 : CollatzResearch.WordTrace tailWord_1824468 prefixEnd_1824468 624552681831515329506287 := by
  unfold tailWord_1824468
  simp only [CollatzResearch.WordTrace]
  refine ⟨33271907377135752586109029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44362543169514336781478705 33271907377135752586109029)
  ·
    refine ⟨6238482633212953609895443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33271907377135752586109029 6238482633212953609895443)
    ·
      refine ⟨9357723949819430414843165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6238482633212953609895443 9357723949819430414843165)
      ·
        refine ⟨3509146481182286405566187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9357723949819430414843165 3509146481182286405566187)
        ·
          refine ⟨5263719721773429608349281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3509146481182286405566187 5263719721773429608349281)
          ·
            refine ⟨3947789791330072206261961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5263719721773429608349281 3947789791330072206261961)
            ·
              refine ⟨2960842343497554154696471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3947789791330072206261961 2960842343497554154696471)
              ·
                refine ⟨4441263515246331232044707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2960842343497554154696471 4441263515246331232044707)
                ·
                  refine ⟨6661895272869496848067061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4441263515246331232044707 6661895272869496848067061)
                  ·
                    refine ⟨624552681831515329506287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6661895272869496848067061 624552681831515329506287)
                    ·
                      rfl

theorem cell22_1824468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 2, 1, 1, 5].length) (baseStart_1824468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1824468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1824468 prefixEnd_1824468 := by exact prefixLift 1824468
  have htrace : WordTrace (prefixWord ++ tailWord_1824468) baseStart_1824468 baseEnd_1824468 := by
    simpa [prefixWord, tailWord_1824468, baseEnd_1824468] using wordTrace_append hprefix tailTrace_1824468
  have hstable : (prefixWord ++ tailWord_1824468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824468).length < 2 ^ (prefixWord ++ tailWord_1824468).sum := by decide
  have hdescent : baseEnd_1824468 < baseStart_1824468 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824470 : List Nat := [5, 2, 1, 3, 1, 1, 1, 2, 6]
def baseStart_1824470 : Nat := 118140960795 + 1824470 * 2 ^ 59
def prefixEnd_1824470 : Nat := 4983230072969 + 3 ^ 40 * 1824470 * 2
def baseEnd_1824470 : Nat := 208184455490795996985427

theorem tailTrace_1824470 : CollatzResearch.WordTrace tailWord_1824470 prefixEnd_1824470 208184455490795996985427 := by
  unfold tailWord_1824470
  simp only [CollatzResearch.WordTrace]
  refine ⟨4158992981266516219611929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44362591800176173009193909 4158992981266516219611929)
  ·
    refine ⟨3119244735949887164708947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4158992981266516219611929 3119244735949887164708947)
    ·
      refine ⟨4678867103924830747063421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3119244735949887164708947 4678867103924830747063421)
      ·
        refine ⟨1754575163971811530148783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4678867103924830747063421 1754575163971811530148783)
        ·
          refine ⟨2631862745957717295223175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1754575163971811530148783 2631862745957717295223175)
          ·
            refine ⟨3947794118936575942834763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2631862745957717295223175 3947794118936575942834763)
            ·
              refine ⟨5921691178404863914252145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3947794118936575942834763 5921691178404863914252145)
              ·
                refine ⟨4441268383803647935689109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5921691178404863914252145 4441268383803647935689109)
                ·
                  refine ⟨208184455490795996985427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4441268383803647935689109 208184455490795996985427)
                  ·
                    rfl

theorem cell22_1824470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 2, 6].length) (baseStart_1824470 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1824470 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1824470 prefixEnd_1824470 := by exact prefixLift 1824470
  have htrace : WordTrace (prefixWord ++ tailWord_1824470) baseStart_1824470 baseEnd_1824470 := by
    simpa [prefixWord, tailWord_1824470, baseEnd_1824470] using wordTrace_append hprefix tailTrace_1824470
  have hstable : (prefixWord ++ tailWord_1824470).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824470).length < 2 ^ (prefixWord ++ tailWord_1824470).sum := by decide
  have hdescent : baseEnd_1824470 < baseStart_1824470 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824526 : List Nat := [4, 1, 1, 2, 1, 1, 2, 5, 5]
def baseStart_1824526 : Nat := 118140960795 + 1824526 * 2 ^ 59
def prefixEnd_1824526 : Nat := 4983230072969 + 3 ^ 40 * 1824526 * 2
def baseEnd_1824526 : Nat := 208190845472274170518703

theorem tailTrace_1824526 : CollatzResearch.WordTrace tailWord_1824526 prefixEnd_1824526 208190845472274170518703 := by
  unfold tailWord_1824526
  simp only [CollatzResearch.WordTrace]
  refine ⟨8318241273507672634728679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44363953458707587385219621 8318241273507672634728679)
  ·
    refine ⟨12477361910261508952093019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8318241273507672634728679 12477361910261508952093019)
    ·
      refine ⟨18716042865392263428139529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12477361910261508952093019 18716042865392263428139529)
      ·
        refine ⟨14037032149044197571104647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18716042865392263428139529 14037032149044197571104647)
        ·
          refine ⟨21055548223566296356656971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14037032149044197571104647 21055548223566296356656971)
          ·
            refine ⟨31583322335349444534985457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21055548223566296356656971 31583322335349444534985457)
            ·
              refine ⟨23687491751512083401239093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31583322335349444534985457 23687491751512083401239093)
              ·
                refine ⟨2220702351704257818866165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23687491751512083401239093 2220702351704257818866165)
                ·
                  refine ⟨208190845472274170518703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2220702351704257818866165 208190845472274170518703)
                  ·
                    rfl

theorem cell22_1824526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 5, 5].length) (baseStart_1824526 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1824526 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1824526 prefixEnd_1824526 := by exact prefixLift 1824526
  have htrace : WordTrace (prefixWord ++ tailWord_1824526) baseStart_1824526 baseEnd_1824526 := by
    simpa [prefixWord, tailWord_1824526, baseEnd_1824526] using wordTrace_append hprefix tailTrace_1824526
  have hstable : (prefixWord ++ tailWord_1824526).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824526).length < 2 ^ (prefixWord ++ tailWord_1824526).sum := by decide
  have hdescent : baseEnd_1824526 < baseStart_1824526 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824530 : List Nat := [3, 2, 4, 1, 1, 1, 2, 2, 3, 3]
def baseStart_1824530 : Nat := 118140960795 + 1824530 * 2 ^ 59
def prefixEnd_1824530 : Nat := 4983230072969 + 3 ^ 40 * 1824530 * 2
def baseEnd_1824530 : Nat := 624573905698567834456097

theorem tailTrace_1824530 : CollatzResearch.WordTrace tailWord_1824530 prefixEnd_1824530 624573905698567834456097 := by
  unfold tailWord_1824530
  simp only [CollatzResearch.WordTrace]
  refine ⟨16636519020011722440243761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44364050720031259840650029 16636519020011722440243761)
  ·
    refine ⟨12477389265008791830182821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16636519020011722440243761 12477389265008791830182821)
    ·
      refine ⟨2339510487189148468159279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12477389265008791830182821 2339510487189148468159279)
      ·
        refine ⟨3509265730783722702238919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2339510487189148468159279 3509265730783722702238919)
        ·
          refine ⟨5263898596175584053358379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3509265730783722702238919 5263898596175584053358379)
          ·
            refine ⟨7895847894263376080037569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5263898596175584053358379 7895847894263376080037569)
            ·
              refine ⟨5921885920697532060028177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7895847894263376080037569 5921885920697532060028177)
              ·
                refine ⟨4441414440523149045021133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5921885920697532060028177 4441414440523149045021133)
                ·
                  refine ⟨1665530415196180891882925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4441414440523149045021133 1665530415196180891882925)
                  ·
                    refine ⟨624573905698567834456097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1665530415196180891882925 624573905698567834456097)
                    ·
                      rfl

theorem cell22_1824530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_1824530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1824530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1824530 prefixEnd_1824530 := by exact prefixLift 1824530
  have htrace : WordTrace (prefixWord ++ tailWord_1824530) baseStart_1824530 baseEnd_1824530 := by
    simpa [prefixWord, tailWord_1824530, baseEnd_1824530] using wordTrace_append hprefix tailTrace_1824530
  have hstable : (prefixWord ++ tailWord_1824530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824530).length < 2 ^ (prefixWord ++ tailWord_1824530).sum := by decide
  have hdescent : baseEnd_1824530 < baseStart_1824530 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824564 : List Nat := [2, 5, 1, 1, 2, 2, 3, 2, 1, 3]
def baseStart_1824564 : Nat := 118140960795 + 1824564 * 2 ^ 59
def prefixEnd_1824564 : Nat := 4983230072969 + 3 ^ 40 * 1824564 * 2
def baseEnd_1824564 : Nat := 624585544593403079105993

theorem tailTrace_1824564 : CollatzResearch.WordTrace tailWord_1824564 prefixEnd_1824564 624585544593403079105993 := by
  unfold tailWord_1824564
  simp only [CollatzResearch.WordTrace]
  refine ⟨33273658080961856783856373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44364877441282475711808497 33273658080961856783856373)
  ·
    refine ⟨3119405445090174073486535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33273658080961856783856373 3119405445090174073486535)
    ·
      refine ⟨4679108167635261110229803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3119405445090174073486535 4679108167635261110229803)
      ·
        refine ⟨7018662251452891665344705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4679108167635261110229803 7018662251452891665344705)
        ·
          refine ⟨5263996688589668749008529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7018662251452891665344705 5263996688589668749008529)
          ·
            refine ⟨3947997516442251561756397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5263996688589668749008529 3947997516442251561756397)
            ·
              refine ⟨1480499068665844335658649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3947997516442251561756397 1480499068665844335658649)
              ·
                refine ⟨1110374301499383251743987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1480499068665844335658649 1110374301499383251743987)
                ·
                  refine ⟨1665561452249074877615981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1110374301499383251743987 1665561452249074877615981)
                  ·
                    refine ⟨624585544593403079105993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1665561452249074877615981 624585544593403079105993)
                    ·
                      rfl

theorem cell22_1824564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 3, 2, 1, 3].length) (baseStart_1824564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1824564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1824564 prefixEnd_1824564 := by exact prefixLift 1824564
  have htrace : WordTrace (prefixWord ++ tailWord_1824564) baseStart_1824564 baseEnd_1824564 := by
    simpa [prefixWord, tailWord_1824564, baseEnd_1824564] using wordTrace_append hprefix tailTrace_1824564
  have hstable : (prefixWord ++ tailWord_1824564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824564).length < 2 ^ (prefixWord ++ tailWord_1824564).sum := by decide
  have hdescent : baseEnd_1824564 < baseStart_1824564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824586 : List Nat := [3, 1, 2, 1, 1, 1, 4, 3, 1, 5]
def baseStart_1824586 : Nat := 118140960795 + 1824586 * 2 ^ 59
def prefixEnd_1824586 : Nat := 4983230072969 + 3 ^ 40 * 1824586 * 2
def baseEnd_1824586 : Nat := 624593075643002355055925

theorem tailTrace_1824586 : CollatzResearch.WordTrace tailWord_1824586 prefixEnd_1824586 624593075643002355055925 := by
  unfold tailWord_1824586
  simp only [CollatzResearch.WordTrace]
  refine ⟨16637029641961002831253403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44365412378562674216675741 16637029641961002831253403)
  ·
    refine ⟨24955544462941504246880105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16637029641961002831253403 24955544462941504246880105)
    ·
      refine ⟨18716658347206128185160079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24955544462941504246880105 18716658347206128185160079)
      ·
        refine ⟨28074987520809192277740119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18716658347206128185160079 28074987520809192277740119)
        ·
          refine ⟨42112481281213788416610179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28074987520809192277740119 42112481281213788416610179)
          ·
            refine ⟨63168721921820682624915269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42112481281213788416610179 63168721921820682624915269)
            ·
              refine ⟨11844135360341377992171613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63168721921820682624915269 11844135360341377992171613)
              ·
                refine ⟨4441550760128016747064355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11844135360341377992171613 4441550760128016747064355)
                ·
                  refine ⟨6662326140192025120596533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4441550760128016747064355 6662326140192025120596533)
                  ·
                    refine ⟨624593075643002355055925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6662326140192025120596533 624593075643002355055925)
                    ·
                      rfl

theorem cell22_1824586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 3, 1, 5].length) (baseStart_1824586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1824586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1824586 prefixEnd_1824586 := by exact prefixLift 1824586
  have htrace : WordTrace (prefixWord ++ tailWord_1824586) baseStart_1824586 baseEnd_1824586 := by
    simpa [prefixWord, tailWord_1824586, baseEnd_1824586] using wordTrace_append hprefix tailTrace_1824586
  have hstable : (prefixWord ++ tailWord_1824586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824586).length < 2 ^ (prefixWord ++ tailWord_1824586).sum := by decide
  have hdescent : baseEnd_1824586 < baseStart_1824586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824620 : List Nat := [2, 2, 1, 1, 4, 3, 2, 2, 2, 3]
def baseStart_1824620 : Nat := 118140960795 + 1824620 * 2 ^ 59
def prefixEnd_1824620 : Nat := 4983230072969 + 3 ^ 40 * 1824620 * 2
def baseEnd_1824620 : Nat := 624604714537837599705821

theorem tailTrace_1824620 : CollatzResearch.WordTrace tailWord_1824620 prefixEnd_1824620 624604714537837599705821 := by
  unfold tailWord_1824620
  simp only [CollatzResearch.WordTrace]
  refine ⟨33274679324860417565875657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44366239099813890087834209 33274679324860417565875657)
  ·
    refine ⟨24956009493645313174406743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33274679324860417565875657 24956009493645313174406743)
    ·
      refine ⟨37434014240467969761610115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24956009493645313174406743 37434014240467969761610115)
      ·
        refine ⟨56151021360701954642415173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37434014240467969761610115 56151021360701954642415173)
        ·
          refine ⟨10528316505131616495452845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56151021360701954642415173 10528316505131616495452845)
          ·
            refine ⟨3948118689424356185794817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10528316505131616495452845 3948118689424356185794817)
            ·
              refine ⟨2961089017068267139346113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3948118689424356185794817 2961089017068267139346113)
              ·
                refine ⟨2220816762801200354509585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2961089017068267139346113 2220816762801200354509585)
                ·
                  refine ⟨1665612572100900265882189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2220816762801200354509585 1665612572100900265882189)
                  ·
                    refine ⟨624604714537837599705821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1665612572100900265882189 624604714537837599705821)
                    ·
                      rfl

theorem cell22_1824620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 3].length) (baseStart_1824620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1824620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1824620 prefixEnd_1824620 := by exact prefixLift 1824620
  have htrace : WordTrace (prefixWord ++ tailWord_1824620) baseStart_1824620 baseEnd_1824620 := by
    simpa [prefixWord, tailWord_1824620, baseEnd_1824620] using wordTrace_append hprefix tailTrace_1824620
  have hstable : (prefixWord ++ tailWord_1824620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824620).length < 2 ^ (prefixWord ++ tailWord_1824620).sum := by decide
  have hdescent : baseEnd_1824620 < baseStart_1824620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824622 : List Nat := [4, 1, 2, 3, 1, 1, 4, 2, 4]
def baseStart_1824622 : Nat := 118140960795 + 1824622 * 2 ^ 59
def prefixEnd_1824622 : Nat := 4983230072969 + 3 ^ 40 * 1824622 * 2
def baseEnd_1824622 : Nat := 208201799726236753718605

theorem tailTrace_1824622 : CollatzResearch.WordTrace tailWord_1824622 prefixEnd_1824622 208201799726236753718605 := by
  unfold tailWord_1824622
  simp only [CollatzResearch.WordTrace]
  refine ⟨8318678949464198684165515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44366287730475726315549413 8318678949464198684165515)
  ·
    refine ⟨12478018424196298026248273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8318678949464198684165515 12478018424196298026248273)
    ·
      refine ⟨9358513818147223519686205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12478018424196298026248273 9358513818147223519686205)
      ·
        refine ⟨3509442681805208819882327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9358513818147223519686205 3509442681805208819882327)
        ·
          refine ⟨5264164022707813229823491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3509442681805208819882327 5264164022707813229823491)
          ·
            refine ⟨7896246034061719844735237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5264164022707813229823491 7896246034061719844735237)
            ·
              refine ⟨1480546131386572470887857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7896246034061719844735237 1480546131386572470887857)
              ·
                refine ⟨1110409598539929353165893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1480546131386572470887857 1110409598539929353165893)
                ·
                  refine ⟨208201799726236753718605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1110409598539929353165893 208201799726236753718605)
                  ·
                    rfl

theorem cell22_1824622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 4, 2, 4].length) (baseStart_1824622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1824622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1824622 prefixEnd_1824622 := by exact prefixLift 1824622
  have htrace : WordTrace (prefixWord ++ tailWord_1824622) baseStart_1824622 baseEnd_1824622 := by
    simpa [prefixWord, tailWord_1824622, baseEnd_1824622] using wordTrace_append hprefix tailTrace_1824622
  have hstable : (prefixWord ++ tailWord_1824622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824622).length < 2 ^ (prefixWord ++ tailWord_1824622).sum := by decide
  have hdescent : baseEnd_1824622 < baseStart_1824622 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824650 : List Nat := [3, 1, 2, 4, 2, 1, 3, 6]
def baseStart_1824650 : Nat := 118140960795 + 1824650 * 2 ^ 59
def prefixEnd_1824650 : Nat := 4983230072969 + 3 ^ 40 * 1824650 * 2
def baseEnd_1824650 : Nat := 69401664905658613495081

theorem tailTrace_1824650 : CollatzResearch.WordTrace tailWord_1824650 prefixEnd_1824650 69401664905658613495081 := by
  unfold tailWord_1824650
  simp only [CollatzResearch.WordTrace]
  refine ⟨16637613209903037563835851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44366968559741433503562269 16637613209903037563835851)
  ·
    refine ⟨24956419814854556345753777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16637613209903037563835851 24956419814854556345753777)
    ·
      refine ⟨18717314861140917259315333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24956419814854556345753777 18717314861140917259315333)
      ·
        refine ⟨3509496536463921986121625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18717314861140917259315333 3509496536463921986121625)
        ·
          refine ⟨2632122402347941489591219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3509496536463921986121625 2632122402347941489591219)
          ·
            refine ⟨3948183603521912234386829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2632122402347941489591219 3948183603521912234386829)
            ·
              refine ⟨1480568851320717087895061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3948183603521912234386829 1480568851320717087895061)
              ·
                refine ⟨69401664905658613495081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1480568851320717087895061 69401664905658613495081)
                ·
                  rfl

theorem cell22_1824650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 3, 6].length) (baseStart_1824650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1824650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1824650 prefixEnd_1824650 := by exact prefixLift 1824650
  have htrace : WordTrace (prefixWord ++ tailWord_1824650) baseStart_1824650 baseEnd_1824650 := by
    simpa [prefixWord, tailWord_1824650, baseEnd_1824650] using wordTrace_append hprefix tailTrace_1824650
  have hstable : (prefixWord ++ tailWord_1824650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824650).length < 2 ^ (prefixWord ++ tailWord_1824650).sum := by decide
  have hdescent : baseEnd_1824650 < baseStart_1824650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824661 : List Nat := [1, 3, 2, 1, 1, 3, 2, 2, 7]
def baseStart_1824661 : Nat := 118140960795 + 1824661 * 2 ^ 59
def prefixEnd_1824661 : Nat := 4983230072969 + 3 ^ 40 * 1824661 * 2
def baseEnd_1824661 : Nat := 208206249891909053143565

theorem tailTrace_1824661 : CollatzResearch.WordTrace tailWord_1824661 prefixEnd_1824661 208206249891909053143565 := by
  unfold tailWord_1824661
  simp only [CollatzResearch.WordTrace]
  refine ⟨66550854042572299133993837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44367236028381532755995891 66550854042572299133993837)
  ·
    refine ⟨24956570265964612175247689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66550854042572299133993837 24956570265964612175247689)
    ·
      refine ⟨18717427699473459131435767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24956570265964612175247689 18717427699473459131435767)
      ·
        refine ⟨28076141549210188697153651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18717427699473459131435767 28076141549210188697153651)
        ·
          refine ⟨42114212323815283045730477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28076141549210188697153651 42114212323815283045730477)
          ·
            refine ⟨15792829621430731142148929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42114212323815283045730477 15792829621430731142148929)
            ·
              refine ⟨11844622216073048356611697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15792829621430731142148929 11844622216073048356611697)
              ·
                refine ⟨8883466662054786267458773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11844622216073048356611697 8883466662054786267458773)
                ·
                  refine ⟨208206249891909053143565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8883466662054786267458773 208206249891909053143565)
                  ·
                    rfl

theorem cell22_1824661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 2, 7].length) (baseStart_1824661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1824661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1824661 prefixEnd_1824661 := by exact prefixLift 1824661
  have htrace : WordTrace (prefixWord ++ tailWord_1824661) baseStart_1824661 baseEnd_1824661 := by
    simpa [prefixWord, tailWord_1824661, baseEnd_1824661] using wordTrace_append hprefix tailTrace_1824661
  have hstable : (prefixWord ++ tailWord_1824661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824661).length < 2 ^ (prefixWord ++ tailWord_1824661).sum := by decide
  have hdescent : baseEnd_1824661 < baseStart_1824661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824665 : List Nat := [1, 2, 1, 2, 1, 3, 3, 5, 1, 3]
def baseStart_1824665 : Nat := 118140960795 + 1824665 * 2 ^ 59
def prefixEnd_1824665 : Nat := 4983230072969 + 3 ^ 40 * 1824665 * 2
def baseEnd_1824665 : Nat := 624620118957472482330683

theorem tailTrace_1824665 : CollatzResearch.WordTrace tailWord_1824665 prefixEnd_1824665 624620118957472482330683 := by
  unfold tailWord_1824665
  simp only [CollatzResearch.WordTrace]
  refine ⟨66550999934557807817139449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44367333289705205211426299 66550999934557807817139449)
  ·
    refine ⟨49913249950918355862854587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66550999934557807817139449 49913249950918355862854587)
    ·
      refine ⟨74869874926377533794281881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49913249950918355862854587 74869874926377533794281881)
      ·
        refine ⟨56152406194783150345711411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74869874926377533794281881 56152406194783150345711411)
        ·
          refine ⟨84228609292174725518567117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56152406194783150345711411 84228609292174725518567117)
          ·
            refine ⟨31585728484565522069462669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84228609292174725518567117 31585728484565522069462669)
            ·
              refine ⟨11844648181712070776048501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31585728484565522069462669 11844648181712070776048501)
              ·
                refine ⟨1110435767035506635254547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11844648181712070776048501 1110435767035506635254547)
                ·
                  refine ⟨1665653650553259952881821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1110435767035506635254547 1665653650553259952881821)
                  ·
                    refine ⟨624620118957472482330683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1665653650553259952881821 624620118957472482330683)
                    ·
                      rfl

theorem cell22_1824665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 5, 1, 3].length) (baseStart_1824665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1824665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1824665 prefixEnd_1824665 := by exact prefixLift 1824665
  have htrace : WordTrace (prefixWord ++ tailWord_1824665) baseStart_1824665 baseEnd_1824665 := by
    simpa [prefixWord, tailWord_1824665, baseEnd_1824665] using wordTrace_append hprefix tailTrace_1824665
  have hstable : (prefixWord ++ tailWord_1824665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824665).length < 2 ^ (prefixWord ++ tailWord_1824665).sum := by decide
  have hdescent : baseEnd_1824665 < baseStart_1824665 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824693 : List Nat := [1, 3, 3, 2, 1, 2, 2, 1, 2, 5]
def baseStart_1824693 : Nat := 118140960795 + 1824693 * 2 ^ 59
def prefixEnd_1824693 : Nat := 4983230072969 + 3 ^ 40 * 1824693 * 2
def baseEnd_1824693 : Nat := 624629703929689742630597

theorem tailTrace_1824693 : CollatzResearch.WordTrace tailWord_1824693 prefixEnd_1824693 624629703929689742630597 := by
  unfold tailWord_1824693
  simp only [CollatzResearch.WordTrace]
  refine ⟨66552021178456368599158733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44368014118970912399439155 66552021178456368599158733)
  ·
    refine ⟨24957007941921138224684525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66552021178456368599158733 24957007941921138224684525)
    ·
      refine ⟨9358877978220426834256697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24957007941921138224684525 9358877978220426834256697)
      ·
        refine ⟨7019158483665320125692523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9358877978220426834256697 7019158483665320125692523)
        ·
          refine ⟨10528737725497980188538785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7019158483665320125692523 10528737725497980188538785)
          ·
            refine ⟨7896553294123485141404089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10528737725497980188538785 7896553294123485141404089)
            ·
              refine ⟨5922414970592613856053067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7896553294123485141404089 5922414970592613856053067)
              ·
                refine ⟨8883622455888920784079601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5922414970592613856053067 8883622455888920784079601)
                ·
                  refine ⟨6662716841916690588059701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8883622455888920784079601 6662716841916690588059701)
                  ·
                    refine ⟨624629703929689742630597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6662716841916690588059701 624629703929689742630597)
                    ·
                      rfl

theorem cell22_1824693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 1, 2, 5].length) (baseStart_1824693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1824693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1824693 prefixEnd_1824693 := by exact prefixLift 1824693
  have htrace : WordTrace (prefixWord ++ tailWord_1824693) baseStart_1824693 baseEnd_1824693 := by
    simpa [prefixWord, tailWord_1824693, baseEnd_1824693] using wordTrace_append hprefix tailTrace_1824693
  have hstable : (prefixWord ++ tailWord_1824693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824693).length < 2 ^ (prefixWord ++ tailWord_1824693).sum := by decide
  have hdescent : baseEnd_1824693 < baseStart_1824693 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824725 : List Nat := [1, 3, 2, 3, 2, 1, 2, 3, 1, 4]
def baseStart_1824725 : Nat := 118140960795 + 1824725 * 2 ^ 59
def prefixEnd_1824725 : Nat := 4983230072969 + 3 ^ 40 * 1824725 * 2
def baseEnd_1824725 : Nat := 624640658183652325830499

theorem tailTrace_1824725 : CollatzResearch.WordTrace tailWord_1824725 prefixEnd_1824725 624640658183652325830499 := by
  unfold tailWord_1824725
  simp only [CollatzResearch.WordTrace]
  refine ⟨66553188314340438064323629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44368792209560292042882419 66553188314340438064323629)
  ·
    refine ⟨24957445617877664274121361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66553188314340438064323629 24957445617877664274121361)
    ·
      refine ⟨18718084213408248205591021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24957445617877664274121361 18718084213408248205591021)
      ·
        refine ⟨7019281580028093077096633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18718084213408248205591021 7019281580028093077096633)
        ·
          refine ⟨5264461185021069807822475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7019281580028093077096633 5264461185021069807822475)
          ·
            refine ⟨7896691777531604711733713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5264461185021069807822475 7896691777531604711733713)
            ·
              refine ⟨5922518833148703533800285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7896691777531604711733713 5922518833148703533800285)
              ·
                refine ⟨2220944562430763825175107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5922518833148703533800285 2220944562430763825175107)
                ·
                  refine ⟨3331416843646145737762661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2220944562430763825175107 3331416843646145737762661)
                  ·
                    refine ⟨624640658183652325830499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3331416843646145737762661 624640658183652325830499)
                    ·
                      rfl

theorem cell22_1824725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 3, 1, 4].length) (baseStart_1824725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1824725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1824725 prefixEnd_1824725 := by exact prefixLift 1824725
  have htrace : WordTrace (prefixWord ++ tailWord_1824725) baseStart_1824725 baseEnd_1824725 := by
    simpa [prefixWord, tailWord_1824725, baseEnd_1824725] using wordTrace_append hprefix tailTrace_1824725
  have hstable : (prefixWord ++ tailWord_1824725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824725).length < 2 ^ (prefixWord ++ tailWord_1824725).sum := by decide
  have hdescent : baseEnd_1824725 < baseStart_1824725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824772 : List Nat := [2, 3, 2, 4, 1, 1, 1, 2, 1, 5]
def baseStart_1824772 : Nat := 118140960795 + 1824772 * 2 ^ 59
def prefixEnd_1824772 : Nat := 4983230072969 + 3 ^ 40 * 1824772 * 2
def baseEnd_1824772 : Nat := 624656747244159869905355

theorem tailTrace_1824772 : CollatzResearch.WordTrace tailWord_1824772 prefixEnd_1824772 624656747244159869905355 := by
  unfold tailWord_1824772
  simp only [CollatzResearch.WordTrace]
  refine ⟨33277451272585082545642285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44369935030113443394189713 33277451272585082545642285)
  ·
    refine ⟨12479044227219405954615857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33277451272585082545642285 12479044227219405954615857)
    ·
      refine ⟨9359283170414554465961893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12479044227219405954615857 9359283170414554465961893)
      ·
        refine ⟨1754865594452728962367855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9359283170414554465961893 1754865594452728962367855)
        ·
          refine ⟨2632298391679093443551783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1754865594452728962367855 2632298391679093443551783)
          ·
            refine ⟨3948447587518640165327675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2632298391679093443551783 3948447587518640165327675)
            ·
              refine ⟨5922671381277960247991513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3948447587518640165327675 5922671381277960247991513)
              ·
                refine ⟨4442003535958470185993635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5922671381277960247991513 4442003535958470185993635)
                ·
                  refine ⟨6663005303937705278990453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4442003535958470185993635 6663005303937705278990453)
                  ·
                    refine ⟨624656747244159869905355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6663005303937705278990453 624656747244159869905355)
                    ·
                      rfl

theorem cell22_1824772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 2, 1, 5].length) (baseStart_1824772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1824772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1824772 prefixEnd_1824772 := by exact prefixLift 1824772
  have htrace : WordTrace (prefixWord ++ tailWord_1824772) baseStart_1824772 baseEnd_1824772 := by
    simpa [prefixWord, tailWord_1824772, baseEnd_1824772] using wordTrace_append hprefix tailTrace_1824772
  have hstable : (prefixWord ++ tailWord_1824772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824772).length < 2 ^ (prefixWord ++ tailWord_1824772).sum := by decide
  have hdescent : baseEnd_1824772 < baseStart_1824772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824791 : List Nat := [1, 1, 3, 5, 3, 1, 2, 2, 4]
def baseStart_1824791 : Nat := 118140960795 + 1824791 * 2 ^ 59
def prefixEnd_1824791 : Nat := 4983230072969 + 3 ^ 40 * 1824791 * 2
def baseEnd_1824791 : Nat := 208221083777483384560099

theorem tailTrace_1824791 : CollatzResearch.WordTrace tailWord_1824791 prefixEnd_1824791 208221083777483384560099 := by
  unfold tailWord_1824791
  simp only [CollatzResearch.WordTrace]
  refine ⟨66555595532101331336226227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44370397021400887557484151 66555595532101331336226227)
  ·
    refine ⟨99833393298151997004339341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66555595532101331336226227 99833393298151997004339341)
    ·
      refine ⟨37437522486806998876627253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99833393298151997004339341 37437522486806998876627253)
      ·
        refine ⟨3509767733138156144683805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37437522486806998876627253 3509767733138156144683805)
        ·
          refine ⟨1316162899926808554256427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3509767733138156144683805 1316162899926808554256427)
          ·
            refine ⟨1974244349890212831384641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1316162899926808554256427 1974244349890212831384641)
            ·
              refine ⟨1480683262417659623538481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1974244349890212831384641 1480683262417659623538481)
              ·
                refine ⟨1110512446813244717653861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1480683262417659623538481 1110512446813244717653861)
                ·
                  refine ⟨208221083777483384560099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1110512446813244717653861 208221083777483384560099)
                  ·
                    rfl

theorem cell22_1824791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 2, 2, 4].length) (baseStart_1824791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1824791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1824791 prefixEnd_1824791 := by exact prefixLift 1824791
  have htrace : WordTrace (prefixWord ++ tailWord_1824791) baseStart_1824791 baseEnd_1824791 := by
    simpa [prefixWord, tailWord_1824791, baseEnd_1824791] using wordTrace_append hprefix tailTrace_1824791
  have hstable : (prefixWord ++ tailWord_1824791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824791).length < 2 ^ (prefixWord ++ tailWord_1824791).sum := by decide
  have hdescent : baseEnd_1824791 < baseStart_1824791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824828 : List Nat := [2, 2, 2, 2, 2, 1, 1, 2, 1, 7]
def baseStart_1824828 : Nat := 118140960795 + 1824828 * 2 ^ 59
def prefixEnd_1824828 : Nat := 4983230072969 + 3 ^ 40 * 1824828 * 2
def baseEnd_1824828 : Nat := 624675917188594390505183

theorem tailTrace_1824828 : CollatzResearch.WordTrace tailWord_1824828 prefixEnd_1824828 624675917188594390505183 := by
  unfold tailWord_1824828
  simp only [CollatzResearch.WordTrace]
  refine ⟨33278472516483643327661569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44371296688644857770215425 33278472516483643327661569)
  ·
    refine ⟨24958854387362732495746177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33278472516483643327661569 24958854387362732495746177)
    ·
      refine ⟨18719140790522049371809633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24958854387362732495746177 18719140790522049371809633)
      ·
        refine ⟨14039355592891537028857225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18719140790522049371809633 14039355592891537028857225)
        ·
          refine ⟨10529516694668652771642919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14039355592891537028857225 10529516694668652771642919)
          ·
            refine ⟨15794275042002979157464379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10529516694668652771642919 15794275042002979157464379)
            ·
              refine ⟨23691412563004468736196569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15794275042002979157464379 23691412563004468736196569)
              ·
                refine ⟨17768559422253351552147427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23691412563004468736196569 17768559422253351552147427)
                ·
                  refine ⟨26652839133380027328221141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17768559422253351552147427 26652839133380027328221141)
                  ·
                    refine ⟨624675917188594390505183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26652839133380027328221141 624675917188594390505183)
                    ·
                      rfl

theorem cell22_1824828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 2, 1, 7].length) (baseStart_1824828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1824828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1824828 prefixEnd_1824828 := by exact prefixLift 1824828
  have htrace : WordTrace (prefixWord ++ tailWord_1824828) baseStart_1824828 baseEnd_1824828 := by
    simpa [prefixWord, tailWord_1824828, baseEnd_1824828] using wordTrace_append hprefix tailTrace_1824828
  have hstable : (prefixWord ++ tailWord_1824828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824828).length < 2 ^ (prefixWord ++ tailWord_1824828).sum := by decide
  have hdescent : baseEnd_1824828 < baseStart_1824828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824845 : List Nat := [1, 6, 1, 1, 1, 1, 1, 1, 4, 5]
def baseStart_1824845 : Nat := 118140960795 + 1824845 * 2 ^ 59
def prefixEnd_1824845 : Nat := 4983230072969 + 3 ^ 40 * 1824845 * 2
def baseEnd_1824845 : Nat := 624681736636012012830131

theorem tailTrace_1824845 : CollatzResearch.WordTrace tailWord_1824845 prefixEnd_1824845 624681736636012012830131 := by
  unfold tailWord_1824845
  simp only [CollatzResearch.WordTrace]
  refine ⟨66557565073905698558691989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44371710049270465705794659 66557565073905698558691989)
  ·
    refine ⟨3119885862839329619938687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 66557565073905698558691989 3119885862839329619938687)
    ·
      refine ⟨4679828794258994429908031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3119885862839329619938687 4679828794258994429908031)
      ·
        refine ⟨7019743191388491644862047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4679828794258994429908031 7019743191388491644862047)
        ·
          refine ⟨10529614787082737467293071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7019743191388491644862047 10529614787082737467293071)
          ·
            refine ⟨15794422180624106200939607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10529614787082737467293071 15794422180624106200939607)
            ·
              refine ⟨23691633270936159301409411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15794422180624106200939607 23691633270936159301409411)
              ·
                refine ⟨35537449906404238952114117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23691633270936159301409411 35537449906404238952114117)
                ·
                  refine ⟨6663271857450794803521397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35537449906404238952114117 6663271857450794803521397)
                  ·
                    refine ⟨624681736636012012830131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6663271857450794803521397 624681736636012012830131)
                    ·
                      rfl

theorem cell22_1824845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_1824845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1824845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1824845 prefixEnd_1824845 := by exact prefixLift 1824845
  have htrace : WordTrace (prefixWord ++ tailWord_1824845) baseStart_1824845 baseEnd_1824845 := by
    simpa [prefixWord, tailWord_1824845, baseEnd_1824845] using wordTrace_append hprefix tailTrace_1824845
  have hstable : (prefixWord ++ tailWord_1824845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824845).length < 2 ^ (prefixWord ++ tailWord_1824845).sum := by decide
  have hdescent : baseEnd_1824845 < baseStart_1824845 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824877 : List Nat := [1, 5, 1, 1, 2, 1, 4, 2, 1, 4]
def baseStart_1824877 : Nat := 118140960795 + 1824877 * 2 ^ 59
def prefixEnd_1824877 : Nat := 4983230072969 + 3 ^ 40 * 1824877 * 2
def baseEnd_1824877 : Nat := 624692690889974596030033

theorem tailTrace_1824877 : CollatzResearch.WordTrace tailWord_1824877 prefixEnd_1824877 624692690889974596030033 := by
  unfold tailWord_1824877
  simp only [CollatzResearch.WordTrace]
  refine ⟨66558732209789768023856885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44372488139859845349237923 66558732209789768023856885)
  ·
    refine ⟨6239881144667790752236583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 66558732209789768023856885 6239881144667790752236583)
    ·
      refine ⟨9359821717001686128354875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6239881144667790752236583 9359821717001686128354875)
      ·
        refine ⟨14039732575502529192532313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9359821717001686128354875 14039732575502529192532313)
        ·
          refine ⟨10529799431626896894399235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14039732575502529192532313 10529799431626896894399235)
          ·
            refine ⟨15794699147440345341598853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10529799431626896894399235 15794699147440345341598853)
            ·
              refine ⟨2961506090145064751549785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15794699147440345341598853 2961506090145064751549785)
              ·
                refine ⟨2221129567608798563662339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2961506090145064751549785 2221129567608798563662339)
                ·
                  refine ⟨3331694351413197845493509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2221129567608798563662339 3331694351413197845493509)
                  ·
                    refine ⟨624692690889974596030033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3331694351413197845493509 624692690889974596030033)
                    ·
                      rfl

theorem cell22_1824877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 4, 2, 1, 4].length) (baseStart_1824877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1824877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1824877 prefixEnd_1824877 := by exact prefixLift 1824877
  have htrace : WordTrace (prefixWord ++ tailWord_1824877) baseStart_1824877 baseEnd_1824877 := by
    simpa [prefixWord, tailWord_1824877, baseEnd_1824877] using wordTrace_append hprefix tailTrace_1824877
  have hstable : (prefixWord ++ tailWord_1824877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824877).length < 2 ^ (prefixWord ++ tailWord_1824877).sum := by decide
  have hdescent : baseEnd_1824877 < baseStart_1824877 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824892 : List Nat := [2, 2, 2, 1, 1, 4, 3, 3, 4]
def baseStart_1824892 : Nat := 118140960795 + 1824892 * 2 ^ 59
def prefixEnd_1824892 : Nat := 4983230072969 + 3 ^ 40 * 1824892 * 2
def baseEnd_1824892 : Nat := 208232608565506518968329

theorem tailTrace_1824892 : CollatzResearch.WordTrace tailWord_1824892 prefixEnd_1824892 208232608565506518968329 := by
  unfold tailWord_1824892
  simp only [CollatzResearch.WordTrace]
  refine ⟨33279639652367712792826465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44372852869823617057101953 33279639652367712792826465)
  ·
    refine ⟨24959729739275784594619849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33279639652367712792826465 24959729739275784594619849)
    ·
      refine ⟨18719797304456838445964887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24959729739275784594619849 18719797304456838445964887)
      ·
        refine ⟨28079695956685257668947331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18719797304456838445964887 28079695956685257668947331)
        ·
          refine ⟨42119543935027886503420997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28079695956685257668947331 42119543935027886503420997)
          ·
            refine ⟨7897414487817728719391437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42119543935027886503420997 7897414487817728719391437)
            ·
              refine ⟨2961530432931648269771789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7897414487817728719391437 2961530432931648269771789)
              ·
                refine ⟨1110573912349368101164421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2961530432931648269771789 1110573912349368101164421)
                ·
                  refine ⟨208232608565506518968329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1110573912349368101164421 208232608565506518968329)
                  ·
                    rfl

theorem cell22_1824892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 3, 3, 4].length) (baseStart_1824892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1824892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1824892 prefixEnd_1824892 := by exact prefixLift 1824892
  have htrace : WordTrace (prefixWord ++ tailWord_1824892) baseStart_1824892 baseEnd_1824892 := by
    simpa [prefixWord, tailWord_1824892, baseEnd_1824892] using wordTrace_append hprefix tailTrace_1824892
  have hstable : (prefixWord ++ tailWord_1824892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824892).length < 2 ^ (prefixWord ++ tailWord_1824892).sum := by decide
  have hdescent : baseEnd_1824892 < baseStart_1824892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824903 : List Nat := [1, 1, 4, 2, 1, 1, 12]
def baseStart_1824903 : Nat := 118140960795 + 1824903 * 2 ^ 59
def prefixEnd_1824903 : Nat := 4983230072969 + 3 ^ 40 * 1824903 * 2
def baseEnd_1824903 : Nat := 23137095971159970180739

theorem tailTrace_1824903 : CollatzResearch.WordTrace tailWord_1824903 prefixEnd_1824903 23137095971159970180739 := by
  unfold tailWord_1824903
  simp only [CollatzResearch.WordTrace]
  refine ⟨66559680507695574464303363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44373120338463716309535575 66559680507695574464303363)
  ·
    refine ⟨99839520761543361696455045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66559680507695574464303363 99839520761543361696455045)
    ·
      refine ⟨18719910142789380318085321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99839520761543361696455045 18719910142789380318085321)
      ·
        refine ⟨14039932607092035238563991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18719910142789380318085321 14039932607092035238563991)
        ·
          refine ⟨21059898910638052857845987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14039932607092035238563991 21059898910638052857845987)
          ·
            refine ⟨31589848365957079286768981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21059898910638052857845987 31589848365957079286768981)
            ·
              refine ⟨23137095971159970180739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 31589848365957079286768981 23137095971159970180739)
              ·
                rfl

theorem cell22_1824903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 12].length) (baseStart_1824903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1824903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1824903 prefixEnd_1824903 := by exact prefixLift 1824903
  have htrace : WordTrace (prefixWord ++ tailWord_1824903) baseStart_1824903 baseEnd_1824903 := by
    simpa [prefixWord, tailWord_1824903, baseEnd_1824903] using wordTrace_append hprefix tailTrace_1824903
  have hstable : (prefixWord ++ tailWord_1824903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824903).length < 2 ^ (prefixWord ++ tailWord_1824903).sum := by decide
  have hdescent : baseEnd_1824903 < baseStart_1824903 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824905 : List Nat := [1, 2, 1, 1, 4, 2, 3, 2, 2, 4]
def baseStart_1824905 : Nat := 118140960795 + 1824905 * 2 ^ 59
def prefixEnd_1824905 : Nat := 4983230072969 + 3 ^ 40 * 1824905 * 2
def baseEnd_1824905 : Nat := 624702275862191856329947

theorem tailTrace_1824905 : CollatzResearch.WordTrace tailWord_1824905 prefixEnd_1824905 624702275862191856329947 := by
  unfold tailWord_1824905
  simp only [CollatzResearch.WordTrace]
  refine ⟨66559753453688328805876169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44373168969125552537250779 66559753453688328805876169)
  ·
    refine ⟨49919815090266246604407127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66559753453688328805876169 49919815090266246604407127)
    ·
      refine ⟨74879722635399369906610691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49919815090266246604407127 74879722635399369906610691)
      ·
        refine ⟨112319583953099054859916037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74879722635399369906610691 112319583953099054859916037)
        ·
          refine ⟨21059921991206072786234257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112319583953099054859916037 21059921991206072786234257)
          ·
            refine ⟨15794941493404554589675693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21059921991206072786234257 15794941493404554589675693)
            ·
              refine ⟨5923103060026707971128385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15794941493404554589675693 5923103060026707971128385)
              ·
                refine ⟨4442327295020030978346289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5923103060026707971128385 4442327295020030978346289)
                ·
                  refine ⟨3331745471265023233759717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4442327295020030978346289 3331745471265023233759717)
                  ·
                    refine ⟨624702275862191856329947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3331745471265023233759717 624702275862191856329947)
                    ·
                      rfl

theorem cell22_1824905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 2, 2, 4].length) (baseStart_1824905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1824905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1824905 prefixEnd_1824905 := by exact prefixLift 1824905
  have htrace : WordTrace (prefixWord ++ tailWord_1824905) baseStart_1824905 baseEnd_1824905 := by
    simpa [prefixWord, tailWord_1824905, baseEnd_1824905] using wordTrace_append hprefix tailTrace_1824905
  have hstable : (prefixWord ++ tailWord_1824905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824905).length < 2 ^ (prefixWord ++ tailWord_1824905).sum := by decide
  have hdescent : baseEnd_1824905 < baseStart_1824905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824965 : List Nat := [1, 3, 1, 1, 1, 1, 5, 4, 5]
def baseStart_1824965 : Nat := 118140960795 + 1824965 * 2 ^ 59
def prefixEnd_1824965 : Nat := 4983230072969 + 3 ^ 40 * 1824965 * 2
def baseEnd_1824965 : Nat := 208240938362790566609921

theorem tailTrace_1824965 : CollatzResearch.WordTrace tailWord_1824965 prefixEnd_1824965 208240938362790566609921 := by
  unfold tailWord_1824965
  simp only [CollatzResearch.WordTrace]
  refine ⟨66561941833470959053060349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44374627888980639368706899 66561941833470959053060349)
  ·
    refine ⟨24960728187551609644897631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66561941833470959053060349 24960728187551609644897631)
    ·
      refine ⟨37441092281327414467346447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24960728187551609644897631 37441092281327414467346447)
      ·
        refine ⟨56161638421991121701019671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37441092281327414467346447 56161638421991121701019671)
        ·
          refine ⟨84242457632986682551529507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56161638421991121701019671 84242457632986682551529507)
          ·
            refine ⟨126363686449480023827294261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84242457632986682551529507 126363686449480023827294261)
            ·
              refine ⟨11846595604638752233808837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 126363686449480023827294261 11846595604638752233808837)
              ·
                refine ⟨2221236675869766043839157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11846595604638752233808837 2221236675869766043839157)
                ·
                  refine ⟨208240938362790566609921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2221236675869766043839157 208240938362790566609921)
                  ·
                    rfl

theorem cell22_1824965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 4, 5].length) (baseStart_1824965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1824965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1824965 prefixEnd_1824965 := by exact prefixLift 1824965
  have htrace : WordTrace (prefixWord ++ tailWord_1824965) baseStart_1824965 baseEnd_1824965 := by
    simpa [prefixWord, tailWord_1824965, baseEnd_1824965] using wordTrace_append hprefix tailTrace_1824965
  have hstable : (prefixWord ++ tailWord_1824965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824965).length < 2 ^ (prefixWord ++ tailWord_1824965).sum := by decide
  have hdescent : baseEnd_1824965 < baseStart_1824965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1825027 : List Nat := [1, 1, 1, 3, 2, 3, 1, 6, 4]
def baseStart_1825027 : Nat := 118140960795 + 1825027 * 2 ^ 59
def prefixEnd_1825027 : Nat := 4983230072969 + 3 ^ 40 * 1825027 * 2
def baseEnd_1825027 : Nat := 208248012985141401593191

theorem tailTrace_1825027 : CollatzResearch.WordTrace tailWord_1825027 prefixEnd_1825027 208248012985141401593191 := by
  unfold tailWord_1825027
  simp only [CollatzResearch.WordTrace]
  refine ⟨66564203159246343641817335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44376135439497562427878223 66564203159246343641817335)
  ·
    refine ⟨99846304738869515462726003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66564203159246343641817335 99846304738869515462726003)
    ·
      refine ⟨149769457108304273194089005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99846304738869515462726003 149769457108304273194089005)
      ·
        refine ⟨56163546415614102447783377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149769457108304273194089005 56163546415614102447783377)
        ·
          refine ⟨42122659811710576835837533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56163546415614102447783377 42122659811710576835837533)
          ·
            refine ⟨15795997429391466313439075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42122659811710576835837533 15795997429391466313439075)
            ·
              refine ⟨23693996144087199470158613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15795997429391466313439075 23693996144087199470158613)
              ·
                refine ⟨1110656069254087475163685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 23693996144087199470158613 1110656069254087475163685)
                ·
                  refine ⟨208248012985141401593191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1110656069254087475163685 208248012985141401593191)
                  ·
                    rfl

theorem cell22_1825027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 6, 4].length) (baseStart_1825027 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1825027 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1825027 prefixEnd_1825027 := by exact prefixLift 1825027
  have htrace : WordTrace (prefixWord ++ tailWord_1825027) baseStart_1825027 baseEnd_1825027 := by
    simpa [prefixWord, tailWord_1825027, baseEnd_1825027] using wordTrace_append hprefix tailTrace_1825027
  have hstable : (prefixWord ++ tailWord_1825027).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1825027).length < 2 ^ (prefixWord ++ tailWord_1825027).sum := by decide
  have hdescent : baseEnd_1825027 < baseStart_1825027 := by decide
  rcases family_descends (prefixWord ++ tailWord_1825027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1825061 : List Nat := [1, 3, 1, 2, 5, 2, 1, 3, 4]
def baseStart_1825061 : Nat := 118140960795 + 1825061 * 2 ^ 59
def prefixEnd_1825061 : Nat := 4983230072969 + 3 ^ 40 * 1825061 * 2
def baseEnd_1825061 : Nat := 208251892616753149809823

theorem tailTrace_1825061 : CollatzResearch.WordTrace tailWord_1825061 prefixEnd_1825061 208251892616753149809823 := by
  unfold tailWord_1825061
  simp only [CollatzResearch.WordTrace]
  refine ⟨66565443241123167448555037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44376962160748778299036691 66565443241123167448555037)
  ·
    refine ⟨24962041215421187793208139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66565443241123167448555037 24962041215421187793208139)
    ·
      refine ⟨37443061823131781689812209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24962041215421187793208139 37443061823131781689812209)
      ·
        refine ⟨28082296367348836267359157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37443061823131781689812209 28082296367348836267359157)
        ·
          refine ⟨2632715284438953400064921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28082296367348836267359157 2632715284438953400064921)
          ·
            refine ⟨1974536463329215050048691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2632715284438953400064921 1974536463329215050048691)
            ·
              refine ⟨2961804694993822575073037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1974536463329215050048691 2961804694993822575073037)
              ·
                refine ⟨1110676760622683465652389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2961804694993822575073037 1110676760622683465652389)
                ·
                  refine ⟨208251892616753149809823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1110676760622683465652389 208251892616753149809823)
                  ·
                    rfl

theorem cell22_1825061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 1, 3, 4].length) (baseStart_1825061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1825061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1825061 prefixEnd_1825061 := by exact prefixLift 1825061
  have htrace : WordTrace (prefixWord ++ tailWord_1825061) baseStart_1825061 baseEnd_1825061 := by
    simpa [prefixWord, tailWord_1825061, baseEnd_1825061] using wordTrace_append hprefix tailTrace_1825061
  have hstable : (prefixWord ++ tailWord_1825061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1825061).length < 2 ^ (prefixWord ++ tailWord_1825061).sum := by decide
  have hdescent : baseEnd_1825061 < baseStart_1825061 := by decide
  rcases family_descends (prefixWord ++ tailWord_1825061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1825074 : List Nat := [3, 2, 1, 1, 5, 1, 1, 2, 2, 4]
def baseStart_1825074 : Nat := 118140960795 + 1825074 * 2 ^ 59
def prefixEnd_1825074 : Nat := 4983230072969 + 3 ^ 40 * 1825074 * 2
def baseEnd_1825074 : Nat := 624760128015931748854429

theorem tailTrace_1825074 : CollatzResearch.WordTrace tailWord_1825074 prefixEnd_1825074 624760128015931748854429 := by
  unfold tailWord_1825074
  simp only [CollatzResearch.WordTrace]
  refine ⟨16641479347519017667194569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44377278260050713779185517 16641479347519017667194569)
  ·
    refine ⟨12481109510639263250395927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16641479347519017667194569 12481109510639263250395927)
    ·
      refine ⟨18721664265958894875593891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12481109510639263250395927 18721664265958894875593891)
      ·
        refine ⟨28082496398938342313390837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18721664265958894875593891 28082496398938342313390837)
        ·
          refine ⟨2632734037400469591880391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28082496398938342313390837 2632734037400469591880391)
          ·
            refine ⟨3949101056100704387820587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2632734037400469591880391 3949101056100704387820587)
            ·
              refine ⟨5923651584151056581730881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3949101056100704387820587 5923651584151056581730881)
              ·
                refine ⟨4442738688113292436298161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5923651584151056581730881 4442738688113292436298161)
                ·
                  refine ⟨3332054016084969327223621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4442738688113292436298161 3332054016084969327223621)
                  ·
                    refine ⟨624760128015931748854429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3332054016084969327223621 624760128015931748854429)
                    ·
                      rfl

theorem cell22_1825074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 2, 2, 4].length) (baseStart_1825074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1825074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1825074 prefixEnd_1825074 := by exact prefixLift 1825074
  have htrace : WordTrace (prefixWord ++ tailWord_1825074) baseStart_1825074 baseEnd_1825074 := by
    simpa [prefixWord, tailWord_1825074, baseEnd_1825074] using wordTrace_append hprefix tailTrace_1825074
  have hstable : (prefixWord ++ tailWord_1825074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1825074).length < 2 ^ (prefixWord ++ tailWord_1825074).sum := by decide
  have hdescent : baseEnd_1825074 < baseStart_1825074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1825074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1825089 : List Nat := [1, 2, 5, 2, 2, 1, 2, 7]
def baseStart_1825089 : Nat := 118140960795 + 1825089 * 2 ^ 59
def prefixEnd_1825089 : Nat := 4983230072969 + 3 ^ 40 * 1825089 * 2
def baseEnd_1825089 : Nat := 69418362535830745525487

theorem tailTrace_1825089 : CollatzResearch.WordTrace tailWord_1825089 prefixEnd_1825089 69418362535830745525487 := by
  unfold tailWord_1825089
  simp only [CollatzResearch.WordTrace]
  refine ⟨66566464485021728230574321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44377642990014485487049547 66566464485021728230574321)
  ·
    refine ⟨49924848363766296172930741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66566464485021728230574321 49924848363766296172930741)
    ·
      refine ⟨4680454534103090266212257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 49924848363766296172930741 4680454534103090266212257)
      ·
        refine ⟨3510340900577317699659193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4680454534103090266212257 3510340900577317699659193)
        ·
          refine ⟨2632755675432988274744395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3510340900577317699659193 2632755675432988274744395)
          ·
            refine ⟨3949133513149482412116593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2632755675432988274744395 3949133513149482412116593)
            ·
              refine ⟨2961850134862111809087445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3949133513149482412116593 2961850134862111809087445)
              ·
                refine ⟨69418362535830745525487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2961850134862111809087445 69418362535830745525487)
                ·
                  rfl

theorem cell22_1825089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 2, 7].length) (baseStart_1825089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1825089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1825089 prefixEnd_1825089 := by exact prefixLift 1825089
  have htrace : WordTrace (prefixWord ++ tailWord_1825089) baseStart_1825089 baseEnd_1825089 := by
    simpa [prefixWord, tailWord_1825089, baseEnd_1825089] using wordTrace_append hprefix tailTrace_1825089
  have hstable : (prefixWord ++ tailWord_1825089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1825089).length < 2 ^ (prefixWord ++ tailWord_1825089).sum := by decide
  have hdescent : baseEnd_1825089 < baseStart_1825089 := by decide
  rcases family_descends (prefixWord ++ tailWord_1825089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1825138 : List Nat := [3, 2, 1, 2, 1, 3, 4, 2, 1, 3]
def baseStart_1825138 : Nat := 118140960795 + 1825138 * 2 ^ 59
def prefixEnd_1825138 : Nat := 4983230072969 + 3 ^ 40 * 1825138 * 2
def baseEnd_1825138 : Nat := 624782036523856915254233

theorem tailTrace_1825138 : CollatzResearch.WordTrace tailWord_1825138 prefixEnd_1825138 624782036523856915254233 := by
  unfold tailWord_1825138
  simp only [CollatzResearch.WordTrace]
  refine ⟨16642062915461052399777017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44378834441229473066072045 16642062915461052399777017)
  ·
    refine ⟨12481547186595789299832763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16642062915461052399777017 12481547186595789299832763)
    ·
      refine ⟨18722320779893683949749145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12481547186595789299832763 18722320779893683949749145)
      ·
        refine ⟨14041740584920262962311859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18722320779893683949749145 14041740584920262962311859)
        ·
          refine ⟨21062610877380394443467789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14041740584920262962311859 21062610877380394443467789)
          ·
            refine ⟨7898479079017647916300421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21062610877380394443467789 7898479079017647916300421)
            ·
              refine ⟨1480964827315808984306329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7898479079017647916300421 1480964827315808984306329)
              ·
                refine ⟨1110723620486856738229747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1480964827315808984306329 1110723620486856738229747)
                ·
                  refine ⟨1666085430730285107344621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1110723620486856738229747 1666085430730285107344621)
                  ·
                    refine ⟨624782036523856915254233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1666085430730285107344621 624782036523856915254233)
                    ·
                      rfl

theorem cell22_1825138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 4, 2, 1, 3].length) (baseStart_1825138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1825138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1825138 prefixEnd_1825138 := by exact prefixLift 1825138
  have htrace : WordTrace (prefixWord ++ tailWord_1825138) baseStart_1825138 baseEnd_1825138 := by
    simpa [prefixWord, tailWord_1825138, baseEnd_1825138] using wordTrace_append hprefix tailTrace_1825138
  have hstable : (prefixWord ++ tailWord_1825138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1825138).length < 2 ^ (prefixWord ++ tailWord_1825138).sum := by decide
  have hdescent : baseEnd_1825138 < baseStart_1825138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1825138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1825147 : List Nat := [1, 1, 1, 1, 1, 7, 1, 2, 3, 4]
def baseStart_1825147 : Nat := 118140960795 + 1825147 * 2 ^ 59
def prefixEnd_1825147 : Nat := 4983230072969 + 3 ^ 40 * 1825147 * 2
def baseEnd_1825147 : Nat := 624785117407783891779205

theorem tailTrace_1825147 : CollatzResearch.WordTrace tailWord_1825147 prefixEnd_1825147 624785117407783891779205 := by
  unfold tailWord_1825147
  simp only [CollatzResearch.WordTrace]
  refine ⟨66568579918811604136185695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44379053279207736090790463 66568579918811604136185695)
  ·
    refine ⟨99852869878217406204278543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66568579918811604136185695 99852869878217406204278543)
    ·
      refine ⟨149779304817326109306417815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99852869878217406204278543 149779304817326109306417815)
      ·
        refine ⟨224668957225989163959626723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149779304817326109306417815 224668957225989163959626723)
        ·
          refine ⟨337003435838983745939440085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224668957225989163959626723 337003435838983745939440085)
          ·
            refine ⟨7898518027476181545455627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 337003435838983745939440085 7898518027476181545455627)
            ·
              refine ⟨11847777041214272318183441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7898518027476181545455627 11847777041214272318183441)
              ·
                refine ⟨8885832780910704238637581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11847777041214272318183441 8885832780910704238637581)
                ·
                  refine ⟨3332187292841514089489093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8885832780910704238637581 3332187292841514089489093)
                  ·
                    refine ⟨624785117407783891779205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3332187292841514089489093 624785117407783891779205)
                    ·
                      rfl

theorem cell22_1825147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 2, 3, 4].length) (baseStart_1825147 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1825147 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1825147 prefixEnd_1825147 := by exact prefixLift 1825147
  have htrace : WordTrace (prefixWord ++ tailWord_1825147) baseStart_1825147 baseEnd_1825147 := by
    simpa [prefixWord, tailWord_1825147, baseEnd_1825147] using wordTrace_append hprefix tailTrace_1825147
  have hstable : (prefixWord ++ tailWord_1825147).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1825147).length < 2 ^ (prefixWord ++ tailWord_1825147).sum := by decide
  have hdescent : baseEnd_1825147 < baseStart_1825147 := by decide
  rcases family_descends (prefixWord ++ tailWord_1825147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1825177 : List Nat := [1, 2, 1, 2, 1, 4, 1, 4, 1, 5]
def baseStart_1825177 : Nat := 118140960795 + 1825177 * 2 ^ 59
def prefixEnd_1825177 : Nat := 4983230072969 + 3 ^ 40 * 1825177 * 2
def baseEnd_1825177 : Nat := 624795387020873813529113

theorem tailTrace_1825177 : CollatzResearch.WordTrace tailWord_1825177 prefixEnd_1825177 624795387020873813529113 := by
  unfold tailWord_1825177
  simp only [CollatzResearch.WordTrace]
  refine ⟨66569674108702919259777785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44379782739135279506518523 66569674108702919259777785)
  ·
    refine ⟨49927255581527189444833339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66569674108702919259777785 49927255581527189444833339)
    ·
      refine ⟨74890883372290784167250009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49927255581527189444833339 74890883372290784167250009)
      ·
        refine ⟨56168162529218088125437507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74890883372290784167250009 56168162529218088125437507)
        ·
          refine ⟨84252243793827132188156261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56168162529218088125437507 84252243793827132188156261)
          ·
            refine ⟨15797295711342587285279299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84252243793827132188156261 15797295711342587285279299)
            ·
              refine ⟨23695943567013880927918949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15797295711342587285279299 23695943567013880927918949)
              ·
                refine ⟨4442989418815102673984803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23695943567013880927918949 4442989418815102673984803)
                ·
                  refine ⟨6664484128222654010977205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4442989418815102673984803 6664484128222654010977205)
                  ·
                    refine ⟨624795387020873813529113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6664484128222654010977205 624795387020873813529113)
                    ·
                      rfl

theorem cell22_1825177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 4, 1, 5].length) (baseStart_1825177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1825177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1825177 prefixEnd_1825177 := by exact prefixLift 1825177
  have htrace : WordTrace (prefixWord ++ tailWord_1825177) baseStart_1825177 baseEnd_1825177 := by
    simpa [prefixWord, tailWord_1825177, baseEnd_1825177] using wordTrace_append hprefix tailTrace_1825177
  have hstable : (prefixWord ++ tailWord_1825177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1825177).length < 2 ^ (prefixWord ++ tailWord_1825177).sum := by decide
  have hdescent : baseEnd_1825177 < baseStart_1825177 := by decide
  rcases family_descends (prefixWord ++ tailWord_1825177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1825181 : List Nat := [1, 4, 2, 1, 4, 1, 1, 3, 1, 4]
def baseStart_1825181 : Nat := 118140960795 + 1825181 * 2 ^ 59
def prefixEnd_1825181 : Nat := 4983230072969 + 3 ^ 40 * 1825181 * 2
def baseEnd_1825181 : Nat := 624796756302619136429101

theorem tailTrace_1825181 : CollatzResearch.WordTrace tailWord_1825181 prefixEnd_1825181 624796756302619136429101 := by
  unfold tailWord_1825181
  simp only [CollatzResearch.WordTrace]
  refine ⟨66569820000688427942923397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44379880000458951961948931 66569820000688427942923397)
  ·
    refine ⟨12481841250129080239298137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66569820000688427942923397 12481841250129080239298137)
    ·
      refine ⟨9361380937596810179473603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12481841250129080239298137 9361380937596810179473603)
      ·
        refine ⟨14042071406395215269210405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9361380937596810179473603 14042071406395215269210405)
        ·
          refine ⟨2632888388699102862976951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14042071406395215269210405 2632888388699102862976951)
          ·
            refine ⟨3949332583048654294465427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2632888388699102862976951 3949332583048654294465427)
            ·
              refine ⟨5923998874572981441698141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3949332583048654294465427 5923998874572981441698141)
              ·
                refine ⟨2221499577964868040636803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5923998874572981441698141 2221499577964868040636803)
                ·
                  refine ⟨3332249366947302060955205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2221499577964868040636803 3332249366947302060955205)
                  ·
                    refine ⟨624796756302619136429101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3332249366947302060955205 624796756302619136429101)
                    ·
                      rfl

theorem cell22_1825181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 3, 1, 4].length) (baseStart_1825181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1825181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1825181 prefixEnd_1825181 := by exact prefixLift 1825181
  have htrace : WordTrace (prefixWord ++ tailWord_1825181) baseStart_1825181 baseEnd_1825181 := by
    simpa [prefixWord, tailWord_1825181, baseEnd_1825181] using wordTrace_append hprefix tailTrace_1825181
  have hstable : (prefixWord ++ tailWord_1825181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1825181).length < 2 ^ (prefixWord ++ tailWord_1825181).sum := by decide
  have hdescent : baseEnd_1825181 < baseStart_1825181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1825181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1825224 : List Nat := [2, 1, 3, 1, 3, 2, 4, 6]
def baseStart_1825224 : Nat := 118140960795 + 1825224 * 2 ^ 59
def prefixEnd_1825224 : Nat := 4983230072969 + 3 ^ 40 * 1825224 * 2
def baseEnd_1825224 : Nat := 69423497342375706400441

theorem tailTrace_1825224 : CollatzResearch.WordTrace tailWord_1825224 prefixEnd_1825224 69423497342375706400441 := by
  unfold tailWord_1825224
  simp only [CollatzResearch.WordTrace]
  refine ⟨33285694169766323143369363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44380925559688430857825817 33285694169766323143369363)
  ·
    refine ⟨49928541254649484715054045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33285694169766323143369363 49928541254649484715054045)
    ·
      refine ⟨18723202970493556768145267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49928541254649484715054045 18723202970493556768145267)
      ·
        refine ⟨28084804455740335152217901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18723202970493556768145267 28084804455740335152217901)
        ·
          refine ⟨10531801670902625682081713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28084804455740335152217901 10531801670902625682081713)
          ·
            refine ⟨7898851253176969261561285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10531801670902625682081713 7898851253176969261561285)
            ·
              refine ⟨1481034609970681736542741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7898851253176969261561285 1481034609970681736542741)
              ·
                refine ⟨69423497342375706400441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1481034609970681736542741 69423497342375706400441)
                ·
                  rfl

theorem cell22_1825224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 4, 6].length) (baseStart_1825224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1825224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1825224 prefixEnd_1825224 := by exact prefixLift 1825224
  have htrace : WordTrace (prefixWord ++ tailWord_1825224) baseStart_1825224 baseEnd_1825224 := by
    simpa [prefixWord, tailWord_1825224, baseEnd_1825224] using wordTrace_append hprefix tailTrace_1825224
  have hstable : (prefixWord ++ tailWord_1825224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1825224).length < 2 ^ (prefixWord ++ tailWord_1825224).sum := by decide
  have hdescent : baseEnd_1825224 < baseStart_1825224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1825224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1825256 : List Nat := [2, 1, 4, 1, 1, 3, 3, 1, 3, 3]
def baseStart_1825256 : Nat := 118140960795 + 1825256 * 2 ^ 59
def prefixEnd_1825256 : Nat := 4983230072969 + 3 ^ 40 * 1825256 * 2
def baseEnd_1825256 : Nat := 624822430335343940803871

theorem tailTrace_1825256 : CollatzResearch.WordTrace tailWord_1825256 prefixEnd_1825256 624822430335343940803871 := by
  unfold tailWord_1825256
  simp only [CollatzResearch.WordTrace]
  refine ⟨33286277737708357875951811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44381703650277810501269081 33286277737708357875951811)
  ·
    refine ⟨49929416606562536813927717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33286277737708357875951811 49929416606562536813927717)
    ·
      refine ⟨9361765613730475652611447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49929416606562536813927717 9361765613730475652611447)
      ·
        refine ⟨14042648420595713478917171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9361765613730475652611447 14042648420595713478917171)
        ·
          refine ⟨21063972630893570218375757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14042648420595713478917171 21063972630893570218375757)
          ·
            refine ⟨7898989736585088831890909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21063972630893570218375757 7898989736585088831890909)
            ·
              refine ⟨2962121151219408311959091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7898989736585088831890909 2962121151219408311959091)
              ·
                refine ⟨4443181726829112467938637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2962121151219408311959091 4443181726829112467938637)
                ·
                  refine ⟨1666193147560917175476989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4443181726829112467938637 1666193147560917175476989)
                  ·
                    refine ⟨624822430335343940803871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1666193147560917175476989 624822430335343940803871)
                    ·
                      rfl

theorem cell22_1825256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 3, 1, 3, 3].length) (baseStart_1825256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1825256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1825256 prefixEnd_1825256 := by exact prefixLift 1825256
  have htrace : WordTrace (prefixWord ++ tailWord_1825256) baseStart_1825256 baseEnd_1825256 := by
    simpa [prefixWord, tailWord_1825256, baseEnd_1825256] using wordTrace_append hprefix tailTrace_1825256
  have hstable : (prefixWord ++ tailWord_1825256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1825256).length < 2 ^ (prefixWord ++ tailWord_1825256).sum := by decide
  have hdescent : baseEnd_1825256 < baseStart_1825256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1825256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1825267 : List Nat := [1, 1, 1, 2, 2, 2, 4, 1, 1, 7]
def baseStart_1825267 : Nat := 118140960795 + 1825267 * 2 ^ 59
def prefixEnd_1825267 : Nat := 4983230072969 + 3 ^ 40 * 1825267 * 2
def baseEnd_1825267 : Nat := 624826195860143578778837

theorem tailTrace_1825267 : CollatzResearch.WordTrace tailWord_1825267 prefixEnd_1825267 624826195860143578778837 := by
  unfold tailWord_1825267
  simp only [CollatzResearch.WordTrace]
  refine ⟨66572956678376864630554055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44381971118917909753702703 66572956678376864630554055)
  ·
    refine ⟨99859435017565296945831083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66572956678376864630554055 99859435017565296945831083)
    ·
      refine ⟨149789152526347945418746625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99859435017565296945831083 149789152526347945418746625)
      ·
        refine ⟨112341864394760959064059969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149789152526347945418746625 112341864394760959064059969)
        ·
          refine ⟨84256398296070719298044977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112341864394760959064059969 84256398296070719298044977)
          ·
            refine ⟨63192298722053039473533733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84256398296070719298044977 63192298722053039473533733)
            ·
              refine ⟨11848556010384944901287575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63192298722053039473533733 11848556010384944901287575)
              ·
                refine ⟨17772834015577417351931363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11848556010384944901287575 17772834015577417351931363)
                ·
                  refine ⟨26659251023366126027897045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17772834015577417351931363 26659251023366126027897045)
                  ·
                    refine ⟨624826195860143578778837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26659251023366126027897045 624826195860143578778837)
                    ·
                      rfl

theorem cell22_1825267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 1, 1, 7].length) (baseStart_1825267 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1825267 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1825267 prefixEnd_1825267 := by exact prefixLift 1825267
  have htrace : WordTrace (prefixWord ++ tailWord_1825267) baseStart_1825267 baseEnd_1825267 := by
    simpa [prefixWord, tailWord_1825267, baseEnd_1825267] using wordTrace_append hprefix tailTrace_1825267
  have hstable : (prefixWord ++ tailWord_1825267).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1825267).length < 2 ^ (prefixWord ++ tailWord_1825267).sum := by decide
  have hdescent : baseEnd_1825267 < baseStart_1825267 := by decide
  rcases family_descends (prefixWord ++ tailWord_1825267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1825297 : List Nat := [1, 2, 2, 1, 1, 2, 2, 1, 10]
def baseStart_1825297 : Nat := 118140960795 + 1825297 * 2 ^ 59
def prefixEnd_1825297 : Nat := 4983230072969 + 3 ^ 40 * 1825297 * 2
def baseEnd_1825297 : Nat := 208278821824411166842915

theorem tailTrace_1825297 : CollatzResearch.WordTrace tailWord_1825297 prefixEnd_1825297 208278821824411166842915 := by
  unfold tailWord_1825297
  simp only [CollatzResearch.WordTrace]
  refine ⟨66574050868268179754146145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44382700578845453169430763 66574050868268179754146145)
  ·
    refine ⟨49930538151201134815609609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66574050868268179754146145 49930538151201134815609609)
    ·
      refine ⟨37447903613400851111707207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49930538151201134815609609 37447903613400851111707207)
      ·
        refine ⟨56171855420101276667560811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37447903613400851111707207 56171855420101276667560811)
        ·
          refine ⟨84257783130151915001341217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56171855420101276667560811 84257783130151915001341217)
          ·
            refine ⟨63193337347613936251005913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84257783130151915001341217 63193337347613936251005913)
            ·
              refine ⟨47395003010710452188254435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63193337347613936251005913 47395003010710452188254435)
              ·
                refine ⟨71092504516065678282381653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47395003010710452188254435 71092504516065678282381653)
                ·
                  refine ⟨208278821824411166842915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 71092504516065678282381653 208278821824411166842915)
                  ·
                    rfl

theorem cell22_1825297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 10].length) (baseStart_1825297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1825297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1825297 prefixEnd_1825297 := by exact prefixLift 1825297
  have htrace : WordTrace (prefixWord ++ tailWord_1825297) baseStart_1825297 baseEnd_1825297 := by
    simpa [prefixWord, tailWord_1825297, baseEnd_1825297] using wordTrace_append hprefix tailTrace_1825297
  have hstable : (prefixWord ++ tailWord_1825297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1825297).length < 2 ^ (prefixWord ++ tailWord_1825297).sum := by decide
  have hdescent : baseEnd_1825297 < baseStart_1825297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1825297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1825303 : List Nat := [1, 1, 3, 6, 1, 1, 2, 2, 5]
def baseStart_1825303 : Nat := 118140960795 + 1825303 * 2 ^ 59
def prefixEnd_1825303 : Nat := 4983230072969 + 3 ^ 40 * 1825303 * 2
def baseEnd_1825303 : Nat := 208279506465283828292909

theorem tailTrace_1825303 : CollatzResearch.WordTrace tailWord_1825303 prefixEnd_1825303 208279506465283828292909 := by
  unfold tailWord_1825303
  simp only [CollatzResearch.WordTrace]
  refine ⟨66574269706246442778864563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44382846470830961852576375 66574269706246442778864563)
  ·
    refine ⟨99861404559369664168296845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66574269706246442778864563 99861404559369664168296845)
    ·
      refine ⟨37448026709763624063111317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99861404559369664168296845 37448026709763624063111317)
      ·
        refine ⟨1755376252020169877958343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 37448026709763624063111317 1755376252020169877958343)
        ·
          refine ⟨2633064378030254816937515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1755376252020169877958343 2633064378030254816937515)
          ·
            refine ⟨3949596567045382225406273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2633064378030254816937515 3949596567045382225406273)
            ·
              refine ⟨2962197425284036669054705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3949596567045382225406273 2962197425284036669054705)
              ·
                refine ⟨2221648068963027501791029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2962197425284036669054705 2221648068963027501791029)
                ·
                  refine ⟨208279506465283828292909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2221648068963027501791029 208279506465283828292909)
                  ·
                    rfl

theorem cell22_1825303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 2, 2, 5].length) (baseStart_1825303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1825303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1825303 prefixEnd_1825303 := by exact prefixLift 1825303
  have htrace : WordTrace (prefixWord ++ tailWord_1825303) baseStart_1825303 baseEnd_1825303 := by
    simpa [prefixWord, tailWord_1825303, baseEnd_1825303] using wordTrace_append hprefix tailTrace_1825303
  have hstable : (prefixWord ++ tailWord_1825303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1825303).length < 2 ^ (prefixWord ++ tailWord_1825303).sum := by decide
  have hdescent : baseEnd_1825303 < baseStart_1825303 := by decide
  rcases family_descends (prefixWord ++ tailWord_1825303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1825314 : List Nat := [3, 3, 1, 1, 1, 1, 1, 5, 6]
def baseStart_1825314 : Nat := 118140960795 + 1825314 * 2 ^ 59
def prefixEnd_1825314 : Nat := 4983230072969 + 3 ^ 40 * 1825314 * 2
def baseEnd_1825314 : Nat := 208280761640217040951231

theorem tailTrace_1825314 : CollatzResearch.WordTrace tailWord_1825314 prefixEnd_1825314 208280761640217040951231 := by
  unfold tailWord_1825314
  simp only [CollatzResearch.WordTrace]
  refine ⟨16643667727301647914378749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44383113939471061105009997 16643667727301647914378749)
  ·
    refine ⟨6241375397738117967892031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16643667727301647914378749 6241375397738117967892031)
    ·
      refine ⟨9362063096607176951838047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6241375397738117967892031 9362063096607176951838047)
      ·
        refine ⟨14043094644910765427757071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9362063096607176951838047 14043094644910765427757071)
        ·
          refine ⟨21064641967366148141635607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14043094644910765427757071 21064641967366148141635607)
          ·
            refine ⟨31596962951049222212453411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21064641967366148141635607 31596962951049222212453411)
            ·
              refine ⟨47395444426573833318680117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31596962951049222212453411 47395444426573833318680117)
              ·
                refine ⟨4443322914991296873626261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47395444426573833318680117 4443322914991296873626261)
                ·
                  refine ⟨208280761640217040951231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4443322914991296873626261 208280761640217040951231)
                  ·
                    rfl

theorem cell22_1825314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 5, 6].length) (baseStart_1825314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1825314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1825314 prefixEnd_1825314 := by exact prefixLift 1825314
  have htrace : WordTrace (prefixWord ++ tailWord_1825314) baseStart_1825314 baseEnd_1825314 := by
    simpa [prefixWord, tailWord_1825314, baseEnd_1825314] using wordTrace_append hprefix tailTrace_1825314
  have hstable : (prefixWord ++ tailWord_1825314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1825314).length < 2 ^ (prefixWord ++ tailWord_1825314).sum := by decide
  have hdescent : baseEnd_1825314 < baseStart_1825314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1825314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1825329 : List Nat := [1, 2, 2, 3, 1, 1, 3, 3, 1, 5]
def baseStart_1825329 : Nat := 118140960795 + 1825329 * 2 ^ 59
def prefixEnd_1825329 : Nat := 4983230072969 + 3 ^ 40 * 1825329 * 2
def baseEnd_1825329 : Nat := 624847419727196083728647

theorem tailTrace_1825329 : CollatzResearch.WordTrace tailWord_1825329 prefixEnd_1825329 624847419727196083728647 := by
  unfold tailWord_1825329
  simp only [CollatzResearch.WordTrace]
  refine ⟨66575218004152249219311041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44383478669434832812874027 66575218004152249219311041)
  ·
    refine ⟨49931413503114186914483281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66575218004152249219311041 49931413503114186914483281)
    ·
      refine ⟨37448560127335640185862461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49931413503114186914483281 37448560127335640185862461)
      ·
        refine ⟨14043210047750865069698423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37448560127335640185862461 14043210047750865069698423)
        ·
          refine ⟨21064815071626297604547635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14043210047750865069698423 21064815071626297604547635)
          ·
            refine ⟨31597222607439446406821453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21064815071626297604547635 31597222607439446406821453)
            ·
              refine ⟨11848958477789792402558045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31597222607439446406821453 11848958477789792402558045)
              ·
                refine ⟨4443359429171172150959267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11848958477789792402558045 4443359429171172150959267)
                ·
                  refine ⟨6665039143756758226438901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4443359429171172150959267 6665039143756758226438901)
                  ·
                    refine ⟨624847419727196083728647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6665039143756758226438901 624847419727196083728647)
                    ·
                      rfl

theorem cell22_1825329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 3, 1, 5].length) (baseStart_1825329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1825329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1825329 prefixEnd_1825329 := by exact prefixLift 1825329
  have htrace : WordTrace (prefixWord ++ tailWord_1825329) baseStart_1825329 baseEnd_1825329 := by
    simpa [prefixWord, tailWord_1825329, baseEnd_1825329] using wordTrace_append hprefix tailTrace_1825329
  have hstable : (prefixWord ++ tailWord_1825329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1825329).length < 2 ^ (prefixWord ++ tailWord_1825329).sum := by decide
  have hdescent : baseEnd_1825329 < baseStart_1825329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1825329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1825350 : List Nat := [6, 1, 1, 1, 2, 2, 1, 3, 1, 4]
def baseStart_1825350 : Nat := 118140960795 + 1825350 * 2 ^ 59
def prefixEnd_1825350 : Nat := 4983230072969 + 3 ^ 40 * 1825350 * 2
def baseEnd_1825350 : Nat := 624854608456359028953583

theorem tailTrace_1825350 : CollatzResearch.WordTrace tailWord_1825350 prefixEnd_1825350 624854608456359028953583 := by
  unfold tailWord_1825350
  simp only [CollatzResearch.WordTrace]
  refine ⟨2080499498033630306432047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 44383989291384113203883669 2080499498033630306432047)
  ·
    refine ⟨3120749247050445459648071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2080499498033630306432047 3120749247050445459648071)
    ·
      refine ⟨4681123870575668189472107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3120749247050445459648071 4681123870575668189472107)
      ·
        refine ⟨7021685805863502284208161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4681123870575668189472107 7021685805863502284208161)
        ·
          refine ⟨5266264354397626713156121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7021685805863502284208161 5266264354397626713156121)
          ·
            refine ⟨3949698265798220034867091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5266264354397626713156121 3949698265798220034867091)
            ·
              refine ⟨5924547398697330052300637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3949698265798220034867091 5924547398697330052300637)
              ·
                refine ⟨2221705274511498769612739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5924547398697330052300637 2221705274511498769612739)
                ·
                  refine ⟨3332557911767248154419109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2221705274511498769612739 3332557911767248154419109)
                  ·
                    refine ⟨624854608456359028953583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3332557911767248154419109 624854608456359028953583)
                    ·
                      rfl

theorem cell22_1825350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_1825350 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1825350 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1825350 prefixEnd_1825350 := by exact prefixLift 1825350
  have htrace : WordTrace (prefixWord ++ tailWord_1825350) baseStart_1825350 baseEnd_1825350 := by
    simpa [prefixWord, tailWord_1825350, baseEnd_1825350] using wordTrace_append hprefix tailTrace_1825350
  have hstable : (prefixWord ++ tailWord_1825350).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1825350).length < 2 ^ (prefixWord ++ tailWord_1825350).sum := by decide
  have hdescent : baseEnd_1825350 < baseStart_1825350 := by decide
  rcases family_descends (prefixWord ++ tailWord_1825350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1825391 : List Nat := [1, 1, 2, 1, 3, 2, 4, 2, 3, 3]
def baseStart_1825391 : Nat := 118140960795 + 1825391 * 2 ^ 59
def prefixEnd_1825391 : Nat := 4983230072969 + 3 ^ 40 * 1825391 * 2
def baseEnd_1825391 : Nat := 624868643594248588678457

theorem tailTrace_1825391 : CollatzResearch.WordTrace tailWord_1825391 prefixEnd_1825391 624868643594248588678457 := by
  unfold tailWord_1825391
  simp only [CollatzResearch.WordTrace]
  refine ⟨66577479329927633808068027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44384986219951755872045351 66577479329927633808068027)
  ·
    refine ⟨99866218994891450712102041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66577479329927633808068027 99866218994891450712102041)
    ·
      refine ⟨74899664246168588034076531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99866218994891450712102041 74899664246168588034076531)
      ·
        refine ⟨112349496369252882051114797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74899664246168588034076531 112349496369252882051114797)
        ·
          refine ⟨42131061138469830769168049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112349496369252882051114797 42131061138469830769168049)
          ·
            refine ⟨31598295853852373076876037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42131061138469830769168049 31598295853852373076876037)
            ·
              refine ⟨5924680472597319951914257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31598295853852373076876037 5924680472597319951914257)
              ·
                refine ⟨4443510354447989963935693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5924680472597319951914257 4443510354447989963935693)
                ·
                  refine ⟨1666316382917996236475885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4443510354447989963935693 1666316382917996236475885)
                  ·
                    refine ⟨624868643594248588678457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1666316382917996236475885 624868643594248588678457)
                    ·
                      rfl

theorem cell22_1825391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 2, 3, 3].length) (baseStart_1825391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1825391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1825391 prefixEnd_1825391 := by exact prefixLift 1825391
  have htrace : WordTrace (prefixWord ++ tailWord_1825391) baseStart_1825391 baseEnd_1825391 := by
    simpa [prefixWord, tailWord_1825391, baseEnd_1825391] using wordTrace_append hprefix tailTrace_1825391
  have hstable : (prefixWord ++ tailWord_1825391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1825391).length < 2 ^ (prefixWord ++ tailWord_1825391).sum := by decide
  have hdescent : baseEnd_1825391 < baseStart_1825391 := by decide
  rcases family_descends (prefixWord ++ tailWord_1825391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1825404 : List Nat := [2, 2, 2, 1, 1, 2, 3, 2, 7]
def baseStart_1825404 : Nat := 118140960795 + 1825404 * 2 ^ 59
def prefixEnd_1825404 : Nat := 4983230072969 + 3 ^ 40 * 1825404 * 2
def baseEnd_1825404 : Nat := 208291031253306962701139

theorem tailTrace_1825404 : CollatzResearch.WordTrace tailWord_1825404 prefixEnd_1825404 208291031253306962701139 := by
  unfold tailWord_1825404
  simp only [CollatzResearch.WordTrace]
  refine ⟨33288976739440268514145633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44385302319253691352194177 33288976739440268514145633)
  ·
    refine ⟨24966732554580201385609225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33288976739440268514145633 24966732554580201385609225)
    ·
      refine ⟨18725049415935151039206919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24966732554580201385609225 18725049415935151039206919)
      ·
        refine ⟨28087574123902726558810379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18725049415935151039206919 28087574123902726558810379)
        ·
          refine ⟨42131361185854089838215569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28087574123902726558810379 42131361185854089838215569)
          ·
            refine ⟨31598520889390567378661677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42131361185854089838215569 31598520889390567378661677)
            ·
              refine ⟨11849445333521462766998129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31598520889390567378661677 11849445333521462766998129)
              ·
                refine ⟨8887084000141097075248597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11849445333521462766998129 8887084000141097075248597)
                ·
                  refine ⟨208291031253306962701139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8887084000141097075248597 208291031253306962701139)
                  ·
                    rfl

theorem cell22_1825404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 2, 7].length) (baseStart_1825404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1825404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1825404 prefixEnd_1825404 := by exact prefixLift 1825404
  have htrace : WordTrace (prefixWord ++ tailWord_1825404) baseStart_1825404 baseEnd_1825404 := by
    simpa [prefixWord, tailWord_1825404, baseEnd_1825404] using wordTrace_append hprefix tailTrace_1825404
  have hstable : (prefixWord ++ tailWord_1825404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1825404).length < 2 ^ (prefixWord ++ tailWord_1825404).sum := by decide
  have hdescent : baseEnd_1825404 < baseStart_1825404 := by decide
  rcases family_descends (prefixWord ++ tailWord_1825404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1825419 : List Nat := [1, 1, 1, 1, 4, 1, 2, 4, 2, 5]
def baseStart_1825419 : Nat := 118140960795 + 1825419 * 2 ^ 59
def prefixEnd_1825419 : Nat := 4983230072969 + 3 ^ 40 * 1825419 * 2
def baseEnd_1825419 : Nat := 624878228566465848978371

theorem tailTrace_1825419 : CollatzResearch.WordTrace tailWord_1825419 prefixEnd_1825419 624878228566465848978371 := by
  unfold tailWord_1825419
  simp only [CollatzResearch.WordTrace]
  refine ⟨66578500573826194590087311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44385667049217463060058207 66578500573826194590087311)
  ·
    refine ⟨99867750860739291885130967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66578500573826194590087311 99867750860739291885130967)
    ·
      refine ⟨149801626291108937827696451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99867750860739291885130967 149801626291108937827696451)
      ·
        refine ⟨224702439436663406741544677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149801626291108937827696451 224702439436663406741544677)
        ·
          refine ⟨42131707394374388764039627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 224702439436663406741544677 42131707394374388764039627)
          ·
            refine ⟨63197561091561583146059441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42131707394374388764039627 63197561091561583146059441)
            ·
              refine ⟨47398170818671187359544581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63197561091561583146059441 47398170818671187359544581)
              ·
                refine ⟨8887157028500847629914609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47398170818671187359544581 8887157028500847629914609)
                ·
                  refine ⟨6665367771375635722435957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8887157028500847629914609 6665367771375635722435957)
                  ·
                    refine ⟨624878228566465848978371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6665367771375635722435957 624878228566465848978371)
                    ·
                      rfl

theorem cell22_1825419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 4, 2, 5].length) (baseStart_1825419 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1825419 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1825419 prefixEnd_1825419 := by exact prefixLift 1825419
  have htrace : WordTrace (prefixWord ++ tailWord_1825419) baseStart_1825419 baseEnd_1825419 := by
    simpa [prefixWord, tailWord_1825419, baseEnd_1825419] using wordTrace_append hprefix tailTrace_1825419
  have hstable : (prefixWord ++ tailWord_1825419).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1825419).length < 2 ^ (prefixWord ++ tailWord_1825419).sum := by decide
  have hdescent : baseEnd_1825419 < baseStart_1825419 := by decide
  rcases family_descends (prefixWord ++ tailWord_1825419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1825438 : List Nat := [4, 3, 1, 1, 1, 1, 3, 3, 5]
def baseStart_1825438 : Nat := 118140960795 + 1825438 * 2 ^ 59
def prefixEnd_1825438 : Nat := 4983230072969 + 3 ^ 40 * 1825438 * 2
def baseEnd_1825438 : Nat := 208294910884918710917771

theorem tailTrace_1825438 : CollatzResearch.WordTrace tailWord_1825438 prefixEnd_1825438 208294910884918710917771 := by
  unfold tailWord_1825438
  simp only [CollatzResearch.WordTrace]
  refine ⟨8322399195094670104378621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44386129040504907223352645 8322399195094670104378621)
  ·
    refine ⟨3120899698160501289141983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8322399195094670104378621 3120899698160501289141983)
    ·
      refine ⟨4681349547240751933712975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3120899698160501289141983 4681349547240751933712975)
      ·
        refine ⟨7022024320861127900569463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4681349547240751933712975 7022024320861127900569463)
        ·
          refine ⟨10533036481291691850854195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7022024320861127900569463 10533036481291691850854195)
          ·
            refine ⟨15799554721937537776281293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10533036481291691850854195 15799554721937537776281293)
            ·
              refine ⟨5924833020726576666105485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15799554721937537776281293 5924833020726576666105485)
              ·
                refine ⟨2221812382772466249789557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5924833020726576666105485 2221812382772466249789557)
                ·
                  refine ⟨208294910884918710917771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2221812382772466249789557 208294910884918710917771)
                  ·
                    rfl

theorem cell22_1825438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 3, 5].length) (baseStart_1825438 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1825438 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1825438 prefixEnd_1825438 := by exact prefixLift 1825438
  have htrace : WordTrace (prefixWord ++ tailWord_1825438) baseStart_1825438 baseEnd_1825438 := by
    simpa [prefixWord, tailWord_1825438, baseEnd_1825438] using wordTrace_append hprefix tailTrace_1825438
  have hstable : (prefixWord ++ tailWord_1825438).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1825438).length < 2 ^ (prefixWord ++ tailWord_1825438).sum := by decide
  have hdescent : baseEnd_1825438 < baseStart_1825438 := by decide
  rcases family_descends (prefixWord ++ tailWord_1825438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1825498 : List Nat := [3, 1, 1, 2, 2, 2, 1, 5, 2, 3]
def baseStart_1825498 : Nat := 118140960795 + 1825498 * 2 ^ 59
def prefixEnd_1825498 : Nat := 4983230072969 + 3 ^ 40 * 1825498 * 2
def baseEnd_1825498 : Nat := 624905271880935976253129

theorem tailTrace_1825498 : CollatzResearch.WordTrace tailWord_1825498 prefixEnd_1825498 624905271880935976253129 := by
  unfold tailWord_1825498
  simp only [CollatzResearch.WordTrace]
  refine ⟨16645345485134997770553287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44387587960359994054808765 16645345485134997770553287)
  ·
    refine ⟨24968018227702496655829931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16645345485134997770553287 24968018227702496655829931)
    ·
      refine ⟨37452027341553744983744897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24968018227702496655829931 37452027341553744983744897)
      ·
        refine ⟨28089020506165308737808673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37452027341553744983744897 28089020506165308737808673)
        ·
          refine ⟨21066765379623981553356505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28089020506165308737808673 21066765379623981553356505)
          ·
            refine ⟨15800074034717986165017379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21066765379623981553356505 15800074034717986165017379)
            ·
              refine ⟨23700111052076979247526069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15800074034717986165017379 23700111052076979247526069)
              ·
                refine ⟨2221885411132216804455569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23700111052076979247526069 2221885411132216804455569)
                ·
                  refine ⟨1666414058349162603341677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2221885411132216804455569 1666414058349162603341677)
                  ·
                    refine ⟨624905271880935976253129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1666414058349162603341677 624905271880935976253129)
                    ·
                      rfl

theorem cell22_1825498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 5, 2, 3].length) (baseStart_1825498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1825498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1825498 prefixEnd_1825498 := by exact prefixLift 1825498
  have htrace : WordTrace (prefixWord ++ tailWord_1825498) baseStart_1825498 baseEnd_1825498 := by
    simpa [prefixWord, tailWord_1825498, baseEnd_1825498] using wordTrace_append hprefix tailTrace_1825498
  have hstable : (prefixWord ++ tailWord_1825498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1825498).length < 2 ^ (prefixWord ++ tailWord_1825498).sum := by decide
  have hdescent : baseEnd_1825498 < baseStart_1825498 := by decide
  rcases family_descends (prefixWord ++ tailWord_1825498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1825594 : List Nat := [3, 1, 1, 1, 6, 1, 3, 2, 1, 3]
def baseStart_1825594 : Nat := 118140960795 + 1825594 * 2 ^ 59
def prefixEnd_1825594 : Nat := 4983230072969 + 3 ^ 40 * 1825594 * 2
def baseEnd_1825594 : Nat := 624938134642823725852835

theorem tailTrace_1825594 : CollatzResearch.WordTrace tailWord_1825594 prefixEnd_1825594 624938134642823725852835 := by
  unfold tailWord_1825594
  simp only [CollatzResearch.WordTrace]
  refine ⟨16646220837048049869426959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44389922232128132985138557 16646220837048049869426959)
  ·
    refine ⟨24969331255572074804140439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16646220837048049869426959 24969331255572074804140439)
    ·
      refine ⟨37453996883358112206210659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24969331255572074804140439 37453996883358112206210659)
      ·
        refine ⟨56180995325037168309315989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37453996883358112206210659 56180995325037168309315989)
        ·
          refine ⟨2633484155861117264499187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 56180995325037168309315989 2633484155861117264499187)
          ·
            refine ⟨3950226233791675896748781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2633484155861117264499187 3950226233791675896748781)
            ·
              refine ⟨1481334837671878461280793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3950226233791675896748781 1481334837671878461280793)
              ·
                refine ⟨1111001128253908845960595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1481334837671878461280793 1111001128253908845960595)
                ·
                  refine ⟨1666501692380863268940893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1111001128253908845960595 1666501692380863268940893)
                  ·
                    refine ⟨624938134642823725852835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1666501692380863268940893 624938134642823725852835)
                    ·
                      rfl

theorem cell22_1825594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 3, 2, 1, 3].length) (baseStart_1825594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1825594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1825594 prefixEnd_1825594 := by exact prefixLift 1825594
  have htrace : WordTrace (prefixWord ++ tailWord_1825594) baseStart_1825594 baseEnd_1825594 := by
    simpa [prefixWord, tailWord_1825594, baseEnd_1825594] using wordTrace_append hprefix tailTrace_1825594
  have hstable : (prefixWord ++ tailWord_1825594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1825594).length < 2 ^ (prefixWord ++ tailWord_1825594).sum := by decide
  have hdescent : baseEnd_1825594 < baseStart_1825594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1825594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1825620 : List Nat := [2, 4, 1, 1, 4, 1, 1, 1, 3, 4]
def baseStart_1825620 : Nat := 118140960795 + 1825620 * 2 ^ 59
def prefixEnd_1825620 : Nat := 4983230072969 + 3 ^ 40 * 1825620 * 2
def baseEnd_1825620 : Nat := 624947034974168324702755

theorem tailTrace_1825620 : CollatzResearch.WordTrace tailWord_1825620 prefixEnd_1825620 624947034974168324702755 := by
  unfold tailWord_1825620
  simp only [CollatzResearch.WordTrace]
  refine ⟨33292915823049002959077157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44390554430732003945436209 33292915823049002959077157)
  ·
    refine ⟨6242421716821688054826967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33292915823049002959077157 6242421716821688054826967)
    ·
      refine ⟨9363632575232532082240451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6242421716821688054826967 9363632575232532082240451)
      ·
        refine ⟨14045448862848798123360677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9363632575232532082240451 14045448862848798123360677)
        ·
          refine ⟨2633521661784149648130127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14045448862848798123360677 2633521661784149648130127)
          ·
            refine ⟨3950282492676224472195191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2633521661784149648130127 3950282492676224472195191)
            ·
              refine ⟨5925423739014336708292787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3950282492676224472195191 5925423739014336708292787)
              ·
                refine ⟨8888135608521505062439181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5925423739014336708292787 8888135608521505062439181)
                ·
                  refine ⟨3333050853195564398414693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8888135608521505062439181 3333050853195564398414693)
                  ·
                    refine ⟨624947034974168324702755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3333050853195564398414693 624947034974168324702755)
                    ·
                      rfl

theorem cell22_1825620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 1, 3, 4].length) (baseStart_1825620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1825620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1825620 prefixEnd_1825620 := by exact prefixLift 1825620
  have htrace : WordTrace (prefixWord ++ tailWord_1825620) baseStart_1825620 baseEnd_1825620 := by
    simpa [prefixWord, tailWord_1825620, baseEnd_1825620] using wordTrace_append hprefix tailTrace_1825620
  have hstable : (prefixWord ++ tailWord_1825620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1825620).length < 2 ^ (prefixWord ++ tailWord_1825620).sum := by decide
  have hdescent : baseEnd_1825620 < baseStart_1825620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1825620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1825633 : List Nat := [1, 2, 3, 1, 1, 1, 2, 4, 4, 3]
def baseStart_1825633 : Nat := 118140960795 + 1825633 * 2 ^ 59
def prefixEnd_1825633 : Nat := 4983230072969 + 3 ^ 40 * 1825633 * 2
def baseEnd_1825633 : Nat := 624951485139840624127715

theorem tailTrace_1825633 : CollatzResearch.WordTrace tailWord_1825633 prefixEnd_1825633 624951485139840624127715 := by
  unfold tailWord_1825633
  simp only [CollatzResearch.WordTrace]
  refine ⟨66586305795050909138377553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44390870530033939425585035 66586305795050909138377553)
  ·
    refine ⟨49939729346288181853783165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66586305795050909138377553 49939729346288181853783165)
    ·
      refine ⟨18727398504858068195168687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49939729346288181853783165 18727398504858068195168687)
      ·
        refine ⟨28091097757287102292753031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18727398504858068195168687 28091097757287102292753031)
        ·
          refine ⟨42136646635930653439129547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28091097757287102292753031 42136646635930653439129547)
          ·
            refine ⟨63204969953895980158694321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42136646635930653439129547 63204969953895980158694321)
            ·
              refine ⟨47403727465421985119020741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63204969953895980158694321 47403727465421985119020741)
              ·
                refine ⟨8888198899766622209816389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47403727465421985119020741 8888198899766622209816389)
                ·
                  refine ⟨1666537293706241664340573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8888198899766622209816389 1666537293706241664340573)
                  ·
                    refine ⟨624951485139840624127715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1666537293706241664340573 624951485139840624127715)
                    ·
                      rfl

theorem cell22_1825633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 4, 4, 3].length) (baseStart_1825633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1825633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1825633 prefixEnd_1825633 := by exact prefixLift 1825633
  have htrace : WordTrace (prefixWord ++ tailWord_1825633) baseStart_1825633 baseEnd_1825633 := by
    simpa [prefixWord, tailWord_1825633, baseEnd_1825633] using wordTrace_append hprefix tailTrace_1825633
  have hstable : (prefixWord ++ tailWord_1825633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1825633).length < 2 ^ (prefixWord ++ tailWord_1825633).sum := by decide
  have hdescent : baseEnd_1825633 < baseStart_1825633 := by decide
  rcases family_descends (prefixWord ++ tailWord_1825633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1825648 : List Nat := [2, 1, 1, 1, 4, 1, 4, 2, 2, 4]
def baseStart_1825648 : Nat := 118140960795 + 1825648 * 2 ^ 59
def prefixEnd_1825648 : Nat := 4983230072969 + 3 ^ 40 * 1825648 * 2
def baseEnd_1825648 : Nat := 624956619946385585002669

theorem tailTrace_1825648 : CollatzResearch.WordTrace tailWord_1825648 prefixEnd_1825648 624956619946385585002669 := by
  unfold tailWord_1825648
  simp only [CollatzResearch.WordTrace]
  refine ⟨33293426444998283350086799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44391235259997711133449065 33293426444998283350086799)
  ·
    refine ⟨49940139667497425025130199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33293426444998283350086799 49940139667497425025130199)
    ·
      refine ⟨74910209501246137537695299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49940139667497425025130199 74910209501246137537695299)
      ·
        refine ⟨112365314251869206306542949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74910209501246137537695299 112365314251869206306542949)
        ·
          refine ⟨21068496422225476182476803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112365314251869206306542949 21068496422225476182476803)
          ·
            refine ⟨31602744633338214273715205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21068496422225476182476803 31602744633338214273715205)
            ·
              refine ⟨5925514618750915176321601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31602744633338214273715205 5925514618750915176321601)
              ·
                refine ⟨4444135964063186382241201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5925514618750915176321601 4444135964063186382241201)
                ·
                  refine ⟨3333101973047389786680901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4444135964063186382241201 3333101973047389786680901)
                  ·
                    refine ⟨624956619946385585002669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3333101973047389786680901 624956619946385585002669)
                    ·
                      rfl

theorem cell22_1825648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 2, 2, 4].length) (baseStart_1825648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1825648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1825648 prefixEnd_1825648 := by exact prefixLift 1825648
  have htrace : WordTrace (prefixWord ++ tailWord_1825648) baseStart_1825648 baseEnd_1825648 := by
    simpa [prefixWord, tailWord_1825648, baseEnd_1825648] using wordTrace_append hprefix tailTrace_1825648
  have hstable : (prefixWord ++ tailWord_1825648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1825648).length < 2 ^ (prefixWord ++ tailWord_1825648).sum := by decide
  have hdescent : baseEnd_1825648 < baseStart_1825648 := by decide
  rcases family_descends (prefixWord ++ tailWord_1825648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1825650 : List Nat := [3, 2, 1, 2, 1, 1, 3, 4, 2, 3]
def baseStart_1825650 : Nat := 118140960795 + 1825650 * 2 ^ 59
def prefixEnd_1825650 : Nat := 4983230072969 + 3 ^ 40 * 1825650 * 2
def baseEnd_1825650 : Nat := 624957304587258246452663

theorem tailTrace_1825650 : CollatzResearch.WordTrace tailWord_1825650 prefixEnd_1825650 624957304587258246452663 := by
  unfold tailWord_1825650
  simp only [CollatzResearch.WordTrace]
  refine ⟨16646731458997330260436601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44391283890659547361164269 16646731458997330260436601)
  ·
    refine ⟨12485048594247997695327451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16646731458997330260436601 12485048594247997695327451)
    ·
      refine ⟨18727572891371996542991177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12485048594247997695327451 18727572891371996542991177)
      ·
        refine ⟨14045679668528997407243383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18727572891371996542991177 14045679668528997407243383)
        ·
          refine ⟨21068519502793496110865075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14045679668528997407243383 21068519502793496110865075)
          ·
            refine ⟨31602779254190244166297613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21068519502793496110865075 31602779254190244166297613)
            ·
              refine ⟨11851042220321341562361605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31602779254190244166297613 11851042220321341562361605)
              ·
                refine ⟨2222070416310251542942801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11851042220321341562361605 2222070416310251542942801)
                ·
                  refine ⟨1666552812232688657207101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2222070416310251542942801 1666552812232688657207101)
                  ·
                    refine ⟨624957304587258246452663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1666552812232688657207101 624957304587258246452663)
                    ·
                      rfl

theorem cell22_1825650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 4, 2, 3].length) (baseStart_1825650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1825650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1825650 prefixEnd_1825650 := by exact prefixLift 1825650
  have htrace : WordTrace (prefixWord ++ tailWord_1825650) baseStart_1825650 baseEnd_1825650 := by
    simpa [prefixWord, tailWord_1825650, baseEnd_1825650] using wordTrace_append hprefix tailTrace_1825650
  have hstable : (prefixWord ++ tailWord_1825650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1825650).length < 2 ^ (prefixWord ++ tailWord_1825650).sum := by decide
  have hdescent : baseEnd_1825650 < baseStart_1825650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1825650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1825686 : List Nat := [5, 3, 1, 1, 1, 2, 2, 3, 4]
def baseStart_1825686 : Nat := 118140960795 + 1825686 * 2 ^ 59
def prefixEnd_1825686 : Nat := 4983230072969 + 3 ^ 40 * 1825686 * 2
def baseEnd_1825686 : Nat := 208323209374322050850851

theorem tailTrace_1825686 : CollatzResearch.WordTrace tailWord_1825686 prefixEnd_1825686 208323209374322050850851 := by
  unfold tailWord_1825686
  simp only [CollatzResearch.WordTrace]
  refine ⟨4161764928991181199378557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44392159242572599460037941 4161764928991181199378557)
  ·
    refine ⟨1560661848371692949766959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4161764928991181199378557 1560661848371692949766959)
    ·
      refine ⟨2340992772557539424650439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1560661848371692949766959 2340992772557539424650439)
      ·
        refine ⟨3511489158836309136975659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2340992772557539424650439 3511489158836309136975659)
        ·
          refine ⟨5267233738254463705463489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3511489158836309136975659 5267233738254463705463489)
          ·
            refine ⟨3950425303690847779097617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5267233738254463705463489 3950425303690847779097617)
            ·
              refine ⟨2962818977768135834323213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3950425303690847779097617 2962818977768135834323213)
              ·
                refine ⟨1111057116663050937871205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2962818977768135834323213 1111057116663050937871205)
                ·
                  refine ⟨208323209374322050850851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1111057116663050937871205 208323209374322050850851)
                  ·
                    rfl

theorem cell22_1825686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_1825686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1825686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1825686 prefixEnd_1825686 := by exact prefixLift 1825686
  have htrace : WordTrace (prefixWord ++ tailWord_1825686) baseStart_1825686 baseEnd_1825686 := by
    simpa [prefixWord, tailWord_1825686, baseEnd_1825686] using wordTrace_append hprefix tailTrace_1825686
  have hstable : (prefixWord ++ tailWord_1825686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1825686).length < 2 ^ (prefixWord ++ tailWord_1825686).sum := by decide
  have hdescent : baseEnd_1825686 < baseStart_1825686 := by decide
  rcases family_descends (prefixWord ++ tailWord_1825686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1825718 : List Nat := [5, 1, 4, 1, 2, 1, 1, 1, 1, 5]
def baseStart_1825718 : Nat := 118140960795 + 1825718 * 2 ^ 59
def prefixEnd_1825718 : Nat := 4983230072969 + 3 ^ 40 * 1825718 * 2
def baseEnd_1825718 : Nat := 624980582376928735752455

theorem tailTrace_1825718 : CollatzResearch.WordTrace tailWord_1825718 prefixEnd_1825718 624980582376928735752455 := by
  unfold tailWord_1825718
  simp only [CollatzResearch.WordTrace]
  refine ⟨4161837874983935540951363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44392937333161979103481205 4161837874983935540951363)
  ·
    refine ⟨6242756812475903311427045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4161837874983935540951363 6242756812475903311427045)
    ·
      refine ⟨1170516902339231870892571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6242756812475903311427045 1170516902339231870892571)
      ·
        refine ⟨1755775353508847806338857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1170516902339231870892571 1755775353508847806338857)
        ·
          refine ⟨1316831515131635854754143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1755775353508847806338857 1316831515131635854754143)
          ·
            refine ⟨1975247272697453782131215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1316831515131635854754143 1975247272697453782131215)
            ·
              refine ⟨2962870909046180673196823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1975247272697453782131215 2962870909046180673196823)
              ·
                refine ⟨4444306363569271009795235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2962870909046180673196823 4444306363569271009795235)
                ·
                  refine ⟨6666459545353906514692853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4444306363569271009795235 6666459545353906514692853)
                  ·
                    refine ⟨624980582376928735752455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6666459545353906514692853 624980582376928735752455)
                    ·
                      rfl

theorem cell22_1825718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_1825718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1825718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1825718 prefixEnd_1825718 := by exact prefixLift 1825718
  have htrace : WordTrace (prefixWord ++ tailWord_1825718) baseStart_1825718 baseEnd_1825718 := by
    simpa [prefixWord, tailWord_1825718, baseEnd_1825718] using wordTrace_append hprefix tailTrace_1825718
  have hstable : (prefixWord ++ tailWord_1825718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1825718).length < 2 ^ (prefixWord ++ tailWord_1825718).sum := by decide
  have hdescent : baseEnd_1825718 < baseStart_1825718 := by decide
  rcases family_descends (prefixWord ++ tailWord_1825718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1825746 : List Nat := [3, 2, 2, 3, 1, 3, 1, 3, 1, 3]
def baseStart_1825746 : Nat := 118140960795 + 1825746 * 2 ^ 59
def prefixEnd_1825746 : Nat := 4983230072969 + 3 ^ 40 * 1825746 * 2
def baseEnd_1825746 : Nat := 624990167349145996052369

theorem tailTrace_1825746 : CollatzResearch.WordTrace tailWord_1825746 prefixEnd_1825746 624990167349145996052369 := by
  unfold tailWord_1825746
  simp only [CollatzResearch.WordTrace]
  refine ⟨16647606810910382359310273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44393618162427686291494061 16647606810910382359310273)
  ·
    refine ⟨12485705108182786769482705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16647606810910382359310273 12485705108182786769482705)
    ·
      refine ⟨9364278831137090077112029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12485705108182786769482705 9364278831137090077112029)
      ·
        refine ⟨3511604561676408778917011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9364278831137090077112029 3511604561676408778917011)
        ·
          refine ⟨5267406842514613168375517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3511604561676408778917011 5267406842514613168375517)
          ·
            refine ⟨1975277565942979938140819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5267406842514613168375517 1975277565942979938140819)
            ·
              refine ⟨2962916348914469907211229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1975277565942979938140819 2962916348914469907211229)
              ·
                refine ⟨1111093630842926215204211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2962916348914469907211229 1111093630842926215204211)
                ·
                  refine ⟨1666640446264389322806317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1111093630842926215204211 1666640446264389322806317)
                  ·
                    refine ⟨624990167349145996052369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1666640446264389322806317 624990167349145996052369)
                    ·
                      rfl

theorem cell22_1825746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 1, 3, 1, 3].length) (baseStart_1825746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1825746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1825746 prefixEnd_1825746 := by exact prefixLift 1825746
  have htrace : WordTrace (prefixWord ++ tailWord_1825746) baseStart_1825746 baseEnd_1825746 := by
    simpa [prefixWord, tailWord_1825746, baseEnd_1825746] using wordTrace_append hprefix tailTrace_1825746
  have hstable : (prefixWord ++ tailWord_1825746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1825746).length < 2 ^ (prefixWord ++ tailWord_1825746).sum := by decide
  have hdescent : baseEnd_1825746 < baseStart_1825746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1825746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1825770 : List Nat := [3, 1, 3, 1, 2, 2, 3, 1, 6]
def baseStart_1825770 : Nat := 118140960795 + 1825770 * 2 ^ 59
def prefixEnd_1825770 : Nat := 4983230072969 + 3 ^ 40 * 1825770 * 2
def baseEnd_1825770 : Nat := 208332794346539311150765

theorem tailTrace_1825770 : CollatzResearch.WordTrace tailWord_1825770 prefixEnd_1825770 208332794346539311150765 := by
  unfold tailWord_1825770
  simp only [CollatzResearch.WordTrace]
  refine ⟨16647825648888645384028691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44394201730369721024076509 16647825648888645384028691)
  ·
    refine ⟨24971738473332968076043037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16647825648888645384028691 24971738473332968076043037)
    ·
      refine ⟨9364401927499863028516139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24971738473332968076043037 9364401927499863028516139)
      ·
        refine ⟨14046602891249794542774209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9364401927499863028516139 14046602891249794542774209)
        ·
          refine ⟨10534952168437345907080657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14046602891249794542774209 10534952168437345907080657)
          ·
            refine ⟨7901214126328009430310493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10534952168437345907080657 7901214126328009430310493)
            ·
              refine ⟨2962955297373003536366435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7901214126328009430310493 2962955297373003536366435)
              ·
                refine ⟨4444432946059505304549653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2962955297373003536366435 4444432946059505304549653)
                ·
                  refine ⟨208332794346539311150765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4444432946059505304549653 208332794346539311150765)
                  ·
                    rfl

theorem cell22_1825770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 3, 1, 6].length) (baseStart_1825770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1825770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1825770 prefixEnd_1825770 := by exact prefixLift 1825770
  have htrace : WordTrace (prefixWord ++ tailWord_1825770) baseStart_1825770 baseEnd_1825770 := by
    simpa [prefixWord, tailWord_1825770, baseEnd_1825770] using wordTrace_append hprefix tailTrace_1825770
  have hstable : (prefixWord ++ tailWord_1825770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1825770).length < 2 ^ (prefixWord ++ tailWord_1825770).sum := by decide
  have hdescent : baseEnd_1825770 < baseStart_1825770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1825770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1825800 : List Nat := [2, 1, 3, 2, 1, 3, 1, 3, 2, 4]
def baseStart_1825800 : Nat := 118140960795 + 1825800 * 2 ^ 59
def prefixEnd_1825800 : Nat := 4983230072969 + 3 ^ 40 * 1825800 * 2
def baseEnd_1825800 : Nat := 625008652652707855202203

theorem tailTrace_1825800 : CollatzResearch.WordTrace tailWord_1825800 prefixEnd_1825800 625008652652707855202203 := by
  unfold tailWord_1825800
  simp only [CollatzResearch.WordTrace]
  refine ⟨33296198392722948329853427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44394931190297264439804569 33296198392722948329853427)
  ·
    refine ⟨49944297589084422494780141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33296198392722948329853427 49944297589084422494780141)
    ·
      refine ⟨18729111595906658435542553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49944297589084422494780141 18729111595906658435542553)
      ·
        refine ⟨14046833696929993826656915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18729111595906658435542553 14046833696929993826656915)
        ·
          refine ⟨21070250545394990739985373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14046833696929993826656915 21070250545394990739985373)
          ·
            refine ⟨7901343954523121527494515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21070250545394990739985373 7901343954523121527494515)
            ·
              refine ⟨11852015931784682291241773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7901343954523121527494515 11852015931784682291241773)
              ·
                refine ⟨4444505974419255859215665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11852015931784682291241773 4444505974419255859215665)
                ·
                  refine ⟨3333379480814441894411749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4444505974419255859215665 3333379480814441894411749)
                  ·
                    refine ⟨625008652652707855202203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3333379480814441894411749 625008652652707855202203)
                    ·
                      rfl

theorem cell22_1825800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 3, 2, 4].length) (baseStart_1825800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1825800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1825800 prefixEnd_1825800 := by exact prefixLift 1825800
  have htrace : WordTrace (prefixWord ++ tailWord_1825800) baseStart_1825800 baseEnd_1825800 := by
    simpa [prefixWord, tailWord_1825800, baseEnd_1825800] using wordTrace_append hprefix tailTrace_1825800
  have hstable : (prefixWord ++ tailWord_1825800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1825800).length < 2 ^ (prefixWord ++ tailWord_1825800).sum := by decide
  have hdescent : baseEnd_1825800 < baseStart_1825800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1825800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1825821 : List Nat := [1, 4, 2, 2, 3, 2, 2, 2, 4]
def baseStart_1825821 : Nat := 118140960795 + 1825821 * 2 ^ 59
def prefixEnd_1825821 : Nat := 4983230072969 + 3 ^ 40 * 1825821 * 2
def baseEnd_1825821 : Nat := 208338613793956933475713

theorem tailTrace_1825821 : CollatzResearch.WordTrace tailWord_1825821 prefixEnd_1825821 208338613793956933475713 := by
  unfold tailWord_1825821
  simp only [CollatzResearch.WordTrace]
  refine ⟨66593162718369817246221317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44395441812246544830814211 66593162718369817246221317)
  ·
    refine ⟨12486218009694340733666497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66593162718369817246221317 12486218009694340733666497)
    ·
      refine ⟨9364663507270755550249873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12486218009694340733666497 9364663507270755550249873)
      ·
        refine ⟨7023497630453066662687405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9364663507270755550249873 7023497630453066662687405)
        ·
          refine ⟨2633811611419899998507777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7023497630453066662687405 2633811611419899998507777)
          ·
            refine ⟨1975358708564924998880833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2633811611419899998507777 1975358708564924998880833)
            ·
              refine ⟨1481519031423693749160625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1975358708564924998880833 1481519031423693749160625)
              ·
                refine ⟨1111139273567770311870469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1481519031423693749160625 1111139273567770311870469)
                ·
                  refine ⟨208338613793956933475713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1111139273567770311870469 208338613793956933475713)
                  ·
                    rfl

theorem cell22_1825821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 2, 2, 4].length) (baseStart_1825821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1825821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1825821 prefixEnd_1825821 := by exact prefixLift 1825821
  have htrace : WordTrace (prefixWord ++ tailWord_1825821) baseStart_1825821 baseEnd_1825821 := by
    simpa [prefixWord, tailWord_1825821, baseEnd_1825821] using wordTrace_append hprefix tailTrace_1825821
  have hstable : (prefixWord ++ tailWord_1825821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1825821).length < 2 ^ (prefixWord ++ tailWord_1825821).sum := by decide
  have hdescent : baseEnd_1825821 < baseStart_1825821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1825821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1825843 : List Nat := [1, 1, 1, 2, 4, 1, 1, 2, 9]
def baseStart_1825843 : Nat := 118140960795 + 1825843 * 2 ^ 59
def prefixEnd_1825843 : Nat := 4983230072969 + 3 ^ 40 * 1825843 * 2
def baseEnd_1825843 : Nat := 208341124143823358792357

theorem tailTrace_1825843 : CollatzResearch.WordTrace tailWord_1825843 prefixEnd_1825843 208341124143823358792357 := by
  unfold tailWord_1825843
  simp only [CollatzResearch.WordTrace]
  refine ⟨66593965124290115003522183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44395976749526743335681455 66593965124290115003522183)
  ·
    refine ⟨99890947686435172505283275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66593965124290115003522183 99890947686435172505283275)
    ·
      refine ⟨149836421529652758757924913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99890947686435172505283275 149836421529652758757924913)
      ·
        refine ⟨112377316147239569068443685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149836421529652758757924913 112377316147239569068443685)
        ·
          refine ⟨21070746777607419200333191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112377316147239569068443685 21070746777607419200333191)
          ·
            refine ⟨31606120166411128800499787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21070746777607419200333191 31606120166411128800499787)
            ·
              refine ⟨47409180249616693200749681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31606120166411128800499787 47409180249616693200749681)
              ·
                refine ⟨35556885187212519900562261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47409180249616693200749681 35556885187212519900562261)
                ·
                  refine ⟨208341124143823358792357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 35556885187212519900562261 208341124143823358792357)
                  ·
                    rfl

theorem cell22_1825843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 9].length) (baseStart_1825843 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1825843 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1825843 prefixEnd_1825843 := by exact prefixLift 1825843
  have htrace : WordTrace (prefixWord ++ tailWord_1825843) baseStart_1825843 baseEnd_1825843 := by
    simpa [prefixWord, tailWord_1825843, baseEnd_1825843] using wordTrace_append hprefix tailTrace_1825843
  have hstable : (prefixWord ++ tailWord_1825843).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1825843).length < 2 ^ (prefixWord ++ tailWord_1825843).sum := by decide
  have hdescent : baseEnd_1825843 < baseStart_1825843 := by decide
  rcases family_descends (prefixWord ++ tailWord_1825843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1825864 : List Nat := [2, 1, 3, 1, 1, 1, 6, 3, 1, 3]
def baseStart_1825864 : Nat := 118140960795 + 1825864 * 2 ^ 59
def prefixEnd_1825864 : Nat := 4983230072969 + 3 ^ 40 * 1825864 * 2
def baseEnd_1825864 : Nat := 625030561160633021602007

theorem tailTrace_1825864 : CollatzResearch.WordTrace tailWord_1825864 prefixEnd_1825864 625030561160633021602007 := by
  unfold tailWord_1825864
  simp only [CollatzResearch.WordTrace]
  refine ⟨33297365528607017795018323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44396487371476023726691097 33297365528607017795018323)
  ·
    refine ⟨49946048292910526692527485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33297365528607017795018323 49946048292910526692527485)
    ·
      refine ⟨18729768109841447509697807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49946048292910526692527485 18729768109841447509697807)
      ·
        refine ⟨28094652164762171264546711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18729768109841447509697807 28094652164762171264546711)
        ·
          refine ⟨42141978247143256896820067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28094652164762171264546711 42141978247143256896820067)
          ·
            refine ⟨63212967370714885345230101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42141978247143256896820067 63212967370714885345230101)
            ·
              refine ⟨2963107845502260250557661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 63212967370714885345230101 2963107845502260250557661)
              ·
                refine ⟨1111165442063347593959123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2963107845502260250557661 1111165442063347593959123)
                ·
                  refine ⟨1666748163095021390938685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1111165442063347593959123 1666748163095021390938685)
                  ·
                    refine ⟨625030561160633021602007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1666748163095021390938685 625030561160633021602007)
                    ·
                      rfl

theorem cell22_1825864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 6, 3, 1, 3].length) (baseStart_1825864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1825864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1825864 prefixEnd_1825864 := by exact prefixLift 1825864
  have htrace : WordTrace (prefixWord ++ tailWord_1825864) baseStart_1825864 baseEnd_1825864 := by
    simpa [prefixWord, tailWord_1825864, baseEnd_1825864] using wordTrace_append hprefix tailTrace_1825864
  have hstable : (prefixWord ++ tailWord_1825864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1825864).length < 2 ^ (prefixWord ++ tailWord_1825864).sum := by decide
  have hdescent : baseEnd_1825864 < baseStart_1825864 := by decide
  rcases family_descends (prefixWord ++ tailWord_1825864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1825920 : List Nat := [2, 1, 1, 2, 1, 3, 2, 4, 1, 5]
def baseStart_1825920 : Nat := 118140960795 + 1825920 * 2 ^ 59
def prefixEnd_1825920 : Nat := 4983230072969 + 3 ^ 40 * 1825920 * 2
def baseEnd_1825920 : Nat := 625049731105067542201835

theorem tailTrace_1825920 : CollatzResearch.WordTrace tailWord_1825920 prefixEnd_1825920 625049731105067542201835 := by
  unfold tailWord_1825920
  simp only [CollatzResearch.WordTrace]
  refine ⟨33298386772505578577037607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44397849030007438102716809 33298386772505578577037607)
  ·
    refine ⟨49947580158758367865556411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33298386772505578577037607 49947580158758367865556411)
    ·
      refine ⟨74921370238137551798334617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49947580158758367865556411 74921370238137551798334617)
      ·
        refine ⟨56191027678603163848750963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74921370238137551798334617 56191027678603163848750963)
        ·
          refine ⟨84286541517904745773126445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56191027678603163848750963 84286541517904745773126445)
          ·
            refine ⟨31607453069214279664922417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84286541517904745773126445 31607453069214279664922417)
            ·
              refine ⟨23705589801910709748691813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31607453069214279664922417 23705589801910709748691813)
              ·
                refine ⟨4444798087858258077879715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23705589801910709748691813 4444798087858258077879715)
                ·
                  refine ⟨6667197131787387116819573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4444798087858258077879715 6667197131787387116819573)
                  ·
                    refine ⟨625049731105067542201835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6667197131787387116819573 625049731105067542201835)
                    ·
                      rfl

theorem cell22_1825920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 4, 1, 5].length) (baseStart_1825920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1825920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1825920 prefixEnd_1825920 := by exact prefixLift 1825920
  have htrace : WordTrace (prefixWord ++ tailWord_1825920) baseStart_1825920 baseEnd_1825920 := by
    simpa [prefixWord, tailWord_1825920, baseEnd_1825920] using wordTrace_append hprefix tailTrace_1825920
  have hstable : (prefixWord ++ tailWord_1825920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1825920).length < 2 ^ (prefixWord ++ tailWord_1825920).sum := by decide
  have hdescent : baseEnd_1825920 < baseStart_1825920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1825920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1825969 : List Nat := [1, 2, 2, 5, 1, 2, 2, 1, 2, 4]
def baseStart_1825969 : Nat := 118140960795 + 1825969 * 2 ^ 59
def prefixEnd_1825969 : Nat := 4983230072969 + 3 ^ 40 * 1825969 * 2
def baseEnd_1825969 : Nat := 625066504806447747726685

theorem tailTrace_1825969 : CollatzResearch.WordTrace tailWord_1825969 prefixEnd_1825969 625066504806447747726685 := by
  unfold tailWord_1825969
  simp only [CollatzResearch.WordTrace]
  refine ⟨66598560721833638522608961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44399040481222425681739307 66598560721833638522608961)
  ·
    refine ⟨49948920541375228891956721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66598560721833638522608961 49948920541375228891956721)
    ·
      refine ⟨37461690406031421668967541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49948920541375228891956721 37461690406031421668967541)
      ·
        refine ⟨3512033475565445781465707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37461690406031421668967541 3512033475565445781465707)
        ·
          refine ⟨5268050213348168672198561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3512033475565445781465707 5268050213348168672198561)
          ·
            refine ⟨3951037660011126504148921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5268050213348168672198561 3951037660011126504148921)
            ·
              refine ⟨2963278245008344878111691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3951037660011126504148921 2963278245008344878111691)
              ·
                refine ⟨4444917367512517317167537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2963278245008344878111691 4444917367512517317167537)
                ·
                  refine ⟨3333688025634387987875653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4444917367512517317167537 3333688025634387987875653)
                  ·
                    refine ⟨625066504806447747726685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3333688025634387987875653 625066504806447747726685)
                    ·
                      rfl

theorem cell22_1825969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 2, 1, 2, 4].length) (baseStart_1825969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1825969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1825969 prefixEnd_1825969 := by exact prefixLift 1825969
  have htrace : WordTrace (prefixWord ++ tailWord_1825969) baseStart_1825969 baseEnd_1825969 := by
    simpa [prefixWord, tailWord_1825969, baseEnd_1825969] using wordTrace_append hprefix tailTrace_1825969
  have hstable : (prefixWord ++ tailWord_1825969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1825969).length < 2 ^ (prefixWord ++ tailWord_1825969).sum := by decide
  have hdescent : baseEnd_1825969 < baseStart_1825969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1825969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1825990 : List Nat := [6, 1, 2, 2, 1, 1, 1, 4, 4]
def baseStart_1825990 : Nat := 118140960795 + 1825990 * 2 ^ 59
def prefixEnd_1825990 : Nat := 4983230072969 + 3 ^ 40 * 1825990 * 2
def baseEnd_1825990 : Nat := 208357897845203564317207

theorem tailTrace_1825990 : CollatzResearch.WordTrace tailWord_1825990 prefixEnd_1825990 208357897845203564317207 := by
  unfold tailWord_1825990
  simp only [CollatzResearch.WordTrace]
  refine ⟨2081228957961173722160107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 44399551103171706072748949 2081228957961173722160107)
  ·
    refine ⟨3121843436941760583240161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2081228957961173722160107 3121843436941760583240161)
    ·
      refine ⟨2341382577706320437430121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3121843436941760583240161 2341382577706320437430121)
      ·
        refine ⟨1756036933279740328072591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2341382577706320437430121 1756036933279740328072591)
        ·
          refine ⟨2634055399919610492108887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1756036933279740328072591 2634055399919610492108887)
          ·
            refine ⟨3951083099879415738163331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2634055399919610492108887 3951083099879415738163331)
            ·
              refine ⟨5926624649819123607244997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3951083099879415738163331 5926624649819123607244997)
              ·
                refine ⟨1111242121841085676358437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5926624649819123607244997 1111242121841085676358437)
                ·
                  refine ⟨208357897845203564317207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1111242121841085676358437 208357897845203564317207)
                  ·
                    rfl

theorem cell22_1825990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 4, 4].length) (baseStart_1825990 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1825990 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1825990 prefixEnd_1825990 := by exact prefixLift 1825990
  have htrace : WordTrace (prefixWord ++ tailWord_1825990) baseStart_1825990 baseEnd_1825990 := by
    simpa [prefixWord, tailWord_1825990, baseEnd_1825990] using wordTrace_append hprefix tailTrace_1825990
  have hstable : (prefixWord ++ tailWord_1825990).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1825990).length < 2 ^ (prefixWord ++ tailWord_1825990).sum := by decide
  have hdescent : baseEnd_1825990 < baseStart_1825990 := by decide
  rcases family_descends (prefixWord ++ tailWord_1825990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1826046 : List Nat := [4, 2, 2, 1, 1, 4, 1, 2, 5]
def baseStart_1826046 : Nat := 118140960795 + 1826046 * 2 ^ 59
def prefixEnd_1826046 : Nat := 4983230072969 + 3 ^ 40 * 1826046 * 2
def baseEnd_1826046 : Nat := 208364287826681737850483

theorem tailTrace_1826046 : CollatzResearch.WordTrace tailWord_1826046 prefixEnd_1826046 208364287826681737850483 := by
  unfold tailWord_1826046
  simp only [CollatzResearch.WordTrace]
  refine ⟨8325171142819335084145249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44400912761703120448774661 8325171142819335084145249)
  ·
    refine ⟨6243878357114501313108937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8325171142819335084145249 6243878357114501313108937)
    ·
      refine ⟨4682908767835875984831703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6243878357114501313108937 4682908767835875984831703)
      ·
        refine ⟨7024363151753813977247555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4682908767835875984831703 7024363151753813977247555)
        ·
          refine ⟨10536544727630720965871333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7024363151753813977247555 10536544727630720965871333)
          ·
            refine ⟨1975602136430760181100875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10536544727630720965871333 1975602136430760181100875)
            ·
              refine ⟨2963403204646140271651313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1975602136430760181100875 2963403204646140271651313)
              ·
                refine ⟨2222552403484605203738485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2963403204646140271651313 2222552403484605203738485)
                ·
                  refine ⟨208364287826681737850483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2222552403484605203738485 208364287826681737850483)
                  ·
                    rfl

theorem cell22_1826046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 1, 2, 5].length) (baseStart_1826046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1826046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1826046 prefixEnd_1826046 := by exact prefixLift 1826046
  have htrace : WordTrace (prefixWord ++ tailWord_1826046) baseStart_1826046 baseEnd_1826046 := by
    simpa [prefixWord, tailWord_1826046, baseEnd_1826046] using wordTrace_append hprefix tailTrace_1826046
  have hstable : (prefixWord ++ tailWord_1826046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1826046).length < 2 ^ (prefixWord ++ tailWord_1826046).sum := by decide
  have hdescent : baseEnd_1826046 < baseStart_1826046 := by decide
  rcases family_descends (prefixWord ++ tailWord_1826046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1826057 : List Nat := [1, 2, 1, 1, 3, 3, 4, 1, 6]
def baseStart_1826057 : Nat := 118140960795 + 1826057 * 2 ^ 59
def prefixEnd_1826057 : Nat := 4983230072969 + 3 ^ 40 * 1826057 * 2
def baseEnd_1826057 : Nat := 208365543001614950508805

theorem tailTrace_1826057 : CollatzResearch.WordTrace tailWord_1826057 prefixEnd_1826057 208365543001614950508805 := by
  unfold tailWord_1826057
  simp only [CollatzResearch.WordTrace]
  refine ⟨66601770345514829551812425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44401180230343219701208283 66601770345514829551812425)
  ·
    refine ⟨49951327759136122163859319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66601770345514829551812425 49951327759136122163859319)
    ·
      refine ⟨74926991638704183245788979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49951327759136122163859319 74926991638704183245788979)
      ·
        refine ⟨112390487458056274868683469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74926991638704183245788979 112390487458056274868683469)
        ·
          refine ⟨42146432796771103075756301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112390487458056274868683469 42146432796771103075756301)
          ·
            refine ⟨15804912298789163653408613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42146432796771103075756301 15804912298789163653408613)
            ·
              refine ⟨2963421056022968185014115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15804912298789163653408613 2963421056022968185014115)
              ·
                refine ⟨4445131584034452277521173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2963421056022968185014115 4445131584034452277521173)
                ·
                  refine ⟨208365543001614950508805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4445131584034452277521173 208365543001614950508805)
                  ·
                    rfl

theorem cell22_1826057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 4, 1, 6].length) (baseStart_1826057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1826057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1826057 prefixEnd_1826057 := by exact prefixLift 1826057
  have htrace : WordTrace (prefixWord ++ tailWord_1826057) baseStart_1826057 baseEnd_1826057 := by
    simpa [prefixWord, tailWord_1826057, baseEnd_1826057] using wordTrace_append hprefix tailTrace_1826057
  have hstable : (prefixWord ++ tailWord_1826057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1826057).length < 2 ^ (prefixWord ++ tailWord_1826057).sum := by decide
  have hdescent : baseEnd_1826057 < baseStart_1826057 := by decide
  rcases family_descends (prefixWord ++ tailWord_1826057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1826179 : List Nat := [1, 1, 1, 3, 5, 2, 1, 1, 2, 5]
def baseStart_1826179 : Nat := 118140960795 + 1826179 * 2 ^ 59
def prefixEnd_1826179 : Nat := 4983230072969 + 3 ^ 40 * 1826179 * 2
def baseEnd_1826179 : Nat := 625138392098077199976041

theorem tailTrace_1826179 : CollatzResearch.WordTrace tailWord_1826179 prefixEnd_1826179 625138392098077199976041 := by
  unfold tailWord_1826179
  simp only [CollatzResearch.WordTrace]
  refine ⟨66606220051072844387753591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44404146700715229591835727 66606220051072844387753591)
  ·
    refine ⟨99909330076609266581630387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66606220051072844387753591 99909330076609266581630387)
    ·
      refine ⟨149863995114913899872445581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99909330076609266581630387 149863995114913899872445581)
      ·
        refine ⟨56198998168092712452167093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149863995114913899872445581 56198998168092712452167093)
        ·
          refine ⟨5268656078258691792390665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56198998168092712452167093 5268656078258691792390665)
          ·
            refine ⟨3951492058694018844292999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5268656078258691792390665 3951492058694018844292999)
            ·
              refine ⟨5927238088041028266439499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3951492058694018844292999 5927238088041028266439499)
              ·
                refine ⟨8890857132061542399659249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5927238088041028266439499 8890857132061542399659249)
                ·
                  refine ⟨6668142849046156799744437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8890857132061542399659249 6668142849046156799744437)
                  ·
                    refine ⟨625138392098077199976041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6668142849046156799744437 625138392098077199976041)
                    ·
                      rfl

theorem cell22_1826179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 1, 2, 5].length) (baseStart_1826179 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1826179 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1826179 prefixEnd_1826179 := by exact prefixLift 1826179
  have htrace : WordTrace (prefixWord ++ tailWord_1826179) baseStart_1826179 baseEnd_1826179 := by
    simpa [prefixWord, tailWord_1826179, baseEnd_1826179] using wordTrace_append hprefix tailTrace_1826179
  have hstable : (prefixWord ++ tailWord_1826179).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1826179).length < 2 ^ (prefixWord ++ tailWord_1826179).sum := by decide
  have hdescent : baseEnd_1826179 < baseStart_1826179 := by decide
  rcases family_descends (prefixWord ++ tailWord_1826179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1826260 : List Nat := [2, 4, 1, 2, 3, 2, 1, 3, 4]
def baseStart_1826260 : Nat := 118140960795 + 1826260 * 2 ^ 59
def prefixEnd_1826260 : Nat := 4983230072969 + 3 ^ 40 * 1826260 * 2
def baseEnd_1826260 : Nat := 208388706684473329566931

theorem tailTrace_1826260 : CollatzResearch.WordTrace tailWord_1826260 prefixEnd_1826260 208388706684473329566931 := by
  unfold tailWord_1826260
  simp only [CollatzResearch.WordTrace]
  refine ⟨33304587181889697610726117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44406116242519596814301489 33304587181889697610726117)
  ·
    refine ⟨6244610096604318302011147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33304587181889697610726117 6244610096604318302011147)
    ·
      refine ⟨9366915144906477453016721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6244610096604318302011147 9366915144906477453016721)
      ·
        refine ⟨7025186358679858089762541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9366915144906477453016721 7025186358679858089762541)
        ·
          refine ⟨2634444884504946783660953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7025186358679858089762541 2634444884504946783660953)
          ·
            refine ⟨1975833663378710087745715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2634444884504946783660953 1975833663378710087745715)
            ·
              refine ⟨2963750495068065131618573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1975833663378710087745715 2963750495068065131618573)
              ·
                refine ⟨1111406435650524424356965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2963750495068065131618573 1111406435650524424356965)
                ·
                  refine ⟨208388706684473329566931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1111406435650524424356965 208388706684473329566931)
                  ·
                    rfl

theorem cell22_1826260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 1, 3, 4].length) (baseStart_1826260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1826260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1826260 prefixEnd_1826260 := by exact prefixLift 1826260
  have htrace : WordTrace (prefixWord ++ tailWord_1826260) baseStart_1826260 baseEnd_1826260 := by
    simpa [prefixWord, tailWord_1826260, baseEnd_1826260] using wordTrace_append hprefix tailTrace_1826260
  have hstable : (prefixWord ++ tailWord_1826260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1826260).length < 2 ^ (prefixWord ++ tailWord_1826260).sum := by decide
  have hdescent : baseEnd_1826260 < baseStart_1826260 := by decide
  rcases family_descends (prefixWord ++ tailWord_1826260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1826299 : List Nat := [1, 1, 1, 1, 1, 3, 2, 7, 5]
def baseStart_1826299 : Nat := 118140960795 + 1826299 * 2 ^ 59
def prefixEnd_1826299 : Nat := 4983230072969 + 3 ^ 40 * 1826299 * 2
def baseEnd_1826299 : Nat := 208393156850145628991891

theorem tailTrace_1826299 : CollatzResearch.WordTrace tailWord_1826299 prefixEnd_1826299 208393156850145628991891 := by
  unfold tailWord_1826299
  simp only [CollatzResearch.WordTrace]
  refine ⟨66610596810638104882121951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44407064540425403254747967 66610596810638104882121951)
  ·
    refine ⟨99915895215957157323182927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66610596810638104882121951 99915895215957157323182927)
    ·
      refine ⟨149873842823935735984774391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99915895215957157323182927 149873842823935735984774391)
      ·
        refine ⟨224810764235903603977161587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149873842823935735984774391 224810764235903603977161587)
        ·
          refine ⟨337216146353855405965742381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224810764235903603977161587 337216146353855405965742381)
          ·
            refine ⟨126456054882695777237153393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 337216146353855405965742381 126456054882695777237153393)
            ·
              refine ⟨94842041162021832927865045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126456054882695777237153393 94842041162021832927865045)
              ·
                refine ⟨2222860339734886709246837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 94842041162021832927865045 2222860339734886709246837)
                ·
                  refine ⟨208393156850145628991891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2222860339734886709246837 208393156850145628991891)
                  ·
                    rfl

theorem cell22_1826299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 7, 5].length) (baseStart_1826299 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1826299 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1826299 prefixEnd_1826299 := by exact prefixLift 1826299
  have htrace : WordTrace (prefixWord ++ tailWord_1826299) baseStart_1826299 baseEnd_1826299 := by
    simpa [prefixWord, tailWord_1826299, baseEnd_1826299] using wordTrace_append hprefix tailTrace_1826299
  have hstable : (prefixWord ++ tailWord_1826299).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1826299).length < 2 ^ (prefixWord ++ tailWord_1826299).sum := by decide
  have hdescent : baseEnd_1826299 < baseStart_1826299 := by decide
  rcases family_descends (prefixWord ++ tailWord_1826299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1826329 : List Nat := [1, 2, 1, 2, 1, 1, 2, 1, 7, 4]
def baseStart_1826329 : Nat := 118140960795 + 1826329 * 2 ^ 59
def prefixEnd_1826329 : Nat := 4983230072969 + 3 ^ 40 * 1826329 * 2
def baseEnd_1826329 : Nat := 625189740163526808725581

theorem tailTrace_1826329 : CollatzResearch.WordTrace tailWord_1826329 prefixEnd_1826329 625189740163526808725581 := by
  unfold tailWord_1826329
  simp only [CollatzResearch.WordTrace]
  refine ⟨66611691000529420005714041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44407794000352946670476027 66611691000529420005714041)
  ·
    refine ⟨49958768250397065004285531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66611691000529420005714041 49958768250397065004285531)
    ·
      refine ⟨74938152375595597506428297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49958768250397065004285531 74938152375595597506428297)
      ·
        refine ⟨56203614281696698129821223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74938152375595597506428297 56203614281696698129821223)
        ·
          refine ⟨84305421422545047194731835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56203614281696698129821223 84305421422545047194731835)
          ·
            refine ⟨126458132133817570792097753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84305421422545047194731835 126458132133817570792097753)
            ·
              refine ⟨94843599100363178094073315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126458132133817570792097753 94843599100363178094073315)
              ·
                refine ⟨142265398650544767141109973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94843599100363178094073315 142265398650544767141109973)
                ·
                  refine ⟨3334345280872142979869765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 142265398650544767141109973 3334345280872142979869765)
                  ·
                    refine ⟨625189740163526808725581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3334345280872142979869765 625189740163526808725581)
                    ·
                      rfl

theorem cell22_1826329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 7, 4].length) (baseStart_1826329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1826329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1826329 prefixEnd_1826329 := by exact prefixLift 1826329
  have htrace : WordTrace (prefixWord ++ tailWord_1826329) baseStart_1826329 baseEnd_1826329 := by
    simpa [prefixWord, tailWord_1826329, baseEnd_1826329] using wordTrace_append hprefix tailTrace_1826329
  have hstable : (prefixWord ++ tailWord_1826329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1826329).length < 2 ^ (prefixWord ++ tailWord_1826329).sum := by decide
  have hdescent : baseEnd_1826329 < baseStart_1826329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1826329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1826337 : List Nat := [1, 2, 3, 2, 2, 4, 2, 2, 1, 3]
def baseStart_1826337 : Nat := 118140960795 + 1826337 * 2 ^ 59
def prefixEnd_1826337 : Nat := 4983230072969 + 3 ^ 40 * 1826337 * 2
def baseEnd_1826337 : Nat := 625192478727017454525557

theorem tailTrace_1826337 : CollatzResearch.WordTrace tailWord_1826337 prefixEnd_1826337 625192478727017454525557 := by
  unfold tailWord_1826337
  simp only [CollatzResearch.WordTrace]
  refine ⟨66611982784500437372005265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44407988523000291581336843 66611982784500437372005265)
  ·
    refine ⟨49958987088375328029003949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66611982784500437372005265 49958987088375328029003949)
    ·
      refine ⟨18734620158140748010876481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49958987088375328029003949 18734620158140748010876481)
      ·
        refine ⟨14050965118605561008157361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18734620158140748010876481 14050965118605561008157361)
        ·
          refine ⟨10538223838954170756118021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14050965118605561008157361 10538223838954170756118021)
          ·
            refine ⟨1975916969803907016772129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10538223838954170756118021 1975916969803907016772129)
            ·
              refine ⟨1481937727352930262579097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1975916969803907016772129 1481937727352930262579097)
              ·
                refine ⟨1111453295514697696934323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1481937727352930262579097 1111453295514697696934323)
                ·
                  refine ⟨1667179943272046545401485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1111453295514697696934323 1667179943272046545401485)
                  ·
                    refine ⟨625192478727017454525557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1667179943272046545401485 625192478727017454525557)
                    ·
                      rfl

theorem cell22_1826337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 2, 2, 1, 3].length) (baseStart_1826337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1826337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1826337 prefixEnd_1826337 := by exact prefixLift 1826337
  have htrace : WordTrace (prefixWord ++ tailWord_1826337) baseStart_1826337 baseEnd_1826337 := by
    simpa [prefixWord, tailWord_1826337, baseEnd_1826337] using wordTrace_append hprefix tailTrace_1826337
  have hstable : (prefixWord ++ tailWord_1826337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1826337).length < 2 ^ (prefixWord ++ tailWord_1826337).sum := by decide
  have hdescent : baseEnd_1826337 < baseStart_1826337 := by decide
  rcases family_descends (prefixWord ++ tailWord_1826337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1826346 : List Nat := [3, 1, 4, 1, 1, 1, 1, 1, 5, 4]
def baseStart_1826346 : Nat := 118140960795 + 1826346 * 2 ^ 59
def prefixEnd_1826346 : Nat := 4983230072969 + 3 ^ 40 * 1826346 * 2
def baseEnd_1826346 : Nat := 625195559610944431050529

theorem tailTrace_1826346 : CollatzResearch.WordTrace tailWord_1826346 prefixEnd_1826346 625195559610944431050529 := by
  unfold tailWord_1826346
  simp only [CollatzResearch.WordTrace]
  refine ⟨16653077760366957977270723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44408207360978554606055261 16653077760366957977270723)
  ·
    refine ⟨24979616640550436965906085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16653077760366957977270723 24979616640550436965906085)
    ·
      refine ⟨4683678120103206931107391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24979616640550436965906085 4683678120103206931107391)
      ·
        refine ⟨7025517180154810396661087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4683678120103206931107391 7025517180154810396661087)
        ·
          refine ⟨10538275770232215594991631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7025517180154810396661087 10538275770232215594991631)
          ·
            refine ⟨15807413655348323392487447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10538275770232215594991631 15807413655348323392487447)
            ·
              refine ⟨23711120483022485088731171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15807413655348323392487447 23711120483022485088731171)
              ·
                refine ⟨35566680724533727633096757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23711120483022485088731171 35566680724533727633096757)
                ·
                  refine ⟨3334376317925036965602821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35566680724533727633096757 3334376317925036965602821)
                  ·
                    refine ⟨625195559610944431050529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3334376317925036965602821 625195559610944431050529)
                    ·
                      rfl

theorem cell22_1826346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_1826346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1826346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1826346 prefixEnd_1826346 := by exact prefixLift 1826346
  have htrace : WordTrace (prefixWord ++ tailWord_1826346) baseStart_1826346 baseEnd_1826346 := by
    simpa [prefixWord, tailWord_1826346, baseEnd_1826346] using wordTrace_append hprefix tailTrace_1826346
  have hstable : (prefixWord ++ tailWord_1826346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1826346).length < 2 ^ (prefixWord ++ tailWord_1826346).sum := by decide
  have hdescent : baseEnd_1826346 < baseStart_1826346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1826346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1826361 : List Nat := [1, 2, 1, 5, 1, 3, 1, 2, 6]
def baseStart_1826361 : Nat := 118140960795 + 1826361 * 2 ^ 59
def prefixEnd_1826361 : Nat := 4983230072969 + 3 ^ 40 * 1826361 * 2
def baseEnd_1826361 : Nat := 208400231472496463975161

theorem tailTrace_1826361 : CollatzResearch.WordTrace tailWord_1826361 prefixEnd_1826361 208400231472496463975161 := by
  unfold tailWord_1826361
  simp only [CollatzResearch.WordTrace]
  refine ⟨66612858136413489470878937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44408572090942326313919291 66612858136413489470878937)
  ·
    refine ⟨49959643602310117103159203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66612858136413489470878937 49959643602310117103159203)
    ·
      refine ⟨74939465403465175654738805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49959643602310117103159203 74939465403465175654738805)
      ·
        refine ⟨7025574881574860217631763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 74939465403465175654738805 7025574881574860217631763)
        ·
          refine ⟨10538362322362290326447645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7025574881574860217631763 10538362322362290326447645)
          ·
            refine ⟨3951885870885858872417867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10538362322362290326447645 3951885870885858872417867)
            ·
              refine ⟨5927828806328788308626801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3951885870885858872417867 5927828806328788308626801)
              ·
                refine ⟨4445871604746591231470101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5927828806328788308626801 4445871604746591231470101)
                ·
                  refine ⟨208400231472496463975161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4445871604746591231470101 208400231472496463975161)
                  ·
                    rfl

theorem cell22_1826361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 2, 6].length) (baseStart_1826361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1826361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1826361 prefixEnd_1826361 := by exact prefixLift 1826361
  have htrace : WordTrace (prefixWord ++ tailWord_1826361) baseStart_1826361 baseEnd_1826361 := by
    simpa [prefixWord, tailWord_1826361, baseEnd_1826361] using wordTrace_append hprefix tailTrace_1826361
  have hstable : (prefixWord ++ tailWord_1826361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1826361).length < 2 ^ (prefixWord ++ tailWord_1826361).sum := by decide
  have hdescent : baseEnd_1826361 < baseStart_1826361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1826361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1826378 : List Nat := [3, 1, 2, 1, 1, 3, 4, 3, 4]
def baseStart_1826378 : Nat := 118140960795 + 1826378 * 2 ^ 59
def prefixEnd_1826378 : Nat := 4983230072969 + 3 ^ 40 * 1826378 * 2
def baseEnd_1826378 : Nat := 208402171288302338083477

theorem tailTrace_1826378 : CollatzResearch.WordTrace tailWord_1826378 prefixEnd_1826378 208402171288302338083477 := by
  unfold tailWord_1826378
  simp only [CollatzResearch.WordTrace]
  refine ⟨16653369544337975343561947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44408985451567934249498525 16653369544337975343561947)
  ·
    refine ⟨24980054316506963015342921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16653369544337975343561947 24980054316506963015342921)
    ·
      refine ⟨18735040737380222261507191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24980054316506963015342921 18735040737380222261507191)
      ·
        refine ⟨28102561106070333392260787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18735040737380222261507191 28102561106070333392260787)
        ·
          refine ⟨42153841659105500088391181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28102561106070333392260787 42153841659105500088391181)
          ·
            refine ⟨15807690622164562533146693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42153841659105500088391181 15807690622164562533146693)
            ·
              refine ⟨2963941991655855474965005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15807690622164562533146693 2963941991655855474965005)
              ·
                refine ⟨1111478246870945803111877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2963941991655855474965005 1111478246870945803111877)
                ·
                  refine ⟨208402171288302338083477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1111478246870945803111877 208402171288302338083477)
                  ·
                    rfl

theorem cell22_1826378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 4, 3, 4].length) (baseStart_1826378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1826378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1826378 prefixEnd_1826378 := by exact prefixLift 1826378
  have htrace : WordTrace (prefixWord ++ tailWord_1826378) baseStart_1826378 baseEnd_1826378 := by
    simpa [prefixWord, tailWord_1826378, baseEnd_1826378] using wordTrace_append hprefix tailTrace_1826378
  have hstable : (prefixWord ++ tailWord_1826378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1826378).length < 2 ^ (prefixWord ++ tailWord_1826378).sum := by decide
  have hdescent : baseEnd_1826378 < baseStart_1826378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1826378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1826380 : List Nat := [2, 2, 1, 3, 1, 5, 2, 1, 1, 4]
def baseStart_1826380 : Nat := 118140960795 + 1826380 * 2 ^ 59
def prefixEnd_1826380 : Nat := 4983230072969 + 3 ^ 40 * 1826380 * 2
def baseEnd_1826380 : Nat := 625207198505779675700425

theorem tailTrace_1826380 : CollatzResearch.WordTrace tailWord_1826380 prefixEnd_1826380 625207198505779675700425 := by
  unfold tailWord_1826380
  simp only [CollatzResearch.WordTrace]
  refine ⟨33306775561672327857910297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44409034082229770477213729 33306775561672327857910297)
  ·
    refine ⟨24980081671254245893432723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33306775561672327857910297 24980081671254245893432723)
    ·
      refine ⟨37470122506881368840149085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24980081671254245893432723 37470122506881368840149085)
      ·
        refine ⟨14051295940080513315055907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37470122506881368840149085 14051295940080513315055907)
        ·
          refine ⟨21076943910120769972583861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14051295940080513315055907 21076943910120769972583861)
          ·
            refine ⟨1975963491573822184929737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21076943910120769972583861 1975963491573822184929737)
            ·
              refine ⟨1481972618680366638697303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1975963491573822184929737 1481972618680366638697303)
              ·
                refine ⟨2222958928020549958045955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1481972618680366638697303 2222958928020549958045955)
                ·
                  refine ⟨3334438392030824937068933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2222958928020549958045955 3334438392030824937068933)
                  ·
                    refine ⟨625207198505779675700425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3334438392030824937068933 625207198505779675700425)
                    ·
                      rfl

theorem cell22_1826380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 2, 1, 1, 4].length) (baseStart_1826380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1826380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1826380 prefixEnd_1826380 := by exact prefixLift 1826380
  have htrace : WordTrace (prefixWord ++ tailWord_1826380) baseStart_1826380 baseEnd_1826380 := by
    simpa [prefixWord, tailWord_1826380, baseEnd_1826380] using wordTrace_append hprefix tailTrace_1826380
  have hstable : (prefixWord ++ tailWord_1826380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1826380).length < 2 ^ (prefixWord ++ tailWord_1826380).sum := by decide
  have hdescent : baseEnd_1826380 < baseStart_1826380 := by decide
  rcases family_descends (prefixWord ++ tailWord_1826380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1826419 : List Nat := [1, 1, 1, 2, 2, 1, 1, 2, 3, 8]
def baseStart_1826419 : Nat := 118140960795 + 1826419 * 2 ^ 59
def prefixEnd_1826419 : Nat := 4983230072969 + 3 ^ 40 * 1826419 * 2
def baseEnd_1826419 : Nat := 625220549002796573975305

theorem tailTrace_1826419 : CollatzResearch.WordTrace tailWord_1826419 prefixEnd_1826419 625220549002796573975305 := by
  unfold tailWord_1826419
  simp only [CollatzResearch.WordTrace]
  refine ⟨66614973570203365376490311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44409982380135576917660207 66614973570203365376490311)
  ·
    refine ⟨99922460355305048064735467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66614973570203365376490311 99922460355305048064735467)
    ·
      refine ⟨149883690532957572097103201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99922460355305048064735467 149883690532957572097103201)
      ·
        refine ⟨112412767899718179072827401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149883690532957572097103201 112412767899718179072827401)
        ·
          refine ⟨84309575924788634304620551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112412767899718179072827401 84309575924788634304620551)
          ·
            refine ⟨126464363887182951456930827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84309575924788634304620551 126464363887182951456930827)
            ·
              refine ⟨189696545830774427185396241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126464363887182951456930827 189696545830774427185396241)
              ·
                refine ⟨142272409373080820389047181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 189696545830774427185396241 142272409373080820389047181)
                ·
                  refine ⟨53352153514905307645892693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 142272409373080820389047181 53352153514905307645892693)
                  ·
                    refine ⟨625220549002796573975305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 53352153514905307645892693 625220549002796573975305)
                    ·
                      rfl

theorem cell22_1826419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 8].length) (baseStart_1826419 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1826419 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1826419 prefixEnd_1826419 := by exact prefixLift 1826419
  have htrace : WordTrace (prefixWord ++ tailWord_1826419) baseStart_1826419 baseEnd_1826419 := by
    simpa [prefixWord, tailWord_1826419, baseEnd_1826419] using wordTrace_append hprefix tailTrace_1826419
  have hstable : (prefixWord ++ tailWord_1826419).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1826419).length < 2 ^ (prefixWord ++ tailWord_1826419).sum := by decide
  have hdescent : baseEnd_1826419 < baseStart_1826419 := by decide
  rcases family_descends (prefixWord ++ tailWord_1826419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1826440 : List Nat := [2, 1, 3, 5, 2, 1, 8]
def baseStart_1826440 : Nat := 118140960795 + 1826440 * 2 ^ 59
def prefixEnd_1826440 : Nat := 4983230072969 + 3 ^ 40 * 1826440 * 2
def baseEnd_1826440 : Nat := 23156582878961463674083

theorem tailTrace_1826440 : CollatzResearch.WordTrace tailWord_1826440 prefixEnd_1826440 23156582878961463674083 := by
  unfold tailWord_1826440
  simp only [CollatzResearch.WordTrace]
  refine ⟨33307869751563642981502387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44410493002084857308669849 33307869751563642981502387)
  ·
    refine ⟨49961804627345464472253581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33307869751563642981502387 49961804627345464472253581)
    ·
      refine ⟨18735676735254549177095093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49961804627345464472253581 18735676735254549177095093)
      ·
        refine ⟨1756469693930113985352665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18735676735254549177095093 1756469693930113985352665)
        ·
          refine ⟨1317352270447585489014499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1756469693930113985352665 1317352270447585489014499)
          ·
            refine ⟨1976028405671378233521749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1317352270447585489014499 1976028405671378233521749)
            ·
              refine ⟨23156582878961463674083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1976028405671378233521749 23156582878961463674083)
              ·
                rfl

theorem cell22_1826440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 8].length) (baseStart_1826440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1826440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1826440 prefixEnd_1826440 := by exact prefixLift 1826440
  have htrace : WordTrace (prefixWord ++ tailWord_1826440) baseStart_1826440 baseEnd_1826440 := by
    simpa [prefixWord, tailWord_1826440, baseEnd_1826440] using wordTrace_append hprefix tailTrace_1826440
  have hstable : (prefixWord ++ tailWord_1826440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1826440).length < 2 ^ (prefixWord ++ tailWord_1826440).sum := by decide
  have hdescent : baseEnd_1826440 < baseStart_1826440 := by decide
  rcases family_descends (prefixWord ++ tailWord_1826440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1826455 : List Nat := [1, 1, 3, 3, 2, 4, 1, 1, 3, 3]
def baseStart_1826455 : Nat := 118140960795 + 1826455 * 2 ^ 59
def prefixEnd_1826455 : Nat := 4983230072969 + 3 ^ 40 * 1826455 * 2
def baseEnd_1826455 : Nat := 625232872538504480075195

theorem tailTrace_1826455 : CollatzResearch.WordTrace tailWord_1826455 prefixEnd_1826455 625232872538504480075195 := by
  unfold tailWord_1826455
  simp only [CollatzResearch.WordTrace]
  refine ⟨66616286598072943524800819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44410857732048629016533879 66616286598072943524800819)
  ·
    refine ⟨99924429897109415287201229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66616286598072943524800819 99924429897109415287201229)
    ·
      refine ⟨37471661211416030732700461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99924429897109415287201229 37471661211416030732700461)
      ·
        refine ⟨14051872954281011524762673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37471661211416030732700461 14051872954281011524762673)
        ·
          refine ⟨10538904715710758643572005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14051872954281011524762673 10538904715710758643572005)
          ·
            refine ⟨1976044634195767245669751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10538904715710758643572005 1976044634195767245669751)
            ·
              refine ⟨2964066951293650868504627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1976044634195767245669751 2964066951293650868504627)
              ·
                refine ⟨4446100426940476302756941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2964066951293650868504627 4446100426940476302756941)
                ·
                  refine ⟨1667287660102678613533853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4446100426940476302756941 1667287660102678613533853)
                  ·
                    refine ⟨625232872538504480075195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1667287660102678613533853 625232872538504480075195)
                    ·
                      rfl

theorem cell22_1826455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 1, 1, 3, 3].length) (baseStart_1826455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1826455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1826455 prefixEnd_1826455 := by exact prefixLift 1826455
  have htrace : WordTrace (prefixWord ++ tailWord_1826455) baseStart_1826455 baseEnd_1826455 := by
    simpa [prefixWord, tailWord_1826455, baseEnd_1826455] using wordTrace_append hprefix tailTrace_1826455
  have hstable : (prefixWord ++ tailWord_1826455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1826455).length < 2 ^ (prefixWord ++ tailWord_1826455).sum := by decide
  have hdescent : baseEnd_1826455 < baseStart_1826455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1826455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1826468 : List Nat := [2, 3, 1, 2, 2, 3, 1, 3, 5]
def baseStart_1826468 : Nat := 118140960795 + 1826468 * 2 ^ 59
def prefixEnd_1826468 : Nat := 4983230072969 + 3 ^ 40 * 1826468 * 2
def baseEnd_1826468 : Nat := 208412440901392259833385

theorem tailTrace_1826468 : CollatzResearch.WordTrace tailWord_1826468 prefixEnd_1826468 208412440901392259833385 := by
  unfold tailWord_1826468
  simp only [CollatzResearch.WordTrace]
  refine ⟨33308380373512923372512029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44411173831350564496682705 33308380373512923372512029)
  ·
    refine ⟨12490642640067346264692011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33308380373512923372512029 12490642640067346264692011)
    ·
      refine ⟨18735963960101019397038017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12490642640067346264692011 18735963960101019397038017)
      ·
        refine ⟨14051972970075764547778513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18735963960101019397038017 14051972970075764547778513)
        ·
          refine ⟨10538979727556823410833885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14051972970075764547778513 10538979727556823410833885)
          ·
            refine ⟨3952117397833808779062707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10538979727556823410833885 3952117397833808779062707)
            ·
              refine ⟨5928176096750713168594061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3952117397833808779062707 5928176096750713168594061)
              ·
                refine ⟨2223066036281517438222773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5928176096750713168594061 2223066036281517438222773)
                ·
                  refine ⟨208412440901392259833385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2223066036281517438222773 208412440901392259833385)
                  ·
                    rfl

theorem cell22_1826468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 3, 5].length) (baseStart_1826468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1826468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1826468 prefixEnd_1826468 := by exact prefixLift 1826468
  have htrace : WordTrace (prefixWord ++ tailWord_1826468) baseStart_1826468 baseEnd_1826468 := by
    simpa [prefixWord, tailWord_1826468, baseEnd_1826468] using wordTrace_append hprefix tailTrace_1826468
  have hstable : (prefixWord ++ tailWord_1826468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1826468).length < 2 ^ (prefixWord ++ tailWord_1826468).sum := by decide
  have hdescent : baseEnd_1826468 < baseStart_1826468 := by decide
  rcases family_descends (prefixWord ++ tailWord_1826468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1826502 : List Nat := [6, 1, 2, 1, 1, 1, 1, 4, 5]
def baseStart_1826502 : Nat := 118140960795 + 1826502 * 2 ^ 59
def prefixEnd_1826502 : Nat := 4983230072969 + 3 ^ 40 * 1826502 * 2
def baseEnd_1826502 : Nat := 208416320533004008050017

theorem tailTrace_1826502 : CollatzResearch.WordTrace tailWord_1826502 prefixEnd_1826502 208416320533004008050017 := by
  unfold tailWord_1826502
  simp only [CollatzResearch.WordTrace]
  refine ⟨2081812525903208454742555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 44412000552601780367841173 2081812525903208454742555)
  ·
    refine ⟨3122718788854812682113833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2081812525903208454742555 3122718788854812682113833)
    ·
      refine ⟨2342039091641109511585375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3122718788854812682113833 2342039091641109511585375)
      ·
        refine ⟨3513058637461664267378063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2342039091641109511585375 3513058637461664267378063)
        ·
          refine ⟨5269587956192496401067095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3513058637461664267378063 5269587956192496401067095)
          ·
            refine ⟨7904381934288744601600643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5269587956192496401067095 7904381934288744601600643)
            ·
              refine ⟨11856572901433116902400965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7904381934288744601600643 11856572901433116902400965)
              ·
                refine ⟨2223107419018709419200181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11856572901433116902400965 2223107419018709419200181)
                ·
                  refine ⟨208416320533004008050017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2223107419018709419200181 208416320533004008050017)
                  ·
                    rfl

theorem cell22_1826502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 4, 5].length) (baseStart_1826502 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1826502 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1826502 prefixEnd_1826502 := by exact prefixLift 1826502
  have htrace : WordTrace (prefixWord ++ tailWord_1826502) baseStart_1826502 baseEnd_1826502 := by
    simpa [prefixWord, tailWord_1826502, baseEnd_1826502] using wordTrace_append hprefix tailTrace_1826502
  have hstable : (prefixWord ++ tailWord_1826502).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1826502).length < 2 ^ (prefixWord ++ tailWord_1826502).sum := by decide
  have hdescent : baseEnd_1826502 < baseStart_1826502 := by decide
  rcases family_descends (prefixWord ++ tailWord_1826502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1826506 : List Nat := [3, 1, 2, 1, 6, 1, 2, 2, 1, 3]
def baseStart_1826506 : Nat := 118140960795 + 1826506 * 2 ^ 59
def prefixEnd_1826506 : Nat := 4983230072969 + 3 ^ 40 * 1826506 * 2
def baseEnd_1826506 : Nat := 625250330880757347050039

theorem tailTrace_1826506 : CollatzResearch.WordTrace tailWord_1826506 prefixEnd_1826506 625250330880757347050039 := by
  unfold tailWord_1826506
  simp only [CollatzResearch.WordTrace]
  refine ⟨16654536680222044808726843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44412097813925452823271581 16654536680222044808726843)
  ·
    refine ⟨24981805020333067213090265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16654536680222044808726843 24981805020333067213090265)
    ·
      refine ⟨18736353765249800409817699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24981805020333067213090265 18736353765249800409817699)
      ·
        refine ⟨28104530647874700614726549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18736353765249800409817699 28104530647874700614726549)
        ·
          refine ⟨1317399874119126591315307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 28104530647874700614726549 1317399874119126591315307)
          ·
            refine ⟨1976099811178689886972961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1317399874119126591315307 1976099811178689886972961)
            ·
              refine ⟨1482074858384017415229721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1976099811178689886972961 1482074858384017415229721)
              ·
                refine ⟨1111556143788013061422291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1482074858384017415229721 1111556143788013061422291)
                ·
                  refine ⟨1667334215682019592133437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1111556143788013061422291 1667334215682019592133437)
                  ·
                    refine ⟨625250330880757347050039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1667334215682019592133437 625250330880757347050039)
                    ·
                      rfl

theorem cell22_1826506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 2, 2, 1, 3].length) (baseStart_1826506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1826506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1826506 prefixEnd_1826506 := by exact prefixLift 1826506
  have htrace : WordTrace (prefixWord ++ tailWord_1826506) baseStart_1826506 baseEnd_1826506 := by
    simpa [prefixWord, tailWord_1826506, baseEnd_1826506] using wordTrace_append hprefix tailTrace_1826506
  have hstable : (prefixWord ++ tailWord_1826506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1826506).length < 2 ^ (prefixWord ++ tailWord_1826506).sum := by decide
  have hdescent : baseEnd_1826506 < baseStart_1826506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1826506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1826571 : List Nat := [1, 1, 1, 1, 5, 1, 2, 1, 1, 8]
def baseStart_1826571 : Nat := 118140960795 + 1826571 * 2 ^ 59
def prefixEnd_1826571 : Nat := 4983230072969 + 3 ^ 40 * 1826571 * 2
def baseEnd_1826571 : Nat := 625272581709118844174839

theorem tailTrace_1826571 : CollatzResearch.WordTrace tailWord_1826571 prefixEnd_1826571 625272581709118844174839 := by
  unfold tailWord_1826571
  simp only [CollatzResearch.WordTrace]
  refine ⟨66620517465652695336023567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44413678310435130224015711 66620517465652695336023567)
  ·
    refine ⟨99930776198479043004035351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66620517465652695336023567 99930776198479043004035351)
    ·
      refine ⟨149896164297718564506053027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99930776198479043004035351 149896164297718564506053027)
      ·
        refine ⟨224844246446577846759079541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149896164297718564506053027 224844246446577846759079541)
        ·
          refine ⟨21079148104366673133663707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 224844246446577846759079541 21079148104366673133663707)
          ·
            refine ⟨31618722156550009700495561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21079148104366673133663707 31618722156550009700495561)
            ·
              refine ⟨23714041617412507275371671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31618722156550009700495561 23714041617412507275371671)
              ·
                refine ⟨35571062426118760913057507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23714041617412507275371671 35571062426118760913057507)
                ·
                  refine ⟨53356593639178141369586261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35571062426118760913057507 53356593639178141369586261)
                  ·
                    refine ⟨625272581709118844174839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 53356593639178141369586261 625272581709118844174839)
                    ·
                      rfl

theorem cell22_1826571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 8].length) (baseStart_1826571 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1826571 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1826571 prefixEnd_1826571 := by exact prefixLift 1826571
  have htrace : WordTrace (prefixWord ++ tailWord_1826571) baseStart_1826571 baseEnd_1826571 := by
    simpa [prefixWord, tailWord_1826571, baseEnd_1826571] using wordTrace_append hprefix tailTrace_1826571
  have hstable : (prefixWord ++ tailWord_1826571).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1826571).length < 2 ^ (prefixWord ++ tailWord_1826571).sum := by decide
  have hdescent : baseEnd_1826571 < baseStart_1826571 := by decide
  rcases family_descends (prefixWord ++ tailWord_1826571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1826633 : List Nat := [1, 2, 1, 1, 2, 4, 2, 2, 3, 4]
def baseStart_1826633 : Nat := 118140960795 + 1826633 * 2 ^ 59
def prefixEnd_1826633 : Nat := 4983230072969 + 3 ^ 40 * 1826633 * 2
def baseEnd_1826633 : Nat := 625293805576171349124649

theorem tailTrace_1826633 : CollatzResearch.WordTrace tailWord_1826633 prefixEnd_1826633 625293805576171349124649 := by
  unfold tailWord_1826633
  simp only [CollatzResearch.WordTrace]
  refine ⟨66622778791428079924780553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44415185860952053283187035 66622778791428079924780553)
  ·
    refine ⟨49967084093571059943585415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66622778791428079924780553 49967084093571059943585415)
    ·
      refine ⟨74950626140356589915378123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49967084093571059943585415 74950626140356589915378123)
      ·
        refine ⟨112425939210534884873067185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74950626140356589915378123 112425939210534884873067185)
        ·
          refine ⟨84319454407901163654800389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112425939210534884873067185 84319454407901163654800389)
          ·
            refine ⟨15809897701481468185275073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84319454407901163654800389 15809897701481468185275073)
            ·
              refine ⟨11857423276111101138956305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15809897701481468185275073 11857423276111101138956305)
              ·
                refine ⟨8893067457083325854217229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11857423276111101138956305 8893067457083325854217229)
                ·
                  refine ⟨3334900296406247195331461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8893067457083325854217229 3334900296406247195331461)
                  ·
                    refine ⟨625293805576171349124649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3334900296406247195331461 625293805576171349124649)
                    ·
                      rfl

theorem cell22_1826633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 2, 3, 4].length) (baseStart_1826633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1826633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1826633 prefixEnd_1826633 := by exact prefixLift 1826633
  have htrace : WordTrace (prefixWord ++ tailWord_1826633) baseStart_1826633 baseEnd_1826633 := by
    simpa [prefixWord, tailWord_1826633, baseEnd_1826633] using wordTrace_append hprefix tailTrace_1826633
  have hstable : (prefixWord ++ tailWord_1826633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1826633).length < 2 ^ (prefixWord ++ tailWord_1826633).sum := by decide
  have hdescent : baseEnd_1826633 < baseStart_1826633 := by decide
  rcases family_descends (prefixWord ++ tailWord_1826633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1826637 : List Nat := [1, 6, 1, 2, 1, 2, 1, 3, 5]
def baseStart_1826637 : Nat := 118140960795 + 1826637 * 2 ^ 59
def prefixEnd_1826637 : Nat := 4983230072969 + 3 ^ 40 * 1826637 * 2
def baseEnd_1826637 : Nat := 208431724952638890674879

theorem tailTrace_1826637 : CollatzResearch.WordTrace tailWord_1826637 prefixEnd_1826637 208431724952638890674879 := by
  unfold tailWord_1826637
  simp only [CollatzResearch.WordTrace]
  refine ⟨66622924683413588607926165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44415283122275725738617443 66622924683413588607926165)
  ·
    refine ⟨3122949594535011965996539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 66622924683413588607926165 3122949594535011965996539)
    ·
      refine ⟨4684424391802517948994809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3122949594535011965996539 4684424391802517948994809)
      ·
        refine ⟨3513318293851888461746107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4684424391802517948994809 3513318293851888461746107)
        ·
          refine ⟨5269977440777832692619161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3513318293851888461746107 5269977440777832692619161)
          ·
            refine ⟨3952483080583374519464371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5269977440777832692619161 3952483080583374519464371)
            ·
              refine ⟨5928724620875061779196557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3952483080583374519464371 5928724620875061779196557)
              ·
                refine ⟨2223271732828148167198709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5928724620875061779196557 2223271732828148167198709)
                ·
                  refine ⟨208431724952638890674879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2223271732828148167198709 208431724952638890674879)
                  ·
                    rfl

theorem cell22_1826637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 3, 5].length) (baseStart_1826637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1826637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1826637 prefixEnd_1826637 := by exact prefixLift 1826637
  have htrace : WordTrace (prefixWord ++ tailWord_1826637) baseStart_1826637 baseEnd_1826637 := by
    simpa [prefixWord, tailWord_1826637, baseEnd_1826637] using wordTrace_append hprefix tailTrace_1826637
  have hstable : (prefixWord ++ tailWord_1826637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1826637).length < 2 ^ (prefixWord ++ tailWord_1826637).sum := by decide
  have hdescent : baseEnd_1826637 < baseStart_1826637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1826637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1826682 : List Nat := [3, 1, 1, 1, 1, 1, 8, 2, 4]
def baseStart_1826682 : Nat := 118140960795 + 1826682 * 2 ^ 59
def prefixEnd_1826682 : Nat := 4983230072969 + 3 ^ 40 * 1826682 * 2
def baseEnd_1826682 : Nat := 208436859759183851549833

theorem tailTrace_1826682 : CollatzResearch.WordTrace tailWord_1826682 prefixEnd_1826682 208436859759183851549833 := by
  unfold tailWord_1826682
  simp only [CollatzResearch.WordTrace]
  refine ⟨16656141492062640323328575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44416377312167040862209533 16656141492062640323328575)
  ·
    refine ⟨24984212238093960484992863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16656141492062640323328575 24984212238093960484992863)
    ·
      refine ⟨37476318357140940727489295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24984212238093960484992863 37476318357140940727489295)
      ·
        refine ⟨56214477535711411091233943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37476318357140940727489295 56214477535711411091233943)
        ·
          refine ⟨84321716303567116636850915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56214477535711411091233943 84321716303567116636850915)
          ·
            refine ⟨126482574455350674955276373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84321716303567116636850915 126482574455350674955276373)
            ·
              refine ⟨1482217669398640722132145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 126482574455350674955276373 1482217669398640722132145)
              ·
                refine ⟨1111663252048980541599109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1482217669398640722132145 1111663252048980541599109)
                ·
                  refine ⟨208436859759183851549833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1111663252048980541599109 208436859759183851549833)
                  ·
                    rfl

theorem cell22_1826682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 8, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 8, 2, 4].length) (baseStart_1826682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1826682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1826682 prefixEnd_1826682 := by exact prefixLift 1826682
  have htrace : WordTrace (prefixWord ++ tailWord_1826682) baseStart_1826682 baseEnd_1826682 := by
    simpa [prefixWord, tailWord_1826682, baseEnd_1826682] using wordTrace_append hprefix tailTrace_1826682
  have hstable : (prefixWord ++ tailWord_1826682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1826682).length < 2 ^ (prefixWord ++ tailWord_1826682).sum := by decide
  have hdescent : baseEnd_1826682 < baseStart_1826682 := by decide
  rcases family_descends (prefixWord ++ tailWord_1826682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1826712 : List Nat := [2, 1, 2, 6, 1, 1, 1, 1, 1, 6]
def baseStart_1826712 : Nat := 118140960795 + 1826712 * 2 ^ 59
def prefixEnd_1826712 : Nat := 4983230072969 + 3 ^ 40 * 1826712 * 2
def baseEnd_1826712 : Nat := 625320848890641476399407

theorem tailTrace_1826712 : CollatzResearch.WordTrace tailWord_1826712 prefixEnd_1826712 625320848890641476399407 := by
  unfold tailWord_1826712
  simp only [CollatzResearch.WordTrace]
  refine ⟨33312830079070938208453195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44417106772094584277937593 33312830079070938208453195)
  ·
    refine ⟨49969245118606407312679793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33312830079070938208453195 49969245118606407312679793)
    ·
      refine ⟨37476933838954805484509845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49969245118606407312679793 37476933838954805484509845)
      ·
        refine ⟨1756731273701006507086399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 37476933838954805484509845 1756731273701006507086399)
        ·
          refine ⟨2635096910551509760629599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1756731273701006507086399 2635096910551509760629599)
          ·
            refine ⟨3952645365827264640944399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2635096910551509760629599 3952645365827264640944399)
            ·
              refine ⟨5928968048740896961416599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3952645365827264640944399 5928968048740896961416599)
              ·
                refine ⟨8893452073111345442124899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5928968048740896961416599 8893452073111345442124899)
                ·
                  refine ⟨13340178109667018163187349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8893452073111345442124899 13340178109667018163187349)
                  ·
                    refine ⟨625320848890641476399407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13340178109667018163187349 625320848890641476399407)
                    ·
                      rfl

theorem cell22_1826712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 1, 1, 6].length) (baseStart_1826712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1826712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1826712 prefixEnd_1826712 := by exact prefixLift 1826712
  have htrace : WordTrace (prefixWord ++ tailWord_1826712) baseStart_1826712 baseEnd_1826712 := by
    simpa [prefixWord, tailWord_1826712, baseEnd_1826712] using wordTrace_append hprefix tailTrace_1826712
  have hstable : (prefixWord ++ tailWord_1826712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1826712).length < 2 ^ (prefixWord ++ tailWord_1826712).sum := by decide
  have hdescent : baseEnd_1826712 < baseStart_1826712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1826712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1826718 : List Nat := [4, 3, 1, 3, 1, 2, 2, 1, 1, 4]
def baseStart_1826718 : Nat := 118140960795 + 1826718 * 2 ^ 59
def prefixEnd_1826718 : Nat := 4983230072969 + 3 ^ 40 * 1826718 * 2
def baseEnd_1826718 : Nat := 625322902813259460749389

theorem tailTrace_1826718 : CollatzResearch.WordTrace tailWord_1826718 prefixEnd_1826718 625322902813259460749389 := by
  unfold tailWord_1826718
  simp only [CollatzResearch.WordTrace]
  refine ⟨8328234874515017430203101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44417252664080092961083205 8328234874515017430203101)
  ·
    refine ⟨3123088077943131536326163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8328234874515017430203101 3123088077943131536326163)
    ·
      refine ⟨4684632116914697304489245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3123088077943131536326163 4684632116914697304489245)
      ·
        refine ⟨1756737043843011489183467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4684632116914697304489245 1756737043843011489183467)
        ·
          refine ⟨2635105565764517233775201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1756737043843011489183467 2635105565764517233775201)
          ·
            refine ⟨1976329174323387925331401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2635105565764517233775201 1976329174323387925331401)
            ·
              refine ⟨1482246880742540943998551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1976329174323387925331401 1482246880742540943998551)
              ·
                refine ⟨2223370321113811415997827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1482246880742540943998551 2223370321113811415997827)
                ·
                  refine ⟨3335055481670717123996741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2223370321113811415997827 3335055481670717123996741)
                  ·
                    refine ⟨625322902813259460749389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3335055481670717123996741 625322902813259460749389)
                    ·
                      rfl

theorem cell22_1826718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 2, 1, 1, 4].length) (baseStart_1826718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1826718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1826718 prefixEnd_1826718 := by exact prefixLift 1826718
  have htrace : WordTrace (prefixWord ++ tailWord_1826718) baseStart_1826718 baseEnd_1826718 := by
    simpa [prefixWord, tailWord_1826718, baseEnd_1826718] using wordTrace_append hprefix tailTrace_1826718
  have hstable : (prefixWord ++ tailWord_1826718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1826718).length < 2 ^ (prefixWord ++ tailWord_1826718).sum := by decide
  have hdescent : baseEnd_1826718 < baseStart_1826718 := by decide
  rcases family_descends (prefixWord ++ tailWord_1826718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1826800 : List Nat := [2, 1, 1, 1, 3, 2, 5, 1, 6]
def baseStart_1826800 : Nat := 118140960795 + 1826800 * 2 ^ 59
def prefixEnd_1826800 : Nat := 4983230072969 + 3 ^ 40 * 1826800 * 2
def baseEnd_1826800 : Nat := 208450324363012860066379

theorem tailTrace_1826800 : CollatzResearch.WordTrace tailWord_1826800 prefixEnd_1826800 208450324363012860066379 := by
  unfold tailWord_1826800
  simp only [CollatzResearch.WordTrace]
  refine ⟨33314434890911533723054927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44419246521215378297406569 33314434890911533723054927)
  ·
    refine ⟨49971652336367300584582391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33314434890911533723054927 49971652336367300584582391)
    ·
      refine ⟨74957478504550950876873587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49971652336367300584582391 74957478504550950876873587)
      ·
        refine ⟨112436217756826426315310381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74957478504550950876873587 112436217756826426315310381)
        ·
          refine ⟨42163581658809909868241393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112436217756826426315310381 42163581658809909868241393)
          ·
            refine ⟨31622686244107432401181045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42163581658809909868241393 31622686244107432401181045)
            ·
              refine ⟨2964626835385071787610723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31622686244107432401181045 2964626835385071787610723)
              ·
                refine ⟨4446940253077607681416085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2964626835385071787610723 4446940253077607681416085)
                ·
                  refine ⟨208450324363012860066379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4446940253077607681416085 208450324363012860066379)
                  ·
                    rfl

theorem cell22_1826800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 5, 1, 6].length) (baseStart_1826800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1826800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1826800 prefixEnd_1826800 := by exact prefixLift 1826800
  have htrace : WordTrace (prefixWord ++ tailWord_1826800) baseStart_1826800 baseEnd_1826800 := by
    simpa [prefixWord, tailWord_1826800, baseEnd_1826800] using wordTrace_append hprefix tailTrace_1826800
  have hstable : (prefixWord ++ tailWord_1826800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1826800).length < 2 ^ (prefixWord ++ tailWord_1826800).sum := by decide
  have hdescent : baseEnd_1826800 < baseStart_1826800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1826800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1826806 : List Nat := [5, 1, 1, 1, 4, 2, 2, 1, 5]
def baseStart_1826806 : Nat := 118140960795 + 1826806 * 2 ^ 59
def prefixEnd_1826806 : Nat := 4983230072969 + 3 ^ 40 * 1826806 * 2
def baseEnd_1826806 : Nat := 208451009003885521516373

theorem tailTrace_1826806 : CollatzResearch.WordTrace tailWord_1826806 prefixEnd_1826806 208451009003885521516373 := by
  unfold tailWord_1826806
  simp only [CollatzResearch.WordTrace]
  refine ⟨4164318038737583154426767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44419392413200886980552181 4164318038737583154426767)
  ·
    refine ⟨6246477058106374731640151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4164318038737583154426767 6246477058106374731640151)
    ·
      refine ⟨9369715587159562097460227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6246477058106374731640151 9369715587159562097460227)
      ·
        refine ⟨14054573380739343146190341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9369715587159562097460227 14054573380739343146190341)
        ·
          refine ⟨2635232508888626839910689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14054573380739343146190341 2635232508888626839910689)
          ·
            refine ⟨1976424381666470129933017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2635232508888626839910689 1976424381666470129933017)
            ·
              refine ⟨1482318286249852597449763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1976424381666470129933017 1482318286249852597449763)
              ·
                refine ⟨2223477429374778896174645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1482318286249852597449763 2223477429374778896174645)
                ·
                  refine ⟨208451009003885521516373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2223477429374778896174645 208451009003885521516373)
                  ·
                    rfl

theorem cell22_1826806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 2, 1, 5].length) (baseStart_1826806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1826806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1826806 prefixEnd_1826806 := by exact prefixLift 1826806
  have htrace : WordTrace (prefixWord ++ tailWord_1826806) baseStart_1826806 baseEnd_1826806 := by
    simpa [prefixWord, tailWord_1826806, baseEnd_1826806] using wordTrace_append hprefix tailTrace_1826806
  have hstable : (prefixWord ++ tailWord_1826806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1826806).length < 2 ^ (prefixWord ++ tailWord_1826806).sum := by decide
  have hdescent : baseEnd_1826806 < baseStart_1826806 := by decide
  rcases family_descends (prefixWord ++ tailWord_1826806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1826845 : List Nat := [1, 4, 2, 2, 2, 11]
def baseStart_1826845 : Nat := 118140960795 + 1826845 * 2 ^ 59
def prefixEnd_1826845 : Nat := 4983230072969 + 3 ^ 40 * 1826845 * 2
def baseEnd_1826845 : Nat := 7720572561835474849679

theorem tailTrace_1826845 : CollatzResearch.WordTrace tailWord_1826845 prefixEnd_1826845 7720572561835474849679 := by
  unfold tailWord_1826845
  simp only [CollatzResearch.WordTrace]
  refine ⟨66630511066660040131497989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44420340711106693420998659 66630511066660040131497989)
  ·
    refine ⟨12493220824998757524655873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66630511066660040131497989 12493220824998757524655873)
    ·
      refine ⟨9369915618749068143491905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12493220824998757524655873 9369915618749068143491905)
      ·
        refine ⟨7027436714061801107618929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9369915618749068143491905 7027436714061801107618929)
        ·
          refine ⟨5270577535546350830714197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7027436714061801107618929 5270577535546350830714197)
          ·
            refine ⟨7720572561835474849679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 5270577535546350830714197 7720572561835474849679)
            ·
              rfl

theorem cell22_1826845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 11].length) (baseStart_1826845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1826845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1826845 prefixEnd_1826845 := by exact prefixLift 1826845
  have htrace : WordTrace (prefixWord ++ tailWord_1826845) baseStart_1826845 baseEnd_1826845 := by
    simpa [prefixWord, tailWord_1826845, baseEnd_1826845] using wordTrace_append hprefix tailTrace_1826845
  have hstable : (prefixWord ++ tailWord_1826845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1826845).length < 2 ^ (prefixWord ++ tailWord_1826845).sum := by decide
  have hdescent : baseEnd_1826845 < baseStart_1826845 := by decide
  rcases family_descends (prefixWord ++ tailWord_1826845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1826862 : List Nat := [4, 1, 3, 1, 1, 2, 3, 7]
def baseStart_1826862 : Nat := 118140960795 + 1826862 * 2 ^ 59
def prefixEnd_1826862 : Nat := 4983230072969 + 3 ^ 40 * 1826862 * 2
def baseEnd_1826862 : Nat := 69485799661787898349883

theorem tailTrace_1826862 : CollatzResearch.WordTrace tailWord_1826862 prefixEnd_1826862 69485799661787898349883 := by
  unfold tailWord_1826862
  simp only [CollatzResearch.WordTrace]
  refine ⟨8328891388449806504358355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44420754071732301356577893 8328891388449806504358355)
  ·
    refine ⟨12493337082674709756537533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8328891388449806504358355 12493337082674709756537533)
    ·
      refine ⟨4685001406003016158701575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12493337082674709756537533 4685001406003016158701575)
      ·
        refine ⟨7027502109004524238052363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4685001406003016158701575 7027502109004524238052363)
        ·
          refine ⟨10541253163506786357078545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7027502109004524238052363 10541253163506786357078545)
          ·
            refine ⟨7905939872630089767808909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10541253163506786357078545 7905939872630089767808909)
            ·
              refine ⟨2964727452236283662928341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7905939872630089767808909 2964727452236283662928341)
              ·
                refine ⟨69485799661787898349883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2964727452236283662928341 69485799661787898349883)
                ·
                  rfl

theorem cell22_1826862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 3, 7].length) (baseStart_1826862 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1826862 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1826862 prefixEnd_1826862 := by exact prefixLift 1826862
  have htrace : WordTrace (prefixWord ++ tailWord_1826862) baseStart_1826862 baseEnd_1826862 := by
    simpa [prefixWord, tailWord_1826862, baseEnd_1826862] using wordTrace_append hprefix tailTrace_1826862
  have hstable : (prefixWord ++ tailWord_1826862).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1826862).length < 2 ^ (prefixWord ++ tailWord_1826862).sum := by decide
  have hdescent : baseEnd_1826862 < baseStart_1826862 := by decide
  rcases family_descends (prefixWord ++ tailWord_1826862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1826890 : List Nat := [3, 1, 2, 1, 1, 2, 1, 4, 7]
def baseStart_1826890 : Nat := 118140960795 + 1826890 * 2 ^ 59
def prefixEnd_1826890 : Nat := 4983230072969 + 3 ^ 40 * 1826890 * 2
def baseEnd_1826890 : Nat := 208460593976102781816287

theorem tailTrace_1826890 : CollatzResearch.WordTrace tailWord_1826890 prefixEnd_1826890 208460593976102781816287 := by
  unfold tailWord_1826890
  simp only [CollatzResearch.WordTrace]
  refine ⟨16658038087874253204221531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44421434900998008544590749 16658038087874253204221531)
  ·
    refine ⟨24987057131811379806332297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16658038087874253204221531 24987057131811379806332297)
    ·
      refine ⟨18740292848858534854749223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24987057131811379806332297 18740292848858534854749223)
      ·
        refine ⟨28110439273287802282123835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18740292848858534854749223 28110439273287802282123835)
        ·
          refine ⟨42165658909931703423185753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28110439273287802282123835 42165658909931703423185753)
          ·
            refine ⟨31624244182448777567389315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42165658909931703423185753 31624244182448777567389315)
            ·
              refine ⟨47436366273673166351083973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31624244182448777567389315 47436366273673166351083973)
              ·
                refine ⟨8894318676313718690828245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47436366273673166351083973 8894318676313718690828245)
                ·
                  refine ⟨208460593976102781816287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8894318676313718690828245 208460593976102781816287)
                  ·
                    rfl

theorem cell22_1826890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 4, 7].length) (baseStart_1826890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1826890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1826890 prefixEnd_1826890 := by exact prefixLift 1826890
  have htrace : WordTrace (prefixWord ++ tailWord_1826890) baseStart_1826890 baseEnd_1826890 := by
    simpa [prefixWord, tailWord_1826890, baseEnd_1826890] using wordTrace_append hprefix tailTrace_1826890
  have hstable : (prefixWord ++ tailWord_1826890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1826890).length < 2 ^ (prefixWord ++ tailWord_1826890).sum := by decide
  have hdescent : baseEnd_1826890 < baseStart_1826890 := by decide
  rcases family_descends (prefixWord ++ tailWord_1826890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1826905 : List Nat := [1, 2, 1, 2, 2, 1, 3, 1, 4, 5]
def baseStart_1826905 : Nat := 118140960795 + 1826905 * 2 ^ 59
def prefixEnd_1826905 : Nat := 4983230072969 + 3 ^ 40 * 1826905 * 2
def baseEnd_1826905 : Nat := 625386916734853306323815

theorem tailTrace_1826905 : CollatzResearch.WordTrace tailWord_1826905 prefixEnd_1826905 625386916734853306323815 := by
  unfold tailWord_1826905
  simp only [CollatzResearch.WordTrace]
  refine ⟨66632699446442670378682169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44421799630961780252454779 66632699446442670378682169)
  ·
    refine ⟨49974524584832002784011627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66632699446442670378682169 49974524584832002784011627)
    ·
      refine ⟨74961786877248004176017441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49974524584832002784011627 74961786877248004176017441)
      ·
        refine ⟨56221340157936003132013081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74961786877248004176017441 56221340157936003132013081)
        ·
          refine ⟨42166005118452002349009811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56221340157936003132013081 42166005118452002349009811)
          ·
            refine ⟨63249007677678003523514717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42166005118452002349009811 63249007677678003523514717)
            ·
              refine ⟨23718377879129251321318019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63249007677678003523514717 23718377879129251321318019)
              ·
                refine ⟨35577566818693876981977029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23718377879129251321318019 35577566818693876981977029)
                ·
                  refine ⟨6670793778505101934120693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35577566818693876981977029 6670793778505101934120693)
                  ·
                    refine ⟨625386916734853306323815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6670793778505101934120693 625386916734853306323815)
                    ·
                      rfl

theorem cell22_1826905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 4, 5].length) (baseStart_1826905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1826905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1826905 prefixEnd_1826905 := by exact prefixLift 1826905
  have htrace : WordTrace (prefixWord ++ tailWord_1826905) baseStart_1826905 baseEnd_1826905 := by
    simpa [prefixWord, tailWord_1826905, baseEnd_1826905] using wordTrace_append hprefix tailTrace_1826905
  have hstable : (prefixWord ++ tailWord_1826905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1826905).length < 2 ^ (prefixWord ++ tailWord_1826905).sum := by decide
  have hdescent : baseEnd_1826905 < baseStart_1826905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1826905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1826924 : List Nat := [2, 2, 1, 1, 3, 4, 3, 1, 5]
def baseStart_1826924 : Nat := 118140960795 + 1826924 * 2 ^ 59
def prefixEnd_1826924 : Nat := 4983230072969 + 3 ^ 40 * 1826924 * 2
def baseEnd_1826924 : Nat := 208464473607714530032919

theorem tailTrace_1826924 : CollatzResearch.WordTrace tailWord_1826924 prefixEnd_1826924 208464473607714530032919 := by
  unfold tailWord_1826924
  simp only [CollatzResearch.WordTrace]
  refine ⟨33316696216686918311811913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44422261622249224415749217 33316696216686918311811913)
  ·
    refine ⟨24987522162515188733858935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33316696216686918311811913 24987522162515188733858935)
    ·
      refine ⟨37481283243772783100788403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24987522162515188733858935 37481283243772783100788403)
      ·
        refine ⟨56221924865659174651182605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37481283243772783100788403 56221924865659174651182605)
        ·
          refine ⟨21083221824622190494193477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56221924865659174651182605 21083221824622190494193477)
          ·
            refine ⟨3953104092116660717661277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21083221824622190494193477 3953104092116660717661277)
            ·
              refine ⟨1482414034543747769122979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3953104092116660717661277 1482414034543747769122979)
              ·
                refine ⟨2223621051815621653684469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1482414034543747769122979 2223621051815621653684469)
                ·
                  refine ⟨208464473607714530032919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2223621051815621653684469 208464473607714530032919)
                  ·
                    rfl

theorem cell22_1826924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 5].length) (baseStart_1826924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1826924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1826924 prefixEnd_1826924 := by exact prefixLift 1826924
  have htrace : WordTrace (prefixWord ++ tailWord_1826924) baseStart_1826924 baseEnd_1826924 := by
    simpa [prefixWord, tailWord_1826924, baseEnd_1826924] using wordTrace_append hprefix tailTrace_1826924
  have hstable : (prefixWord ++ tailWord_1826924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1826924).length < 2 ^ (prefixWord ++ tailWord_1826924).sum := by decide
  have hdescent : baseEnd_1826924 < baseStart_1826924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1826924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1826945 : List Nat := [1, 2, 4, 2, 4, 1, 1, 3, 1, 3]
def baseStart_1826945 : Nat := 118140960795 + 1826945 * 2 ^ 59
def prefixEnd_1826945 : Nat := 4983230072969 + 3 ^ 40 * 1826945 * 2
def baseEnd_1826945 : Nat := 625400609552306535323693

theorem tailTrace_1826945 : CollatzResearch.WordTrace tailWord_1826945 prefixEnd_1826945 625400609552306535323693 := by
  unfold tailWord_1826945
  simp only [CollatzResearch.WordTrace]
  refine ⟨66634158366297757210138289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44422772244198504806758859 66634158366297757210138289)
  ·
    refine ⟨49975618774723317907603717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66634158366297757210138289 49975618774723317907603717)
    ·
      refine ⟨9370428520260622107675697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49975618774723317907603717 9370428520260622107675697)
      ·
        refine ⟨7027821390195466580756773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9370428520260622107675697 7027821390195466580756773)
        ·
          refine ⟨1317716510661649983891895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7027821390195466580756773 1317716510661649983891895)
          ·
            refine ⟨1976574765992474975837843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1317716510661649983891895 1976574765992474975837843)
            ·
              refine ⟨2964862148988712463756765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1976574765992474975837843 2964862148988712463756765)
              ·
                refine ⟨1111823305870767173908787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2964862148988712463756765 1111823305870767173908787)
                ·
                  refine ⟨1667734958806150760863181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1111823305870767173908787 1667734958806150760863181)
                  ·
                    refine ⟨625400609552306535323693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1667734958806150760863181 625400609552306535323693)
                    ·
                      rfl

theorem cell22_1826945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 1, 3, 1, 3].length) (baseStart_1826945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1826945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1826945 prefixEnd_1826945 := by exact prefixLift 1826945
  have htrace : WordTrace (prefixWord ++ tailWord_1826945) baseStart_1826945 baseEnd_1826945 := by
    simpa [prefixWord, tailWord_1826945, baseEnd_1826945] using wordTrace_append hprefix tailTrace_1826945
  have hstable : (prefixWord ++ tailWord_1826945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1826945).length < 2 ^ (prefixWord ++ tailWord_1826945).sum := by decide
  have hdescent : baseEnd_1826945 < baseStart_1826945 := by decide
  rcases family_descends (prefixWord ++ tailWord_1826945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1826954 : List Nat := [3, 1, 2, 3, 1, 2, 2, 3, 1, 4]
def baseStart_1826954 : Nat := 118140960795 + 1826954 * 2 ^ 59
def prefixEnd_1826954 : Nat := 4983230072969 + 3 ^ 40 * 1826954 * 2
def baseEnd_1826954 : Nat := 625403690436233511848665

theorem tailTrace_1826954 : CollatzResearch.WordTrace tailWord_1826954 prefixEnd_1826954 625403690436233511848665 := by
  unfold tailWord_1826954
  simp only [CollatzResearch.WordTrace]
  refine ⟨16658621655816287936803979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44422991082176767831477277 16658621655816287936803979)
  ·
    refine ⟨24987932483724431905205969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16658621655816287936803979 24987932483724431905205969)
    ·
      refine ⟨18740949362793323928904477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24987932483724431905205969 18740949362793323928904477)
      ·
        refine ⟨7027856011047496473339179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18740949362793323928904477 7027856011047496473339179)
        ·
          refine ⟨10541784016571244710008769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7027856011047496473339179 10541784016571244710008769)
          ·
            refine ⟨7906338012428433532506577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10541784016571244710008769 7906338012428433532506577)
            ·
              refine ⟨5929753509321325149379933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7906338012428433532506577 5929753509321325149379933)
              ·
                refine ⟨2223657565995496931017475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5929753509321325149379933 2223657565995496931017475)
                ·
                  refine ⟨3335486348993245396526213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2223657565995496931017475 3335486348993245396526213)
                  ·
                    refine ⟨625403690436233511848665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3335486348993245396526213 625403690436233511848665)
                    ·
                      rfl

theorem cell22_1826954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 3, 1, 4].length) (baseStart_1826954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1826954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1826954 prefixEnd_1826954 := by exact prefixLift 1826954
  have htrace : WordTrace (prefixWord ++ tailWord_1826954) baseStart_1826954 baseEnd_1826954 := by
    simpa [prefixWord, tailWord_1826954, baseEnd_1826954] using wordTrace_append hprefix tailTrace_1826954
  have hstable : (prefixWord ++ tailWord_1826954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1826954).length < 2 ^ (prefixWord ++ tailWord_1826954).sum := by decide
  have hdescent : baseEnd_1826954 < baseStart_1826954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1826954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1826999 : List Nat := [1, 1, 3, 1, 4, 3, 2, 1, 2, 4]
def baseStart_1826999 : Nat := 118140960795 + 1826999 * 2 ^ 59
def prefixEnd_1826999 : Nat := 4983230072969 + 3 ^ 40 * 1826999 * 2
def baseEnd_1826999 : Nat := 625419094855868394473527

theorem tailTrace_1826999 : CollatzResearch.WordTrace tailWord_1826999 prefixEnd_1826999 625419094855868394473527 := by
  unfold tailWord_1826999
  simp only [CollatzResearch.WordTrace]
  refine ⟨66636127908102124432604051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44424085272068082955069367 66636127908102124432604051)
  ·
    refine ⟨99954191862153186648906077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66636127908102124432604051 99954191862153186648906077)
    ·
      refine ⟨37482821948307444993339779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99954191862153186648906077 37482821948307444993339779)
      ·
        refine ⟨56224232922461167490009669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37482821948307444993339779 56224232922461167490009669)
        ·
          refine ⟨10542043672961468904376813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56224232922461167490009669 10542043672961468904376813)
          ·
            refine ⟨3953266377360550839141305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10542043672961468904376813 3953266377360550839141305)
            ·
              refine ⟨2964949783020413129355979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3953266377360550839141305 2964949783020413129355979)
              ·
                refine ⟨4447424674530619694033969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2964949783020413129355979 4447424674530619694033969)
                ·
                  refine ⟨3335568505897964770525477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4447424674530619694033969 3335568505897964770525477)
                  ·
                    refine ⟨625419094855868394473527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3335568505897964770525477 625419094855868394473527)
                    ·
                      rfl

theorem cell22_1826999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 2, 1, 2, 4].length) (baseStart_1826999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1826999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1826999 prefixEnd_1826999 := by exact prefixLift 1826999
  have htrace : WordTrace (prefixWord ++ tailWord_1826999) baseStart_1826999 baseEnd_1826999 := by
    simpa [prefixWord, tailWord_1826999, baseEnd_1826999] using wordTrace_append hprefix tailTrace_1826999
  have hstable : (prefixWord ++ tailWord_1826999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1826999).length < 2 ^ (prefixWord ++ tailWord_1826999).sum := by decide
  have hdescent : baseEnd_1826999 < baseStart_1826999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1826999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1827014 : List Nat := [6, 1, 2, 13]
def baseStart_1827014 : Nat := 118140960795 + 1827014 * 2 ^ 59
def prefixEnd_1827014 : Nat := 4983230072969 + 3 ^ 40 * 1827014 * 2
def baseEnd_1827014 : Nat := 857920753995080048489

theorem tailTrace_1827014 : CollatzResearch.WordTrace tailWord_1827014 prefixEnd_1827014 857920753995080048489 := by
  unfold tailWord_1827014
  simp only [CollatzResearch.WordTrace]
  refine ⟨2082396093845243187325003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 44424450002031854662933397 2082396093845243187325003)
  ·
    refine ⟨3123594140767864780987505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2082396093845243187325003 3123594140767864780987505)
    ·
      refine ⟨2342695605575898585740629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3123594140767864780987505 2342695605575898585740629)
      ·
        refine ⟨857920753995080048489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 13 2342695605575898585740629 857920753995080048489)
        ·
          rfl

theorem cell22_1827014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 13].length) (baseStart_1827014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1827014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1827014 prefixEnd_1827014 := by exact prefixLift 1827014
  have htrace : WordTrace (prefixWord ++ tailWord_1827014) baseStart_1827014 baseEnd_1827014 := by
    simpa [prefixWord, tailWord_1827014, baseEnd_1827014] using wordTrace_append hprefix tailTrace_1827014
  have hstable : (prefixWord ++ tailWord_1827014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1827014).length < 2 ^ (prefixWord ++ tailWord_1827014).sum := by decide
  have hdescent : baseEnd_1827014 < baseStart_1827014 := by decide
  rcases family_descends (prefixWord ++ tailWord_1827014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1827020 : List Nat := [2, 2, 1, 6, 1, 2, 2, 2, 4]
def baseStart_1827020 : Nat := 118140960795 + 1827020 * 2 ^ 59
def prefixEnd_1827020 : Nat := 4983230072969 + 3 ^ 40 * 1827020 * 2
def baseEnd_1827020 : Nat := 208475427861677113232821

theorem tailTrace_1827020 : CollatzResearch.WordTrace tailWord_1827020 prefixEnd_1827020 208475427861677113232821 := by
  unfold tailWord_1827020
  simp only [CollatzResearch.WordTrace]
  refine ⟨33318446920513022509559257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44424595894017363346079009 33318446920513022509559257)
  ·
    refine ⟨24988835190384766882169443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33318446920513022509559257 24988835190384766882169443)
    ·
      refine ⟨37483252785577150323254165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24988835190384766882169443 37483252785577150323254165)
      ·
        refine ⟨1757027474323928921402539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 37483252785577150323254165 1757027474323928921402539)
        ·
          refine ⟨2635541211485893382103809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1757027474323928921402539 2635541211485893382103809)
          ·
            refine ⟨1976655908614420036577857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2635541211485893382103809 1976655908614420036577857)
            ·
              refine ⟨1482491931460815027433393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1976655908614420036577857 1482491931460815027433393)
              ·
                refine ⟨1111868948595611270575045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1482491931460815027433393 1111868948595611270575045)
                ·
                  refine ⟨208475427861677113232821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1111868948595611270575045 208475427861677113232821)
                  ·
                    rfl

theorem cell22_1827020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 2, 2, 4].length) (baseStart_1827020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1827020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1827020 prefixEnd_1827020 := by exact prefixLift 1827020
  have htrace : WordTrace (prefixWord ++ tailWord_1827020) baseStart_1827020 baseEnd_1827020 := by
    simpa [prefixWord, tailWord_1827020, baseEnd_1827020] using wordTrace_append hprefix tailTrace_1827020
  have hstable : (prefixWord ++ tailWord_1827020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1827020).length < 2 ^ (prefixWord ++ tailWord_1827020).sum := by decide
  have hdescent : baseEnd_1827020 < baseStart_1827020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1827020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1827104 : List Nat := [2, 1, 1, 5, 2, 1, 2, 2, 6]
def baseStart_1827104 : Nat := 118140960795 + 1827104 * 2 ^ 59
def prefixEnd_1827104 : Nat := 4983230072969 + 3 ^ 40 * 1827104 * 2
def baseEnd_1827104 : Nat := 208485012833894373532735

theorem tailTrace_1827104 : CollatzResearch.WordTrace tailWord_1827104 prefixEnd_1827104 208485012833894373532735 := by
  unfold tailWord_1827104
  simp only [CollatzResearch.WordTrace]
  refine ⟨33319978786360863682588183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44426638381814484910117577 33319978786360863682588183)
  ·
    refine ⟨49979968179541295523882275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33319978786360863682588183 49979968179541295523882275)
    ·
      refine ⟨74969952269311943285823413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49979968179541295523882275 74969952269311943285823413)
      ·
        refine ⟨7028433025247994683045945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 74969952269311943285823413 7028433025247994683045945)
        ·
          refine ⟨5271324768935996012284459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7028433025247994683045945 5271324768935996012284459)
          ·
            refine ⟨7906987153403994018426689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5271324768935996012284459 7906987153403994018426689)
            ·
              refine ⟨5930240365052995513820017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7906987153403994018426689 5930240365052995513820017)
              ·
                refine ⟨4447680273789746635365013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5930240365052995513820017 4447680273789746635365013)
                ·
                  refine ⟨208485012833894373532735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4447680273789746635365013 208485012833894373532735)
                  ·
                    rfl

theorem cell22_1827104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 2, 6].length) (baseStart_1827104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1827104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1827104 prefixEnd_1827104 := by exact prefixLift 1827104
  have htrace : WordTrace (prefixWord ++ tailWord_1827104) baseStart_1827104 baseEnd_1827104 := by
    simpa [prefixWord, tailWord_1827104, baseEnd_1827104] using wordTrace_append hprefix tailTrace_1827104
  have hstable : (prefixWord ++ tailWord_1827104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1827104).length < 2 ^ (prefixWord ++ tailWord_1827104).sum := by decide
  have hdescent : baseEnd_1827104 < baseStart_1827104 := by decide
  rcases family_descends (prefixWord ++ tailWord_1827104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1827106 : List Nat := [3, 3, 1, 1, 3, 1, 1, 4, 1, 4]
def baseStart_1827106 : Nat := 118140960795 + 1827106 * 2 ^ 59
def prefixEnd_1827106 : Nat := 4983230072969 + 3 ^ 40 * 1827106 * 2
def baseEnd_1827106 : Nat := 625455723142555782048199

theorem tailTrace_1827106 : CollatzResearch.WordTrace tailWord_1827106 prefixEnd_1827106 625455723142555782048199 := by
  unfold tailWord_1827106
  simp only [CollatzResearch.WordTrace]
  refine ⟨16660007629678620426687293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44426687012476321137832781 16660007629678620426687293)
  ·
    refine ⟨6247502861129482660007735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16660007629678620426687293 6247502861129482660007735)
    ·
      refine ⟨9371254291694223990011603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6247502861129482660007735 9371254291694223990011603)
      ·
        refine ⟨14056881437541335985017405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9371254291694223990011603 14056881437541335985017405)
        ·
          refine ⟨5271330539078000994381527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14056881437541335985017405 5271330539078000994381527)
          ·
            refine ⟨7906995808617001491572291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5271330539078000994381527 7906995808617001491572291)
            ·
              refine ⟨11860493712925502237358437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7906995808617001491572291 11860493712925502237358437)
              ·
                refine ⟨2223842571173531669504707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11860493712925502237358437 2223842571173531669504707)
                ·
                  refine ⟨3335763856760297504257061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2223842571173531669504707 3335763856760297504257061)
                  ·
                    refine ⟨625455723142555782048199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3335763856760297504257061 625455723142555782048199)
                    ·
                      rfl

theorem cell22_1827106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 4, 1, 4].length) (baseStart_1827106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1827106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1827106 prefixEnd_1827106 := by exact prefixLift 1827106
  have htrace : WordTrace (prefixWord ++ tailWord_1827106) baseStart_1827106 baseEnd_1827106 := by
    simpa [prefixWord, tailWord_1827106, baseEnd_1827106] using wordTrace_append hprefix tailTrace_1827106
  have hstable : (prefixWord ++ tailWord_1827106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1827106).length < 2 ^ (prefixWord ++ tailWord_1827106).sum := by decide
  have hdescent : baseEnd_1827106 < baseStart_1827106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1827106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
