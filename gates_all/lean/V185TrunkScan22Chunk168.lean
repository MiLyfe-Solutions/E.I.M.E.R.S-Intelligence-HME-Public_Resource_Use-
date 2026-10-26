import V185TrunkScan22Chunk167

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1498980 : List Nat := [2, 3, 1, 1, 5, 1, 1, 2, 2, 4]
def baseStart_1498980 : Nat := 118140960795 + 1498980 * 2 ^ 59
def prefixEnd_1498980 : Nat := 4983230072969 + 3 ^ 40 * 1498980 * 2
def baseEnd_1498980 : Nat := 513131487651100311704215

theorem tailTrace_1498980 : CollatzResearch.WordTrace tailWord_1498980 prefixEnd_1498980 513131487651100311704215 := by
  unfold tailWord_1498980
  simp only [CollatzResearch.WordTrace]
  refine ⟨27336146054729470123739197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36448194739639293498318929 27336146054729470123739197)
  ·
    refine ⟨10251054770523551296402199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27336146054729470123739197 10251054770523551296402199)
    ·
      refine ⟨15376582155785326944603299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10251054770523551296402199 15376582155785326944603299)
      ·
        refine ⟨23064873233677990416904949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15376582155785326944603299 23064873233677990416904949)
        ·
          refine ⟨2162331865657311601584839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23064873233677990416904949 2162331865657311601584839)
          ·
            refine ⟨3243497798485967402377259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2162331865657311601584839 3243497798485967402377259)
            ·
              refine ⟨4865246697728951103565889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3243497798485967402377259 4865246697728951103565889)
              ·
                refine ⟨3648935023296713327674417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4865246697728951103565889 3648935023296713327674417)
                ·
                  refine ⟨2736701267472534995755813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3648935023296713327674417 2736701267472534995755813)
                  ·
                    refine ⟨513131487651100311704215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2736701267472534995755813 513131487651100311704215)
                    ·
                      rfl

theorem cell22_1498980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 2, 2, 4].length) (baseStart_1498980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1498980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1498980 prefixEnd_1498980 := by exact prefixLift 1498980
  have htrace : WordTrace (prefixWord ++ tailWord_1498980) baseStart_1498980 baseEnd_1498980 := by
    simpa [prefixWord, tailWord_1498980, baseEnd_1498980] using wordTrace_append hprefix tailTrace_1498980
  have hstable : (prefixWord ++ tailWord_1498980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1498980).length < 2 ^ (prefixWord ++ tailWord_1498980).sum := by decide
  have hdescent : baseEnd_1498980 < baseStart_1498980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1498980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1499044 : List Nat := [2, 3, 1, 2, 1, 3, 4, 2, 1, 3]
def baseStart_1499044 : Nat := 118140960795 + 1499044 * 2 ^ 59
def prefixEnd_1499044 : Nat := 4983230072969 + 3 ^ 40 * 1499044 * 2
def baseEnd_1499044 : Nat := 513153396159025478104019

theorem tailTrace_1499044 : CollatzResearch.WordTrace tailWord_1499044 prefixEnd_1499044 513153396159025478104019 := by
  unfold tailWord_1499044
  simp only [CollatzResearch.WordTrace]
  refine ⟨27337313190613539588904093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36449750920818052785205457 27337313190613539588904093)
  ·
    refine ⟨10251492446480077345839035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27337313190613539588904093 10251492446480077345839035)
    ·
      refine ⟨15377238669720116018758553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10251492446480077345839035 15377238669720116018758553)
      ·
        refine ⟨11532929002290087014068915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15377238669720116018758553 11532929002290087014068915)
        ·
          refine ⟨17299393503435130521103373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11532929002290087014068915 17299393503435130521103373)
          ·
            refine ⟨6487272563788173945413765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17299393503435130521103373 6487272563788173945413765)
            ·
              refine ⟨1216363605710282614765081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6487272563788173945413765 1216363605710282614765081)
              ·
                refine ⟨912272704282711961073811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1216363605710282614765081 912272704282711961073811)
                ·
                  refine ⟨1368409056424067941610717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 912272704282711961073811 1368409056424067941610717)
                  ·
                    refine ⟨513153396159025478104019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1368409056424067941610717 513153396159025478104019)
                    ·
                      rfl

theorem cell22_1499044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 4, 2, 1, 3].length) (baseStart_1499044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1499044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1499044 prefixEnd_1499044 := by exact prefixLift 1499044
  have htrace : WordTrace (prefixWord ++ tailWord_1499044) baseStart_1499044 baseEnd_1499044 := by
    simpa [prefixWord, tailWord_1499044, baseEnd_1499044] using wordTrace_append hprefix tailTrace_1499044
  have hstable : (prefixWord ++ tailWord_1499044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1499044).length < 2 ^ (prefixWord ++ tailWord_1499044).sum := by decide
  have hdescent : baseEnd_1499044 < baseStart_1499044 := by decide
  rcases family_descends (prefixWord ++ tailWord_1499044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1499070 : List Nat := [4, 2, 1, 1, 1, 3, 2, 1, 3, 4]
def baseStart_1499070 : Nat := 118140960795 + 1499070 * 2 ^ 59
def prefixEnd_1499070 : Nat := 4983230072969 + 3 ^ 40 * 1499070 * 2
def baseEnd_1499070 : Nat := 513162296490370076953939

theorem tailTrace_1499070 : CollatzResearch.WordTrace tailWord_1499070 prefixEnd_1499070 513162296490370076953939 := by
  unfold tailWord_1499070
  simp only [CollatzResearch.WordTrace]
  refine ⟨6834446834891610702281833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36450383119421923745503109 6834446834891610702281833)
  ·
    refine ⟨5125835126168708026711375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6834446834891610702281833 5125835126168708026711375)
    ·
      refine ⟨7688752689253062040067063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5125835126168708026711375 7688752689253062040067063)
      ·
        refine ⟨11533129033879593060100595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7688752689253062040067063 11533129033879593060100595)
        ·
          refine ⟨17299693550819389590150893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11533129033879593060100595 17299693550819389590150893)
          ·
            refine ⟨6487385081557271096306585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17299693550819389590150893 6487385081557271096306585)
            ·
              refine ⟨4865538811167953322229939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6487385081557271096306585 4865538811167953322229939)
              ·
                refine ⟨7298308216751929983344909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4865538811167953322229939 7298308216751929983344909)
                ·
                  refine ⟨2736865581281973743754341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7298308216751929983344909 2736865581281973743754341)
                  ·
                    refine ⟨513162296490370076953939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2736865581281973743754341 513162296490370076953939)
                    ·
                      rfl

theorem cell22_1499070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 1, 3, 4].length) (baseStart_1499070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1499070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1499070 prefixEnd_1499070 := by exact prefixLift 1499070
  have htrace : WordTrace (prefixWord ++ tailWord_1499070) baseStart_1499070 baseEnd_1499070 := by
    simpa [prefixWord, tailWord_1499070, baseEnd_1499070] using wordTrace_append hprefix tailTrace_1499070
  have hstable : (prefixWord ++ tailWord_1499070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1499070).length < 2 ^ (prefixWord ++ tailWord_1499070).sum := by decide
  have hdescent : baseEnd_1499070 < baseStart_1499070 := by decide
  rcases family_descends (prefixWord ++ tailWord_1499070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1499083 : List Nat := [1, 1, 1, 1, 3, 4, 1, 4, 1, 5]
def baseStart_1499083 : Nat := 118140960795 + 1499083 * 2 ^ 59
def prefixEnd_1499083 : Nat := 4983230072969 + 3 ^ 40 * 1499083 * 2
def baseEnd_1499083 : Nat := 513166746656042376378899

theorem tailTrace_1499083 : CollatzResearch.WordTrace tailWord_1499083 prefixEnd_1499083 513166746656042376378899 := by
  unfold tailWord_1499083
  simp only [CollatzResearch.WordTrace]
  refine ⟨54676048828085788838477903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36450699218723859225651935 54676048828085788838477903)
  ·
    refine ⟨82014073242128683257716855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54676048828085788838477903 82014073242128683257716855)
    ·
      refine ⟨123021109863193024886575283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82014073242128683257716855 123021109863193024886575283)
      ·
        refine ⟨184531664794789537329862925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123021109863193024886575283 184531664794789537329862925)
        ·
          refine ⟨69199374298046076498698597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 184531664794789537329862925 69199374298046076498698597)
          ·
            refine ⟨12974882680883639343505987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69199374298046076498698597 12974882680883639343505987)
            ·
              refine ⟨19462324021325459015258981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12974882680883639343505987 19462324021325459015258981)
              ·
                refine ⟨3649185753998523565361059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19462324021325459015258981 3649185753998523565361059)
                ·
                  refine ⟨5473778630997785348041589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3649185753998523565361059 5473778630997785348041589)
                  ·
                    refine ⟨513166746656042376378899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5473778630997785348041589 513166746656042376378899)
                    ·
                      rfl

theorem cell22_1499083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 1, 5].length) (baseStart_1499083 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1499083 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1499083 prefixEnd_1499083 := by exact prefixLift 1499083
  have htrace : WordTrace (prefixWord ++ tailWord_1499083) baseStart_1499083 baseEnd_1499083 := by
    simpa [prefixWord, tailWord_1499083, baseEnd_1499083] using wordTrace_append hprefix tailTrace_1499083
  have hstable : (prefixWord ++ tailWord_1499083).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1499083).length < 2 ^ (prefixWord ++ tailWord_1499083).sum := by decide
  have hdescent : baseEnd_1499083 < baseStart_1499083 := by decide
  rcases family_descends (prefixWord ++ tailWord_1499083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1499162 : List Nat := [3, 1, 1, 3, 1, 3, 3, 1, 3, 3]
def baseStart_1499162 : Nat := 118140960795 + 1499162 * 2 ^ 59
def prefixEnd_1499162 : Nat := 4983230072969 + 3 ^ 40 * 1499162 * 2
def baseEnd_1499162 : Nat := 513193789970512503653657

theorem tailTrace_1499162 : CollatzResearch.WordTrace tailWord_1499162 prefixEnd_1499162 513193789970512503653657 := by
  unfold tailWord_1499162
  simp only [CollatzResearch.WordTrace]
  refine ⟨13669732548699896332650935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36452620129866390220402493 13669732548699896332650935)
  ·
    refine ⟨20504598823049844498976403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13669732548699896332650935 20504598823049844498976403)
    ·
      refine ⟨30756898234574766748464605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20504598823049844498976403 30756898234574766748464605)
      ·
        refine ⟨11533836837965537530674227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30756898234574766748464605 11533836837965537530674227)
        ·
          refine ⟨17300755256948306296011341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11533836837965537530674227 17300755256948306296011341)
          ·
            refine ⟨6487783221355614861004253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17300755256948306296011341 6487783221355614861004253)
            ·
              refine ⟨2432918708008355572876595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6487783221355614861004253 2432918708008355572876595)
              ·
                refine ⟨3649378062012533359314893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2432918708008355572876595 3649378062012533359314893)
                ·
                  refine ⟨1368516773254700009743085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3649378062012533359314893 1368516773254700009743085)
                  ·
                    refine ⟨513193789970512503653657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1368516773254700009743085 513193789970512503653657)
                    ·
                      rfl

theorem cell22_1499162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 3, 1, 3, 3].length) (baseStart_1499162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1499162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1499162 prefixEnd_1499162 := by exact prefixLift 1499162
  have htrace : WordTrace (prefixWord ++ tailWord_1499162) baseStart_1499162 baseEnd_1499162 := by
    simpa [prefixWord, tailWord_1499162, baseEnd_1499162] using wordTrace_append hprefix tailTrace_1499162
  have hstable : (prefixWord ++ tailWord_1499162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1499162).length < 2 ^ (prefixWord ++ tailWord_1499162).sum := by decide
  have hdescent : baseEnd_1499162 < baseStart_1499162 := by decide
  rcases family_descends (prefixWord ++ tailWord_1499162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1499203 : List Nat := [1, 1, 1, 3, 1, 2, 2, 1, 10]
def baseStart_1499203 : Nat := 118140960795 + 1499203 * 2 ^ 59
def prefixEnd_1499203 : Nat := 4983230072969 + 3 ^ 40 * 1499203 * 2
def baseEnd_1499203 : Nat := 171069275036134021126177

theorem tailTrace_1499203 : CollatzResearch.WordTrace tailWord_1499203 prefixEnd_1499203 171069275036134021126177 := by
  unfold tailWord_1499203
  simp only [CollatzResearch.WordTrace]
  refine ⟨54680425587651049332846263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36453617058434032888564175 54680425587651049332846263)
  ·
    refine ⟨82020638381476573999269395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54680425587651049332846263 82020638381476573999269395)
    ·
      refine ⟨123030957572214860998904093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82020638381476573999269395 123030957572214860998904093)
      ·
        refine ⟨46136609089580572874589035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123030957572214860998904093 46136609089580572874589035)
        ·
          refine ⟨69204913634370859311883553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46136609089580572874589035 69204913634370859311883553)
          ·
            refine ⟨51903685225778144483912665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69204913634370859311883553 51903685225778144483912665)
            ·
              refine ⟨38927763919333608362934499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51903685225778144483912665 38927763919333608362934499)
              ·
                refine ⟨58391645879000412544401749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38927763919333608362934499 58391645879000412544401749)
                ·
                  refine ⟨171069275036134021126177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 58391645879000412544401749 171069275036134021126177)
                  ·
                    rfl

theorem cell22_1499203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 10].length) (baseStart_1499203 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1499203 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1499203 prefixEnd_1499203 := by exact prefixLift 1499203
  have htrace : WordTrace (prefixWord ++ tailWord_1499203) baseStart_1499203 baseEnd_1499203 := by
    simpa [prefixWord, tailWord_1499203, baseEnd_1499203] using wordTrace_append hprefix tailTrace_1499203
  have hstable : (prefixWord ++ tailWord_1499203).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1499203).length < 2 ^ (prefixWord ++ tailWord_1499203).sum := by decide
  have hdescent : baseEnd_1499203 < baseStart_1499203 := by decide
  rcases family_descends (prefixWord ++ tailWord_1499203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1499220 : List Nat := [2, 4, 1, 1, 1, 1, 1, 5, 6]
def baseStart_1499220 : Nat := 118140960795 + 1499220 * 2 ^ 59
def prefixEnd_1499220 : Nat := 4983230072969 + 3 ^ 40 * 1499220 * 2
def baseEnd_1499220 : Nat := 171071214851939895234493

theorem tailTrace_1499220 : CollatzResearch.WordTrace tailWord_1499220 prefixEnd_1499220 171071214851939895234493 := by
  unfold tailWord_1499220
  simp only [CollatzResearch.WordTrace]
  refine ⟨27340522814294730618107557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36454030419059640824143409 27340522814294730618107557)
  ·
    refine ⟨5126348027680261990895167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27340522814294730618107557 5126348027680261990895167)
    ·
      refine ⟨7689522041520392986342751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5126348027680261990895167 7689522041520392986342751)
      ·
        refine ⟨11534283062280589479514127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7689522041520392986342751 11534283062280589479514127)
        ·
          refine ⟨17301424593420884219271191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11534283062280589479514127 17301424593420884219271191)
          ·
            refine ⟨25952136890131326328906787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17301424593420884219271191 25952136890131326328906787)
            ·
              refine ⟨38928205335196989493360181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25952136890131326328906787 38928205335196989493360181)
              ·
                refine ⟨3649519250174717765002517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38928205335196989493360181 3649519250174717765002517)
                ·
                  refine ⟨171071214851939895234493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3649519250174717765002517 171071214851939895234493)
                  ·
                    rfl

theorem cell22_1499220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 5, 6].length) (baseStart_1499220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1499220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1499220 prefixEnd_1499220 := by exact prefixLift 1499220
  have htrace : WordTrace (prefixWord ++ tailWord_1499220) baseStart_1499220 baseEnd_1499220 := by
    simpa [prefixWord, tailWord_1499220, baseEnd_1499220] using wordTrace_append hprefix tailTrace_1499220
  have hstable : (prefixWord ++ tailWord_1499220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1499220).length < 2 ^ (prefixWord ++ tailWord_1499220).sum := by decide
  have hdescent : baseEnd_1499220 < baseStart_1499220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1499220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1499235 : List Nat := [1, 1, 1, 5, 1, 1, 3, 3, 1, 5]
def baseStart_1499235 : Nat := 118140960795 + 1499235 * 2 ^ 59
def prefixEnd_1499235 : Nat := 4983230072969 + 3 ^ 40 * 1499235 * 2
def baseEnd_1499235 : Nat := 513218779362364646578433

theorem tailTrace_1499235 : CollatzResearch.WordTrace tailWord_1499235 prefixEnd_1499235 513218779362364646578433 := by
  unfold tailWord_1499235
  simp only [CollatzResearch.WordTrace]
  refine ⟨54681592723535118798011159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36454395149023412532007439 54681592723535118798011159)
  ·
    refine ⟨82022389085302678197016739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54681592723535118798011159 82022389085302678197016739)
    ·
      refine ⟨123033583627954017295525109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82022389085302678197016739 123033583627954017295525109)
      ·
        refine ⟨11534398465120689121455479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 123033583627954017295525109 11534398465120689121455479)
        ·
          refine ⟨17301597697681033682183219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11534398465120689121455479 17301597697681033682183219)
          ·
            refine ⟨25952396546521550523274829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17301597697681033682183219 25952396546521550523274829)
            ·
              refine ⟨9732148704945581446228061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25952396546521550523274829 9732148704945581446228061)
              ·
                refine ⟨3649555764354593042335523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9732148704945581446228061 3649555764354593042335523)
                ·
                  refine ⟨5474333646531889563503285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3649555764354593042335523 5474333646531889563503285)
                  ·
                    refine ⟨513218779362364646578433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5474333646531889563503285 513218779362364646578433)
                    ·
                      rfl

theorem cell22_1499235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 3, 1, 5].length) (baseStart_1499235 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1499235 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1499235 prefixEnd_1499235 := by exact prefixLift 1499235
  have htrace : WordTrace (prefixWord ++ tailWord_1499235) baseStart_1499235 baseEnd_1499235 := by
    simpa [prefixWord, tailWord_1499235, baseEnd_1499235] using wordTrace_append hprefix tailTrace_1499235
  have hstable : (prefixWord ++ tailWord_1499235).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1499235).length < 2 ^ (prefixWord ++ tailWord_1499235).sum := by decide
  have hdescent : baseEnd_1499235 < baseStart_1499235 := by decide
  rcases family_descends (prefixWord ++ tailWord_1499235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1499254 : List Nat := [5, 1, 1, 2, 1, 2, 1, 5, 4]
def baseStart_1499254 : Nat := 118140960795 + 1499254 * 2 ^ 59
def prefixEnd_1499254 : Nat := 4983230072969 + 3 ^ 40 * 1499254 * 2
def baseEnd_1499254 : Nat := 171075094483551643451125

theorem tailTrace_1499254 : CollatzResearch.WordTrace tailWord_1499254 prefixEnd_1499254 171075094483551643451125 := by
  unfold tailWord_1499254
  simp only [CollatzResearch.WordTrace]
  refine ⟨3417642856904142815184551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36454857140310856695301877 3417642856904142815184551)
  ·
    refine ⟨5126464285356214222776827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3417642856904142815184551 5126464285356214222776827)
    ·
      refine ⟨7689696428034321334165241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5126464285356214222776827 7689696428034321334165241)
      ·
        refine ⟨5767272321025741000623931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7689696428034321334165241 5767272321025741000623931)
        ·
          refine ⟨8650908481538611500935897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5767272321025741000623931 8650908481538611500935897)
          ·
            refine ⟨6488181361153958625701923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8650908481538611500935897 6488181361153958625701923)
            ·
              refine ⟨9732272041730937938552885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6488181361153958625701923 9732272041730937938552885)
              ·
                refine ⟨912400503912275431739333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9732272041730937938552885 912400503912275431739333)
                ·
                  refine ⟨171075094483551643451125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 912400503912275431739333 171075094483551643451125)
                  ·
                    rfl

theorem cell22_1499254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 5, 4].length) (baseStart_1499254 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1499254 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1499254 prefixEnd_1499254 := by exact prefixLift 1499254
  have htrace : WordTrace (prefixWord ++ tailWord_1499254) baseStart_1499254 baseEnd_1499254 := by
    simpa [prefixWord, tailWord_1499254, baseEnd_1499254] using wordTrace_append hprefix tailTrace_1499254
  have hstable : (prefixWord ++ tailWord_1499254).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1499254).length < 2 ^ (prefixWord ++ tailWord_1499254).sum := by decide
  have hdescent : baseEnd_1499254 < baseStart_1499254 := by decide
  rcases family_descends (prefixWord ++ tailWord_1499254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1499269 : List Nat := [1, 3, 1, 1, 5, 1, 3, 2, 2, 3]
def baseStart_1499269 : Nat := 118140960795 + 1499269 * 2 ^ 59
def prefixEnd_1499269 : Nat := 4983230072969 + 3 ^ 40 * 1499269 * 2
def baseEnd_1499269 : Nat := 513230418257199891228329

theorem tailTrace_1499269 : CollatzResearch.WordTrace tailWord_1499269 prefixEnd_1499269 513230418257199891228329 := by
  unfold tailWord_1499269
  simp only [CollatzResearch.WordTrace]
  refine ⟨54682832805411942604748861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36455221870274628403165907 54682832805411942604748861)
  ·
    refine ⟨20506062302029478476780823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54682832805411942604748861 20506062302029478476780823)
    ·
      refine ⟨30759093453044217715171235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20506062302029478476780823 30759093453044217715171235)
      ·
        refine ⟨46138640179566326572756853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30759093453044217715171235 46138640179566326572756853)
        ·
          refine ⟨4325497516834343116195955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46138640179566326572756853 4325497516834343116195955)
          ·
            refine ⟨6488246275251514674293933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4325497516834343116195955 6488246275251514674293933)
            ·
              refine ⟨2433092353219318002860225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6488246275251514674293933 2433092353219318002860225)
              ·
                refine ⟨1824819264914488502145169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2433092353219318002860225 1824819264914488502145169)
                ·
                  refine ⟨1368614448685866376608877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1824819264914488502145169 1368614448685866376608877)
                  ·
                    refine ⟨513230418257199891228329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1368614448685866376608877 513230418257199891228329)
                    ·
                      rfl

theorem cell22_1499269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 3, 2, 2, 3].length) (baseStart_1499269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1499269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1499269 prefixEnd_1499269 := by exact prefixLift 1499269
  have htrace : WordTrace (prefixWord ++ tailWord_1499269) baseStart_1499269 baseEnd_1499269 := by
    simpa [prefixWord, tailWord_1499269, baseEnd_1499269] using wordTrace_append hprefix tailTrace_1499269
  have hstable : (prefixWord ++ tailWord_1499269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1499269).length < 2 ^ (prefixWord ++ tailWord_1499269).sum := by decide
  have hdescent : baseEnd_1499269 < baseStart_1499269 := by decide
  rcases family_descends (prefixWord ++ tailWord_1499269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1499402 : List Nat := [3, 1, 2, 2, 1, 1, 2, 2, 4, 4]
def baseStart_1499402 : Nat := 118140960795 + 1499402 * 2 ^ 59
def prefixEnd_1499402 : Nat := 4983230072969 + 3 ^ 40 * 1499402 * 2
def baseEnd_1499402 : Nat := 513275946875231877652921

theorem tailTrace_1499402 : CollatzResearch.WordTrace tailWord_1499402 prefixEnd_1499402 513275946875231877652921 := by
  unfold tailWord_1499402
  simp only [CollatzResearch.WordTrace]
  refine ⟨13671920928482526579835115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36458455809286737546226973 13671920928482526579835115)
  ·
    refine ⟨20507881392723789869752673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13671920928482526579835115 20507881392723789869752673)
    ·
      refine ⟨15380911044542842402314505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20507881392723789869752673 15380911044542842402314505)
      ·
        refine ⟨11535683283407131801735879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15380911044542842402314505 11535683283407131801735879)
        ·
          refine ⟨17303524925110697702603819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11535683283407131801735879 17303524925110697702603819)
          ·
            refine ⟨25955287387666046553905729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17303524925110697702603819 25955287387666046553905729)
            ·
              refine ⟨19466465540749534915429297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25955287387666046553905729 19466465540749534915429297)
              ·
                refine ⟨14599849155562151186571973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19466465540749534915429297 14599849155562151186571973)
                ·
                  refine ⟨2737471716667903347482245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14599849155562151186571973 2737471716667903347482245)
                  ·
                    refine ⟨513275946875231877652921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2737471716667903347482245 513275946875231877652921)
                    ·
                      rfl

theorem cell22_1499402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 2, 4, 4].length) (baseStart_1499402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1499402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1499402 prefixEnd_1499402 := by exact prefixLift 1499402
  have htrace : WordTrace (prefixWord ++ tailWord_1499402) baseStart_1499402 baseEnd_1499402 := by
    simpa [prefixWord, tailWord_1499402, baseEnd_1499402] using wordTrace_append hprefix tailTrace_1499402
  have hstable : (prefixWord ++ tailWord_1499402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1499402).length < 2 ^ (prefixWord ++ tailWord_1499402).sum := by decide
  have hdescent : baseEnd_1499402 < baseStart_1499402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1499402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1499404 : List Nat := [2, 2, 1, 2, 2, 2, 1, 5, 2, 3]
def baseStart_1499404 : Nat := 118140960795 + 1499404 * 2 ^ 59
def prefixEnd_1499404 : Nat := 4983230072969 + 3 ^ 40 * 1499404 * 2
def baseEnd_1499404 : Nat := 513276631516104539102915

theorem tailTrace_1499404 : CollatzResearch.WordTrace tailWord_1499404 prefixEnd_1499404 513276631516104539102915 := by
  unfold tailWord_1499404
  simp only [CollatzResearch.WordTrace]
  refine ⟨27343878329961430330456633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36458504439948573773942177 27343878329961430330456633)
  ·
    refine ⟨20507908747471072747842475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27343878329961430330456633 20507908747471072747842475)
    ·
      refine ⟨30761863121206609121763713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20507908747471072747842475 30761863121206609121763713)
      ·
        refine ⟨23071397340904956841322785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30761863121206609121763713 23071397340904956841322785)
        ·
          refine ⟨17303548005678717630992089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23071397340904956841322785 17303548005678717630992089)
          ·
            refine ⟨12977661004259038223244067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17303548005678717630992089 12977661004259038223244067)
            ·
              refine ⟨19466491506388557334866101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12977661004259038223244067 19466491506388557334866101)
              ·
                refine ⟨1824983578723927250143697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19466491506388557334866101 1824983578723927250143697)
                ·
                  refine ⟨1368737684042945437607773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1824983578723927250143697 1368737684042945437607773)
                  ·
                    refine ⟨513276631516104539102915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1368737684042945437607773 513276631516104539102915)
                    ·
                      rfl

theorem cell22_1499404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 5, 2, 3].length) (baseStart_1499404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1499404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1499404 prefixEnd_1499404 := by exact prefixLift 1499404
  have htrace : WordTrace (prefixWord ++ tailWord_1499404) baseStart_1499404 baseEnd_1499404 := by
    simpa [prefixWord, tailWord_1499404, baseEnd_1499404] using wordTrace_append hprefix tailTrace_1499404
  have hstable : (prefixWord ++ tailWord_1499404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1499404).length < 2 ^ (prefixWord ++ tailWord_1499404).sum := by decide
  have hdescent : baseEnd_1499404 < baseStart_1499404 := by decide
  rcases family_descends (prefixWord ++ tailWord_1499404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1499434 : List Nat := [3, 1, 4, 2, 2, 1, 9]
def baseStart_1499434 : Nat := 118140960795 + 1499434 * 2 ^ 59
def prefixEnd_1499434 : Nat := 4983230072969 + 3 ^ 40 * 1499434 * 2
def baseEnd_1499434 : Nat := 19010625967747942994549

theorem tailTrace_1499434 : CollatzResearch.WordTrace tailWord_1499434 prefixEnd_1499434 19010625967747942994549 := by
  unfold tailWord_1499434
  simp only [CollatzResearch.WordTrace]
  refine ⟨13672212712453543946126339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36459233899876117189670237 13672212712453543946126339)
  ·
    refine ⟨20508319068680315919189509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13672212712453543946126339 20508319068680315919189509)
    ·
      refine ⟨3845309825377559234848033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20508319068680315919189509 3845309825377559234848033)
      ·
        refine ⟨2883982369033169426136025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3845309825377559234848033 2883982369033169426136025)
        ·
          refine ⟨2162986776774877069602019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2883982369033169426136025 2162986776774877069602019)
          ·
            refine ⟨3244480165162315604403029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2162986776774877069602019 3244480165162315604403029)
            ·
              refine ⟨19010625967747942994549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3244480165162315604403029 19010625967747942994549)
              ·
                rfl

theorem cell22_1499434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 9].length) (baseStart_1499434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1499434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1499434 prefixEnd_1499434 := by exact prefixLift 1499434
  have htrace : WordTrace (prefixWord ++ tailWord_1499434) baseStart_1499434 baseEnd_1499434 := by
    simpa [prefixWord, tailWord_1499434, baseEnd_1499434] using wordTrace_append hprefix tailTrace_1499434
  have hstable : (prefixWord ++ tailWord_1499434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1499434).length < 2 ^ (prefixWord ++ tailWord_1499434).sum := by decide
  have hdescent : baseEnd_1499434 < baseStart_1499434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1499434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1499438 : List Nat := [4, 1, 3, 3, 1, 1, 1, 1, 4, 3]
def baseStart_1499438 : Nat := 118140960795 + 1499438 * 2 ^ 59
def prefixEnd_1499438 : Nat := 4983230072969 + 3 ^ 40 * 1499438 * 2
def baseEnd_1499438 : Nat := 513288270410939783752811

theorem tailTrace_1499438 : CollatzResearch.WordTrace tailWord_1499438 prefixEnd_1499438 513288270410939783752811 := by
  unfold tailWord_1499438
  simp only [CollatzResearch.WordTrace]
  refine ⟨6836124592724960558456371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36459331161199789645100645 6836124592724960558456371)
  ·
    refine ⟨10254186889087440837684557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6836124592724960558456371 10254186889087440837684557)
    ·
      refine ⟨3845320083407790314131709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10254186889087440837684557 3845320083407790314131709)
      ·
        refine ⟨1441995031277921367799391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3845320083407790314131709 1441995031277921367799391)
        ·
          refine ⟨2162992546916882051699087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1441995031277921367799391 2162992546916882051699087)
          ·
            refine ⟨3244488820375323077548631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2162992546916882051699087 3244488820375323077548631)
            ·
              refine ⟨4866733230562984616322947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3244488820375323077548631 4866733230562984616322947)
              ·
                refine ⟨7300099845844476924484421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4866733230562984616322947 7300099845844476924484421)
                ·
                  refine ⟨1368768721095839423340829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7300099845844476924484421 1368768721095839423340829)
                  ·
                    refine ⟨513288270410939783752811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1368768721095839423340829 513288270410939783752811)
                    ·
                      rfl

theorem cell22_1499438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 1, 4, 3].length) (baseStart_1499438 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1499438 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1499438 prefixEnd_1499438 := by exact prefixLift 1499438
  have htrace : WordTrace (prefixWord ++ tailWord_1499438) baseStart_1499438 baseEnd_1499438 := by
    simpa [prefixWord, tailWord_1499438, baseEnd_1499438] using wordTrace_append hprefix tailTrace_1499438
  have hstable : (prefixWord ++ tailWord_1499438).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1499438).length < 2 ^ (prefixWord ++ tailWord_1499438).sum := by decide
  have hdescent : baseEnd_1499438 < baseStart_1499438 := by decide
  rcases family_descends (prefixWord ++ tailWord_1499438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1499500 : List Nat := [2, 2, 1, 1, 6, 1, 3, 2, 1, 3]
def baseStart_1499500 : Nat := 118140960795 + 1499500 * 2 ^ 59
def prefixEnd_1499500 : Nat := 4983230072969 + 3 ^ 40 * 1499500 * 2
def baseEnd_1499500 : Nat := 513309494277992288702621

theorem tailTrace_1499500 : CollatzResearch.WordTrace tailWord_1499500 prefixEnd_1499500 513309494277992288702621 := by
  unfold tailWord_1499500
  simp only [CollatzResearch.WordTrace]
  refine ⟨27345629033787534528203977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36460838711716712704271969 27345629033787534528203977)
  ·
    refine ⟨20509221775340650896152983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27345629033787534528203977 20509221775340650896152983)
    ·
      refine ⟨30763832663010976344229475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20509221775340650896152983 30763832663010976344229475)
      ·
        refine ⟨46145748994516464516344213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30763832663010976344229475 46145748994516464516344213)
        ·
          refine ⟨2163081984117959274203635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 46145748994516464516344213 2163081984117959274203635)
          ·
            refine ⟨3244622976176938911305453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2163081984117959274203635 3244622976176938911305453)
            ·
              refine ⟨1216733616066352091739545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3244622976176938911305453 1216733616066352091739545)
              ·
                refine ⟨912550212049764068804659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1216733616066352091739545 912550212049764068804659)
                ·
                  refine ⟨1368825318074646103206989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 912550212049764068804659 1368825318074646103206989)
                  ·
                    refine ⟨513309494277992288702621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1368825318074646103206989 513309494277992288702621)
                    ·
                      rfl

theorem cell22_1499500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 3, 2, 1, 3].length) (baseStart_1499500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1499500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1499500 prefixEnd_1499500 := by exact prefixLift 1499500
  have htrace : WordTrace (prefixWord ++ tailWord_1499500) baseStart_1499500 baseEnd_1499500 := by
    simpa [prefixWord, tailWord_1499500, baseEnd_1499500] using wordTrace_append hprefix tailTrace_1499500
  have hstable : (prefixWord ++ tailWord_1499500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1499500).length < 2 ^ (prefixWord ++ tailWord_1499500).sum := by decide
  have hdescent : baseEnd_1499500 < baseStart_1499500 := by decide
  rcases family_descends (prefixWord ++ tailWord_1499500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1499552 : List Nat := [2, 1, 1, 4, 1, 13]
def baseStart_1499552 : Nat := 118140960795 + 1499552 * 2 ^ 59
def prefixEnd_1499552 : Nat := 4983230072969 + 3 ^ 40 * 1499552 * 2
def baseEnd_1499552 : Nat := 6337374011613351683981

theorem tailTrace_1499552 : CollatzResearch.WordTrace tailWord_1499552 prefixEnd_1499552 6337374011613351683981 := by
  unfold tailWord_1499552
  simp only [CollatzResearch.WordTrace]
  refine ⟨27346577331693340968650455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36462103108924454624867273 27346577331693340968650455)
  ·
    refine ⟨41019865997540011452975683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27346577331693340968650455 41019865997540011452975683)
    ·
      refine ⟨61529798996310017179463525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41019865997540011452975683 61529798996310017179463525)
      ·
        refine ⟨11536837311808128221149411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61529798996310017179463525 11536837311808128221149411)
        ·
          refine ⟨17305255967712192331724117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11536837311808128221149411 17305255967712192331724117)
          ·
            refine ⟨6337374011613351683981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 17305255967712192331724117 6337374011613351683981)
            ·
              rfl

theorem cell22_1499552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 13].length) (baseStart_1499552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1499552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1499552 prefixEnd_1499552 := by exact prefixLift 1499552
  have htrace : WordTrace (prefixWord ++ tailWord_1499552) baseStart_1499552 baseEnd_1499552 := by
    simpa [prefixWord, tailWord_1499552, baseEnd_1499552] using wordTrace_append hprefix tailTrace_1499552
  have hstable : (prefixWord ++ tailWord_1499552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1499552).length < 2 ^ (prefixWord ++ tailWord_1499552).sum := by decide
  have hdescent : baseEnd_1499552 < baseStart_1499552 := by decide
  rcases family_descends (prefixWord ++ tailWord_1499552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1499556 : List Nat := [2, 3, 1, 2, 1, 1, 3, 4, 2, 3]
def baseStart_1499556 : Nat := 118140960795 + 1499556 * 2 ^ 59
def prefixEnd_1499556 : Nat := 4983230072969 + 3 ^ 40 * 1499556 * 2
def baseEnd_1499556 : Nat := 513328664222426809302449

theorem tailTrace_1499556 : CollatzResearch.WordTrace tailWord_1499556 prefixEnd_1499556 513328664222426809302449 := by
  unfold tailWord_1499556
  simp only [CollatzResearch.WordTrace]
  refine ⟨27346650277686095310223261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36462200370248127080297681 27346650277686095310223261)
  ·
    refine ⟨10254993854132285741333723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27346650277686095310223261 10254993854132285741333723)
    ·
      refine ⟨15382490781198428612000585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10254993854132285741333723 15382490781198428612000585)
      ·
        refine ⟨11536868085898821459000439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15382490781198428612000585 11536868085898821459000439)
        ·
          refine ⟨17305302128848232188500659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11536868085898821459000439 17305302128848232188500659)
          ·
            refine ⟨25957953193272348282750989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17305302128848232188500659 25957953193272348282750989)
            ·
              refine ⟨9734232447477130606031621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25957953193272348282750989 9734232447477130606031621)
              ·
                refine ⟨1825168583901961988630929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9734232447477130606031621 1825168583901961988630929)
                ·
                  refine ⟨1368876437926471491473197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1825168583901961988630929 1368876437926471491473197)
                  ·
                    refine ⟨513328664222426809302449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1368876437926471491473197 513328664222426809302449)
                    ·
                      rfl

theorem cell22_1499556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 4, 2, 3].length) (baseStart_1499556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1499556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1499556 prefixEnd_1499556 := by exact prefixLift 1499556
  have htrace : WordTrace (prefixWord ++ tailWord_1499556) baseStart_1499556 baseEnd_1499556 := by
    simpa [prefixWord, tailWord_1499556, baseEnd_1499556] using wordTrace_append hprefix tailTrace_1499556
  have hstable : (prefixWord ++ tailWord_1499556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1499556).length < 2 ^ (prefixWord ++ tailWord_1499556).sum := by decide
  have hdescent : baseEnd_1499556 < baseStart_1499556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1499556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1499567 : List Nat := [1, 1, 2, 1, 2, 2, 1, 1, 4, 7]
def baseStart_1499567 : Nat := 118140960795 + 1499567 * 2 ^ 59
def prefixEnd_1499567 : Nat := 4983230072969 + 3 ^ 40 * 1499567 * 2
def baseEnd_1499567 : Nat := 513332429747226447277415

theorem tailTrace_1499567 : CollatzResearch.WordTrace tailWord_1499567 prefixEnd_1499567 513332429747226447277415 := by
  unfold tailWord_1499567
  simp only [CollatzResearch.WordTrace]
  refine ⟨54693701758332339499096955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36462467838888226332731303 54693701758332339499096955)
  ·
    refine ⟨82040552637498509248645433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54693701758332339499096955 82040552637498509248645433)
    ·
      refine ⟨61530414478123881936484075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82040552637498509248645433 61530414478123881936484075)
      ·
        refine ⟨92295621717185822904726113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61530414478123881936484075 92295621717185822904726113)
        ·
          refine ⟨69221716287889367178544585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92295621717185822904726113 69221716287889367178544585)
          ·
            refine ⟨51916287215917025383908439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69221716287889367178544585 51916287215917025383908439)
            ·
              refine ⟨77874430823875538075862659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51916287215917025383908439 77874430823875538075862659)
              ·
                refine ⟨116811646235813307113793989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77874430823875538075862659 116811646235813307113793989)
                ·
                  refine ⟨21902183669214995083836373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 116811646235813307113793989 21902183669214995083836373)
                  ·
                    refine ⟨513332429747226447277415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21902183669214995083836373 513332429747226447277415)
                    ·
                      rfl

theorem cell22_1499567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 4, 7].length) (baseStart_1499567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1499567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1499567 prefixEnd_1499567 := by exact prefixLift 1499567
  have htrace : WordTrace (prefixWord ++ tailWord_1499567) baseStart_1499567 baseEnd_1499567 := by
    simpa [prefixWord, tailWord_1499567, baseEnd_1499567] using wordTrace_append hprefix tailTrace_1499567
  have hstable : (prefixWord ++ tailWord_1499567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1499567).length < 2 ^ (prefixWord ++ tailWord_1499567).sum := by decide
  have hdescent : baseEnd_1499567 < baseStart_1499567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1499567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1499569 : List Nat := [1, 2, 2, 4, 1, 2, 3, 7]
def baseStart_1499569 : Nat := 118140960795 + 1499569 * 2 ^ 59
def prefixEnd_1499569 : Nat := 4983230072969 + 3 ^ 40 * 1499569 * 2
def baseEnd_1499569 : Nat := 57037012709788789858601

theorem tailTrace_1499569 : CollatzResearch.WordTrace tailWord_1499569 prefixEnd_1499569 57037012709788789858601 := by
  unfold tailWord_1499569
  simp only [CollatzResearch.WordTrace]
  refine ⟨54693774704325093840669761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36462516469550062560446507 54693774704325093840669761)
  ·
    refine ⟨41020331028243820380502321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54693774704325093840669761 41020331028243820380502321)
    ·
      refine ⟨30765248271182865285376741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41020331028243820380502321 30765248271182865285376741)
      ·
        refine ⟨5768484050846787241008139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30765248271182865285376741 5768484050846787241008139)
        ·
          refine ⟨8652726076270180861512209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5768484050846787241008139 8652726076270180861512209)
          ·
            refine ⟨6489544557202635646134157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8652726076270180861512209 6489544557202635646134157)
            ·
              refine ⟨2433579208950988367300309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6489544557202635646134157 2433579208950988367300309)
              ·
                refine ⟨57037012709788789858601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2433579208950988367300309 57037012709788789858601)
                ·
                  rfl

theorem cell22_1499569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 3, 7].length) (baseStart_1499569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1499569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1499569 prefixEnd_1499569 := by exact prefixLift 1499569
  have htrace : WordTrace (prefixWord ++ tailWord_1499569) baseStart_1499569 baseEnd_1499569 := by
    simpa [prefixWord, tailWord_1499569, baseEnd_1499569] using wordTrace_append hprefix tailTrace_1499569
  have hstable : (prefixWord ++ tailWord_1499569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1499569).length < 2 ^ (prefixWord ++ tailWord_1499569).sum := by decide
  have hdescent : baseEnd_1499569 < baseStart_1499569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1499569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1499652 : List Nat := [2, 3, 2, 3, 1, 3, 1, 3, 1, 3]
def baseStart_1499652 : Nat := 118140960795 + 1499652 * 2 ^ 59
def prefixEnd_1499652 : Nat := 4983230072969 + 3 ^ 40 * 1499652 * 2
def baseEnd_1499652 : Nat := 513361526984314558902155

theorem tailTrace_1499652 : CollatzResearch.WordTrace tailWord_1499652 prefixEnd_1499652 513361526984314558902155 := by
  unfold tailWord_1499652
  simp only [CollatzResearch.WordTrace]
  refine ⟨27348400981512199507970605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36464534642016266010627473 27348400981512199507970605)
  ·
    refine ⟨10255650368067074815488977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27348400981512199507970605 10255650368067074815488977)
    ·
      refine ⟨7691737776050306111616733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10255650368067074815488977 7691737776050306111616733)
      ·
        refine ⟨2884401666018864791856275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7691737776050306111616733 2884401666018864791856275)
        ·
          refine ⟨4326602499028297187784413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2884401666018864791856275 4326602499028297187784413)
          ·
            refine ⟨1622475937135611445419155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4326602499028297187784413 1622475937135611445419155)
            ·
              refine ⟨2433713905703417168128733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1622475937135611445419155 2433713905703417168128733)
              ·
                refine ⟨912642714638781438048275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2433713905703417168128733 912642714638781438048275)
                ·
                  refine ⟨1368964071958172157072413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 912642714638781438048275 1368964071958172157072413)
                  ·
                    refine ⟨513361526984314558902155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1368964071958172157072413 513361526984314558902155)
                    ·
                      rfl

theorem cell22_1499652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 1, 3, 1, 3].length) (baseStart_1499652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1499652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1499652 prefixEnd_1499652 := by exact prefixLift 1499652
  have htrace : WordTrace (prefixWord ++ tailWord_1499652) baseStart_1499652 baseEnd_1499652 := by
    simpa [prefixWord, tailWord_1499652, baseEnd_1499652] using wordTrace_append hprefix tailTrace_1499652
  have hstable : (prefixWord ++ tailWord_1499652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1499652).length < 2 ^ (prefixWord ++ tailWord_1499652).sum := by decide
  have hdescent : baseEnd_1499652 < baseStart_1499652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1499652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1499676 : List Nat := [2, 2, 3, 1, 2, 2, 3, 1, 6]
def baseStart_1499676 : Nat := 118140960795 + 1499676 * 2 ^ 59
def prefixEnd_1499676 : Nat := 4983230072969 + 3 ^ 40 * 1499676 * 2
def baseEnd_1499676 : Nat := 171123247558262165434027

theorem tailTrace_1499676 : CollatzResearch.WordTrace tailWord_1499676 prefixEnd_1499676 171123247558262165434027 := by
  unfold tailWord_1499676
  simp only [CollatzResearch.WordTrace]
  refine ⟨27348838657468725557407441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36465118209958300743209921 27348838657468725557407441)
  ·
    refine ⟨20511628993101544168055581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27348838657468725557407441 20511628993101544168055581)
    ·
      refine ⟨7691860872413079063020843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20511628993101544168055581 7691860872413079063020843)
      ·
        refine ⟨11537791308619618594531265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7691860872413079063020843 11537791308619618594531265)
        ·
          refine ⟨8653343481464713945898449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11537791308619618594531265 8653343481464713945898449)
          ·
            refine ⟨6490007611098535459423837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8653343481464713945898449 6490007611098535459423837)
            ·
              refine ⟨2433752854161950797283939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6490007611098535459423837 2433752854161950797283939)
              ·
                refine ⟨3650629281242926195925909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2433752854161950797283939 3650629281242926195925909)
                ·
                  refine ⟨171123247558262165434027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3650629281242926195925909 171123247558262165434027)
                  ·
                    rfl

theorem cell22_1499676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 3, 1, 6].length) (baseStart_1499676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1499676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1499676 prefixEnd_1499676 := by exact prefixLift 1499676
  have htrace : WordTrace (prefixWord ++ tailWord_1499676) baseStart_1499676 baseEnd_1499676 := by
    simpa [prefixWord, tailWord_1499676, baseEnd_1499676] using wordTrace_append hprefix tailTrace_1499676
  have hstable : (prefixWord ++ tailWord_1499676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1499676).length < 2 ^ (prefixWord ++ tailWord_1499676).sum := by decide
  have hdescent : baseEnd_1499676 < baseStart_1499676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1499676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1499704 : List Nat := [2, 1, 2, 1, 4, 1, 1, 10]
def baseStart_1499704 : Nat := 118140960795 + 1499704 * 2 ^ 59
def prefixEnd_1499704 : Nat := 4983230072969 + 3 ^ 40 * 1499704 * 2
def baseEnd_1499704 : Nat := 57042147516333750733555

theorem tailTrace_1499704 : CollatzResearch.WordTrace tailWord_1499704 prefixEnd_1499704 57042147516333750733555 := by
  unfold tailWord_1499704
  simp only [CollatzResearch.WordTrace]
  refine ⟨27349349279418005948417083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36465799039224007931222777 27349349279418005948417083)
  ·
    refine ⟨41024023919127008922625625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27349349279418005948417083 41024023919127008922625625)
    ·
      refine ⟨30768017939345256691969219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41024023919127008922625625 30768017939345256691969219)
      ·
        refine ⟨46152026909017885037953829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30768017939345256691969219 46152026909017885037953829)
        ·
          refine ⟨8653505045440853444616343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46152026909017885037953829 8653505045440853444616343)
          ·
            refine ⟨12980257568161280166924515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8653505045440853444616343 12980257568161280166924515)
            ·
              refine ⟨19470386352241920250386773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12980257568161280166924515 19470386352241920250386773)
              ·
                refine ⟨57042147516333750733555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 19470386352241920250386773 57042147516333750733555)
                ·
                  rfl

theorem cell22_1499704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 10].length) (baseStart_1499704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1499704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1499704 prefixEnd_1499704 := by exact prefixLift 1499704
  have htrace : WordTrace (prefixWord ++ tailWord_1499704) baseStart_1499704 baseEnd_1499704 := by
    simpa [prefixWord, tailWord_1499704, baseEnd_1499704] using wordTrace_append hprefix tailTrace_1499704
  have hstable : (prefixWord ++ tailWord_1499704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1499704).length < 2 ^ (prefixWord ++ tailWord_1499704).sum := by decide
  have hdescent : baseEnd_1499704 < baseStart_1499704 := by decide
  rcases family_descends (prefixWord ++ tailWord_1499704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1499706 : List Nat := [3, 1, 1, 1, 3, 3, 1, 3, 2, 4]
def baseStart_1499706 : Nat := 118140960795 + 1499706 * 2 ^ 59
def prefixEnd_1499706 : Nat := 4983230072969 + 3 ^ 40 * 1499706 * 2
def baseEnd_1499706 : Nat := 513380012287876418051989

theorem tailTrace_1499706 : CollatzResearch.WordTrace tailWord_1499706 prefixEnd_1499706 513380012287876418051989 := by
  unfold tailWord_1499706
  simp only [CollatzResearch.WordTrace]
  refine ⟨13674692876207191559601743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36465847669885844158937981 13674692876207191559601743)
  ·
    refine ⟨20512039314310787339402615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13674692876207191559601743 20512039314310787339402615)
    ·
      refine ⟨30768058971466181009103923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20512039314310787339402615 30768058971466181009103923)
      ·
        refine ⟨46152088457199271513655885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30768058971466181009103923 46152088457199271513655885)
        ·
          refine ⟨17307033171449726817620957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46152088457199271513655885 17307033171449726817620957)
          ·
            refine ⟨6490137439293647556607859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17307033171449726817620957 6490137439293647556607859)
            ·
              refine ⟨9735206158940471334911789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6490137439293647556607859 9735206158940471334911789)
              ·
                refine ⟨3650702309602676750591921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9735206158940471334911789 3650702309602676750591921)
                ·
                  refine ⟨2738026732202007562943941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3650702309602676750591921 2738026732202007562943941)
                  ·
                    refine ⟨513380012287876418051989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2738026732202007562943941 513380012287876418051989)
                    ·
                      rfl

theorem cell22_1499706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 3, 2, 4].length) (baseStart_1499706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1499706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1499706 prefixEnd_1499706 := by exact prefixLift 1499706
  have htrace : WordTrace (prefixWord ++ tailWord_1499706) baseStart_1499706 baseEnd_1499706 := by
    simpa [prefixWord, tailWord_1499706, baseEnd_1499706] using wordTrace_append hprefix tailTrace_1499706
  have hstable : (prefixWord ++ tailWord_1499706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1499706).length < 2 ^ (prefixWord ++ tailWord_1499706).sum := by decide
  have hdescent : baseEnd_1499706 < baseStart_1499706 := by decide
  rcases family_descends (prefixWord ++ tailWord_1499706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1499725 : List Nat := [1, 6, 1, 1, 2, 1, 1, 4, 2, 3]
def baseStart_1499725 : Nat := 118140960795 + 1499725 * 2 ^ 59
def prefixEnd_1499725 : Nat := 4983230072969 + 3 ^ 40 * 1499725 * 2
def baseEnd_1499725 : Nat := 513386516376166701826931

theorem tailTrace_1499725 : CollatzResearch.WordTrace tailWord_1499725 prefixEnd_1499725 513386516376166701826931 := by
  unfold tailWord_1499725
  simp only [CollatzResearch.WordTrace]
  refine ⟨54699464491759932483348629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36466309661173288322232419 54699464491759932483348629)
  ·
    refine ⟨2564037398051246835156967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 54699464491759932483348629 2564037398051246835156967)
    ·
      refine ⟨3846056097076870252735451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2564037398051246835156967 3846056097076870252735451)
      ·
        refine ⟨5769084145615305379103177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3846056097076870252735451 5769084145615305379103177)
        ·
          refine ⟨4326813109211479034327383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5769084145615305379103177 4326813109211479034327383)
          ·
            refine ⟨6490219663817218551491075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4326813109211479034327383 6490219663817218551491075)
            ·
              refine ⟨9735329495725827827236613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6490219663817218551491075 9735329495725827827236613)
              ·
                refine ⟨1825374280448592717606865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9735329495725827827236613 1825374280448592717606865)
                ·
                  refine ⟨1369030710336444538205149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1825374280448592717606865 1369030710336444538205149)
                  ·
                    refine ⟨513386516376166701826931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1369030710336444538205149 513386516376166701826931)
                    ·
                      rfl

theorem cell22_1499725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 4, 2, 3].length) (baseStart_1499725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1499725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1499725 prefixEnd_1499725 := by exact prefixLift 1499725
  have htrace : WordTrace (prefixWord ++ tailWord_1499725) baseStart_1499725 baseEnd_1499725 := by
    simpa [prefixWord, tailWord_1499725, baseEnd_1499725] using wordTrace_append hprefix tailTrace_1499725
  have hstable : (prefixWord ++ tailWord_1499725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1499725).length < 2 ^ (prefixWord ++ tailWord_1499725).sum := by decide
  have hdescent : baseEnd_1499725 < baseStart_1499725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1499725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1499781 : List Nat := [1, 3, 1, 1, 4, 2, 1, 2, 2, 5]
def baseStart_1499781 : Nat := 118140960795 + 1499781 * 2 ^ 59
def prefixEnd_1499781 : Nat := 4983230072969 + 3 ^ 40 * 1499781 * 2
def baseEnd_1499781 : Nat := 513405686320601222426759

theorem tailTrace_1499781 : CollatzResearch.WordTrace tailWord_1499781 prefixEnd_1499781 513405686320601222426759 := by
  unfold tailWord_1499781
  simp only [CollatzResearch.WordTrace]
  refine ⟨54701506979557054047387197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36467671319704702698258131 54701506979557054047387197)
  ·
    refine ⟨20513065117333895267770199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54701506979557054047387197 20513065117333895267770199)
    ·
      refine ⟨30769597676000842901655299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20513065117333895267770199 30769597676000842901655299)
      ·
        refine ⟨46154396514001264352482949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30769597676000842901655299 46154396514001264352482949)
        ·
          refine ⟨8653949346375237066090553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46154396514001264352482949 8653949346375237066090553)
          ·
            refine ⟨6490462009781427799567915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8653949346375237066090553 6490462009781427799567915)
            ·
              refine ⟨9735693014672141699351873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6490462009781427799567915 9735693014672141699351873)
              ·
                refine ⟨7301769761004106274513905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9735693014672141699351873 7301769761004106274513905)
                ·
                  refine ⟨5476327320753079705885429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7301769761004106274513905 5476327320753079705885429)
                  ·
                    refine ⟨513405686320601222426759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5476327320753079705885429 513405686320601222426759)
                    ·
                      rfl

theorem cell22_1499781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 2, 2, 5].length) (baseStart_1499781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1499781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1499781 prefixEnd_1499781 := by exact prefixLift 1499781
  have htrace : WordTrace (prefixWord ++ tailWord_1499781) baseStart_1499781 baseEnd_1499781 := by
    simpa [prefixWord, tailWord_1499781, baseEnd_1499781] using wordTrace_append hprefix tailTrace_1499781
  have hstable : (prefixWord ++ tailWord_1499781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1499781).length < 2 ^ (prefixWord ++ tailWord_1499781).sum := by decide
  have hdescent : baseEnd_1499781 < baseStart_1499781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1499781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1499826 : List Nat := [3, 2, 1, 1, 1, 2, 1, 3, 3, 5]
def baseStart_1499826 : Nat := 118140960795 + 1499826 * 2 ^ 59
def prefixEnd_1499826 : Nat := 4983230072969 + 3 ^ 40 * 1499826 * 2
def baseEnd_1499826 : Nat := 513421090740236105051621

theorem tailTrace_1499826 : CollatzResearch.WordTrace tailWord_1499826 prefixEnd_1499826 513421090740236105051621 := by
  unfold tailWord_1499826
  simp only [CollatzResearch.WordTrace]
  refine ⟨13675787066098506683193833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36468765509596017821850221 13675787066098506683193833)
  ·
    refine ⟨10256840299573880012395375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13675787066098506683193833 10256840299573880012395375)
    ·
      refine ⟨15385260449360820018593063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10256840299573880012395375 15385260449360820018593063)
      ·
        refine ⟨23077890674041230027889595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15385260449360820018593063 23077890674041230027889595)
        ·
          refine ⟨34616836011061845041834393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23077890674041230027889595 34616836011061845041834393)
          ·
            refine ⟨25962627008296383781375795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34616836011061845041834393 25962627008296383781375795)
            ·
              refine ⟨38943940512444575672063693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25962627008296383781375795 38943940512444575672063693)
              ·
                refine ⟨14603977692166715877023885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38943940512444575672063693 14603977692166715877023885)
                ·
                  refine ⟨5476491634562518453883957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14603977692166715877023885 5476491634562518453883957)
                  ·
                    refine ⟨513421090740236105051621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5476491634562518453883957 513421090740236105051621)
                    ·
                      rfl

theorem cell22_1499826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 3, 3, 5].length) (baseStart_1499826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1499826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1499826 prefixEnd_1499826 := by exact prefixLift 1499826
  have htrace : WordTrace (prefixWord ++ tailWord_1499826) baseStart_1499826 baseEnd_1499826 := by
    simpa [prefixWord, tailWord_1499826, baseEnd_1499826] using wordTrace_append hprefix tailTrace_1499826
  have hstable : (prefixWord ++ tailWord_1499826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1499826).length < 2 ^ (prefixWord ++ tailWord_1499826).sum := by decide
  have hdescent : baseEnd_1499826 < baseStart_1499826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1499826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1499875 : List Nat := [1, 1, 1, 7, 1, 2, 2, 1, 2, 4]
def baseStart_1499875 : Nat := 118140960795 + 1499875 * 2 ^ 59
def prefixEnd_1499875 : Nat := 4983230072969 + 3 ^ 40 * 1499875 * 2
def baseEnd_1499875 : Nat := 513437864441616310576471

theorem tailTrace_1499875 : CollatzResearch.WordTrace tailWord_1499875 prefixEnd_1499875 513437864441616310576471 := by
  unfold tailWord_1499875
  simp only [CollatzResearch.WordTrace]
  refine ⟨54704935441216508101309079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36469956960811005400872719 54704935441216508101309079)
  ·
    refine ⟨82057403161824762151963619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54704935441216508101309079 82057403161824762151963619)
    ·
      refine ⟨123086104742737143227945429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82057403161824762151963619 123086104742737143227945429)
      ·
        refine ⟨2884830579907901794404971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 123086104742737143227945429 2884830579907901794404971)
        ·
          refine ⟨4327245869861852691607457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2884830579907901794404971 4327245869861852691607457)
          ·
            refine ⟨3245434402396389518705593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4327245869861852691607457 3245434402396389518705593)
            ·
              refine ⟨2434075801797292139029195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3245434402396389518705593 2434075801797292139029195)
              ·
                refine ⟨3651113702695938208543793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2434075801797292139029195 3651113702695938208543793)
                ·
                  refine ⟨2738335277021953656407845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3651113702695938208543793 2738335277021953656407845)
                  ·
                    refine ⟨513437864441616310576471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2738335277021953656407845 513437864441616310576471)
                    ·
                      rfl

theorem cell22_1499875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 2, 1, 2, 4].length) (baseStart_1499875 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1499875 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1499875 prefixEnd_1499875 := by exact prefixLift 1499875
  have htrace : WordTrace (prefixWord ++ tailWord_1499875) baseStart_1499875 baseEnd_1499875 := by
    simpa [prefixWord, tailWord_1499875, baseEnd_1499875] using wordTrace_append hprefix tailTrace_1499875
  have hstable : (prefixWord ++ tailWord_1499875).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1499875).length < 2 ^ (prefixWord ++ tailWord_1499875).sum := by decide
  have hdescent : baseEnd_1499875 < baseStart_1499875 := by decide
  rcases family_descends (prefixWord ++ tailWord_1499875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1499950 : List Nat := [4, 1, 3, 2, 1, 1, 1, 2, 2, 5]
def baseStart_1499950 : Nat := 118140960795 + 1499950 * 2 ^ 59
def prefixEnd_1499950 : Nat := 4983230072969 + 3 ^ 40 * 1499950 * 2
def baseEnd_1499950 : Nat := 513463538474341114951241

theorem tailTrace_1499950 : CollatzResearch.WordTrace tailWord_1499950 prefixEnd_1499950 513463538474341114951241 := by
  unfold tailWord_1499950
  simp only [CollatzResearch.WordTrace]
  refine ⟨6838458864493099488786163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36471780610629863940192869 6838458864493099488786163)
  ·
    refine ⟨10257688296739649233179245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6838458864493099488786163 10257688296739649233179245)
    ·
      refine ⟨3846633111277368462442217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10257688296739649233179245 3846633111277368462442217)
      ·
        refine ⟨2884974833458026346831663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3846633111277368462442217 2884974833458026346831663)
        ·
          refine ⟨4327462250187039520247495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2884974833458026346831663 4327462250187039520247495)
          ·
            refine ⟨6491193375280559280371243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4327462250187039520247495 6491193375280559280371243)
            ·
              refine ⟨9736790062920838920556865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6491193375280559280371243 9736790062920838920556865)
              ·
                refine ⟨7302592547190629190417649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9736790062920838920556865 7302592547190629190417649)
                ·
                  refine ⟨5476944410392971892813237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7302592547190629190417649 5476944410392971892813237)
                  ·
                    refine ⟨513463538474341114951241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5476944410392971892813237 513463538474341114951241)
                    ·
                      rfl

theorem cell22_1499950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_1499950 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1499950 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1499950 prefixEnd_1499950 := by exact prefixLift 1499950
  have htrace : WordTrace (prefixWord ++ tailWord_1499950) baseStart_1499950 baseEnd_1499950 := by
    simpa [prefixWord, tailWord_1499950, baseEnd_1499950] using wordTrace_append hprefix tailTrace_1499950
  have hstable : (prefixWord ++ tailWord_1499950).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1499950).length < 2 ^ (prefixWord ++ tailWord_1499950).sum := by decide
  have hdescent : baseEnd_1499950 < baseStart_1499950 := by decide
  rcases family_descends (prefixWord ++ tailWord_1499950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1499969 : List Nat := [1, 2, 5, 3, 1, 1, 3, 1, 5]
def baseStart_1499969 : Nat := 118140960795 + 1499969 * 2 ^ 59
def prefixEnd_1499969 : Nat := 4983230072969 + 3 ^ 40 * 1499969 * 2
def baseEnd_1499969 : Nat := 171156680854210466242061

theorem tailTrace_1499969 : CollatzResearch.WordTrace tailWord_1499969 prefixEnd_1499969 171156680854210466242061 := by
  unfold tailWord_1499969
  simp only [CollatzResearch.WordTrace]
  refine ⟨54708363902875962155230961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36472242601917308103487307 54708363902875962155230961)
  ·
    refine ⟨41031272927156971616423221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54708363902875962155230961 41031272927156971616423221)
    ·
      refine ⟨3846681836920966089039677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 41031272927156971616423221 3846681836920966089039677)
      ·
        refine ⟨1442505688845362283389879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3846681836920966089039677 1442505688845362283389879)
        ·
          refine ⟨2163758533268043425084819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1442505688845362283389879 2163758533268043425084819)
          ·
            refine ⟨3245637799902065137627229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2163758533268043425084819 3245637799902065137627229)
            ·
              refine ⟨1217114174963274426610211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3245637799902065137627229 1217114174963274426610211)
              ·
                refine ⟨1825671262444911639915317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1217114174963274426610211 1825671262444911639915317)
                ·
                  refine ⟨171156680854210466242061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1825671262444911639915317 171156680854210466242061)
                  ·
                    rfl

theorem cell22_1499969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 3, 1, 5].length) (baseStart_1499969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1499969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1499969 prefixEnd_1499969 := by exact prefixLift 1499969
  have htrace : WordTrace (prefixWord ++ tailWord_1499969) baseStart_1499969 baseEnd_1499969 := by
    simpa [prefixWord, tailWord_1499969, baseEnd_1499969] using wordTrace_append hprefix tailTrace_1499969
  have hstable : (prefixWord ++ tailWord_1499969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1499969).length < 2 ^ (prefixWord ++ tailWord_1499969).sum := by decide
  have hdescent : baseEnd_1499969 < baseStart_1499969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1499969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1499978 : List Nat := [3, 1, 2, 1, 1, 1, 2, 5, 1, 5]
def baseStart_1499978 : Nat := 118140960795 + 1499978 * 2 ^ 59
def prefixEnd_1499978 : Nat := 4983230072969 + 3 ^ 40 * 1499978 * 2
def baseEnd_1499978 : Nat := 513473123446558375251155

theorem tailTrace_1499978 : CollatzResearch.WordTrace tailWord_1499978 prefixEnd_1499978 513473123446558375251155 := by
  unfold tailWord_1499978
  simp only [CollatzResearch.WordTrace]
  refine ⟨13677173039960839173077147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36472461439895571128205725 13677173039960839173077147)
  ·
    refine ⟨20515759559941258759615721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13677173039960839173077147 20515759559941258759615721)
    ·
      refine ⟨15386819669955944069711791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20515759559941258759615721 15386819669955944069711791)
      ·
        refine ⟨23080229504933916104567687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15386819669955944069711791 23080229504933916104567687)
        ·
          refine ⟨34620344257400874156851531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23080229504933916104567687 34620344257400874156851531)
          ·
            refine ⟨51930516386101311235277297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34620344257400874156851531 51930516386101311235277297)
            ·
              refine ⟨38947887289575983426457973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51930516386101311235277297 38947887289575983426457973)
              ·
                refine ⟨3651364433397748446230435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38947887289575983426457973 3651364433397748446230435)
                ·
                  refine ⟨5477046650096622669345653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3651364433397748446230435 5477046650096622669345653)
                  ·
                    refine ⟨513473123446558375251155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5477046650096622669345653 513473123446558375251155)
                    ·
                      rfl

theorem cell22_1499978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 5, 1, 5].length) (baseStart_1499978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1499978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1499978 prefixEnd_1499978 := by exact prefixLift 1499978
  have htrace : WordTrace (prefixWord ++ tailWord_1499978) baseStart_1499978 baseEnd_1499978 := by
    simpa [prefixWord, tailWord_1499978, baseEnd_1499978] using wordTrace_append hprefix tailTrace_1499978
  have hstable : (prefixWord ++ tailWord_1499978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1499978).length < 2 ^ (prefixWord ++ tailWord_1499978).sum := by decide
  have hdescent : baseEnd_1499978 < baseStart_1499978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1499978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1499993 : List Nat := [1, 2, 1, 2, 2, 4, 2, 1, 1, 6]
def baseStart_1499993 : Nat := 118140960795 + 1499993 * 2 ^ 59
def prefixEnd_1499993 : Nat := 4983230072969 + 3 ^ 40 * 1499993 * 2
def baseEnd_1499993 : Nat := 513478258253103336126109

theorem tailTrace_1499993 : CollatzResearch.WordTrace tailWord_1499993 prefixEnd_1499993 513478258253103336126109 := by
  unfold tailWord_1499993
  simp only [CollatzResearch.WordTrace]
  refine ⟨54709239254789014254104633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36472826169859342836069755 54709239254789014254104633)
  ·
    refine ⟨41031929441091760690578475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54709239254789014254104633 41031929441091760690578475)
    ·
      refine ⟨61547894161637641035867713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41031929441091760690578475 61547894161637641035867713)
      ·
        refine ⟨46160920621228230776900785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61547894161637641035867713 46160920621228230776900785)
        ·
          refine ⟨34620690465921173082675589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46160920621228230776900785 34620690465921173082675589)
          ·
            refine ⟨6491379462360219953001673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34620690465921173082675589 6491379462360219953001673)
            ·
              refine ⟨4868534596770164964751255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6491379462360219953001673 4868534596770164964751255)
              ·
                refine ⟨7302801895155247447126883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4868534596770164964751255 7302801895155247447126883)
                ·
                  refine ⟨10954202842732871170690325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7302801895155247447126883 10954202842732871170690325)
                  ·
                    refine ⟨513478258253103336126109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10954202842732871170690325 513478258253103336126109)
                    ·
                      rfl

theorem cell22_1499993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 1, 1, 6].length) (baseStart_1499993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1499993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1499993 prefixEnd_1499993 := by exact prefixLift 1499993
  have htrace : WordTrace (prefixWord ++ tailWord_1499993) baseStart_1499993 baseEnd_1499993 := by
    simpa [prefixWord, tailWord_1499993, baseEnd_1499993] using wordTrace_append hprefix tailTrace_1499993
  have hstable : (prefixWord ++ tailWord_1499993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1499993).length < 2 ^ (prefixWord ++ tailWord_1499993).sum := by decide
  have hdescent : baseEnd_1499993 < baseStart_1499993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1499993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1500008 : List Nat := [2, 1, 4, 2, 1, 2, 10]
def baseStart_1500008 : Nat := 118140960795 + 1500008 * 2 ^ 59
def prefixEnd_1500008 : Nat := 4983230072969 + 3 ^ 40 * 1500008 * 2
def baseEnd_1500008 : Nat := 19017903446653640629669

theorem tailTrace_1500008 : CollatzResearch.WordTrace tailWord_1500008 prefixEnd_1500008 19017903446653640629669 := by
  unfold tailWord_1500008
  simp only [CollatzResearch.WordTrace]
  refine ⟨27354893174867335907950339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36473190899823114543933785 27354893174867335907950339)
  ·
    refine ⟨41032339762301003861925509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27354893174867335907950339 41032339762301003861925509)
    ·
      refine ⟨7693563705431438224111033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41032339762301003861925509 7693563705431438224111033)
      ·
        refine ⟨5770172779073578668083275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7693563705431438224111033 5770172779073578668083275)
        ·
          refine ⟨8655259168610368002124913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5770172779073578668083275 8655259168610368002124913)
          ·
            refine ⟨6491444376457776001593685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8655259168610368002124913 6491444376457776001593685)
            ·
              refine ⟨19017903446653640629669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 6491444376457776001593685 19017903446653640629669)
              ·
                rfl

theorem cell22_1500008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 10].length) (baseStart_1500008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1500008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1500008 prefixEnd_1500008 := by exact prefixLift 1500008
  have htrace : WordTrace (prefixWord ++ tailWord_1500008) baseStart_1500008 baseEnd_1500008 := by
    simpa [prefixWord, tailWord_1500008, baseEnd_1500008] using wordTrace_append hprefix tailTrace_1500008
  have hstable : (prefixWord ++ tailWord_1500008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1500008).length < 2 ^ (prefixWord ++ tailWord_1500008).sum := by decide
  have hdescent : baseEnd_1500008 < baseStart_1500008 := by decide
  rcases family_descends (prefixWord ++ tailWord_1500008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1500014 : List Nat := [4, 1, 2, 3, 3, 1, 1, 1, 6]
def baseStart_1500014 : Nat := 118140960795 + 1500014 * 2 ^ 59
def prefixEnd_1500014 : Nat := 4983230072969 + 3 ^ 40 * 1500014 * 2
def baseEnd_1500014 : Nat := 171161815660755427117015

theorem tailTrace_1500014 : CollatzResearch.WordTrace tailWord_1500014 prefixEnd_1500014 171161815660755427117015 := by
  unfold tailWord_1500014
  simp only [CollatzResearch.WordTrace]
  refine ⟨6838750648464116855077387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36473336791808623227079397 6838750648464116855077387)
  ·
    refine ⟨10258125972696175282616081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6838750648464116855077387 10258125972696175282616081)
    ·
      refine ⟨7693594479522131461962061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10258125972696175282616081 7693594479522131461962061)
      ·
        refine ⟨2885097929820799298235773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7693594479522131461962061 2885097929820799298235773)
        ·
          refine ⟨1081911723682799736838415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2885097929820799298235773 1081911723682799736838415)
          ·
            refine ⟨1622867585524199605257623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1081911723682799736838415 1622867585524199605257623)
            ·
              refine ⟨2434301378286299407886435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1622867585524199605257623 2434301378286299407886435)
              ·
                refine ⟨3651452067429449111829653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2434301378286299407886435 3651452067429449111829653)
                ·
                  refine ⟨171161815660755427117015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3651452067429449111829653 171161815660755427117015)
                  ·
                    rfl

theorem cell22_1500014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 1, 1, 6].length) (baseStart_1500014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1500014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1500014 prefixEnd_1500014 := by exact prefixLift 1500014
  have htrace : WordTrace (prefixWord ++ tailWord_1500014) baseStart_1500014 baseEnd_1500014 := by
    simpa [prefixWord, tailWord_1500014, baseEnd_1500014] using wordTrace_append hprefix tailTrace_1500014
  have hstable : (prefixWord ++ tailWord_1500014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1500014).length < 2 ^ (prefixWord ++ tailWord_1500014).sum := by decide
  have hdescent : baseEnd_1500014 < baseStart_1500014 := by decide
  rcases family_descends (prefixWord ++ tailWord_1500014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1500057 : List Nat := [1, 2, 1, 2, 1, 3, 1, 7, 1, 3]
def baseStart_1500057 : Nat := 118140960795 + 1500057 * 2 ^ 59
def prefixEnd_1500057 : Nat := 4983230072969 + 3 ^ 40 * 1500057 * 2
def baseEnd_1500057 : Nat := 513500166761028502525913

theorem tailTrace_1500057 : CollatzResearch.WordTrace tailWord_1500057 prefixEnd_1500057 513500166761028502525913 := by
  unfold tailWord_1500057
  simp only [CollatzResearch.WordTrace]
  refine ⟨54711573526557153184434425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36474382351038102122956283 54711573526557153184434425)
  ·
    refine ⟨41033680144917864888325819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54711573526557153184434425 41033680144917864888325819)
    ·
      refine ⟨61550520217376797332488729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41033680144917864888325819 61550520217376797332488729)
      ·
        refine ⟨46162890163032597999366547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61550520217376797332488729 46162890163032597999366547)
        ·
          refine ⟨69244335244548896999049821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46162890163032597999366547 69244335244548896999049821)
          ·
            refine ⟨25966625716705836374643683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69244335244548896999049821 25966625716705836374643683)
            ·
              refine ⟨38949938575058754561965525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25966625716705836374643683 38949938575058754561965525)
              ·
                refine ⟨912889185352939560046067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 38949938575058754561965525 912889185352939560046067)
                ·
                  refine ⟨1369333778029409340069101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 912889185352939560046067 1369333778029409340069101)
                  ·
                    refine ⟨513500166761028502525913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1369333778029409340069101 513500166761028502525913)
                    ·
                      rfl

theorem cell22_1500057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 7, 1, 3].length) (baseStart_1500057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1500057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1500057 prefixEnd_1500057 := by exact prefixLift 1500057
  have htrace : WordTrace (prefixWord ++ tailWord_1500057) baseStart_1500057 baseEnd_1500057 := by
    simpa [prefixWord, tailWord_1500057, baseEnd_1500057] using wordTrace_append hprefix tailTrace_1500057
  have hstable : (prefixWord ++ tailWord_1500057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1500057).length < 2 ^ (prefixWord ++ tailWord_1500057).sum := by decide
  have hdescent : baseEnd_1500057 < baseStart_1500057 := by decide
  rcases family_descends (prefixWord ++ tailWord_1500057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1500085 : List Nat := [1, 3, 3, 2, 1, 1, 3, 1, 2, 5]
def baseStart_1500085 : Nat := 118140960795 + 1500085 * 2 ^ 59
def prefixEnd_1500085 : Nat := 4983230072969 + 3 ^ 40 * 1500085 * 2
def baseEnd_1500085 : Nat := 513509751733245762825827

theorem tailTrace_1500085 : CollatzResearch.WordTrace tailWord_1500085 prefixEnd_1500085 513509751733245762825827 := by
  unfold tailWord_1500085
  simp only [CollatzResearch.WordTrace]
  refine ⟨54712594770455713966453709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36475063180303809310969139 54712594770455713966453709)
  ·
    refine ⟨20517223038920892737420141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54712594770455713966453709 20517223038920892737420141)
    ·
      refine ⟨7693958639595334776532553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20517223038920892737420141 7693958639595334776532553)
      ·
        refine ⟨5770468979696501082399415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7693958639595334776532553 5770468979696501082399415)
        ·
          refine ⟨8655703469544751623599123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5770468979696501082399415 8655703469544751623599123)
          ·
            refine ⟨12983555204317127435398685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8655703469544751623599123 12983555204317127435398685)
            ·
              refine ⟨4868833201618922788274507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12983555204317127435398685 4868833201618922788274507)
              ·
                refine ⟨7303249802428384182411761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4868833201618922788274507 7303249802428384182411761)
                ·
                  refine ⟨5477437351821288136808821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7303249802428384182411761 5477437351821288136808821)
                  ·
                    refine ⟨513509751733245762825827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5477437351821288136808821 513509751733245762825827)
                    ·
                      rfl

theorem cell22_1500085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 1, 2, 5].length) (baseStart_1500085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1500085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1500085 prefixEnd_1500085 := by exact prefixLift 1500085
  have htrace : WordTrace (prefixWord ++ tailWord_1500085) baseStart_1500085 baseEnd_1500085 := by
    simpa [prefixWord, tailWord_1500085, baseEnd_1500085] using wordTrace_append hprefix tailTrace_1500085
  have hstable : (prefixWord ++ tailWord_1500085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1500085).length < 2 ^ (prefixWord ++ tailWord_1500085).sum := by decide
  have hdescent : baseEnd_1500085 < baseStart_1500085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1500085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1500145 : List Nat := [1, 2, 2, 2, 4, 1, 1, 2, 1, 6]
def baseStart_1500145 : Nat := 118140960795 + 1500145 * 2 ^ 59
def prefixEnd_1500145 : Nat := 4983230072969 + 3 ^ 40 * 1500145 * 2
def baseEnd_1500145 : Nat := 513530290959425606325643

theorem tailTrace_1500145 : CollatzResearch.WordTrace tailWord_1500145 prefixEnd_1500145 513530290959425606325643 := by
  unfold tailWord_1500145
  simp only [CollatzResearch.WordTrace]
  refine ⟨54714783150238344213637889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36476522100158896142425259 54714783150238344213637889)
  ·
    refine ⟨41036087362678758160228417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54714783150238344213637889 41036087362678758160228417)
    ·
      refine ⟨30777065522009068620171313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41036087362678758160228417 30777065522009068620171313)
      ·
        refine ⟨23082799141506801465128485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30777065522009068620171313 23082799141506801465128485)
        ·
          refine ⟨4328024839032525274711591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23082799141506801465128485 4328024839032525274711591)
          ·
            refine ⟨6492037258548787912067387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4328024839032525274711591 6492037258548787912067387)
            ·
              refine ⟨9738055887823181868101081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6492037258548787912067387 9738055887823181868101081)
              ·
                refine ⟨7303541915867386401075811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9738055887823181868101081 7303541915867386401075811)
                ·
                  refine ⟨10955312873801079601613717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7303541915867386401075811 10955312873801079601613717)
                  ·
                    refine ⟨513530290959425606325643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10955312873801079601613717 513530290959425606325643)
                    ·
                      rfl

theorem cell22_1500145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 2, 1, 6].length) (baseStart_1500145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1500145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1500145 prefixEnd_1500145 := by exact prefixLift 1500145
  have htrace : WordTrace (prefixWord ++ tailWord_1500145) baseStart_1500145 baseEnd_1500145 := by
    simpa [prefixWord, tailWord_1500145, baseEnd_1500145] using wordTrace_append hprefix tailTrace_1500145
  have hstable : (prefixWord ++ tailWord_1500145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1500145).length < 2 ^ (prefixWord ++ tailWord_1500145).sum := by decide
  have hdescent : baseEnd_1500145 < baseStart_1500145 := by decide
  rcases family_descends (prefixWord ++ tailWord_1500145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1500235 : List Nat := [1, 1, 1, 1, 3, 1, 2, 1, 7, 4]
def baseStart_1500235 : Nat := 118140960795 + 1500235 * 2 ^ 59
def prefixEnd_1500235 : Nat := 4983230072969 + 3 ^ 40 * 1500235 * 2
def baseEnd_1500235 : Nat := 513561099798695371575367

theorem tailTrace_1500235 : CollatzResearch.WordTrace tailWord_1500235 prefixEnd_1500235 513561099798695371575367 := by
  unfold tailWord_1500235
  simp only [CollatzResearch.WordTrace]
  refine ⟨54718065719912289584414159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36478710479941526389609439 54718065719912289584414159)
  ·
    refine ⟨82077098579868434376621239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54718065719912289584414159 82077098579868434376621239)
    ·
      refine ⟨123115647869802651564931859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82077098579868434376621239 123115647869802651564931859)
      ·
        refine ⟨184673471804703977347397789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123115647869802651564931859 184673471804703977347397789)
        ·
          refine ⟨69252551926763991505274171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 184673471804703977347397789 69252551926763991505274171)
          ·
            refine ⟨103878827890145987257911257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69252551926763991505274171 103878827890145987257911257)
            ·
              refine ⟨77909120917609490443433443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103878827890145987257911257 77909120917609490443433443)
              ·
                refine ⟨116863681376414235665150165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77909120917609490443433443 116863681376414235665150165)
                ·
                  refine ⟨2738992532259708648401957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 116863681376414235665150165 2738992532259708648401957)
                  ·
                    refine ⟨513561099798695371575367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2738992532259708648401957 513561099798695371575367)
                    ·
                      rfl

theorem cell22_1500235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 7, 4].length) (baseStart_1500235 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1500235 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1500235 prefixEnd_1500235 := by exact prefixLift 1500235
  have htrace : WordTrace (prefixWord ++ tailWord_1500235) baseStart_1500235 baseEnd_1500235 := by
    simpa [prefixWord, tailWord_1500235, baseEnd_1500235] using wordTrace_append hprefix tailTrace_1500235
  have hstable : (prefixWord ++ tailWord_1500235).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1500235).length < 2 ^ (prefixWord ++ tailWord_1500235).sum := by decide
  have hdescent : baseEnd_1500235 < baseStart_1500235 := by decide
  rcases family_descends (prefixWord ++ tailWord_1500235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1500252 : List Nat := [2, 2, 4, 1, 1, 1, 1, 1, 5, 4]
def baseStart_1500252 : Nat := 118140960795 + 1500252 * 2 ^ 59
def prefixEnd_1500252 : Nat := 4983230072969 + 3 ^ 40 * 1500252 * 2
def baseEnd_1500252 : Nat := 513566919246112993900315

theorem tailTrace_1500252 : CollatzResearch.WordTrace tailWord_1500252 prefixEnd_1500252 513566919246112993900315 := by
  unfold tailWord_1500252
  simp only [CollatzResearch.WordTrace]
  refine ⟨27359342880425350743891505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36479123840567134325188673 27359342880425350743891505)
  ·
    refine ⟨20519507160319013057918629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27359342880425350743891505 20519507160319013057918629)
    ·
      refine ⟨3847407592559814948359743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20519507160319013057918629 3847407592559814948359743)
      ·
        refine ⟨5771111388839722422539615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3847407592559814948359743 5771111388839722422539615)
        ·
          refine ⟨8656667083259583633809423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5771111388839722422539615 8656667083259583633809423)
          ·
            refine ⟨12985000624889375450714135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8656667083259583633809423 12985000624889375450714135)
            ·
              refine ⟨19477500937334063176071203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12985000624889375450714135 19477500937334063176071203)
              ·
                refine ⟨29216251406001094764106805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19477500937334063176071203 29216251406001094764106805)
                ·
                  refine ⟨2739023569312602634135013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29216251406001094764106805 2739023569312602634135013)
                  ·
                    refine ⟨513566919246112993900315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2739023569312602634135013 513566919246112993900315)
                    ·
                      rfl

theorem cell22_1500252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_1500252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1500252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1500252 prefixEnd_1500252 := by exact prefixLift 1500252
  have htrace : WordTrace (prefixWord ++ tailWord_1500252) baseStart_1500252 baseEnd_1500252 := by
    simpa [prefixWord, tailWord_1500252, baseEnd_1500252] using wordTrace_append hprefix tailTrace_1500252
  have hstable : (prefixWord ++ tailWord_1500252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1500252).length < 2 ^ (prefixWord ++ tailWord_1500252).sum := by decide
  have hdescent : baseEnd_1500252 < baseStart_1500252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1500252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1500284 : List Nat := [2, 2, 2, 1, 1, 3, 4, 3, 4]
def baseStart_1500284 : Nat := 118140960795 + 1500284 * 2 ^ 59
def prefixEnd_1500284 : Nat := 4983230072969 + 3 ^ 40 * 1500284 * 2
def baseEnd_1500284 : Nat := 171192624500025192366739

theorem tailTrace_1500284 : CollatzResearch.WordTrace tailWord_1500284 prefixEnd_1500284 171192624500025192366739 := by
  unfold tailWord_1500284
  simp only [CollatzResearch.WordTrace]
  refine ⟨27359926448367385476473953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36479901931156513968631937 27359926448367385476473953)
  ·
    refine ⟨20519944836275539107355465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27359926448367385476473953 20519944836275539107355465)
    ·
      refine ⟨15389958627206654330516599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20519944836275539107355465 15389958627206654330516599)
      ·
        refine ⟨23084937940809981495774899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15389958627206654330516599 23084937940809981495774899)
        ·
          refine ⟨34627406911214972243662349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23084937940809981495774899 34627406911214972243662349)
          ·
            refine ⟨12985277591705614591373381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34627406911214972243662349 12985277591705614591373381)
            ·
              refine ⟨2434739548444802735882509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12985277591705614591373381 2434739548444802735882509)
              ·
                refine ⟨913027330666801025955941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2434739548444802735882509 913027330666801025955941)
                ·
                  refine ⟨171192624500025192366739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 913027330666801025955941 171192624500025192366739)
                  ·
                    rfl

theorem cell22_1500284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 4, 3, 4].length) (baseStart_1500284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1500284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1500284 prefixEnd_1500284 := by exact prefixLift 1500284
  have htrace : WordTrace (prefixWord ++ tailWord_1500284) baseStart_1500284 baseEnd_1500284 := by
    simpa [prefixWord, tailWord_1500284, baseEnd_1500284] using wordTrace_append hprefix tailTrace_1500284
  have hstable : (prefixWord ++ tailWord_1500284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1500284).length < 2 ^ (prefixWord ++ tailWord_1500284).sum := by decide
  have hdescent : baseEnd_1500284 < baseStart_1500284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1500284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1500357 : List Nat := [1, 3, 1, 1, 1, 1, 3, 6, 5]
def baseStart_1500357 : Nat := 118140960795 + 1500357 * 2 ^ 59
def prefixEnd_1500357 : Nat := 4983230072969 + 3 ^ 40 * 1500357 * 2
def baseEnd_1500357 : Nat := 171200954297309240008331

theorem tailTrace_1500357 : CollatzResearch.WordTrace tailWord_1500357 prefixEnd_1500357 171200954297309240008331 := by
  unfold tailWord_1500357
  simp only [CollatzResearch.WordTrace]
  refine ⟨54722515425470304420355325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36481676950313536280236883 54722515425470304420355325)
  ·
    refine ⟨20520943284551364157633247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54722515425470304420355325 20520943284551364157633247)
    ·
      refine ⟨30781414926827046236449871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20520943284551364157633247 30781414926827046236449871)
      ·
        refine ⟨46172122390240569354674807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30781414926827046236449871 46172122390240569354674807)
        ·
          refine ⟨69258183585360854032012211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46172122390240569354674807 69258183585360854032012211)
          ·
            refine ⟨103887275378041281048018317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69258183585360854032012211 103887275378041281048018317)
            ·
              refine ⟨38957728266765480393006869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103887275378041281048018317 38957728266765480393006869)
              ·
                refine ⟨1826143512504631893422197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 38957728266765480393006869 1826143512504631893422197)
                ·
                  refine ⟨171200954297309240008331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1826143512504631893422197 171200954297309240008331)
                  ·
                    rfl

theorem cell22_1500357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 6, 5].length) (baseStart_1500357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1500357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1500357 prefixEnd_1500357 := by exact prefixLift 1500357
  have htrace : WordTrace (prefixWord ++ tailWord_1500357) baseStart_1500357 baseEnd_1500357 := by
    simpa [prefixWord, tailWord_1500357, baseEnd_1500357] using wordTrace_append hprefix tailTrace_1500357
  have hstable : (prefixWord ++ tailWord_1500357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1500357).length < 2 ^ (prefixWord ++ tailWord_1500357).sum := by decide
  have hdescent : baseEnd_1500357 < baseStart_1500357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1500357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1500412 : List Nat := [2, 2, 2, 1, 6, 1, 2, 2, 1, 3]
def baseStart_1500412 : Nat := 118140960795 + 1500412 * 2 ^ 59
def prefixEnd_1500412 : Nat := 4983230072969 + 3 ^ 40 * 1500412 * 2
def baseEnd_1500412 : Nat := 513621690515925909899825

theorem tailTrace_1500412 : CollatzResearch.WordTrace tailWord_1500412 prefixEnd_1500412 513621690515925909899825 := by
  unfold tailWord_1500412
  simp only [CollatzResearch.WordTrace]
  refine ⟨27362260720135524406803745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36483014293514032542404993 27362260720135524406803745)
  ·
    refine ⟨20521695540101643305102809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27362260720135524406803745 20521695540101643305102809)
    ·
      refine ⟨15391271655076232478827107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20521695540101643305102809 15391271655076232478827107)
      ·
        refine ⟨23086907482614348718240661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15391271655076232478827107 23086907482614348718240661)
        ·
          refine ⟨1082198788247547596167531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 23086907482614348718240661 1082198788247547596167531)
          ·
            refine ⟨1623298182371321394251297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1082198788247547596167531 1623298182371321394251297)
            ·
              refine ⟨1217473636778491045688473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1623298182371321394251297 1217473636778491045688473)
              ·
                refine ⟨913105227583868284266355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1217473636778491045688473 913105227583868284266355)
                ·
                  refine ⟨1369657841375802426399533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 913105227583868284266355 1369657841375802426399533)
                  ·
                    refine ⟨513621690515925909899825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1369657841375802426399533 513621690515925909899825)
                    ·
                      rfl

theorem cell22_1500412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 2, 2, 1, 3].length) (baseStart_1500412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1500412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1500412 prefixEnd_1500412 := by exact prefixLift 1500412
  have htrace : WordTrace (prefixWord ++ tailWord_1500412) baseStart_1500412 baseEnd_1500412 := by
    simpa [prefixWord, tailWord_1500412, baseEnd_1500412] using wordTrace_append hprefix tailTrace_1500412
  have hstable : (prefixWord ++ tailWord_1500412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1500412).length < 2 ^ (prefixWord ++ tailWord_1500412).sum := by decide
  have hdescent : baseEnd_1500412 < baseStart_1500412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1500412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1500530 : List Nat := [3, 2, 1, 2, 1, 2, 5, 2, 1, 3]
def baseStart_1500530 : Nat := 118140960795 + 1500530 * 2 ^ 59
def prefixEnd_1500530 : Nat := 4983230072969 + 3 ^ 40 * 1500530 * 2
def baseEnd_1500530 : Nat := 513662084327412935449463

theorem tailTrace_1500530 : CollatzResearch.WordTrace tailWord_1500530 prefixEnd_1500530 513662084327412935449463 := by
  unfold tailWord_1500530
  simp only [CollatzResearch.WordTrace]
  refine ⟨13682206313460888741600761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36485883502562369977602029 13682206313460888741600761)
  ·
    refine ⟨10261654735095666556200571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13682206313460888741600761 10261654735095666556200571)
    ·
      refine ⟨15392482102643499834300857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10261654735095666556200571 15392482102643499834300857)
      ·
        refine ⟨11544361576982624875725643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15392482102643499834300857 11544361576982624875725643)
        ·
          refine ⟨17316542365473937313588465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11544361576982624875725643 17316542365473937313588465)
          ·
            refine ⟨12987406774105452985191349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17316542365473937313588465 12987406774105452985191349)
            ·
              refine ⟨1217569385072386217361689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12987406774105452985191349 1217569385072386217361689)
              ·
                refine ⟨913177038804289663021267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1217569385072386217361689 913177038804289663021267)
                ·
                  refine ⟨1369765558206434494531901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 913177038804289663021267 1369765558206434494531901)
                  ·
                    refine ⟨513662084327412935449463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1369765558206434494531901 513662084327412935449463)
                    ·
                      rfl

theorem cell22_1500530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 5, 2, 1, 3].length) (baseStart_1500530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1500530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1500530 prefixEnd_1500530 := by exact prefixLift 1500530
  have htrace : WordTrace (prefixWord ++ tailWord_1500530) baseStart_1500530 baseEnd_1500530 := by
    simpa [prefixWord, tailWord_1500530, baseEnd_1500530] using wordTrace_append hprefix tailTrace_1500530
  have hstable : (prefixWord ++ tailWord_1500530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1500530).length < 2 ^ (prefixWord ++ tailWord_1500530).sum := by decide
  have hdescent : baseEnd_1500530 < baseStart_1500530 := by decide
  rcases family_descends (prefixWord ++ tailWord_1500530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1500539 : List Nat := [1, 1, 1, 1, 1, 6, 2, 2, 3, 4]
def baseStart_1500539 : Nat := 118140960795 + 1500539 * 2 ^ 59
def prefixEnd_1500539 : Nat := 4983230072969 + 3 ^ 40 * 1500539 * 2
def baseEnd_1500539 : Nat := 513665165211339911974435

theorem tailTrace_1500539 : CollatzResearch.WordTrace tailWord_1500539 prefixEnd_1500539 513665165211339911974435 := by
  unfold tailWord_1500539
  simp only [CollatzResearch.WordTrace]
  refine ⟨54729153510810949503480671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36486102340540633002320447 54729153510810949503480671)
  ·
    refine ⟨82093730266216424255221007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54729153510810949503480671 82093730266216424255221007)
    ·
      refine ⟨123140595399324636382831511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82093730266216424255221007 123140595399324636382831511)
      ·
        refine ⟨184710893098986954574247267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123140595399324636382831511 184710893098986954574247267)
        ·
          refine ⟨277066339648480431861370901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184710893098986954574247267 277066339648480431861370901)
          ·
            refine ⟨12987484671022520243501761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 277066339648480431861370901 12987484671022520243501761)
            ·
              refine ⟨9740613503266890182626321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12987484671022520243501761 9740613503266890182626321)
              ·
                refine ⟨7305460127450167636969741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9740613503266890182626321 7305460127450167636969741)
                ·
                  refine ⟨2739547547793812863863653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7305460127450167636969741 2739547547793812863863653)
                  ·
                    refine ⟨513665165211339911974435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2739547547793812863863653 513665165211339911974435)
                    ·
                      rfl

theorem cell22_1500539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 2, 3, 4].length) (baseStart_1500539 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1500539 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1500539 prefixEnd_1500539 := by exact prefixLift 1500539
  have htrace : WordTrace (prefixWord ++ tailWord_1500539) baseStart_1500539 baseEnd_1500539 := by
    simpa [prefixWord, tailWord_1500539, baseEnd_1500539] using wordTrace_append hprefix tailTrace_1500539
  have hstable : (prefixWord ++ tailWord_1500539).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1500539).length < 2 ^ (prefixWord ++ tailWord_1500539).sum := by decide
  have hdescent : baseEnd_1500539 < baseStart_1500539 := by decide
  rcases family_descends (prefixWord ++ tailWord_1500539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1500569 : List Nat := [1, 2, 1, 2, 1, 5, 1, 1, 3, 5]
def baseStart_1500569 : Nat := 118140960795 + 1500569 * 2 ^ 59
def prefixEnd_1500569 : Nat := 4983230072969 + 3 ^ 40 * 1500569 * 2
def baseEnd_1500569 : Nat := 513675434824429833724343

theorem tailTrace_1500569 : CollatzResearch.WordTrace tailWord_1500569 prefixEnd_1500569 513675434824429833724343 := by
  unfold tailWord_1500569
  simp only [CollatzResearch.WordTrace]
  refine ⟨54730247700702264627072761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36486831800468176418048507 54730247700702264627072761)
  ·
    refine ⟨41047685775526698470304571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54730247700702264627072761 41047685775526698470304571)
    ·
      refine ⟨61571528663290047705456857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41047685775526698470304571 61571528663290047705456857)
      ·
        refine ⟨46178646497467535779092643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61571528663290047705456857 46178646497467535779092643)
        ·
          refine ⟨69267969746201303668638965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46178646497467535779092643 69267969746201303668638965)
          ·
            refine ⟨6493872163706372218934903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 69267969746201303668638965 6493872163706372218934903)
            ·
              refine ⟨9740808245559558328402355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6493872163706372218934903 9740808245559558328402355)
              ·
                refine ⟨14611212368339337492603533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9740808245559558328402355 14611212368339337492603533)
                ·
                  refine ⟨5479204638127251559726325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14611212368339337492603533 5479204638127251559726325)
                  ·
                    refine ⟨513675434824429833724343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5479204638127251559726325 513675434824429833724343)
                    ·
                      rfl

theorem cell22_1500569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 1, 3, 5].length) (baseStart_1500569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1500569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1500569 prefixEnd_1500569 := by exact prefixLift 1500569
  have htrace : WordTrace (prefixWord ++ tailWord_1500569) baseStart_1500569 baseEnd_1500569 := by
    simpa [prefixWord, tailWord_1500569, baseEnd_1500569] using wordTrace_append hprefix tailTrace_1500569
  have hstable : (prefixWord ++ tailWord_1500569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1500569).length < 2 ^ (prefixWord ++ tailWord_1500569).sum := by decide
  have hdescent : baseEnd_1500569 < baseStart_1500569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1500569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1500588 : List Nat := [2, 2, 1, 1, 1, 1, 8, 2, 4]
def baseStart_1500588 : Nat := 118140960795 + 1500588 * 2 ^ 59
def prefixEnd_1500588 : Nat := 4983230072969 + 3 ^ 40 * 1500588 * 2
def baseEnd_1500588 : Nat := 171227312970906705833095

theorem tailTrace_1500588 : CollatzResearch.WordTrace tailWord_1500588 prefixEnd_1500588 171227312970906705833095 := by
  unfold tailWord_1500588
  simp only [CollatzResearch.WordTrace]
  refine ⟨27365470343816715436007209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36487293791755620581342945 27365470343816715436007209)
  ·
    refine ⟨20524102757862536577005407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27365470343816715436007209 20524102757862536577005407)
    ·
      refine ⟨30786154136793804865508111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20524102757862536577005407 30786154136793804865508111)
      ·
        refine ⟨46179231205190707298262167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30786154136793804865508111 46179231205190707298262167)
        ·
          refine ⟨69268846807786060947393251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46179231205190707298262167 69268846807786060947393251)
          ·
            refine ⟨103903270211679091421089877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69268846807786060947393251 103903270211679091421089877)
            ·
              refine ⟨1217616447793114352590897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 103903270211679091421089877 1217616447793114352590897)
              ·
                refine ⟨913212335844835764443173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1217616447793114352590897 913212335844835764443173)
                ·
                  refine ⟨171227312970906705833095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 913212335844835764443173 171227312970906705833095)
                  ·
                    rfl

theorem cell22_1500588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 8, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 8, 2, 4].length) (baseStart_1500588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1500588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1500588 prefixEnd_1500588 := by exact prefixLift 1500588
  have htrace : WordTrace (prefixWord ++ tailWord_1500588) baseStart_1500588 baseEnd_1500588 := by
    simpa [prefixWord, tailWord_1500588, baseEnd_1500588] using wordTrace_append hprefix tailTrace_1500588
  have hstable : (prefixWord ++ tailWord_1500588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1500588).length < 2 ^ (prefixWord ++ tailWord_1500588).sum := by decide
  have hdescent : baseEnd_1500588 < baseStart_1500588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1500588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1500616 : List Nat := [2, 1, 3, 1, 3, 1, 5, 6]
def baseStart_1500616 : Nat := 118140960795 + 1500616 * 2 ^ 59
def prefixEnd_1500616 : Nat := 4983230072969 + 3 ^ 40 * 1500616 * 2
def baseEnd_1500616 : Nat := 57076835987215264199911

theorem tailTrace_1500616 : CollatzResearch.WordTrace tailWord_1500616 prefixEnd_1500616 57076835987215264199911 := by
  unfold tailWord_1500616
  simp only [CollatzResearch.WordTrace]
  refine ⟨27365980965765995827016851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36487974621021327769355801 27365980965765995827016851)
  ·
    refine ⟨41048971448648993740525277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27365980965765995827016851 41048971448648993740525277)
    ·
      refine ⟨15393364293243372652696979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41048971448648993740525277 15393364293243372652696979)
      ·
        refine ⟨23090046439865058979045469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15393364293243372652696979 23090046439865058979045469)
        ·
          refine ⟨8658767414949397117142051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23090046439865058979045469 8658767414949397117142051)
          ·
            refine ⟨12988151122424095675713077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8658767414949397117142051 12988151122424095675713077)
            ·
              refine ⟨1217639167727258969598101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12988151122424095675713077 1217639167727258969598101)
              ·
                refine ⟨57076835987215264199911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1217639167727258969598101 57076835987215264199911)
                ·
                  rfl

theorem cell22_1500616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 5, 6].length) (baseStart_1500616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1500616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1500616 prefixEnd_1500616 := by exact prefixLift 1500616
  have htrace : WordTrace (prefixWord ++ tailWord_1500616) baseStart_1500616 baseEnd_1500616 := by
    simpa [prefixWord, tailWord_1500616, baseEnd_1500616] using wordTrace_append hprefix tailTrace_1500616
  have hstable : (prefixWord ++ tailWord_1500616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1500616).length < 2 ^ (prefixWord ++ tailWord_1500616).sum := by decide
  have hdescent : baseEnd_1500616 < baseStart_1500616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1500616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1500618 : List Nat := [3, 1, 2, 1, 2, 5, 1, 1, 2, 4]
def baseStart_1500618 : Nat := 118140960795 + 1500618 * 2 ^ 59
def prefixEnd_1500618 : Nat := 4983230072969 + 3 ^ 40 * 1500618 * 2
def baseEnd_1500618 : Nat := 513692208525810039249193

theorem tailTrace_1500618 : CollatzResearch.WordTrace tailWord_1500618 prefixEnd_1500618 513692208525810039249193 := by
  unfold tailWord_1500618
  simp only [CollatzResearch.WordTrace]
  refine ⟨13683008719381186498901627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36488023251683163997071005 13683008719381186498901627)
  ·
    refine ⟨20524513079071779748352441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13683008719381186498901627 20524513079071779748352441)
    ·
      refine ⟨15393384809303834811264331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20524513079071779748352441 15393384809303834811264331)
      ·
        refine ⟨23090077213955752216896497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15393384809303834811264331 23090077213955752216896497)
        ·
          refine ⟨17317557910466814162672373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23090077213955752216896497 17317557910466814162672373)
          ·
            refine ⟨1623521054106263827750535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17317557910466814162672373 1623521054106263827750535)
            ·
              refine ⟨2435281581159395741625803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1623521054106263827750535 2435281581159395741625803)
              ·
                refine ⟨3652922371739093612438705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2435281581159395741625803 3652922371739093612438705)
                ·
                  refine ⟨2739691778804320209329029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3652922371739093612438705 2739691778804320209329029)
                  ·
                    refine ⟨513692208525810039249193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2739691778804320209329029 513692208525810039249193)
                    ·
                      rfl

theorem cell22_1500618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 1, 1, 2, 4].length) (baseStart_1500618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1500618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1500618 prefixEnd_1500618 := by exact prefixLift 1500618
  have htrace : WordTrace (prefixWord ++ tailWord_1500618) baseStart_1500618 baseEnd_1500618 := by
    simpa [prefixWord, tailWord_1500618, baseEnd_1500618] using wordTrace_append hprefix tailTrace_1500618
  have hstable : (prefixWord ++ tailWord_1500618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1500618).length < 2 ^ (prefixWord ++ tailWord_1500618).sum := by decide
  have hdescent : baseEnd_1500618 < baseStart_1500618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1500618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1500648 : List Nat := [2, 1, 4, 1, 1, 2, 4, 1, 3, 3]
def baseStart_1500648 : Nat := 118140960795 + 1500648 * 2 ^ 59
def prefixEnd_1500648 : Nat := 4983230072969 + 3 ^ 40 * 1500648 * 2
def baseEnd_1500648 : Nat := 513702478138899960999101

theorem tailTrace_1500648 : CollatzResearch.WordTrace tailWord_1500648 prefixEnd_1500648 513702478138899960999101 := by
  unfold tailWord_1500648
  simp only [CollatzResearch.WordTrace]
  refine ⟨27366564533708030559599299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36488752711610707412799065 27366564533708030559599299)
  ·
    refine ⟨41049846800562045839398949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27366564533708030559599299 41049846800562045839398949)
    ·
      refine ⟨7696846275105383594887303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41049846800562045839398949 7696846275105383594887303)
      ·
        refine ⟨11545269412658075392330955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7696846275105383594887303 11545269412658075392330955)
        ·
          refine ⟨17317904118987113088496433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11545269412658075392330955 17317904118987113088496433)
          ·
            refine ⟨12988428089240334816372325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17317904118987113088496433 12988428089240334816372325)
            ·
              refine ⟨2435330266732562778069811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12988428089240334816372325 2435330266732562778069811)
              ·
                refine ⟨3652995400098844167104717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2435330266732562778069811 3652995400098844167104717)
                ·
                  refine ⟨1369873275037066562664269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3652995400098844167104717 1369873275037066562664269)
                  ·
                    refine ⟨513702478138899960999101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1369873275037066562664269 513702478138899960999101)
                    ·
                      rfl

theorem cell22_1500648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 4, 1, 3, 3].length) (baseStart_1500648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1500648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1500648 prefixEnd_1500648 := by exact prefixLift 1500648
  have htrace : WordTrace (prefixWord ++ tailWord_1500648) baseStart_1500648 baseEnd_1500648 := by
    simpa [prefixWord, tailWord_1500648, baseEnd_1500648] using wordTrace_append hprefix tailTrace_1500648
  have hstable : (prefixWord ++ tailWord_1500648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1500648).length < 2 ^ (prefixWord ++ tailWord_1500648).sum := by decide
  have hdescent : baseEnd_1500648 < baseStart_1500648 := by decide
  rcases family_descends (prefixWord ++ tailWord_1500648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1500659 : List Nat := [1, 1, 1, 2, 2, 2, 2, 3, 1, 7]
def baseStart_1500659 : Nat := 118140960795 + 1500659 * 2 ^ 59
def prefixEnd_1500659 : Nat := 4983230072969 + 3 ^ 40 * 1500659 * 2
def baseEnd_1500659 : Nat := 513706243663699598974067

theorem tailTrace_1500659 : CollatzResearch.WordTrace tailWord_1500659 prefixEnd_1500659 513706243663699598974067 := by
  unfold tailWord_1500659
  simp only [CollatzResearch.WordTrace]
  refine ⟨54733530270376209997849031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36489020180250806665232687 54733530270376209997849031)
  ·
    refine ⟨82100295405564314996773547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54733530270376209997849031 82100295405564314996773547)
    ·
      refine ⟨123150443108346472495160321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82100295405564314996773547 123150443108346472495160321)
      ·
        refine ⟨92362832331259854371370241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123150443108346472495160321 92362832331259854371370241)
        ·
          refine ⟨69272124248444890778527681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92362832331259854371370241 69272124248444890778527681)
          ·
            refine ⟨51954093186333668083895761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69272124248444890778527681 51954093186333668083895761)
            ·
              refine ⟨38965569889750251062921821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51954093186333668083895761 38965569889750251062921821)
              ·
                refine ⟨14612088708656344148595683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38965569889750251062921821 14612088708656344148595683)
                ·
                  refine ⟨21918133062984516222893525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14612088708656344148595683 21918133062984516222893525)
                  ·
                    refine ⟨513706243663699598974067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21918133062984516222893525 513706243663699598974067)
                    ·
                      rfl

theorem cell22_1500659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 1, 7].length) (baseStart_1500659 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1500659 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1500659 prefixEnd_1500659 := by exact prefixLift 1500659
  have htrace : WordTrace (prefixWord ++ tailWord_1500659) baseStart_1500659 baseEnd_1500659 := by
    simpa [prefixWord, tailWord_1500659, baseEnd_1500659] using wordTrace_append hprefix tailTrace_1500659
  have hstable : (prefixWord ++ tailWord_1500659).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1500659).length < 2 ^ (prefixWord ++ tailWord_1500659).sum := by decide
  have hdescent : baseEnd_1500659 < baseStart_1500659 := by decide
  rcases family_descends (prefixWord ++ tailWord_1500659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1500682 : List Nat := [3, 1, 2, 2, 2, 4, 1, 3, 1, 3]
def baseStart_1500682 : Nat := 118140960795 + 1500682 * 2 ^ 59
def prefixEnd_1500682 : Nat := 4983230072969 + 3 ^ 40 * 1500682 * 2
def baseEnd_1500682 : Nat := 513714117033735205648997

theorem tailTrace_1500682 : CollatzResearch.WordTrace tailWord_1500682 prefixEnd_1500682 513714117033735205648997 := by
  unfold tailWord_1500682
  simp only [CollatzResearch.WordTrace]
  refine ⟨13683592287323221231484075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36489579432861923283957533 13683592287323221231484075)
  ·
    refine ⟨20525388430984831847226113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13683592287323221231484075 20525388430984831847226113)
    ·
      refine ⟨15394041323238623885419585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20525388430984831847226113 15394041323238623885419585)
      ·
        refine ⟨11545530992428967914064689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15394041323238623885419585 11545530992428967914064689)
        ·
          refine ⟨8659148244321725935548517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11545530992428967914064689 8659148244321725935548517)
          ·
            refine ⟨1623590295810323612915347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8659148244321725935548517 1623590295810323612915347)
            ·
              refine ⟨2435385443715485419373021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1623590295810323612915347 2435385443715485419373021)
              ·
                refine ⟨913269541393307032264883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2435385443715485419373021 913269541393307032264883)
                ·
                  refine ⟨1369904312089960548397325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 913269541393307032264883 1369904312089960548397325)
                  ·
                    refine ⟨513714117033735205648997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1369904312089960548397325 513714117033735205648997)
                    ·
                      rfl

theorem cell22_1500682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 1, 3, 1, 3].length) (baseStart_1500682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1500682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1500682 prefixEnd_1500682 := by exact prefixLift 1500682
  have htrace : WordTrace (prefixWord ++ tailWord_1500682) baseStart_1500682 baseEnd_1500682 := by
    simpa [prefixWord, tailWord_1500682, baseEnd_1500682] using wordTrace_append hprefix tailTrace_1500682
  have hstable : (prefixWord ++ tailWord_1500682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1500682).length < 2 ^ (prefixWord ++ tailWord_1500682).sum := by decide
  have hdescent : baseEnd_1500682 < baseStart_1500682 := by decide
  rcases family_descends (prefixWord ++ tailWord_1500682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1500712 : List Nat := [2, 1, 5, 2, 2, 2, 2, 1, 5]
def baseStart_1500712 : Nat := 118140960795 + 1500712 * 2 ^ 59
def prefixEnd_1500712 : Nat := 4983230072969 + 3 ^ 40 * 1500712 * 2
def baseEnd_1500712 : Nat := 171241462215608375799635

theorem tailTrace_1500712 : CollatzResearch.WordTrace tailWord_1500712 prefixEnd_1500712 171241462215608375799635 := by
  unfold tailWord_1500712
  simp only [CollatzResearch.WordTrace]
  refine ⟨27367731669592100024764195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36490308892789466699685593 27367731669592100024764195)
  ·
    refine ⟨41051597504388150037146293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27367731669592100024764195 41051597504388150037146293)
    ·
      refine ⟨3848587266036389065982465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 41051597504388150037146293 3848587266036389065982465)
      ·
        refine ⟨2886440449527291799486849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3848587266036389065982465 2886440449527291799486849)
        ·
          refine ⟨2164830337145468849615137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2886440449527291799486849 2164830337145468849615137)
          ·
            refine ⟨1623622752859101637211353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2164830337145468849615137 1623622752859101637211353)
            ·
              refine ⟨1217717064644326227908515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1623622752859101637211353 1217717064644326227908515)
              ·
                refine ⟨1826575596966489341862773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1217717064644326227908515 1826575596966489341862773)
                ·
                  refine ⟨171241462215608375799635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1826575596966489341862773 171241462215608375799635)
                  ·
                    rfl

theorem cell22_1500712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 2, 1, 5].length) (baseStart_1500712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1500712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1500712 prefixEnd_1500712 := by exact prefixLift 1500712
  have htrace : WordTrace (prefixWord ++ tailWord_1500712) baseStart_1500712 baseEnd_1500712 := by
    simpa [prefixWord, tailWord_1500712, baseEnd_1500712] using wordTrace_append hprefix tailTrace_1500712
  have hstable : (prefixWord ++ tailWord_1500712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1500712).length < 2 ^ (prefixWord ++ tailWord_1500712).sum := by decide
  have hdescent : baseEnd_1500712 < baseStart_1500712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1500712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1500721 : List Nat := [1, 2, 2, 3, 1, 1, 1, 5, 1, 5]
def baseStart_1500721 : Nat := 118140960795 + 1500721 * 2 ^ 59
def prefixEnd_1500721 : Nat := 4983230072969 + 3 ^ 40 * 1500721 * 2
def baseEnd_1500721 : Nat := 513727467530752103923877

theorem tailTrace_1500721 : CollatzResearch.WordTrace tailWord_1500721 prefixEnd_1500721 513727467530752103923877 := by
  unfold tailWord_1500721
  simp only [CollatzResearch.WordTrace]
  refine ⟨54735791596151594586606017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36490527730767729724404011 54735791596151594586606017)
  ·
    refine ⟨41051843697113695939954513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54735791596151594586606017 41051843697113695939954513)
    ·
      refine ⟨30788882772835271954965885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41051843697113695939954513 30788882772835271954965885)
      ·
        refine ⟨11545831039813226983112207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30788882772835271954965885 11545831039813226983112207)
        ·
          refine ⟨17318746559719840474668311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11545831039813226983112207 17318746559719840474668311)
          ·
            refine ⟨25978119839579760712002467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17318746559719840474668311 25978119839579760712002467)
            ·
              refine ⟨38967179759369641068003701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25978119839579760712002467 38967179759369641068003701)
              ·
                refine ⟨3653173102440903850125347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38967179759369641068003701 3653173102440903850125347)
                ·
                  refine ⟨5479759653661355775188021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3653173102440903850125347 5479759653661355775188021)
                  ·
                    refine ⟨513727467530752103923877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5479759653661355775188021 513727467530752103923877)
                    ·
                      rfl

theorem cell22_1500721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 5, 1, 5].length) (baseStart_1500721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1500721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1500721 prefixEnd_1500721 := by exact prefixLift 1500721
  have htrace : WordTrace (prefixWord ++ tailWord_1500721) baseStart_1500721 baseEnd_1500721 := by
    simpa [prefixWord, tailWord_1500721, baseEnd_1500721] using wordTrace_append hprefix tailTrace_1500721
  have hstable : (prefixWord ++ tailWord_1500721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1500721).length < 2 ^ (prefixWord ++ tailWord_1500721).sum := by decide
  have hdescent : baseEnd_1500721 < baseStart_1500721 := by decide
  rcases family_descends (prefixWord ++ tailWord_1500721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1500725 : List Nat := [1, 3, 3, 1, 1, 5, 1, 2, 1, 4]
def baseStart_1500725 : Nat := 118140960795 + 1500725 * 2 ^ 59
def prefixEnd_1500725 : Nat := 4983230072969 + 3 ^ 40 * 1500725 * 2
def baseEnd_1500725 : Nat := 513728836812497426823865

theorem tailTrace_1500725 : CollatzResearch.WordTrace tailWord_1500725 prefixEnd_1500725 513728836812497426823865 := by
  unfold tailWord_1500725
  simp only [CollatzResearch.WordTrace]
  refine ⟨54735937488137103269751629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36490624992091402179834419 54735937488137103269751629)
  ·
    refine ⟨20525976558051413726156861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54735937488137103269751629 20525976558051413726156861)
    ·
      refine ⟨7697241209269280147308823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20525976558051413726156861 7697241209269280147308823)
      ·
        refine ⟨11545861813903920220963235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7697241209269280147308823 11545861813903920220963235)
        ·
          refine ⟨17318792720855880331444853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11545861813903920220963235 17318792720855880331444853)
          ·
            refine ⟨1623636817580238781072955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17318792720855880331444853 1623636817580238781072955)
            ·
              refine ⟨2435455226370358171609433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1623636817580238781072955 2435455226370358171609433)
              ·
                refine ⟨1826591419777768628707075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2435455226370358171609433 1826591419777768628707075)
                ·
                  refine ⟨2739887129666652943060613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1826591419777768628707075 2739887129666652943060613)
                  ·
                    refine ⟨513728836812497426823865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2739887129666652943060613 513728836812497426823865)
                    ·
                      rfl

theorem cell22_1500725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 1, 2, 1, 4].length) (baseStart_1500725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1500725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1500725 prefixEnd_1500725 := by exact prefixLift 1500725
  have htrace : WordTrace (prefixWord ++ tailWord_1500725) baseStart_1500725 baseEnd_1500725 := by
    simpa [prefixWord, tailWord_1500725, baseEnd_1500725] using wordTrace_append hprefix tailTrace_1500725
  have hstable : (prefixWord ++ tailWord_1500725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1500725).length < 2 ^ (prefixWord ++ tailWord_1500725).sum := by decide
  have hdescent : baseEnd_1500725 < baseStart_1500725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1500725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1500796 : List Nat := [2, 2, 2, 1, 1, 2, 1, 4, 7]
def baseStart_1500796 : Nat := 118140960795 + 1500796 * 2 ^ 59
def prefixEnd_1500796 : Nat := 4983230072969 + 3 ^ 40 * 1500796 * 2
def baseEnd_1500796 : Nat := 171251047187825636099549

theorem tailTrace_1500796 : CollatzResearch.WordTrace tailWord_1500796 prefixEnd_1500796 171251047187825636099549 := by
  unfold tailWord_1500796
  simp only [CollatzResearch.WordTrace]
  refine ⟨27369263535439941197793121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36492351380586588263724161 27369263535439941197793121)
  ·
    refine ⟨20526947651579955898344841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27369263535439941197793121 20526947651579955898344841)
    ·
      refine ⟨15395210738684966923758631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20526947651579955898344841 15395210738684966923758631)
      ·
        refine ⟨23092816108027450385637947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15395210738684966923758631 23092816108027450385637947)
        ·
          refine ⟨34639224162041175578456921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23092816108027450385637947 34639224162041175578456921)
          ·
            refine ⟨25979418121530881683842691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34639224162041175578456921 25979418121530881683842691)
            ·
              refine ⟨38969127182296322525764037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25979418121530881683842691 38969127182296322525764037)
              ·
                refine ⟨7306711346680560473580757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38969127182296322525764037 7306711346680560473580757)
                ·
                  refine ⟨171251047187825636099549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7306711346680560473580757 171251047187825636099549)
                  ·
                    rfl

theorem cell22_1500796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 4, 7].length) (baseStart_1500796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1500796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1500796 prefixEnd_1500796 := by exact prefixLift 1500796
  have htrace : WordTrace (prefixWord ++ tailWord_1500796) baseStart_1500796 baseEnd_1500796 := by
    simpa [prefixWord, tailWord_1500796, baseEnd_1500796] using wordTrace_append hprefix tailTrace_1500796
  have hstable : (prefixWord ++ tailWord_1500796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1500796).length < 2 ^ (prefixWord ++ tailWord_1500796).sum := by decide
  have hdescent : baseEnd_1500796 < baseStart_1500796 := by decide
  rcases family_descends (prefixWord ++ tailWord_1500796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1500811 : List Nat := [1, 1, 1, 1, 4, 1, 3, 1, 4, 5]
def baseStart_1500811 : Nat := 118140960795 + 1500811 * 2 ^ 59
def prefixEnd_1500811 : Nat := 4983230072969 + 3 ^ 40 * 1500811 * 2
def baseEnd_1500811 : Nat := 513758276370021869173601

theorem tailTrace_1500811 : CollatzResearch.WordTrace tailWord_1500811 prefixEnd_1500811 513758276370021869173601 := by
  unfold tailWord_1500811
  simp only [CollatzResearch.WordTrace]
  refine ⟨54739074165825539957382287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36492716110550359971588191 54739074165825539957382287)
  ·
    refine ⟨82108611248738309936073431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54739074165825539957382287 82108611248738309936073431)
    ·
      refine ⟨123162916873107464904110147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82108611248738309936073431 123162916873107464904110147)
      ·
        refine ⟨184744375309661197356165221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123162916873107464904110147 184744375309661197356165221)
        ·
          refine ⟨34639570370561474504280979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 184744375309661197356165221 34639570370561474504280979)
          ·
            refine ⟨51959355555842211756421469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34639570370561474504280979 51959355555842211756421469)
            ·
              refine ⟨19484758333440829408658051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51959355555842211756421469 19484758333440829408658051)
              ·
                refine ⟨29227137500161244112987077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19484758333440829408658051 29227137500161244112987077)
                ·
                  refine ⟨5480088281280233271185077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29227137500161244112987077 5480088281280233271185077)
                  ·
                    refine ⟨513758276370021869173601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5480088281280233271185077 513758276370021869173601)
                    ·
                      rfl

theorem cell22_1500811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 4, 5].length) (baseStart_1500811 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1500811 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1500811 prefixEnd_1500811 := by exact prefixLift 1500811
  have htrace : WordTrace (prefixWord ++ tailWord_1500811) baseStart_1500811 baseEnd_1500811 := by
    simpa [prefixWord, tailWord_1500811, baseEnd_1500811] using wordTrace_append hprefix tailTrace_1500811
  have hstable : (prefixWord ++ tailWord_1500811).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1500811).length < 2 ^ (prefixWord ++ tailWord_1500811).sum := by decide
  have hdescent : baseEnd_1500811 < baseStart_1500811 := by decide
  rcases family_descends (prefixWord ++ tailWord_1500811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1500860 : List Nat := [2, 2, 2, 3, 1, 2, 2, 3, 1, 4]
def baseStart_1500860 : Nat := 118140960795 + 1500860 * 2 ^ 59
def prefixEnd_1500860 : Nat := 4983230072969 + 3 ^ 40 * 1500860 * 2
def baseEnd_1500860 : Nat := 513775050071402074698451

theorem tailTrace_1500860 : CollatzResearch.WordTrace tailWord_1500860 prefixEnd_1500860 513775050071402074698451 := by
  unfold tailWord_1500860
  simp only [CollatzResearch.WordTrace]
  refine ⟨27370430671324010662958017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36493907561765347550610689 27370430671324010662958017)
  ·
    refine ⟨20527823003493007997218513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27370430671324010662958017 20527823003493007997218513)
    ·
      refine ⟨15395867252619755997913885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20527823003493007997218513 15395867252619755997913885)
      ·
        refine ⟨5773450219732408499217707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15395867252619755997913885 5773450219732408499217707)
        ·
          refine ⟨8660175329598612748826561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5773450219732408499217707 8660175329598612748826561)
          ·
            refine ⟨6495131497198959561619921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8660175329598612748826561 6495131497198959561619921)
            ·
              refine ⟨4871348622899219671214941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6495131497198959561619921 4871348622899219671214941)
              ·
                refine ⟨1826755733587207376705603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4871348622899219671214941 1826755733587207376705603)
                ·
                  refine ⟨2740133600380811065058405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1826755733587207376705603 2740133600380811065058405)
                  ·
                    refine ⟨513775050071402074698451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2740133600380811065058405 513775050071402074698451)
                    ·
                      rfl

theorem cell22_1500860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 3, 1, 4].length) (baseStart_1500860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1500860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1500860 prefixEnd_1500860 := by exact prefixLift 1500860
  have htrace : WordTrace (prefixWord ++ tailWord_1500860) baseStart_1500860 baseEnd_1500860 := by
    simpa [prefixWord, tailWord_1500860, baseEnd_1500860] using wordTrace_append hprefix tailTrace_1500860
  have hstable : (prefixWord ++ tailWord_1500860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1500860).length < 2 ^ (prefixWord ++ tailWord_1500860).sum := by decide
  have hdescent : baseEnd_1500860 < baseStart_1500860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1500860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1500888 : List Nat := [2, 1, 2, 2, 3, 1, 1, 2, 4, 4]
def baseStart_1500888 : Nat := 118140960795 + 1500888 * 2 ^ 59
def prefixEnd_1500888 : Nat := 4983230072969 + 3 ^ 40 * 1500888 * 2
def baseEnd_1500888 : Nat := 513784635043619334998365

theorem tailTrace_1500888 : CollatzResearch.WordTrace tailWord_1500888 prefixEnd_1500888 513784635043619334998365 := by
  unfold tailWord_1500888
  simp only [CollatzResearch.WordTrace]
  refine ⟨27370941293273291053967659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36494588391031054738623545 27370941293273291053967659)
  ·
    refine ⟨41056411939909936580951489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27370941293273291053967659 41056411939909936580951489)
    ·
      refine ⟨30792308954932452435713617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41056411939909936580951489 30792308954932452435713617)
      ·
        refine ⟨23094231716199339326785213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30792308954932452435713617 23094231716199339326785213)
        ·
          refine ⟨8660336893574752247544455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23094231716199339326785213 8660336893574752247544455)
          ·
            refine ⟨12990505340362128371316683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8660336893574752247544455 12990505340362128371316683)
            ·
              refine ⟨19485758010543192556975025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12990505340362128371316683 19485758010543192556975025)
              ·
                refine ⟨14614318507907394417731269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19485758010543192556975025 14614318507907394417731269)
                ·
                  refine ⟨2740184720232636453324613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14614318507907394417731269 2740184720232636453324613)
                  ·
                    refine ⟨513784635043619334998365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2740184720232636453324613 513784635043619334998365)
                    ·
                      rfl

theorem cell22_1500888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 2, 4, 4].length) (baseStart_1500888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1500888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1500888 prefixEnd_1500888 := by exact prefixLift 1500888
  have htrace : WordTrace (prefixWord ++ tailWord_1500888) baseStart_1500888 baseEnd_1500888 := by
    simpa [prefixWord, tailWord_1500888, baseEnd_1500888] using wordTrace_append hprefix tailTrace_1500888
  have hstable : (prefixWord ++ tailWord_1500888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1500888).length < 2 ^ (prefixWord ++ tailWord_1500888).sum := by decide
  have hdescent : baseEnd_1500888 < baseStart_1500888 := by decide
  rcases family_descends (prefixWord ++ tailWord_1500888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1500926 : List Nat := [4, 2, 2, 1, 3, 2, 2, 2, 4]
def baseStart_1500926 : Nat := 118140960795 + 1500926 * 2 ^ 59
def prefixEnd_1500926 : Nat := 4983230072969 + 3 ^ 40 * 1500926 * 2
def baseEnd_1500926 : Nat := 171265881073399967516083

theorem tailTrace_1500926 : CollatzResearch.WordTrace tailWord_1500926 prefixEnd_1500926 171265881073399967516083 := by
  unfold tailWord_1500926
  simp only [CollatzResearch.WordTrace]
  refine ⟨6842908570051114324727329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36495512373605943065212421 6842908570051114324727329)
  ·
    refine ⟨5132181427538335743545497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6842908570051114324727329 5132181427538335743545497)
    ·
      refine ⟨3849136070653751807659123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5132181427538335743545497 3849136070653751807659123)
      ·
        refine ⟨5773704105980627711488685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3849136070653751807659123 5773704105980627711488685)
        ·
          refine ⟨2165139039742735391808257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5773704105980627711488685 2165139039742735391808257)
          ·
            refine ⟨1623854279807051543856193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2165139039742735391808257 1623854279807051543856193)
            ·
              refine ⟨1217890709855288657892145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1623854279807051543856193 1217890709855288657892145)
              ·
                refine ⟨913418032391466493419109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1217890709855288657892145 913418032391466493419109)
                ·
                  refine ⟨171265881073399967516083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 913418032391466493419109 171265881073399967516083)
                  ·
                    rfl

theorem cell22_1500926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 2, 2, 4].length) (baseStart_1500926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1500926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1500926 prefixEnd_1500926 := by exact prefixLift 1500926
  have htrace : WordTrace (prefixWord ++ tailWord_1500926) baseStart_1500926 baseEnd_1500926 := by
    simpa [prefixWord, tailWord_1500926, baseEnd_1500926] using wordTrace_append hprefix tailTrace_1500926
  have hstable : (prefixWord ++ tailWord_1500926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1500926).length < 2 ^ (prefixWord ++ tailWord_1500926).sum := by decide
  have hdescent : baseEnd_1500926 < baseStart_1500926 := by decide
  rcases family_descends (prefixWord ++ tailWord_1500926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1500982 : List Nat := [5, 1, 2, 2, 1, 2, 1, 1, 7]
def baseStart_1500982 : Nat := 118140960795 + 1500982 * 2 ^ 59
def prefixEnd_1500982 : Nat := 4983230072969 + 3 ^ 40 * 1500982 * 2
def baseEnd_1500982 : Nat := 171272271054878141049359

theorem tailTrace_1500982 : CollatzResearch.WordTrace tailWord_1500982 prefixEnd_1500982 171272271054878141049359 := by
  unfold tailWord_1500982
  simp only [CollatzResearch.WordTrace]
  refine ⟨3421581940512877260116075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36496874032137357441238133 3421581940512877260116075)
  ·
    refine ⟨5132372910769315890174113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3421581940512877260116075 5132372910769315890174113)
    ·
      refine ⟨3849279683076986917630585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5132372910769315890174113 3849279683076986917630585)
      ·
        refine ⟨2886959762307740188222939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3849279683076986917630585 2886959762307740188222939)
        ·
          refine ⟨4330439643461610282334409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2886959762307740188222939 4330439643461610282334409)
          ·
            refine ⟨3247829732596207711750807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4330439643461610282334409 3247829732596207711750807)
            ·
              refine ⟨4871744598894311567626211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3247829732596207711750807 4871744598894311567626211)
              ·
                refine ⟨7307616898341467351439317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4871744598894311567626211 7307616898341467351439317)
                ·
                  refine ⟨171272271054878141049359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7307616898341467351439317 171272271054878141049359)
                  ·
                    rfl

theorem cell22_1500982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 1, 7].length) (baseStart_1500982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1500982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1500982 prefixEnd_1500982 := by exact prefixLift 1500982
  have htrace : WordTrace (prefixWord ++ tailWord_1500982) baseStart_1500982 baseEnd_1500982 := by
    simpa [prefixWord, tailWord_1500982, baseEnd_1500982] using wordTrace_append hprefix tailTrace_1500982
  have hstable : (prefixWord ++ tailWord_1500982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1500982).length < 2 ^ (prefixWord ++ tailWord_1500982).sum := by decide
  have hdescent : baseEnd_1500982 < baseStart_1500982 := by decide
  rcases family_descends (prefixWord ++ tailWord_1500982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1501010 : List Nat := [3, 2, 2, 1, 1, 3, 2, 2, 6]
def baseStart_1501010 : Nat := 118140960795 + 1501010 * 2 ^ 59
def prefixEnd_1501010 : Nat := 4983230072969 + 3 ^ 40 * 1501010 * 2
def baseEnd_1501010 : Nat := 171275466045617227815997

theorem tailTrace_1501010 : CollatzResearch.WordTrace tailWord_1501010 prefixEnd_1501010 171275466045617227815997 := by
  unfold tailWord_1501010
  simp only [CollatzResearch.WordTrace]
  refine ⟨13686583073026149235969121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36497554861403064629250989 13686583073026149235969121)
  ·
    refine ⟨10264937304769611926976841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13686583073026149235969121 10264937304769611926976841)
    ·
      refine ⟨7698702978577208945232631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10264937304769611926976841 7698702978577208945232631)
      ·
        refine ⟨11548054467865813417848947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7698702978577208945232631 11548054467865813417848947)
        ·
          refine ⟨17322081701798720126773421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11548054467865813417848947 17322081701798720126773421)
          ·
            refine ⟨6495780638174520047540033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17322081701798720126773421 6495780638174520047540033)
            ·
              refine ⟨4871835478630890035655025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6495780638174520047540033 4871835478630890035655025)
              ·
                refine ⟨3653876608973167526741269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4871835478630890035655025 3653876608973167526741269)
                ·
                  refine ⟨171275466045617227815997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3653876608973167526741269 171275466045617227815997)
                  ·
                    rfl

theorem cell22_1501010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 2, 6].length) (baseStart_1501010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1501010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1501010 prefixEnd_1501010 := by exact prefixLift 1501010
  have htrace : WordTrace (prefixWord ++ tailWord_1501010) baseStart_1501010 baseEnd_1501010 := by
    simpa [prefixWord, tailWord_1501010, baseEnd_1501010] using wordTrace_append hprefix tailTrace_1501010
  have hstable : (prefixWord ++ tailWord_1501010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1501010).length < 2 ^ (prefixWord ++ tailWord_1501010).sum := by decide
  have hdescent : baseEnd_1501010 < baseStart_1501010 := by decide
  rcases family_descends (prefixWord ++ tailWord_1501010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1501012 : List Nat := [2, 4, 1, 1, 3, 1, 1, 4, 1, 4]
def baseStart_1501012 : Nat := 118140960795 + 1501012 * 2 ^ 59
def prefixEnd_1501012 : Nat := 4983230072969 + 3 ^ 40 * 1501012 * 2
def baseEnd_1501012 : Nat := 513827082777724344897985

theorem tailTrace_1501012 : CollatzResearch.WordTrace tailWord_1501012 prefixEnd_1501012 513827082777724344897985 := by
  unfold tailWord_1501012
  simp only [CollatzResearch.WordTrace]
  refine ⟨27373202619048675642724645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36497603492064900856966193 27373202619048675642724645)
  ·
    refine ⟨5132475491071626683010871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27373202619048675642724645 5132475491071626683010871)
    ·
      refine ⟨7698713236607440024516307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5132475491071626683010871 7698713236607440024516307)
      ·
        refine ⟨11548069854911160036774461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7698713236607440024516307 11548069854911160036774461)
        ·
          refine ⟨4330526195591685013790423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11548069854911160036774461 4330526195591685013790423)
          ·
            refine ⟨6495789293387527520685635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4330526195591685013790423 6495789293387527520685635)
            ·
              refine ⟨9743683940081291281028453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6495789293387527520685635 9743683940081291281028453)
              ·
                refine ⟨1826940738765242115192835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9743683940081291281028453 1826940738765242115192835)
                ·
                  refine ⟨2740411108147863172789253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1826940738765242115192835 2740411108147863172789253)
                  ·
                    refine ⟨513827082777724344897985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2740411108147863172789253 513827082777724344897985)
                    ·
                      rfl

theorem cell22_1501012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 4, 1, 4].length) (baseStart_1501012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1501012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1501012 prefixEnd_1501012 := by exact prefixLift 1501012
  have htrace : WordTrace (prefixWord ++ tailWord_1501012) baseStart_1501012 baseEnd_1501012 := by
    simpa [prefixWord, tailWord_1501012, baseEnd_1501012] using wordTrace_append hprefix tailTrace_1501012
  have hstable : (prefixWord ++ tailWord_1501012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1501012).length < 2 ^ (prefixWord ++ tailWord_1501012).sum := by decide
  have hdescent : baseEnd_1501012 < baseStart_1501012 := by decide
  rcases family_descends (prefixWord ++ tailWord_1501012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1501025 : List Nat := [1, 2, 3, 1, 1, 1, 3, 1, 6, 3]
def baseStart_1501025 : Nat := 118140960795 + 1501025 * 2 ^ 59
def prefixEnd_1501025 : Nat := 4983230072969 + 3 ^ 40 * 1501025 * 2
def baseEnd_1501025 : Nat := 513831532943396644322945

theorem tailTrace_1501025 : CollatzResearch.WordTrace tailWord_1501025 prefixEnd_1501025 513831532943396644322945 := by
  unfold tailWord_1501025
  simp only [CollatzResearch.WordTrace]
  refine ⟨54746879387050254505672529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36497919591366836337115019 54746879387050254505672529)
  ·
    refine ⟨41060159540287690879254397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54746879387050254505672529 41060159540287690879254397)
    ·
      refine ⟨15397559827607884079720399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41060159540287690879254397 15397559827607884079720399)
      ·
        refine ⟨23096339741411826119580599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15397559827607884079720399 23096339741411826119580599)
        ·
          refine ⟨34644509612117739179370899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23096339741411826119580599 34644509612117739179370899)
          ·
            refine ⟨51966764418176608769056349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34644509612117739179370899 51966764418176608769056349)
            ·
              refine ⟨19487536656816228288396131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51966764418176608769056349 19487536656816228288396131)
              ·
                refine ⟨29231304985224342432594197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19487536656816228288396131 29231304985224342432594197)
                ·
                  refine ⟨1370217421182391051527853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 29231304985224342432594197 1370217421182391051527853)
                  ·
                    refine ⟨513831532943396644322945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1370217421182391051527853 513831532943396644322945)
                    ·
                      rfl

theorem cell22_1501025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 6, 3].length) (baseStart_1501025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1501025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1501025 prefixEnd_1501025 := by exact prefixLift 1501025
  have htrace : WordTrace (prefixWord ++ tailWord_1501025) baseStart_1501025 baseEnd_1501025 := by
    simpa [prefixWord, tailWord_1501025, baseEnd_1501025] using wordTrace_append hprefix tailTrace_1501025
  have hstable : (prefixWord ++ tailWord_1501025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1501025).length < 2 ^ (prefixWord ++ tailWord_1501025).sum := by decide
  have hdescent : baseEnd_1501025 < baseStart_1501025 := by decide
  rcases family_descends (prefixWord ++ tailWord_1501025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1501042 : List Nat := [3, 2, 1, 2, 1, 1, 1, 6, 2, 3]
def baseStart_1501042 : Nat := 118140960795 + 1501042 * 2 ^ 59
def prefixEnd_1501042 : Nat := 4983230072969 + 3 ^ 40 * 1501042 * 2
def baseEnd_1501042 : Nat := 513837352390814266647893

theorem tailTrace_1501042 : CollatzResearch.WordTrace tailWord_1501042 prefixEnd_1501042 513837352390814266647893 := by
  unfold tailWord_1501042
  simp only [CollatzResearch.WordTrace]
  refine ⟨13686874856997166602260345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36498332951992444272694253 13686874856997166602260345)
  ·
    refine ⟨10265156142747874951695259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13686874856997166602260345 10265156142747874951695259)
    ·
      refine ⟨15397734214121812427542889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10265156142747874951695259 15397734214121812427542889)
      ·
        refine ⟨11548300660591359320657167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15397734214121812427542889 11548300660591359320657167)
        ·
          refine ⟨17322450990887038980985751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11548300660591359320657167 17322450990887038980985751)
          ·
            refine ⟨25983676486330558471478627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17322450990887038980985751 25983676486330558471478627)
            ·
              refine ⟨38975514729495837707217941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25983676486330558471478627 38975514729495837707217941)
              ·
                refine ⟨1826977252945117392525841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 38975514729495837707217941 1826977252945117392525841)
                ·
                  refine ⟨1370232939708838044394381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1826977252945117392525841 1370232939708838044394381)
                  ·
                    refine ⟨513837352390814266647893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1370232939708838044394381 513837352390814266647893)
                    ·
                      rfl

theorem cell22_1501042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 6, 2, 3].length) (baseStart_1501042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1501042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1501042 prefixEnd_1501042 := by exact prefixLift 1501042
  have htrace : WordTrace (prefixWord ++ tailWord_1501042) baseStart_1501042 baseEnd_1501042 := by
    simpa [prefixWord, tailWord_1501042, baseEnd_1501042] using wordTrace_append hprefix tailTrace_1501042
  have hstable : (prefixWord ++ tailWord_1501042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1501042).length < 2 ^ (prefixWord ++ tailWord_1501042).sum := by decide
  have hdescent : baseEnd_1501042 < baseStart_1501042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1501042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1501059 : List Nat := [1, 1, 1, 3, 4, 2, 4, 1, 2, 3]
def baseStart_1501059 : Nat := 118140960795 + 1501059 * 2 ^ 59
def prefixEnd_1501059 : Nat := 4983230072969 + 3 ^ 40 * 1501059 * 2
def baseEnd_1501059 : Nat := 513843171838231888972841

theorem tailTrace_1501059 : CollatzResearch.WordTrace tailWord_1501059 prefixEnd_1501059 513843171838231888972841 := by
  unfold tailWord_1501059
  simp only [CollatzResearch.WordTrace]
  refine ⟨54748119468927078312410231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36498746312618052208273487 54748119468927078312410231)
  ·
    refine ⟨82122179203390617468615347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54748119468927078312410231 82122179203390617468615347)
    ·
      refine ⟨123183268805085926202923021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82122179203390617468615347 123183268805085926202923021)
      ·
        refine ⟨46193725801907222326096133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123183268805085926202923021 46193725801907222326096133)
        ·
          refine ⟨8661323587857604186143025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46193725801907222326096133 8661323587857604186143025)
          ·
            refine ⟨6495992690893203139607269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8661323587857604186143025 6495992690893203139607269)
            ·
              refine ⟨1217998629542475588676363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6495992690893203139607269 1217998629542475588676363)
              ·
                refine ⟨1826997944313713383014545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1217998629542475588676363 1826997944313713383014545)
                ·
                  refine ⟨1370248458235285037260909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1826997944313713383014545 1370248458235285037260909)
                  ·
                    refine ⟨513843171838231888972841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1370248458235285037260909 513843171838231888972841)
                    ·
                      rfl

theorem cell22_1501059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 4, 1, 2, 3].length) (baseStart_1501059 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1501059 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1501059 prefixEnd_1501059 := by exact prefixLift 1501059
  have htrace : WordTrace (prefixWord ++ tailWord_1501059) baseStart_1501059 baseEnd_1501059 := by
    simpa [prefixWord, tailWord_1501059, baseEnd_1501059] using wordTrace_append hprefix tailTrace_1501059
  have hstable : (prefixWord ++ tailWord_1501059).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1501059).length < 2 ^ (prefixWord ++ tailWord_1501059).sum := by decide
  have hdescent : baseEnd_1501059 < baseStart_1501059 := by decide
  rcases family_descends (prefixWord ++ tailWord_1501059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1501074 : List Nat := [3, 2, 3, 2, 1, 2, 2, 1, 2, 4]
def baseStart_1501074 : Nat := 118140960795 + 1501074 * 2 ^ 59
def prefixEnd_1501074 : Nat := 4983230072969 + 3 ^ 40 * 1501074 * 2
def baseEnd_1501074 : Nat := 513848306644776849847795

theorem tailTrace_1501074 : CollatzResearch.WordTrace tailWord_1501074 prefixEnd_1501074 513848306644776849847795 := by
  unfold tailWord_1501074
  simp only [CollatzResearch.WordTrace]
  refine ⟨13687166640968183968551569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36499111042581823916137517 13687166640968183968551569)
  ·
    refine ⟨10265374980726137976413677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13687166640968183968551569 10265374980726137976413677)
    ·
      refine ⟨3849515617772301741155129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10265374980726137976413677 3849515617772301741155129)
      ·
        refine ⟨2887136713329226305866347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3849515617772301741155129 2887136713329226305866347)
        ·
          refine ⟨4330705069993839458799521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2887136713329226305866347 4330705069993839458799521)
          ·
            refine ⟨3248028802495379594099641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4330705069993839458799521 3248028802495379594099641)
            ·
              refine ⟨2436021601871534695574731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3248028802495379594099641 2436021601871534695574731)
              ·
                refine ⟨3654032402807302043362097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2436021601871534695574731 3654032402807302043362097)
                ·
                  refine ⟨2740524302105476532521573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3654032402807302043362097 2740524302105476532521573)
                  ·
                    refine ⟨513848306644776849847795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2740524302105476532521573 513848306644776849847795)
                    ·
                      rfl

theorem cell22_1501074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_1501074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1501074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1501074 prefixEnd_1501074 := by exact prefixLift 1501074
  have htrace : WordTrace (prefixWord ++ tailWord_1501074) baseStart_1501074 baseEnd_1501074 := by
    simpa [prefixWord, tailWord_1501074, baseEnd_1501074] using wordTrace_append hprefix tailTrace_1501074
  have hstable : (prefixWord ++ tailWord_1501074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1501074).length < 2 ^ (prefixWord ++ tailWord_1501074).sum := by decide
  have hdescent : baseEnd_1501074 < baseStart_1501074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1501074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1501117 : List Nat := [1, 4, 1, 2, 3, 1, 2, 3, 5]
def baseStart_1501117 : Nat := 118140960795 + 1501117 * 2 ^ 59
def prefixEnd_1501117 : Nat := 4983230072969 + 3 ^ 40 * 1501117 * 2
def baseEnd_1501117 : Nat := 171287675474513023674221

theorem tailTrace_1501117 : CollatzResearch.WordTrace tailWord_1501117 prefixEnd_1501117 171287675474513023674221 := by
  unfold tailWord_1501117
  simp only [CollatzResearch.WordTrace]
  refine ⟨54750234902716954218021605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36500156601811302812014403 54750234902716954218021605)
  ·
    refine ⟨10265669044259428915879051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54750234902716954218021605 10265669044259428915879051)
    ·
      refine ⟨15398503566389143373818577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10265669044259428915879051 15398503566389143373818577)
      ·
        refine ⟨11548877674791857530363933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15398503566389143373818577 11548877674791857530363933)
        ·
          refine ⟨4330829128046946573886475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11548877674791857530363933 4330829128046946573886475)
          ·
            refine ⟨6496243692070419860829713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4330829128046946573886475 6496243692070419860829713)
            ·
              refine ⟨4872182769052814895622285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6496243692070419860829713 4872182769052814895622285)
              ·
                refine ⟨1827068538394805585858357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4872182769052814895622285 1827068538394805585858357)
                ·
                  refine ⟨171287675474513023674221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1827068538394805585858357 171287675474513023674221)
                  ·
                    rfl

theorem cell22_1501117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 3, 5].length) (baseStart_1501117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1501117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1501117 prefixEnd_1501117 := by exact prefixLift 1501117
  have htrace : WordTrace (prefixWord ++ tailWord_1501117) baseStart_1501117 baseEnd_1501117 := by
    simpa [prefixWord, tailWord_1501117, baseEnd_1501117] using wordTrace_append hprefix tailTrace_1501117
  have hstable : (prefixWord ++ tailWord_1501117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1501117).length < 2 ^ (prefixWord ++ tailWord_1501117).sum := by decide
  have hdescent : baseEnd_1501117 < baseStart_1501117 := by decide
  rcases family_descends (prefixWord ++ tailWord_1501117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1501138 : List Nat := [3, 2, 2, 3, 2, 1, 2, 3, 1, 3]
def baseStart_1501138 : Nat := 118140960795 + 1501138 * 2 ^ 59
def prefixEnd_1501138 : Nat := 4983230072969 + 3 ^ 40 * 1501138 * 2
def baseEnd_1501138 : Nat := 513870215152702016247599

theorem tailTrace_1501138 : CollatzResearch.WordTrace tailWord_1501138 prefixEnd_1501138 513870215152702016247599 := by
  unfold tailWord_1501138
  simp only [CollatzResearch.WordTrace]
  refine ⟨13687750208910218701134017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36500667223760583203024045 13687750208910218701134017)
  ·
    refine ⟨10265812656682664025850513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13687750208910218701134017 10265812656682664025850513)
    ·
      refine ⟨7699359492511998019387885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10265812656682664025850513 7699359492511998019387885)
      ·
        refine ⟨2887259809691999257270457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7699359492511998019387885 2887259809691999257270457)
        ·
          refine ⟨2165444857268999442952843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2887259809691999257270457 2165444857268999442952843)
          ·
            refine ⟨3248167285903499164429265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2165444857268999442952843 3248167285903499164429265)
            ·
              refine ⟨2436125464427624373321949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3248167285903499164429265 2436125464427624373321949)
              ·
                refine ⟨913547049160359139995731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2436125464427624373321949 913547049160359139995731)
                ·
                  refine ⟨1370320573740538709993597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 913547049160359139995731 1370320573740538709993597)
                  ·
                    refine ⟨513870215152702016247599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1370320573740538709993597 513870215152702016247599)
                    ·
                      rfl

theorem cell22_1501138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 2, 3, 1, 3].length) (baseStart_1501138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1501138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1501138 prefixEnd_1501138 := by exact prefixLift 1501138
  have htrace : WordTrace (prefixWord ++ tailWord_1501138) baseStart_1501138 baseEnd_1501138 := by
    simpa [prefixWord, tailWord_1501138, baseEnd_1501138] using wordTrace_append hprefix tailTrace_1501138
  have hstable : (prefixWord ++ tailWord_1501138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1501138).length < 2 ^ (prefixWord ++ tailWord_1501138).sum := by decide
  have hdescent : baseEnd_1501138 < baseStart_1501138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1501138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1501162 : List Nat := [3, 1, 3, 1, 2, 1, 4, 1, 6]
def baseStart_1501162 : Nat := 118140960795 + 1501162 * 2 ^ 59
def prefixEnd_1501162 : Nat := 4983230072969 + 3 ^ 40 * 1501162 * 2
def baseEnd_1501162 : Nat := 171292810281057984549175

theorem tailTrace_1501162 : CollatzResearch.WordTrace tailWord_1501162 prefixEnd_1501162 171292810281057984549175 := by
  unfold tailWord_1501162
  simp only [CollatzResearch.WordTrace]
  refine ⟨13687969046888481725852435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36501250791702617935606493 13687969046888481725852435)
  ·
    refine ⟨20531953570332722588778653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13687969046888481725852435 20531953570332722588778653)
    ·
      refine ⟨7699482588874770970791995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20531953570332722588778653 7699482588874770970791995)
      ·
        refine ⟨11549223883312156456187993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7699482588874770970791995 11549223883312156456187993)
        ·
          refine ⟨8661917912484117342140995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11549223883312156456187993 8661917912484117342140995)
          ·
            refine ⟨12992876868726176013211493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8661917912484117342140995 12992876868726176013211493)
            ·
              refine ⟨2436164412886158002477155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12992876868726176013211493 2436164412886158002477155)
              ·
                refine ⟨3654246619329237003715733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2436164412886158002477155 3654246619329237003715733)
                ·
                  refine ⟨171292810281057984549175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3654246619329237003715733 171292810281057984549175)
                  ·
                    rfl

theorem cell22_1501162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 4, 1, 6].length) (baseStart_1501162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1501162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1501162 prefixEnd_1501162 := by exact prefixLift 1501162
  have htrace : WordTrace (prefixWord ++ tailWord_1501162) baseStart_1501162 baseEnd_1501162 := by
    simpa [prefixWord, tailWord_1501162, baseEnd_1501162] using wordTrace_append hprefix tailTrace_1501162
  have hstable : (prefixWord ++ tailWord_1501162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1501162).length < 2 ^ (prefixWord ++ tailWord_1501162).sum := by decide
  have hdescent : baseEnd_1501162 < baseStart_1501162 := by decide
  rcases family_descends (prefixWord ++ tailWord_1501162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1501177 : List Nat := [1, 2, 1, 3, 1, 4, 3, 1, 1, 5]
def baseStart_1501177 : Nat := 118140960795 + 1501177 * 2 ^ 59
def prefixEnd_1501177 : Nat := 4983230072969 + 3 ^ 40 * 1501177 * 2
def baseEnd_1501177 : Nat := 513883565649718914522479

theorem tailTrace_1501177 : CollatzResearch.WordTrace tailWord_1501177 prefixEnd_1501177 513883565649718914522479 := by
  unfold tailWord_1501177
  simp only [CollatzResearch.WordTrace]
  refine ⟨54752423282499584465205785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36501615521666389643470523 54752423282499584465205785)
  ·
    refine ⟨41064317461874688348904339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54752423282499584465205785 41064317461874688348904339)
    ·
      refine ⟨61596476192812032523356509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41064317461874688348904339 61596476192812032523356509)
      ·
        refine ⟨23098678572304512196258691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61596476192812032523356509 23098678572304512196258691)
        ·
          refine ⟨34648017858456768294388037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23098678572304512196258691 34648017858456768294388037)
          ·
            refine ⟨6496503348460644055197757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34648017858456768294388037 6496503348460644055197757)
            ·
              refine ⟨2436188755672741520699159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6496503348460644055197757 2436188755672741520699159)
              ·
                refine ⟨3654283133509112281048739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2436188755672741520699159 3654283133509112281048739)
                ·
                  refine ⟨5481424700263668421573109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3654283133509112281048739 5481424700263668421573109)
                  ·
                    refine ⟨513883565649718914522479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5481424700263668421573109 513883565649718914522479)
                    ·
                      rfl

theorem cell22_1501177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 3, 1, 1, 5].length) (baseStart_1501177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1501177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1501177 prefixEnd_1501177 := by exact prefixLift 1501177
  have htrace : WordTrace (prefixWord ++ tailWord_1501177) baseStart_1501177 baseEnd_1501177 := by
    simpa [prefixWord, tailWord_1501177, baseEnd_1501177] using wordTrace_append hprefix tailTrace_1501177
  have hstable : (prefixWord ++ tailWord_1501177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1501177).length < 2 ^ (prefixWord ++ tailWord_1501177).sum := by decide
  have hdescent : baseEnd_1501177 < baseStart_1501177 := by decide
  rcases family_descends (prefixWord ++ tailWord_1501177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1501192 : List Nat := [2, 1, 3, 2, 1, 2, 2, 3, 2, 4]
def baseStart_1501192 : Nat := 118140960795 + 1501192 * 2 ^ 59
def prefixEnd_1501192 : Nat := 4983230072969 + 3 ^ 40 * 1501192 * 2
def baseEnd_1501192 : Nat := 513888700456263875397433

theorem tailTrace_1501192 : CollatzResearch.WordTrace tailWord_1501192 prefixEnd_1501192 513888700456263875397433 := by
  unfold tailWord_1501192
  simp only [CollatzResearch.WordTrace]
  refine ⟨27376485188722621013500915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36501980251630161351334553 27376485188722621013500915)
  ·
    refine ⟨41064727783083931520251373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27376485188722621013500915 41064727783083931520251373)
    ·
      refine ⟨15399272918656474320094265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41064727783083931520251373 15399272918656474320094265)
      ·
        refine ⟨11549454688992355740070699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15399272918656474320094265 11549454688992355740070699)
        ·
          refine ⟨17324182033488533610106049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11549454688992355740070699 17324182033488533610106049)
          ·
            refine ⟨12993136525116400207579537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17324182033488533610106049 12993136525116400207579537)
            ·
              refine ⟨9744852393837300155684653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12993136525116400207579537 9744852393837300155684653)
              ·
                refine ⟨3654319647688987558381745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9744852393837300155684653 3654319647688987558381745)
                ·
                  refine ⟨2740739735766740668786309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3654319647688987558381745 2740739735766740668786309)
                  ·
                    refine ⟨513888700456263875397433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2740739735766740668786309 513888700456263875397433)
                    ·
                      rfl

theorem cell22_1501192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 3, 2, 4].length) (baseStart_1501192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1501192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1501192 prefixEnd_1501192 := by exact prefixLift 1501192
  have htrace : WordTrace (prefixWord ++ tailWord_1501192) baseStart_1501192 baseEnd_1501192 := by
    simpa [prefixWord, tailWord_1501192, baseEnd_1501192] using wordTrace_append hprefix tailTrace_1501192
  have hstable : (prefixWord ++ tailWord_1501192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1501192).length < 2 ^ (prefixWord ++ tailWord_1501192).sum := by decide
  have hdescent : baseEnd_1501192 < baseStart_1501192 := by decide
  rcases family_descends (prefixWord ++ tailWord_1501192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1501269 : List Nat := [1, 3, 2, 2, 1, 4, 2, 2, 5]
def baseStart_1501269 : Nat := 118140960795 + 1501269 * 2 ^ 59
def prefixEnd_1501269 : Nat := 4983230072969 + 3 ^ 40 * 1501269 * 2
def baseEnd_1501269 : Nat := 171305019709953780407399

theorem tailTrace_1501269 : CollatzResearch.WordTrace tailWord_1501269 prefixEnd_1501269 171305019709953780407399 := by
  unfold tailWord_1501269
  simp only [CollatzResearch.WordTrace]
  refine ⟨54755778798166284177554861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36503852532110856118369907 54755778798166284177554861)
  ·
    refine ⟨20533417049312356566583073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54755778798166284177554861 20533417049312356566583073)
    ·
      refine ⟨15400062786984267424937305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20533417049312356566583073 15400062786984267424937305)
      ·
        refine ⟨11550047090238200568702979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15400062786984267424937305 11550047090238200568702979)
        ·
          refine ⟨17325070635357300853054469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11550047090238200568702979 17325070635357300853054469)
          ·
            refine ⟨3248450744129493909947713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17325070635357300853054469 3248450744129493909947713)
            ·
              refine ⟨2436338058097120432460785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3248450744129493909947713 2436338058097120432460785)
              ·
                refine ⟨1827253543572840324345589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2436338058097120432460785 1827253543572840324345589)
                ·
                  refine ⟨171305019709953780407399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1827253543572840324345589 171305019709953780407399)
                  ·
                    rfl

theorem cell22_1501269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 2, 2, 5].length) (baseStart_1501269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1501269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1501269 prefixEnd_1501269 := by exact prefixLift 1501269
  have htrace : WordTrace (prefixWord ++ tailWord_1501269) baseStart_1501269 baseEnd_1501269 := by
    simpa [prefixWord, tailWord_1501269, baseEnd_1501269] using wordTrace_append hprefix tailTrace_1501269
  have hstable : (prefixWord ++ tailWord_1501269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1501269).length < 2 ^ (prefixWord ++ tailWord_1501269).sum := by decide
  have hdescent : baseEnd_1501269 < baseStart_1501269 := by decide
  rcases family_descends (prefixWord ++ tailWord_1501269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1501297 : List Nat := [1, 2, 2, 2, 1, 1, 5, 2, 6]
def baseStart_1501297 : Nat := 118140960795 + 1501297 * 2 ^ 59
def prefixEnd_1501297 : Nat := 4983230072969 + 3 ^ 40 * 1501297 * 2
def baseEnd_1501297 : Nat := 171308214700692867174037

theorem tailTrace_1501297 : CollatzResearch.WordTrace tailWord_1501297 prefixEnd_1501297 171308214700692867174037 := by
  unfold tailWord_1501297
  simp only [CollatzResearch.WordTrace]
  refine ⟨54756800042064844959574145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36504533361376563306382763 54756800042064844959574145)
  ·
    refine ⟨41067600031548633719680609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54756800042064844959574145 41067600031548633719680609)
    ·
      refine ⟨30800700023661475289760457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41067600031548633719680609 30800700023661475289760457)
      ·
        refine ⟨23100525017746106467320343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30800700023661475289760457 23100525017746106467320343)
        ·
          refine ⟨34650787526619159700980515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23100525017746106467320343 34650787526619159700980515)
          ·
            refine ⟨51976181289928739551470773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34650787526619159700980515 51976181289928739551470773)
            ·
              refine ⟨4872766995930819332950385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 51976181289928739551470773 4872766995930819332950385)
              ·
                refine ⟨3654575246948114499712789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4872766995930819332950385 3654575246948114499712789)
                ·
                  refine ⟨171308214700692867174037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3654575246948114499712789 171308214700692867174037)
                  ·
                    rfl

theorem cell22_1501297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 2, 6].length) (baseStart_1501297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1501297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1501297 prefixEnd_1501297 := by exact prefixLift 1501297
  have htrace : WordTrace (prefixWord ++ tailWord_1501297) baseStart_1501297 baseEnd_1501297 := by
    simpa [prefixWord, tailWord_1501297, baseEnd_1501297] using wordTrace_append hprefix tailTrace_1501297
  have hstable : (prefixWord ++ tailWord_1501297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1501297).length < 2 ^ (prefixWord ++ tailWord_1501297).sum := by decide
  have hdescent : baseEnd_1501297 < baseStart_1501297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1501297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1501346 : List Nat := [3, 3, 1, 3, 1, 1, 3, 1, 1, 5]
def baseStart_1501346 : Nat := 118140960795 + 1501346 * 2 ^ 59
def prefixEnd_1501346 : Nat := 4983230072969 + 3 ^ 40 * 1501346 * 2
def baseEnd_1501346 : Nat := 513941417803458807046961

theorem tailTrace_1501346 : CollatzResearch.WordTrace tailWord_1501346 prefixEnd_1501346 513941417803458807046961 := by
  unfold tailWord_1501346
  simp only [CollatzResearch.WordTrace]
  refine ⟨13689646804721831582026973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36505724812591550885405261 13689646804721831582026973)
  ·
    refine ⟨5133617551770686843260115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13689646804721831582026973 5133617551770686843260115)
    ·
      refine ⟨7700426327656030264890173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5133617551770686843260115 7700426327656030264890173)
      ·
        refine ⟨2887659872871011349333815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7700426327656030264890173 2887659872871011349333815)
        ·
          refine ⟨4331489809306517024000723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2887659872871011349333815 4331489809306517024000723)
          ·
            refine ⟨6497234713959775536001085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4331489809306517024000723 6497234713959775536001085)
            ·
              refine ⟨2436463017734915826000407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6497234713959775536001085 2436463017734915826000407)
              ·
                refine ⟨3654694526602373739000611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2436463017734915826000407 3654694526602373739000611)
                ·
                  refine ⟨5482041789903560608500917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3654694526602373739000611 5482041789903560608500917)
                  ·
                    refine ⟨513941417803458807046961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5482041789903560608500917 513941417803458807046961)
                    ·
                      rfl

theorem cell22_1501346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 3, 1, 1, 5].length) (baseStart_1501346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1501346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1501346 prefixEnd_1501346 := by exact prefixLift 1501346
  have htrace : WordTrace (prefixWord ++ tailWord_1501346) baseStart_1501346 baseEnd_1501346 := by
    simpa [prefixWord, tailWord_1501346, baseEnd_1501346] using wordTrace_append hprefix tailTrace_1501346
  have hstable : (prefixWord ++ tailWord_1501346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1501346).length < 2 ^ (prefixWord ++ tailWord_1501346).sum := by decide
  have hdescent : baseEnd_1501346 < baseStart_1501346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1501346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1501365 : List Nat := [1, 3, 3, 4, 1, 2, 1, 3, 4]
def baseStart_1501365 : Nat := 118140960795 + 1501365 * 2 ^ 59
def prefixEnd_1501365 : Nat := 4983230072969 + 3 ^ 40 * 1501365 * 2
def baseEnd_1501365 : Nat := 171315973963916363607301

theorem tailTrace_1501365 : CollatzResearch.WordTrace tailWord_1501365 prefixEnd_1501365 171315973963916363607301 := by
  unfold tailWord_1501365
  simp only [CollatzResearch.WordTrace]
  refine ⟨54759280205818492573049549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36506186803878995048699699 54759280205818492573049549)
  ·
    refine ⟨20534730077181934714893581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54759280205818492573049549 20534730077181934714893581)
    ·
      refine ⟨7700523778943225518085093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20534730077181934714893581 7700523778943225518085093)
      ·
        refine ⟨1443848208551854784640955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7700523778943225518085093 1443848208551854784640955)
        ·
          refine ⟨2165772312827782176961433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1443848208551854784640955 2165772312827782176961433)
          ·
            refine ⟨1624329234620836632721075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2165772312827782176961433 1624329234620836632721075)
            ·
              refine ⟨2436493851931254949081613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1624329234620836632721075 2436493851931254949081613)
              ·
                refine ⟨913685194474220605905605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2436493851931254949081613 913685194474220605905605)
                ·
                  refine ⟨171315973963916363607301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 913685194474220605905605 171315973963916363607301)
                  ·
                    rfl

theorem cell22_1501365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 1, 3, 4].length) (baseStart_1501365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1501365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1501365 prefixEnd_1501365 := by exact prefixLift 1501365
  have htrace : WordTrace (prefixWord ++ tailWord_1501365) baseStart_1501365 baseEnd_1501365 := by
    simpa [prefixWord, tailWord_1501365, baseEnd_1501365] using wordTrace_append hprefix tailTrace_1501365
  have hstable : (prefixWord ++ tailWord_1501365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1501365).length < 2 ^ (prefixWord ++ tailWord_1501365).sum := by decide
  have hdescent : baseEnd_1501365 < baseStart_1501365 := by decide
  rcases family_descends (prefixWord ++ tailWord_1501365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1501378 : List Nat := [3, 5, 1, 1, 1, 1, 1, 1, 4, 4]
def baseStart_1501378 : Nat := 118140960795 + 1501378 * 2 ^ 59
def prefixEnd_1501378 : Nat := 4983230072969 + 3 ^ 40 * 1501378 * 2
def baseEnd_1501378 : Nat := 513952372057421390246863

theorem tailTrace_1501378 : CollatzResearch.WordTrace tailWord_1501378 prefixEnd_1501378 513952372057421390246863 := by
  unfold tailWord_1501378
  simp only [CollatzResearch.WordTrace]
  refine ⟨13689938588692848948318197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36506502903180930528848525 13689938588692848948318197)
  ·
    refine ⟨1283431742689954588904831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13689938588692848948318197 1283431742689954588904831)
    ·
      refine ⟨1925147614034931883357247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1283431742689954588904831 1925147614034931883357247)
      ·
        refine ⟨2887721421052397825035871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1925147614034931883357247 2887721421052397825035871)
        ·
          refine ⟨4331582131578596737553807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2887721421052397825035871 4331582131578596737553807)
          ·
            refine ⟨6497373197367895106330711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4331582131578596737553807 6497373197367895106330711)
            ·
              refine ⟨9746059796051842659496067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6497373197367895106330711 9746059796051842659496067)
              ·
                refine ⟨14619089694077763989244101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9746059796051842659496067 14619089694077763989244101)
                ·
                  refine ⟨2741079317639580747983269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14619089694077763989244101 2741079317639580747983269)
                  ·
                    refine ⟨513952372057421390246863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2741079317639580747983269 513952372057421390246863)
                    ·
                      rfl

theorem cell22_1501378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_1501378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1501378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1501378 prefixEnd_1501378 := by exact prefixLift 1501378
  have htrace : WordTrace (prefixWord ++ tailWord_1501378) baseStart_1501378 baseEnd_1501378 := by
    simpa [prefixWord, tailWord_1501378, baseEnd_1501378] using wordTrace_append hprefix tailTrace_1501378
  have hstable : (prefixWord ++ tailWord_1501378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1501378).length < 2 ^ (prefixWord ++ tailWord_1501378).sum := by decide
  have hdescent : baseEnd_1501378 < baseStart_1501378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1501378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1501387 : List Nat := [1, 1, 1, 1, 3, 2, 3, 3, 7]
def baseStart_1501387 : Nat := 118140960795 + 1501387 * 2 ^ 59
def prefixEnd_1501387 : Nat := 4983230072969 + 3 ^ 40 * 1501387 * 2
def baseEnd_1501387 : Nat := 171318484313782788923945

theorem tailTrace_1501387 : CollatzResearch.WordTrace tailWord_1501387 prefixEnd_1501387 171318484313782788923945 := by
  unfold tailWord_1501387
  simp only [CollatzResearch.WordTrace]
  refine ⟨54760082611738790330350415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36506721741159193553566943 54760082611738790330350415)
  ·
    refine ⟨82140123917608185495525623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54760082611738790330350415 82140123917608185495525623)
    ·
      refine ⟨123210185876412278243288435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82140123917608185495525623 123210185876412278243288435)
      ·
        refine ⟨184815278814618417364932653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123210185876412278243288435 184815278814618417364932653)
        ·
          refine ⟨69305729555481906511849745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 184815278814618417364932653 69305729555481906511849745)
          ·
            refine ⟨51979297166611429883887309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69305729555481906511849745 51979297166611429883887309)
            ·
              refine ⟨19492236437479286206457741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51979297166611429883887309 19492236437479286206457741)
              ·
                refine ⟨7309588664054732327421653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19492236437479286206457741 7309588664054732327421653)
                ·
                  refine ⟨171318484313782788923945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7309588664054732327421653 171318484313782788923945)
                  ·
                    rfl

theorem cell22_1501387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 3, 7].length) (baseStart_1501387 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1501387 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1501387 prefixEnd_1501387 := by exact prefixLift 1501387
  have htrace : WordTrace (prefixWord ++ tailWord_1501387) baseStart_1501387 baseEnd_1501387 := by
    simpa [prefixWord, tailWord_1501387, baseEnd_1501387] using wordTrace_append hprefix tailTrace_1501387
  have hstable : (prefixWord ++ tailWord_1501387).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1501387).length < 2 ^ (prefixWord ++ tailWord_1501387).sum := by decide
  have hdescent : baseEnd_1501387 < baseStart_1501387 := by decide
  rcases family_descends (prefixWord ++ tailWord_1501387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1501397 : List Nat := [1, 3, 2, 4, 3, 1, 2, 1, 2, 3]
def baseStart_1501397 : Nat := 118140960795 + 1501397 * 2 ^ 59
def prefixEnd_1501397 : Nat := 4983230072969 + 3 ^ 40 * 1501397 * 2
def baseEnd_1501397 : Nat := 513958876145711674021805

theorem tailTrace_1501397 : CollatzResearch.WordTrace tailWord_1501397 prefixEnd_1501397 513958876145711674021805 := by
  unfold tailWord_1501397
  simp only [CollatzResearch.WordTrace]
  refine ⟨54760447341702562038214445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36506964894468374692142963 54760447341702562038214445)
  ·
    refine ⟨20535167753138460764330417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54760447341702562038214445 20535167753138460764330417)
    ·
      refine ⟨15401375814853845573247813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20535167753138460764330417 15401375814853845573247813)
      ·
        refine ⟨2887757965285096044983965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15401375814853845573247813 2887757965285096044983965)
        ·
          refine ⟨1082909236981911016868987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2887757965285096044983965 1082909236981911016868987)
          ·
            refine ⟨1624363855472866525303481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1082909236981911016868987 1624363855472866525303481)
            ·
              refine ⟨1218272891604649893977611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1624363855472866525303481 1218272891604649893977611)
              ·
                refine ⟨1827409337406974840966417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1218272891604649893977611 1827409337406974840966417)
                ·
                  refine ⟨1370557003055231130724813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1827409337406974840966417 1370557003055231130724813)
                  ·
                    refine ⟨513958876145711674021805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1370557003055231130724813 513958876145711674021805)
                    ·
                      rfl

theorem cell22_1501397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 2, 1, 2, 3].length) (baseStart_1501397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1501397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1501397 prefixEnd_1501397 := by exact prefixLift 1501397
  have htrace : WordTrace (prefixWord ++ tailWord_1501397) baseStart_1501397 baseEnd_1501397 := by
    simpa [prefixWord, tailWord_1501397, baseEnd_1501397] using wordTrace_append hprefix tailTrace_1501397
  have hstable : (prefixWord ++ tailWord_1501397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1501397).length < 2 ^ (prefixWord ++ tailWord_1501397).sum := by decide
  have hdescent : baseEnd_1501397 < baseStart_1501397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1501397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1501417 : List Nat := [1, 2, 1, 1, 1, 2, 2, 2, 2, 8]
def baseStart_1501417 : Nat := 118140960795 + 1501417 * 2 ^ 59
def prefixEnd_1501417 : Nat := 4983230072969 + 3 ^ 40 * 1501417 * 2
def baseEnd_1501417 : Nat := 513965722554438288521743

theorem tailTrace_1501417 : CollatzResearch.WordTrace tailWord_1501417 prefixEnd_1501417 513965722554438288521743 := by
  unfold tailWord_1501417
  simp only [CollatzResearch.WordTrace]
  refine ⟨54761176801630105453942505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36507451201086736969295003 54761176801630105453942505)
  ·
    refine ⟨41070882601222579090456879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54761176801630105453942505 41070882601222579090456879)
    ·
      refine ⟨61606323901833868635685319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41070882601222579090456879 61606323901833868635685319)
      ·
        refine ⟨92409485852750802953527979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61606323901833868635685319 92409485852750802953527979)
        ·
          refine ⟨138614228779126204430291969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92409485852750802953527979 138614228779126204430291969)
          ·
            refine ⟨103960671584344653322718977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138614228779126204430291969 103960671584344653322718977)
            ·
              refine ⟨77970503688258489992039233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103960671584344653322718977 77970503688258489992039233)
              ·
                refine ⟨58477877766193867494029425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77970503688258489992039233 58477877766193867494029425)
                ·
                  refine ⟨43858408324645400620522069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58477877766193867494029425 43858408324645400620522069)
                  ·
                    refine ⟨513965722554438288521743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 43858408324645400620522069 513965722554438288521743)
                    ·
                      rfl

theorem cell22_1501417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 8].length) (baseStart_1501417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1501417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1501417 prefixEnd_1501417 := by exact prefixLift 1501417
  have htrace : WordTrace (prefixWord ++ tailWord_1501417) baseStart_1501417 baseEnd_1501417 := by
    simpa [prefixWord, tailWord_1501417, baseEnd_1501417] using wordTrace_append hprefix tailTrace_1501417
  have hstable : (prefixWord ++ tailWord_1501417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1501417).length < 2 ^ (prefixWord ++ tailWord_1501417).sum := by decide
  have hdescent : baseEnd_1501417 < baseStart_1501417 := by decide
  rcases family_descends (prefixWord ++ tailWord_1501417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1501442 : List Nat := [3, 4, 1, 1, 2, 1, 4, 2, 1, 3]
def baseStart_1501442 : Nat := 118140960795 + 1501442 * 2 ^ 59
def prefixEnd_1501442 : Nat := 4983230072969 + 3 ^ 40 * 1501442 * 2
def baseEnd_1501442 : Nat := 513974280565346556646667

theorem tailTrace_1501442 : CollatzResearch.WordTrace tailWord_1501442 prefixEnd_1501442 513974280565346556646667 := by
  unfold tailWord_1501442
  simp only [CollatzResearch.WordTrace]
  refine ⟨13690522156634883680900645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36508059084359689815735053 13690522156634883680900645)
  ·
    refine ⟨2566972904369040690168871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13690522156634883680900645 2566972904369040690168871)
    ·
      refine ⟨3850459356553561035253307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2566972904369040690168871 3850459356553561035253307)
      ·
        refine ⟨5775689034830341552879961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3850459356553561035253307 5775689034830341552879961)
        ·
          refine ⟨4331766776122756164659971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5775689034830341552879961 4331766776122756164659971)
          ·
            refine ⟨6497650164184134246989957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4331766776122756164659971 6497650164184134246989957)
            ·
              refine ⟨1218309405784525171310617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6497650164184134246989957 1218309405784525171310617)
              ·
                refine ⟨913732054338393878482963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1218309405784525171310617 913732054338393878482963)
                ·
                  refine ⟨1370598081507590817724445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 913732054338393878482963 1370598081507590817724445)
                  ·
                    refine ⟨513974280565346556646667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1370598081507590817724445 513974280565346556646667)
                    ·
                      rfl

theorem cell22_1501442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 4, 2, 1, 3].length) (baseStart_1501442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1501442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1501442 prefixEnd_1501442 := by exact prefixLift 1501442
  have htrace : WordTrace (prefixWord ++ tailWord_1501442) baseStart_1501442 baseEnd_1501442 := by
    simpa [prefixWord, tailWord_1501442, baseEnd_1501442] using wordTrace_append hprefix tailTrace_1501442
  have hstable : (prefixWord ++ tailWord_1501442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1501442).length < 2 ^ (prefixWord ++ tailWord_1501442).sum := by decide
  have hdescent : baseEnd_1501442 < baseStart_1501442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1501442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1501466 : List Nat := [3, 1, 1, 3, 4, 1, 1, 2, 6]
def baseStart_1501466 : Nat := 118140960795 + 1501466 * 2 ^ 59
def prefixEnd_1501466 : Nat := 4983230072969 + 3 ^ 40 * 1501466 * 2
def baseEnd_1501466 : Nat := 171327498751939498015531

theorem tailTrace_1501466 : CollatzResearch.WordTrace tailWord_1501466 prefixEnd_1501466 171327498751939498015531 := by
  unfold tailWord_1501466
  simp only [CollatzResearch.WordTrace]
  refine ⟨13690740994613146705619063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36508642652301724548317501 13690740994613146705619063)
  ·
    refine ⟨20536111491919720058428595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13690740994613146705619063 20536111491919720058428595)
    ·
      refine ⟨30804167237879580087642893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20536111491919720058428595 30804167237879580087642893)
      ·
        refine ⟨11551562714204842532866085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30804167237879580087642893 11551562714204842532866085)
        ·
          refine ⟨2165918008913407974912391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11551562714204842532866085 2165918008913407974912391)
          ·
            refine ⟨3248877013370111962368587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2165918008913407974912391 3248877013370111962368587)
            ·
              refine ⟨4873315520055167943552881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3248877013370111962368587 4873315520055167943552881)
              ·
                refine ⟨3654986640041375957664661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4873315520055167943552881 3654986640041375957664661)
                ·
                  refine ⟨171327498751939498015531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3654986640041375957664661 171327498751939498015531)
                  ·
                    rfl

theorem cell22_1501466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 2, 6].length) (baseStart_1501466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1501466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1501466 prefixEnd_1501466 := by exact prefixLift 1501466
  have htrace : WordTrace (prefixWord ++ tailWord_1501466) baseStart_1501466 baseEnd_1501466 := by
    simpa [prefixWord, tailWord_1501466, baseEnd_1501466] using wordTrace_append hprefix tailTrace_1501466
  have hstable : (prefixWord ++ tailWord_1501466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1501466).length < 2 ^ (prefixWord ++ tailWord_1501466).sum := by decide
  have hdescent : baseEnd_1501466 < baseStart_1501466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1501466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1501485 : List Nat := [1, 5, 3, 1, 2, 1, 1, 3, 1, 4]
def baseStart_1501485 : Nat := 118140960795 + 1501485 * 2 ^ 59
def prefixEnd_1501485 : Nat := 4983230072969 + 3 ^ 40 * 1501485 * 2
def baseEnd_1501485 : Nat := 513989000344108777821535

theorem tailTrace_1501485 : CollatzResearch.WordTrace tailWord_1501485 prefixEnd_1501485 513989000344108777821535 := by
  unfold tailWord_1501485
  simp only [CollatzResearch.WordTrace]
  refine ⟨54763656965383753067417909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36509104643589168711611939 54763656965383753067417909)
  ·
    refine ⟨5134092840504726850070429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 54763656965383753067417909 5134092840504726850070429)
    ·
      refine ⟨1925284815189272568776411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5134092840504726850070429 1925284815189272568776411)
      ·
        refine ⟨2887927222783908853164617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1925284815189272568776411 2887927222783908853164617)
        ·
          refine ⟨2165945417087931639873463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2887927222783908853164617 2165945417087931639873463)
          ·
            refine ⟨3248918125631897459810195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2165945417087931639873463 3248918125631897459810195)
            ·
              refine ⟨4873377188447846189715293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3248918125631897459810195 4873377188447846189715293)
              ·
                refine ⟨1827516445667942321143235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4873377188447846189715293 1827516445667942321143235)
                ·
                  refine ⟨2741274668501913481714853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1827516445667942321143235 2741274668501913481714853)
                  ·
                    refine ⟨513989000344108777821535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2741274668501913481714853 513989000344108777821535)
                    ·
                      rfl

theorem cell22_1501485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_1501485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1501485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1501485 prefixEnd_1501485 := by exact prefixLift 1501485
  have htrace : WordTrace (prefixWord ++ tailWord_1501485) baseStart_1501485 baseEnd_1501485 := by
    simpa [prefixWord, tailWord_1501485, baseEnd_1501485] using wordTrace_append hprefix tailTrace_1501485
  have hstable : (prefixWord ++ tailWord_1501485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1501485).length < 2 ^ (prefixWord ++ tailWord_1501485).sum := by decide
  have hdescent : baseEnd_1501485 < baseStart_1501485 := by decide
  rcases family_descends (prefixWord ++ tailWord_1501485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1501498 : List Nat := [3, 1, 1, 1, 4, 2, 3, 2, 2, 3]
def baseStart_1501498 : Nat := 118140960795 + 1501498 * 2 ^ 59
def prefixEnd_1501498 : Nat := 4983230072969 + 3 ^ 40 * 1501498 * 2
def baseEnd_1501498 : Nat := 513993450509781077246495

theorem tailTrace_1501498 : CollatzResearch.WordTrace tailWord_1501498 prefixEnd_1501498 513993450509781077246495 := by
  unfold tailWord_1501498
  simp only [CollatzResearch.WordTrace]
  refine ⟨13691032778584164071910287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36509420742891104191760765 13691032778584164071910287)
  ·
    refine ⟨20536549167876246107865431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13691032778584164071910287 20536549167876246107865431)
    ·
      refine ⟨30804823751814369161798147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20536549167876246107865431 30804823751814369161798147)
      ·
        refine ⟨46207235627721553742697221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30804823751814369161798147 46207235627721553742697221)
        ·
          refine ⟨8663856680197791326755729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46207235627721553742697221 8663856680197791326755729)
          ·
            refine ⟨6497892510148343495066797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8663856680197791326755729 6497892510148343495066797)
            ·
              refine ⟨2436709691305628810650049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6497892510148343495066797 2436709691305628810650049)
              ·
                refine ⟨1827532268479221607987537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2436709691305628810650049 1827532268479221607987537)
                ·
                  refine ⟨1370649201359416205990653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1827532268479221607987537 1370649201359416205990653)
                  ·
                    refine ⟨513993450509781077246495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1370649201359416205990653 513993450509781077246495)
                    ·
                      rfl

theorem cell22_1501498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 3, 2, 2, 3].length) (baseStart_1501498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1501498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1501498 prefixEnd_1501498 := by exact prefixLift 1501498
  have htrace : WordTrace (prefixWord ++ tailWord_1501498) baseStart_1501498 baseEnd_1501498 := by
    simpa [prefixWord, tailWord_1501498, baseEnd_1501498] using wordTrace_append hprefix tailTrace_1501498
  have hstable : (prefixWord ++ tailWord_1501498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1501498).length < 2 ^ (prefixWord ++ tailWord_1501498).sum := by decide
  have hdescent : baseEnd_1501498 < baseStart_1501498 := by decide
  rcases family_descends (prefixWord ++ tailWord_1501498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1501539 : List Nat := [1, 1, 1, 5, 2, 1, 1, 1, 9]
def baseStart_1501539 : Nat := 118140960795 + 1501539 * 2 ^ 59
def prefixEnd_1501539 : Nat := 4983230072969 + 3 ^ 40 * 1501539 * 2
def baseEnd_1501539 : Nat := 171335828549223545657123

theorem tailTrace_1501539 : CollatzResearch.WordTrace tailWord_1501539 prefixEnd_1501539 171335828549223545657123 := by
  unfold tailWord_1501539
  simp only [CollatzResearch.WordTrace]
  refine ⟨54765626507188120289883671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36510417671458746859922447 54765626507188120289883671)
  ·
    refine ⟨82148439760782180434825507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54765626507188120289883671 82148439760782180434825507)
    ·
      refine ⟨123222659641173270652238261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82148439760782180434825507 123222659641173270652238261)
      ·
        refine ⟨11552124341359994123647337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 123222659641173270652238261 11552124341359994123647337)
        ·
          refine ⟨8664093256019995592735503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11552124341359994123647337 8664093256019995592735503)
          ·
            refine ⟨12996139884029993389103255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8664093256019995592735503 12996139884029993389103255)
            ·
              refine ⟨19494209826044990083654883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12996139884029993389103255 19494209826044990083654883)
              ·
                refine ⟨29241314739067485125482325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19494209826044990083654883 29241314739067485125482325)
                ·
                  refine ⟨171335828549223545657123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 29241314739067485125482325 171335828549223545657123)
                  ·
                    rfl

theorem cell22_1501539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 9].length) (baseStart_1501539 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1501539 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1501539 prefixEnd_1501539 := by exact prefixLift 1501539
  have htrace : WordTrace (prefixWord ++ tailWord_1501539) baseStart_1501539 baseEnd_1501539 := by
    simpa [prefixWord, tailWord_1501539, baseEnd_1501539] using wordTrace_append hprefix tailTrace_1501539
  have hstable : (prefixWord ++ tailWord_1501539).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1501539).length < 2 ^ (prefixWord ++ tailWord_1501539).sum := by decide
  have hdescent : baseEnd_1501539 < baseStart_1501539 := by decide
  rcases family_descends (prefixWord ++ tailWord_1501539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1501616 : List Nat := [2, 1, 1, 1, 2, 1, 1, 2, 8, 3]
def baseStart_1501616 : Nat := 118140960795 + 1501616 * 2 ^ 59
def prefixEnd_1501616 : Nat := 4983230072969 + 3 ^ 40 * 1501616 * 2
def baseEnd_1501616 : Nat := 514033844321268102796133

theorem tailTrace_1501616 : CollatzResearch.WordTrace tailWord_1501616 prefixEnd_1501616 514033844321268102796133 := by
  unfold tailWord_1501616
  simp only [CollatzResearch.WordTrace]
  refine ⟨27384217463954581220218351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36512289951939441626957801 27384217463954581220218351)
  ·
    refine ⟨41076326195931871830327527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27384217463954581220218351 41076326195931871830327527)
    ·
      refine ⟨61614489293897807745491291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41076326195931871830327527 61614489293897807745491291)
      ·
        refine ⟨92421733940846711618236937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61614489293897807745491291 92421733940846711618236937)
        ·
          refine ⟨69316300455635033713677703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92421733940846711618236937 69316300455635033713677703)
          ·
            refine ⟨103974450683452550570516555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69316300455635033713677703 103974450683452550570516555)
            ·
              refine ⟨155961676025178825855774833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103974450683452550570516555 155961676025178825855774833)
              ·
                refine ⟨116971257018884119391831125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 155961676025178825855774833 116971257018884119391831125)
                ·
                  refine ⟨1370756918190048274123021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 116971257018884119391831125 1370756918190048274123021)
                  ·
                    refine ⟨514033844321268102796133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1370756918190048274123021 514033844321268102796133)
                    ·
                      rfl

theorem cell22_1501616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 8, 3].length) (baseStart_1501616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1501616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1501616 prefixEnd_1501616 := by exact prefixLift 1501616
  have htrace : WordTrace (prefixWord ++ tailWord_1501616) baseStart_1501616 baseEnd_1501616 := by
    simpa [prefixWord, tailWord_1501616, baseEnd_1501616] using wordTrace_append hprefix tailTrace_1501616
  have hstable : (prefixWord ++ tailWord_1501616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1501616).length < 2 ^ (prefixWord ++ tailWord_1501616).sum := by decide
  have hdescent : baseEnd_1501616 < baseStart_1501616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1501616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1501618 : List Nat := [3, 2, 1, 1, 1, 1, 5, 4, 4]
def baseStart_1501618 : Nat := 118140960795 + 1501618 * 2 ^ 59
def prefixEnd_1501618 : Nat := 4983230072969 + 3 ^ 40 * 1501618 * 2
def baseEnd_1501618 : Nat := 171344842987380254748709

theorem tailTrace_1501618 : CollatzResearch.WordTrace tailWord_1501618 prefixEnd_1501618 171344842987380254748709 := by
  unfold tailWord_1501618
  simp only [CollatzResearch.WordTrace]
  refine ⟨13692126968475479195502377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36512338582601277854673005 13692126968475479195502377)
  ·
    refine ⟨10269095226356609396626783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13692126968475479195502377 10269095226356609396626783)
    ·
      refine ⟨15403642839534914094940175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10269095226356609396626783 15403642839534914094940175)
      ·
        refine ⟨23105464259302371142410263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15403642839534914094940175 23105464259302371142410263)
        ·
          refine ⟨34658196388953556713615395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23105464259302371142410263 34658196388953556713615395)
          ·
            refine ⟨51987294583430335070423093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34658196388953556713615395 51987294583430335070423093)
            ·
              refine ⟨4873808867196593912852165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 51987294583430335070423093 4873808867196593912852165)
              ·
                refine ⟨913839162599361358659781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4873808867196593912852165 913839162599361358659781)
                ·
                  refine ⟨171344842987380254748709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 913839162599361358659781 171344842987380254748709)
                  ·
                    rfl

theorem cell22_1501618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 4, 4].length) (baseStart_1501618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1501618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1501618 prefixEnd_1501618 := by exact prefixLift 1501618
  have htrace : WordTrace (prefixWord ++ tailWord_1501618) baseStart_1501618 baseEnd_1501618 := by
    simpa [prefixWord, tailWord_1501618, baseEnd_1501618] using wordTrace_append hprefix tailTrace_1501618
  have hstable : (prefixWord ++ tailWord_1501618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1501618).length < 2 ^ (prefixWord ++ tailWord_1501618).sum := by decide
  have hdescent : baseEnd_1501618 < baseStart_1501618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1501618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1501667 : List Nat := [1, 1, 1, 6, 3, 2, 1, 2, 2, 3]
def baseStart_1501667 : Nat := 118140960795 + 1501667 * 2 ^ 59
def prefixEnd_1501667 : Nat := 4983230072969 + 3 ^ 40 * 1501667 * 2
def baseEnd_1501667 : Nat := 514051302663520969770977

theorem tailTrace_1501667 : CollatzResearch.WordTrace tailWord_1501667 prefixEnd_1501667 514051302663520969770977 := by
  unfold tailWord_1501667
  simp only [CollatzResearch.WordTrace]
  refine ⟨54770295050724398150543255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36513530033816265433695503 54770295050724398150543255)
  ·
    refine ⟨82155442576086597225814883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54770295050724398150543255 82155442576086597225814883)
    ·
      refine ⟨123233163864129895838722325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82155442576086597225814883 123233163864129895838722325)
      ·
        refine ⟨5776554556131088867440109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 123233163864129895838722325 5776554556131088867440109)
        ·
          refine ⟨2166207958549158325290041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5776554556131088867440109 2166207958549158325290041)
          ·
            refine ⟨1624655968911868743967531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2166207958549158325290041 1624655968911868743967531)
            ·
              refine ⟨2436983953367803115951297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1624655968911868743967531 2436983953367803115951297)
              ·
                refine ⟨1827737965025852336963473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2436983953367803115951297 1827737965025852336963473)
                ·
                  refine ⟨1370803473769389252722605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1827737965025852336963473 1370803473769389252722605)
                  ·
                    refine ⟨514051302663520969770977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1370803473769389252722605 514051302663520969770977)
                    ·
                      rfl

theorem cell22_1501667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 1, 2, 2, 3].length) (baseStart_1501667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1501667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1501667 prefixEnd_1501667 := by exact prefixLift 1501667
  have htrace : WordTrace (prefixWord ++ tailWord_1501667) baseStart_1501667 baseEnd_1501667 := by
    simpa [prefixWord, tailWord_1501667, baseEnd_1501667] using wordTrace_append hprefix tailTrace_1501667
  have hstable : (prefixWord ++ tailWord_1501667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1501667).length < 2 ^ (prefixWord ++ tailWord_1501667).sum := by decide
  have hdescent : baseEnd_1501667 < baseStart_1501667 := by decide
  rcases family_descends (prefixWord ++ tailWord_1501667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1501768 : List Nat := [2, 1, 3, 1, 1, 1, 1, 3, 6, 3]
def baseStart_1501768 : Nat := 118140960795 + 1501768 * 2 ^ 59
def prefixEnd_1501768 : Nat := 4983230072969 + 3 ^ 40 * 1501768 * 2
def baseEnd_1501768 : Nat := 514085877027590372995667

theorem tailTrace_1501768 : CollatzResearch.WordTrace tailWord_1501768 prefixEnd_1501768 514085877027590372995667 := by
  unfold tailWord_1501768
  simp only [CollatzResearch.WordTrace]
  refine ⟨27386989411679246199984979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36515985882238994933313305 27386989411679246199984979)
  ·
    refine ⟨41080484117518869299977469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27386989411679246199984979 41080484117518869299977469)
    ·
      refine ⟨15405181544069575987491551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41080484117518869299977469 15405181544069575987491551)
      ·
        refine ⟨23107772316104363981237327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15405181544069575987491551 23107772316104363981237327)
        ·
          refine ⟨34661658474156545971855991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23107772316104363981237327 34661658474156545971855991)
          ·
            refine ⟨51992487711234818957783987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34661658474156545971855991 51992487711234818957783987)
            ·
              refine ⟨77988731566852228436675981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51992487711234818957783987 77988731566852228436675981)
              ·
                refine ⟨29245774337569585663753493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77988731566852228436675981 29245774337569585663753493)
                ·
                  refine ⟨1370895672073574327988445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 29245774337569585663753493 1370895672073574327988445)
                  ·
                    refine ⟨514085877027590372995667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1370895672073574327988445 514085877027590372995667)
                    ·
                      rfl

theorem cell22_1501768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 6, 3].length) (baseStart_1501768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1501768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1501768 prefixEnd_1501768 := by exact prefixLift 1501768
  have htrace : WordTrace (prefixWord ++ tailWord_1501768) baseStart_1501768 baseEnd_1501768 := by
    simpa [prefixWord, tailWord_1501768, baseEnd_1501768] using wordTrace_append hprefix tailTrace_1501768
  have hstable : (prefixWord ++ tailWord_1501768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1501768).length < 2 ^ (prefixWord ++ tailWord_1501768).sum := by decide
  have hdescent : baseEnd_1501768 < baseStart_1501768 := by decide
  rcases family_descends (prefixWord ++ tailWord_1501768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1501783 : List Nat := [1, 1, 3, 2, 2, 2, 1, 4, 2, 4]
def baseStart_1501783 : Nat := 118140960795 + 1501783 * 2 ^ 59
def prefixEnd_1501783 : Nat := 4983230072969 + 3 ^ 40 * 1501783 * 2
def baseEnd_1501783 : Nat := 514091011834135333870621

theorem tailTrace_1501783 : CollatzResearch.WordTrace tailWord_1501783 prefixEnd_1501783 514091011834135333870621 := by
  unfold tailWord_1501783
  simp only [CollatzResearch.WordTrace]
  refine ⟨54774525918304149961766003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36516350612202766641177335 54774525918304149961766003)
  ·
    refine ⟨82161788877456224942649005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54774525918304149961766003 82161788877456224942649005)
    ·
      refine ⟨30810670829046084353493377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82161788877456224942649005 30810670829046084353493377)
      ·
        refine ⟨23108003121784563265120033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30810670829046084353493377 23108003121784563265120033)
        ·
          refine ⟨17331002341338422448840025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23108003121784563265120033 17331002341338422448840025)
          ·
            refine ⟨12998251756003816836630019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17331002341338422448840025 12998251756003816836630019)
            ·
              refine ⟨19497377634005725254945029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12998251756003816836630019 19497377634005725254945029)
              ·
                refine ⟨3655758306376073485302193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19497377634005725254945029 3655758306376073485302193)
                ·
                  refine ⟨2741818729782055113976645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3655758306376073485302193 2741818729782055113976645)
                  ·
                    refine ⟨514091011834135333870621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2741818729782055113976645 514091011834135333870621)
                    ·
                      rfl

theorem cell22_1501783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 4, 2, 4].length) (baseStart_1501783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1501783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1501783 prefixEnd_1501783 := by exact prefixLift 1501783
  have htrace : WordTrace (prefixWord ++ tailWord_1501783) baseStart_1501783 baseEnd_1501783 := by
    simpa [prefixWord, tailWord_1501783, baseEnd_1501783] using wordTrace_append hprefix tailTrace_1501783
  have hstable : (prefixWord ++ tailWord_1501783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1501783).length < 2 ^ (prefixWord ++ tailWord_1501783).sum := by decide
  have hdescent : baseEnd_1501783 < baseStart_1501783 := by decide
  rcases family_descends (prefixWord ++ tailWord_1501783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1501847 : List Nat := [1, 1, 3, 3, 2, 1, 1, 6, 1, 3]
def baseStart_1501847 : Nat := 118140960795 + 1501847 * 2 ^ 59
def prefixEnd_1501847 : Nat := 4983230072969 + 3 ^ 40 * 1501847 * 2
def baseEnd_1501847 : Nat := 514112920342060500270425

theorem tailTrace_1501847 : CollatzResearch.WordTrace tailWord_1501847 prefixEnd_1501847 514112920342060500270425 := by
  unfold tailWord_1501847
  simp only [CollatzResearch.WordTrace]
  refine ⟨54776860190072288892095795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36517906793381525928063863 54776860190072288892095795)
  ·
    refine ⟨82165290285108433338143693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54776860190072288892095795 82165290285108433338143693)
    ·
      refine ⟨30811983856915662501803885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82165290285108433338143693 30811983856915662501803885)
      ·
        refine ⟨11554493946343373438176457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30811983856915662501803885 11554493946343373438176457)
        ·
          refine ⟨8665870459757530078632343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11554493946343373438176457 8665870459757530078632343)
          ·
            refine ⟨12998805689636295117948515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8665870459757530078632343 12998805689636295117948515)
            ·
              refine ⟨19498208534454442676922773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12998805689636295117948515 19498208534454442676922773)
              ·
                refine ⟨913978525052552000480755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 19498208534454442676922773 913978525052552000480755)
                ·
                  refine ⟨1370967787578828000721133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 913978525052552000480755 1370967787578828000721133)
                  ·
                    refine ⟨514112920342060500270425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1370967787578828000721133 514112920342060500270425)
                    ·
                      rfl

theorem cell22_1501847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 6, 1, 3].length) (baseStart_1501847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1501847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1501847 prefixEnd_1501847 := by exact prefixLift 1501847
  have htrace : WordTrace (prefixWord ++ tailWord_1501847) baseStart_1501847 baseEnd_1501847 := by
    simpa [prefixWord, tailWord_1501847, baseEnd_1501847] using wordTrace_append hprefix tailTrace_1501847
  have hstable : (prefixWord ++ tailWord_1501847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1501847).length < 2 ^ (prefixWord ++ tailWord_1501847).sum := by decide
  have hdescent : baseEnd_1501847 < baseStart_1501847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1501847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1501866 : List Nat := [3, 1, 5, 2, 2, 1, 2, 6]
def baseStart_1501866 : Nat := 118140960795 + 1501866 * 2 ^ 59
def prefixEnd_1501866 : Nat := 4983230072969 + 3 ^ 40 * 1501866 * 2
def baseEnd_1501866 : Nat := 57124380492261198227263

theorem tailTrace_1501866 : CollatzResearch.WordTrace tailWord_1501866 prefixEnd_1501866 57124380492261198227263 := by
  unfold tailWord_1501866
  simp only [CollatzResearch.WordTrace]
  refine ⟨13694388294250863784259363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36518368784668970091358301 13694388294250863784259363)
  ·
    refine ⟨20541582441376295676389045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13694388294250863784259363 20541582441376295676389045)
    ·
      refine ⟨1925773353879027719661473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20541582441376295676389045 1925773353879027719661473)
      ·
        refine ⟨1444330015409270789746105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1925773353879027719661473 1444330015409270789746105)
        ·
          refine ⟨1083247511556953092309579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1444330015409270789746105 1083247511556953092309579)
          ·
            refine ⟨1624871267335429638464369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1083247511556953092309579 1624871267335429638464369)
            ·
              refine ⟨1218653450501572228848277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1624871267335429638464369 1218653450501572228848277)
              ·
                refine ⟨57124380492261198227263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1218653450501572228848277 57124380492261198227263)
                ·
                  rfl

theorem cell22_1501866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 2, 6].length) (baseStart_1501866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1501866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1501866 prefixEnd_1501866 := by exact prefixLift 1501866
  have htrace : WordTrace (prefixWord ++ tailWord_1501866) baseStart_1501866 baseEnd_1501866 := by
    simpa [prefixWord, tailWord_1501866, baseEnd_1501866] using wordTrace_append hprefix tailTrace_1501866
  have hstable : (prefixWord ++ tailWord_1501866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1501866).length < 2 ^ (prefixWord ++ tailWord_1501866).sum := by decide
  have hdescent : baseEnd_1501866 < baseStart_1501866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1501866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1501935 : List Nat := [1, 1, 2, 1, 5, 2, 1, 3, 2, 4]
def baseStart_1501935 : Nat := 118140960795 + 1501935 * 2 ^ 59
def prefixEnd_1501935 : Nat := 4983230072969 + 3 ^ 40 * 1501935 * 2
def baseEnd_1501935 : Nat := 514143044540457604070155

theorem tailTrace_1501935 : CollatzResearch.WordTrace tailWord_1501935 prefixEnd_1501935 514143044540457604070155 := by
  unfold tailWord_1501935
  simp only [CollatzResearch.WordTrace]
  refine ⟨54780069813753479921299259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36520046542502319947532839 54780069813753479921299259)
  ·
    refine ⟨82170104720630219881948889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54780069813753479921299259 82170104720630219881948889)
    ·
      refine ⟨61627578540472664911461667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82170104720630219881948889 61627578540472664911461667)
      ·
        refine ⟨92441367810708997367192501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61627578540472664911461667 92441367810708997367192501)
        ·
          refine ⟨8666378232253968503174297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 92441367810708997367192501 8666378232253968503174297)
          ·
            refine ⟨6499783674190476377380723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8666378232253968503174297 6499783674190476377380723)
            ·
              refine ⟨9749675511285714566071085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6499783674190476377380723 9749675511285714566071085)
              ·
                refine ⟨3656128316732142962276657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9749675511285714566071085 3656128316732142962276657)
                ·
                  refine ⟨2742096237549107221707493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3656128316732142962276657 2742096237549107221707493)
                  ·
                    refine ⟨514143044540457604070155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2742096237549107221707493 514143044540457604070155)
                    ·
                      rfl

theorem cell22_1501935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 3, 2, 4].length) (baseStart_1501935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1501935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1501935 prefixEnd_1501935 := by exact prefixLift 1501935
  have htrace : WordTrace (prefixWord ++ tailWord_1501935) baseStart_1501935 baseEnd_1501935 := by
    simpa [prefixWord, tailWord_1501935, baseEnd_1501935] using wordTrace_append hprefix tailTrace_1501935
  have hstable : (prefixWord ++ tailWord_1501935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1501935).length < 2 ^ (prefixWord ++ tailWord_1501935).sum := by decide
  have hdescent : baseEnd_1501935 < baseStart_1501935 := by decide
  rcases family_descends (prefixWord ++ tailWord_1501935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1501950 : List Nat := [4, 2, 2, 1, 2, 11]
def baseStart_1501950 : Nat := 118140960795 + 1501950 * 2 ^ 59
def prefixEnd_1501950 : Nat := 4983230072969 + 3 ^ 40 * 1501950 * 2
def baseEnd_1501950 : Nat := 6347508387000031665989

theorem tailTrace_1501950 : CollatzResearch.WordTrace tailWord_1501950 prefixEnd_1501950 6347508387000031665989 := by
  unfold tailWord_1501950
  simp only [CollatzResearch.WordTrace]
  refine ⟨6847577113587392185386913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36520411272466091655396869 6847577113587392185386913)
  ·
    refine ⟨5135682835190544139040185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6847577113587392185386913 5135682835190544139040185)
    ·
      refine ⟨3851762126392908104280139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5135682835190544139040185 3851762126392908104280139)
      ·
        refine ⟨5777643189589362156420209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3851762126392908104280139 5777643189589362156420209)
        ·
          refine ⟨4333232392192021617315157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5777643189589362156420209 4333232392192021617315157)
          ·
            refine ⟨6347508387000031665989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 4333232392192021617315157 6347508387000031665989)
            ·
              rfl

theorem cell22_1501950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 11].length) (baseStart_1501950 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1501950 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1501950 prefixEnd_1501950 := by exact prefixLift 1501950
  have htrace : WordTrace (prefixWord ++ tailWord_1501950) baseStart_1501950 baseEnd_1501950 := by
    simpa [prefixWord, tailWord_1501950, baseEnd_1501950] using wordTrace_append hprefix tailTrace_1501950
  have hstable : (prefixWord ++ tailWord_1501950).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1501950).length < 2 ^ (prefixWord ++ tailWord_1501950).sum := by decide
  have hdescent : baseEnd_1501950 < baseStart_1501950 := by decide
  rcases family_descends (prefixWord ++ tailWord_1501950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1501954 : List Nat := [3, 4, 1, 1, 1, 2, 1, 4, 2, 3]
def baseStart_1501954 : Nat := 118140960795 + 1501954 * 2 ^ 59
def prefixEnd_1501954 : Nat := 4983230072969 + 3 ^ 40 * 1501954 * 2
def baseEnd_1501954 : Nat := 514149548628747887845097

theorem tailTrace_1501954 : CollatzResearch.WordTrace tailWord_1501954 prefixEnd_1501954 514149548628747887845097 := by
  unfold tailWord_1501954
  simp only [CollatzResearch.WordTrace]
  refine ⟨13695190700171161541560229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36520508533789764110827277 13695190700171161541560229)
  ·
    refine ⟨2567848256282092789042543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13695190700171161541560229 2567848256282092789042543)
    ·
      refine ⟨3851772384423139183563815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2567848256282092789042543 3851772384423139183563815)
      ·
        refine ⟨5777658576634708775345723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3851772384423139183563815 5777658576634708775345723)
        ·
          refine ⟨8666487864952063163018585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5777658576634708775345723 8666487864952063163018585)
          ·
            refine ⟨6499865898714047372263939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8666487864952063163018585 6499865898714047372263939)
            ·
              refine ⟨9749798848071071058395909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6499865898714047372263939 9749798848071071058395909)
              ·
                refine ⟨1828087284013325823449233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9749798848071071058395909 1828087284013325823449233)
                ·
                  refine ⟨1371065463009994367586925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1828087284013325823449233 1371065463009994367586925)
                  ·
                    refine ⟨514149548628747887845097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1371065463009994367586925 514149548628747887845097)
                    ·
                      rfl

theorem cell22_1501954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 4, 2, 3].length) (baseStart_1501954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1501954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1501954 prefixEnd_1501954 := by exact prefixLift 1501954
  have htrace : WordTrace (prefixWord ++ tailWord_1501954) baseStart_1501954 baseEnd_1501954 := by
    simpa [prefixWord, tailWord_1501954, baseEnd_1501954] using wordTrace_append hprefix tailTrace_1501954
  have hstable : (prefixWord ++ tailWord_1501954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1501954).length < 2 ^ (prefixWord ++ tailWord_1501954).sum := by decide
  have hdescent : baseEnd_1501954 < baseStart_1501954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1501954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1502042 : List Nat := [3, 1, 1, 2, 1, 4, 1, 4, 1, 4]
def baseStart_1502042 : Nat := 118140960795 + 1502042 * 2 ^ 59
def prefixEnd_1502042 : Nat := 4983230072969 + 3 ^ 40 * 1502042 * 2
def baseEnd_1502042 : Nat := 514179672827144991644827

theorem tailTrace_1502042 : CollatzResearch.WordTrace tailWord_1502042 prefixEnd_1502042 514179672827144991644827 := by
  unfold tailWord_1502042
  simp only [CollatzResearch.WordTrace]
  refine ⟨13695993106091459298861095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36522648282910558130296253 13695993106091459298861095)
  ·
    refine ⟨20543989659137188948291643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13695993106091459298861095 20543989659137188948291643)
    ·
      refine ⟨30815984488705783422437465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20543989659137188948291643 30815984488705783422437465)
      ·
        refine ⟨23111988366529337566828099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30815984488705783422437465 23111988366529337566828099)
        ·
          refine ⟨34667982549794006350242149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23111988366529337566828099 34667982549794006350242149)
          ·
            refine ⟨6500246728086376190670403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34667982549794006350242149 6500246728086376190670403)
            ·
              refine ⟨9750370092129564286005605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6500246728086376190670403 9750370092129564286005605)
              ·
                refine ⟨1828194392274293303626051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9750370092129564286005605 1828194392274293303626051)
                ·
                  refine ⟨2742291588411439955439077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1828194392274293303626051 2742291588411439955439077)
                  ·
                    refine ⟨514179672827144991644827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2742291588411439955439077 514179672827144991644827)
                    ·
                      rfl

theorem cell22_1502042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 4, 1, 4].length) (baseStart_1502042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1502042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1502042 prefixEnd_1502042 := by exact prefixLift 1502042
  have htrace : WordTrace (prefixWord ++ tailWord_1502042) baseStart_1502042 baseEnd_1502042 := by
    simpa [prefixWord, tailWord_1502042, baseEnd_1502042] using wordTrace_append hprefix tailTrace_1502042
  have hstable : (prefixWord ++ tailWord_1502042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1502042).length < 2 ^ (prefixWord ++ tailWord_1502042).sum := by decide
  have hdescent : baseEnd_1502042 < baseStart_1502042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1502042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1502050 : List Nat := [3, 3, 2, 1, 4, 1, 1, 3, 1, 3]
def baseStart_1502050 : Nat := 118140960795 + 1502050 * 2 ^ 59
def prefixEnd_1502050 : Nat := 4983230072969 + 3 ^ 40 * 1502050 * 2
def baseEnd_1502050 : Nat := 514182411390635637444803

theorem tailTrace_1502050 : CollatzResearch.WordTrace tailWord_1502050 prefixEnd_1502050 514182411390635637444803 := by
  unfold tailWord_1502050
  simp only [CollatzResearch.WordTrace]
  refine ⟨13696066052084213640433901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36522842805557903041157069 13696066052084213640433901)
  ·
    refine ⟨5136024769531580115162713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13696066052084213640433901 5136024769531580115162713)
    ·
      refine ⟨3852018577148685086372035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5136024769531580115162713 3852018577148685086372035)
      ·
        refine ⟨5778027865723027629558053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3852018577148685086372035 5778027865723027629558053)
        ·
          refine ⟨1083380224823067680542135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5778027865723027629558053 1083380224823067680542135)
          ·
            refine ⟨1625070337234601520813203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1083380224823067680542135 1625070337234601520813203)
            ·
              refine ⟨2437605505851902281219805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1625070337234601520813203 2437605505851902281219805)
              ·
                refine ⟨914102064694463355457427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2437605505851902281219805 914102064694463355457427)
                ·
                  refine ⟨1371153097041695033186141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 914102064694463355457427 1371153097041695033186141)
                  ·
                    refine ⟨514182411390635637444803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1371153097041695033186141 514182411390635637444803)
                    ·
                      rfl

theorem cell22_1502050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 1, 3, 1, 3].length) (baseStart_1502050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1502050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1502050 prefixEnd_1502050 := by exact prefixLift 1502050
  have htrace : WordTrace (prefixWord ++ tailWord_1502050) baseStart_1502050 baseEnd_1502050 := by
    simpa [prefixWord, tailWord_1502050, baseEnd_1502050] using wordTrace_append hprefix tailTrace_1502050
  have hstable : (prefixWord ++ tailWord_1502050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1502050).length < 2 ^ (prefixWord ++ tailWord_1502050).sum := by decide
  have hdescent : baseEnd_1502050 < baseStart_1502050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1502050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1502085 : List Nat := [1, 3, 1, 1, 3, 3, 1, 9]
def baseStart_1502085 : Nat := 118140960795 + 1502085 * 2 ^ 59
def prefixEnd_1502085 : Nat := 4983230072969 + 3 ^ 40 * 1502085 * 2
def baseEnd_1502085 : Nat := 57132710289545245868855

theorem tailTrace_1502085 : CollatzResearch.WordTrace tailWord_1502085 prefixEnd_1502085 57132710289545245868855 := by
  unfold tailWord_1502085
  simp only [CollatzResearch.WordTrace]
  refine ⟨54785540763210055539259709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36523693842140037026173139 54785540763210055539259709)
  ·
    refine ⟨20544577786203770827222391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54785540763210055539259709 20544577786203770827222391)
    ·
      refine ⟨30816866679305656240833587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20544577786203770827222391 30816866679305656240833587)
      ·
        refine ⟨46225300018958484361250381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30816866679305656240833587 46225300018958484361250381)
        ·
          refine ⟨17334487507109431635468893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46225300018958484361250381 17334487507109431635468893)
          ·
            refine ⟨6500432815166036863300835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17334487507109431635468893 6500432815166036863300835)
            ·
              refine ⟨9750649222749055294951253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6500432815166036863300835 9750649222749055294951253)
              ·
                refine ⟨57132710289545245868855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9750649222749055294951253 57132710289545245868855)
                ·
                  rfl

theorem cell22_1502085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 9].length) (baseStart_1502085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1502085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1502085 prefixEnd_1502085 := by exact prefixLift 1502085
  have htrace : WordTrace (prefixWord ++ tailWord_1502085) baseStart_1502085 baseEnd_1502085 := by
    simpa [prefixWord, tailWord_1502085, baseEnd_1502085] using wordTrace_append hprefix tailTrace_1502085
  have hstable : (prefixWord ++ tailWord_1502085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1502085).length < 2 ^ (prefixWord ++ tailWord_1502085).sum := by decide
  have hdescent : baseEnd_1502085 < baseStart_1502085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1502085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1502089 : List Nat := [1, 2, 1, 1, 5, 3, 1, 3, 2, 3]
def baseStart_1502089 : Nat := 118140960795 + 1502089 * 2 ^ 59
def prefixEnd_1502089 : Nat := 4983230072969 + 3 ^ 40 * 1502089 * 2
def baseEnd_1502089 : Nat := 514195761887652535719683

theorem tailTrace_1502089 : CollatzResearch.WordTrace tailWord_1502089 prefixEnd_1502089 514195761887652535719683 := by
  unfold tailWord_1502089
  simp only [CollatzResearch.WordTrace]
  refine ⟨54785686655195564222405321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36523791103463709481603547 54785686655195564222405321)
  ·
    refine ⟨41089264991396673166803991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54785686655195564222405321 41089264991396673166803991)
    ·
      refine ⟨61633897487095009750205987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41089264991396673166803991 61633897487095009750205987)
      ·
        refine ⟨92450846230642514625308981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61633897487095009750205987 92450846230642514625308981)
        ·
          refine ⟨8667266834122735746122717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 92450846230642514625308981 8667266834122735746122717)
          ·
            refine ⟨3250225062796025904796019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8667266834122735746122717 3250225062796025904796019)
            ·
              refine ⟨4875337594194038857194029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3250225062796025904796019 4875337594194038857194029)
              ·
                refine ⟨1828251597822764571447761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4875337594194038857194029 1828251597822764571447761)
                ·
                  refine ⟨1371188698367073428585821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1828251597822764571447761 1371188698367073428585821)
                  ·
                    refine ⟨514195761887652535719683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1371188698367073428585821 514195761887652535719683)
                    ·
                      rfl

theorem cell22_1502089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 3, 2, 3].length) (baseStart_1502089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1502089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1502089 prefixEnd_1502089 := by exact prefixLift 1502089
  have htrace : WordTrace (prefixWord ++ tailWord_1502089) baseStart_1502089 baseEnd_1502089 := by
    simpa [prefixWord, tailWord_1502089, baseEnd_1502089] using wordTrace_append hprefix tailTrace_1502089
  have hstable : (prefixWord ++ tailWord_1502089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1502089).length < 2 ^ (prefixWord ++ tailWord_1502089).sum := by decide
  have hdescent : baseEnd_1502089 < baseStart_1502089 := by decide
  rcases family_descends (prefixWord ++ tailWord_1502089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1502125 : List Nat := [1, 5, 2, 3, 1, 2, 2, 2, 4]
def baseStart_1502125 : Nat := 118140960795 + 1502125 * 2 ^ 59
def prefixEnd_1502125 : Nat := 4983230072969 + 3 ^ 40 * 1502125 * 2
def baseEnd_1502125 : Nat := 171402695141120147273191

theorem tailTrace_1502125 : CollatzResearch.WordTrace tailWord_1502125 prefixEnd_1502125 171402695141120147273191 := by
  unfold tailWord_1502125
  simp only [CollatzResearch.WordTrace]
  refine ⟨54786999683065142370715829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36524666455376761580477219 54786999683065142370715829)
  ·
    refine ⟨5136281220287357097254609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 54786999683065142370715829 5136281220287357097254609)
    ·
      refine ⟨3852210915215517822940957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5136281220287357097254609 3852210915215517822940957)
      ·
        refine ⟨1444579093205819183602859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3852210915215517822940957 1444579093205819183602859)
        ·
          refine ⟨2166868639808728775404289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1444579093205819183602859 2166868639808728775404289)
          ·
            refine ⟨1625151479856546581553217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2166868639808728775404289 1625151479856546581553217)
            ·
              refine ⟨1218863609892409936164913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1625151479856546581553217 1218863609892409936164913)
              ·
                refine ⟨914147707419307452123685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1218863609892409936164913 914147707419307452123685)
                ·
                  refine ⟨171402695141120147273191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 914147707419307452123685 171402695141120147273191)
                  ·
                    rfl

theorem cell22_1502125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 2, 2, 4].length) (baseStart_1502125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1502125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1502125 prefixEnd_1502125 := by exact prefixLift 1502125
  have htrace : WordTrace (prefixWord ++ tailWord_1502125) baseStart_1502125 baseEnd_1502125 := by
    simpa [prefixWord, tailWord_1502125, baseEnd_1502125] using wordTrace_append hprefix tailTrace_1502125
  have hstable : (prefixWord ++ tailWord_1502125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1502125).length < 2 ^ (prefixWord ++ tailWord_1502125).sum := by decide
  have hdescent : baseEnd_1502125 < baseStart_1502125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1502125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1502239 : List Nat := [1, 1, 2, 4, 1, 4, 1, 2, 2, 4]
def baseStart_1502239 : Nat := 118140960795 + 1502239 * 2 ^ 59
def prefixEnd_1502239 : Nat := 4983230072969 + 3 ^ 40 * 1502239 * 2
def baseEnd_1502239 : Nat := 514247109953102144469223

theorem tailTrace_1502239 : CollatzResearch.WordTrace tailWord_1502239 prefixEnd_1502239 514247109953102144469223 := by
  unfold tailWord_1502239
  simp only [CollatzResearch.WordTrace]
  refine ⟨54791157604652139840365771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36527438403101426560243847 54791157604652139840365771)
  ·
    refine ⟨82186736406978209760548657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54791157604652139840365771 82186736406978209760548657)
    ·
      refine ⟨61640052305233657320411493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82186736406978209760548657 61640052305233657320411493)
      ·
        refine ⟨11557509807231310747577155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61640052305233657320411493 11557509807231310747577155)
        ·
          refine ⟨17336264710846966121365733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11557509807231310747577155 17336264710846966121365733)
          ·
            refine ⟨3250549633283806147756075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17336264710846966121365733 3250549633283806147756075)
            ·
              refine ⟨4875824449925709221634113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3250549633283806147756075 4875824449925709221634113)
              ·
                refine ⟨3656868337444281916225585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4875824449925709221634113 3656868337444281916225585)
                ·
                  refine ⟨2742651253083211437169189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3656868337444281916225585 2742651253083211437169189)
                  ·
                    refine ⟨514247109953102144469223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2742651253083211437169189 514247109953102144469223)
                    ·
                      rfl

theorem cell22_1502239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 2, 2, 4].length) (baseStart_1502239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1502239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1502239 prefixEnd_1502239 := by exact prefixLift 1502239
  have htrace : WordTrace (prefixWord ++ tailWord_1502239) baseStart_1502239 baseEnd_1502239 := by
    simpa [prefixWord, tailWord_1502239, baseEnd_1502239] using wordTrace_append hprefix tailTrace_1502239
  have hstable : (prefixWord ++ tailWord_1502239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1502239).length < 2 ^ (prefixWord ++ tailWord_1502239).sum := by decide
  have hdescent : baseEnd_1502239 < baseStart_1502239 := by decide
  rcases family_descends (prefixWord ++ tailWord_1502239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1502254 : List Nat := [4, 1, 3, 1, 1, 1, 4, 7]
def baseStart_1502254 : Nat := 118140960795 + 1502254 * 2 ^ 59
def prefixEnd_1502254 : Nat := 4983230072969 + 3 ^ 40 * 1502254 * 2
def baseEnd_1502254 : Nat := 57139138306627456149353

theorem tailTrace_1502254 : CollatzResearch.WordTrace tailWord_1502254 prefixEnd_1502254 57139138306627456149353 := by
  unfold tailWord_1502254
  simp only [CollatzResearch.WordTrace]
  refine ⟨6848963087449724675270227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36527803133065198268107877 6848963087449724675270227)
  ·
    refine ⟨10273444631174587012905341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6848963087449724675270227 10273444631174587012905341)
    ·
      refine ⟨3852541736690470129839503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10273444631174587012905341 3852541736690470129839503)
      ·
        refine ⟨5778812605035705194759255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3852541736690470129839503 5778812605035705194759255)
        ·
          refine ⟨8668218907553557792138883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5778812605035705194759255 8668218907553557792138883)
          ·
            refine ⟨13002328361330336688208325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8668218907553557792138883 13002328361330336688208325)
            ·
              refine ⟨2437936567749438129039061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13002328361330336688208325 2437936567749438129039061)
              ·
                refine ⟨57139138306627456149353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2437936567749438129039061 57139138306627456149353)
                ·
                  rfl

theorem cell22_1502254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 4, 7].length) (baseStart_1502254 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1502254 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1502254 prefixEnd_1502254 := by exact prefixLift 1502254
  have htrace : WordTrace (prefixWord ++ tailWord_1502254) baseStart_1502254 baseEnd_1502254 := by
    simpa [prefixWord, tailWord_1502254, baseEnd_1502254] using wordTrace_append hprefix tailTrace_1502254
  have hstable : (prefixWord ++ tailWord_1502254).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1502254).length < 2 ^ (prefixWord ++ tailWord_1502254).sum := by decide
  have hdescent : baseEnd_1502254 < baseStart_1502254 := by decide
  rcases family_descends (prefixWord ++ tailWord_1502254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1502282 : List Nat := [3, 1, 2, 1, 1, 2, 2, 1, 9]
def baseStart_1502282 : Nat := 118140960795 + 1502282 * 2 ^ 59
def prefixEnd_1502282 : Nat := 4983230072969 + 3 ^ 40 * 1502282 * 2
def baseEnd_1502282 : Nat := 171420609910621455214697

theorem tailTrace_1502282 : CollatzResearch.WordTrace tailWord_1502282 prefixEnd_1502282 171420609910621455214697 := by
  unfold tailWord_1502282
  simp only [CollatzResearch.WordTrace]
  refine ⟨13698181485874089546045275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36528483962330905456120733 13698181485874089546045275)
  ·
    refine ⟨20547272228811134319067913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13698181485874089546045275 20547272228811134319067913)
    ·
      refine ⟨15410454171608350739300935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20547272228811134319067913 15410454171608350739300935)
      ·
        refine ⟨23115681257412526108951403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15410454171608350739300935 23115681257412526108951403)
        ·
          refine ⟨34673521886118789163427105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23115681257412526108951403 34673521886118789163427105)
          ·
            refine ⟨26005141414589091872570329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34673521886118789163427105 26005141414589091872570329)
            ·
              refine ⟨19503856060941818904427747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26005141414589091872570329 19503856060941818904427747)
              ·
                refine ⟨29255784091412728356641621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19503856060941818904427747 29255784091412728356641621)
                ·
                  refine ⟨171420609910621455214697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 29255784091412728356641621 171420609910621455214697)
                  ·
                    rfl

theorem cell22_1502282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 9].length) (baseStart_1502282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1502282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1502282 prefixEnd_1502282 := by exact prefixLift 1502282
  have htrace : WordTrace (prefixWord ++ tailWord_1502282) baseStart_1502282 baseEnd_1502282 := by
    simpa [prefixWord, tailWord_1502282, baseEnd_1502282] using wordTrace_append hprefix tailTrace_1502282
  have hstable : (prefixWord ++ tailWord_1502282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1502282).length < 2 ^ (prefixWord ++ tailWord_1502282).sum := by decide
  have hdescent : baseEnd_1502282 < baseStart_1502282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1502282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1502294 : List Nat := [5, 2, 2, 1, 3, 1, 2, 2, 4]
def baseStart_1502294 : Nat := 118140960795 + 1502294 * 2 ^ 59
def prefixEnd_1502294 : Nat := 4983230072969 + 3 ^ 40 * 1502294 * 2
def baseEnd_1502294 : Nat := 171421979192366778114685

theorem tailTrace_1502294 : CollatzResearch.WordTrace tailWord_1502294 prefixEnd_1502294 171421979192366778114685 := by
  unfold tailWord_1502294
  simp only [CollatzResearch.WordTrace]
  refine ⟨3424572726215805264601121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36528775746301922822411957 3424572726215805264601121)
  ·
    refine ⟨2568429544661853948450841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3424572726215805264601121 2568429544661853948450841)
    ·
      refine ⟨1926322158496390461338131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2568429544661853948450841 1926322158496390461338131)
      ·
        refine ⟨2889483237744585692007197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1926322158496390461338131 2889483237744585692007197)
        ·
          refine ⟨1083556214154219634502699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2889483237744585692007197 1083556214154219634502699)
          ·
            refine ⟨1625334321231329451754049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1083556214154219634502699 1625334321231329451754049)
            ·
              refine ⟨1219000740923497088815537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1625334321231329451754049 1219000740923497088815537)
              ·
                refine ⟨914250555692622816611653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1219000740923497088815537 914250555692622816611653)
                ·
                  refine ⟨171421979192366778114685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 914250555692622816611653 171421979192366778114685)
                  ·
                    rfl

theorem cell22_1502294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 2, 2, 4].length) (baseStart_1502294 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1502294 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1502294 prefixEnd_1502294 := by exact prefixLift 1502294
  have htrace : WordTrace (prefixWord ++ tailWord_1502294) baseStart_1502294 baseEnd_1502294 := by
    simpa [prefixWord, tailWord_1502294, baseEnd_1502294] using wordTrace_append hprefix tailTrace_1502294
  have hstable : (prefixWord ++ tailWord_1502294).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1502294).length < 2 ^ (prefixWord ++ tailWord_1502294).sum := by decide
  have hdescent : baseEnd_1502294 < baseStart_1502294 := by decide
  rcases family_descends (prefixWord ++ tailWord_1502294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1502314 : List Nat := [3, 1, 3, 2, 2, 1, 1, 1, 1, 7]
def baseStart_1502314 : Nat := 118140960795 + 1502314 * 2 ^ 59
def prefixEnd_1502314 : Nat := 4983230072969 + 3 ^ 40 * 1502314 * 2
def baseEnd_1502314 : Nat := 514272783985826948843993

theorem tailTrace_1502314 : CollatzResearch.WordTrace tailWord_1502314 prefixEnd_1502314 514272783985826948843993 := by
  unfold tailWord_1502314
  simp only [CollatzResearch.WordTrace]
  refine ⟨13698473269845106912336499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36529262052920285099563997 13698473269845106912336499)
  ·
    refine ⟨20547709904767660368504749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13698473269845106912336499 20547709904767660368504749)
    ·
      refine ⟨7705391214287872638189281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20547709904767660368504749 7705391214287872638189281)
      ·
        refine ⟨5779043410715904478641961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7705391214287872638189281 5779043410715904478641961)
        ·
          refine ⟨4334282558036928358981471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5779043410715904478641961 4334282558036928358981471)
          ·
            refine ⟨6501423837055392538472207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4334282558036928358981471 6501423837055392538472207)
            ·
              refine ⟨9752135755583088807708311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6501423837055392538472207 9752135755583088807708311)
              ·
                refine ⟨14628203633374633211562467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9752135755583088807708311 14628203633374633211562467)
                ·
                  refine ⟨21942305450061949817343701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14628203633374633211562467 21942305450061949817343701)
                  ·
                    refine ⟨514272783985826948843993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21942305450061949817343701 514272783985826948843993)
                    ·
                      rfl

theorem cell22_1502314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 1, 1, 7].length) (baseStart_1502314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1502314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1502314 prefixEnd_1502314 := by exact prefixLift 1502314
  have htrace : WordTrace (prefixWord ++ tailWord_1502314) baseStart_1502314 baseEnd_1502314 := by
    simpa [prefixWord, tailWord_1502314, baseEnd_1502314] using wordTrace_append hprefix tailTrace_1502314
  have hstable : (prefixWord ++ tailWord_1502314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1502314).length < 2 ^ (prefixWord ++ tailWord_1502314).sum := by decide
  have hdescent : baseEnd_1502314 < baseStart_1502314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1502314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1502346 : List Nat := [3, 1, 2, 3, 1, 1, 3, 3, 1, 4]
def baseStart_1502346 : Nat := 118140960795 + 1502346 * 2 ^ 59
def prefixEnd_1502346 : Nat := 4983230072969 + 3 ^ 40 * 1502346 * 2
def baseEnd_1502346 : Nat := 514283738239789532043895

theorem tailTrace_1502346 : CollatzResearch.WordTrace tailWord_1502346 prefixEnd_1502346 514283738239789532043895 := by
  unfold tailWord_1502346
  simp only [CollatzResearch.WordTrace]
  refine ⟨13698765053816124278627723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36530040143509664743007261 13698765053816124278627723)
  ·
    refine ⟨20548147580724186417941585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13698765053816124278627723 20548147580724186417941585)
    ·
      refine ⟨15411110685543139813456189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20548147580724186417941585 15411110685543139813456189)
      ·
        refine ⟨5779166507078677430046071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15411110685543139813456189 5779166507078677430046071)
        ·
          refine ⟨8668749760618016145069107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5779166507078677430046071 8668749760618016145069107)
          ·
            refine ⟨13003124640927024217603661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8668749760618016145069107 13003124640927024217603661)
            ·
              refine ⟨4876171740347634081601373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13003124640927024217603661 4876171740347634081601373)
              ·
                refine ⟨1828564402630362780600515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4876171740347634081601373 1828564402630362780600515)
                ·
                  refine ⟨2742846603945544170900773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1828564402630362780600515 2742846603945544170900773)
                  ·
                    refine ⟨514283738239789532043895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2742846603945544170900773 514283738239789532043895)
                    ·
                      rfl

theorem cell22_1502346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 3, 1, 4].length) (baseStart_1502346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1502346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1502346 prefixEnd_1502346 := by exact prefixLift 1502346
  have htrace : WordTrace (prefixWord ++ tailWord_1502346) baseStart_1502346 baseEnd_1502346 := by
    simpa [prefixWord, tailWord_1502346, baseEnd_1502346] using wordTrace_append hprefix tailTrace_1502346
  have hstable : (prefixWord ++ tailWord_1502346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1502346).length < 2 ^ (prefixWord ++ tailWord_1502346).sum := by decide
  have hdescent : baseEnd_1502346 < baseStart_1502346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1502346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1502449 : List Nat := [1, 2, 2, 2, 2, 1, 1, 2, 4, 5]
def baseStart_1502449 : Nat := 118140960795 + 1502449 * 2 ^ 59
def prefixEnd_1502449 : Nat := 4983230072969 + 3 ^ 40 * 1502449 * 2
def baseEnd_1502449 : Nat := 514318997244731596718579

theorem tailTrace_1502449 : CollatzResearch.WordTrace tailWord_1502449 prefixEnd_1502449 514318997244731596718579 := by
  unfold tailWord_1502449
  simp only [CollatzResearch.WordTrace]
  refine ⟨54798816933891345705510401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36532544622594230470340267 54798816933891345705510401)
  ·
    refine ⟨41099112700418509279132801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54798816933891345705510401 41099112700418509279132801)
    ·
      refine ⟨30824334525313881959349601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41099112700418509279132801 30824334525313881959349601)
      ·
        refine ⟨23118250893985411469512201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30824334525313881959349601 23118250893985411469512201)
        ·
          refine ⟨17338688170489058602134151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23118250893985411469512201 17338688170489058602134151)
          ·
            refine ⟨26008032255733587903201227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17338688170489058602134151 26008032255733587903201227)
            ·
              refine ⟨39012048383600381854801841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26008032255733587903201227 39012048383600381854801841)
              ·
                refine ⟨29259036287700286391101381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39012048383600381854801841 29259036287700286391101381)
                ·
                  refine ⟨5486069303943803698331509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29259036287700286391101381 5486069303943803698331509)
                  ·
                    refine ⟨514318997244731596718579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5486069303943803698331509 514318997244731596718579)
                    ·
                      rfl

theorem cell22_1502449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 4, 5].length) (baseStart_1502449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1502449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1502449 prefixEnd_1502449 := by exact prefixLift 1502449
  have htrace : WordTrace (prefixWord ++ tailWord_1502449) baseStart_1502449 baseEnd_1502449 := by
    simpa [prefixWord, tailWord_1502449, baseEnd_1502449] using wordTrace_append hprefix tailTrace_1502449
  have hstable : (prefixWord ++ tailWord_1502449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1502449).length < 2 ^ (prefixWord ++ tailWord_1502449).sum := by decide
  have hdescent : baseEnd_1502449 < baseStart_1502449 := by decide
  rcases family_descends (prefixWord ++ tailWord_1502449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1502468 : List Nat := [2, 3, 2, 2, 2, 2, 2, 2, 5]
def baseStart_1502468 : Nat := 118140960795 + 1502468 * 2 ^ 59
def prefixEnd_1502468 : Nat := 4983230072969 + 3 ^ 40 * 1502468 * 2
def baseEnd_1502468 : Nat := 171441833777673960164507

theorem tailTrace_1502468 : CollatzResearch.WordTrace tailWord_1502468 prefixEnd_1502468 171441833777673960164507 := by
  unfold tailWord_1502468
  simp only [CollatzResearch.WordTrace]
  refine ⟨27399754960411255975226029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36533006613881674633634705 27399754960411255975226029)
  ·
    refine ⟨10274908110154220990709761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27399754960411255975226029 10274908110154220990709761)
    ·
      refine ⟨7706181082615665743032321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10274908110154220990709761 7706181082615665743032321)
      ·
        refine ⟨5779635811961749307274241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7706181082615665743032321 5779635811961749307274241)
        ·
          refine ⟨4334726858971311980455681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5779635811961749307274241 4334726858971311980455681)
          ·
            refine ⟨3251045144228483985341761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4334726858971311980455681 3251045144228483985341761)
            ·
              refine ⟨2438283858171362989006321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3251045144228483985341761 2438283858171362989006321)
              ·
                refine ⟨1828712893628522241754741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2438283858171362989006321 1828712893628522241754741)
                ·
                  refine ⟨171441833777673960164507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1828712893628522241754741 171441833777673960164507)
                  ·
                    rfl

theorem cell22_1502468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 2, 2, 5].length) (baseStart_1502468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1502468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1502468 prefixEnd_1502468 := by exact prefixLift 1502468
  have htrace : WordTrace (prefixWord ++ tailWord_1502468) baseStart_1502468 baseEnd_1502468 := by
    simpa [prefixWord, tailWord_1502468, baseEnd_1502468] using wordTrace_append hprefix tailTrace_1502468
  have hstable : (prefixWord ++ tailWord_1502468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1502468).length < 2 ^ (prefixWord ++ tailWord_1502468).sum := by decide
  have hdescent : baseEnd_1502468 < baseStart_1502468 := by decide
  rcases family_descends (prefixWord ++ tailWord_1502468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1502511 : List Nat := [1, 1, 2, 1, 2, 1, 3, 4, 4, 3]
def baseStart_1502511 : Nat := 118140960795 + 1502511 * 2 ^ 59
def prefixEnd_1502511 : Nat := 4983230072969 + 3 ^ 40 * 1502511 * 2
def baseEnd_1502511 : Nat := 514340221111784101668389

theorem tailTrace_1502511 : CollatzResearch.WordTrace tailWord_1502511 prefixEnd_1502511 514340221111784101668389 := by
  unfold tailWord_1502511
  simp only [CollatzResearch.WordTrace]
  refine ⟨54801078259666730294267387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36534052173111153529511591 54801078259666730294267387)
  ·
    refine ⟨82201617389500095441401081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54801078259666730294267387 82201617389500095441401081)
    ·
      refine ⟨61651213042125071581050811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82201617389500095441401081 61651213042125071581050811)
      ·
        refine ⟨92476819563187607371576217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61651213042125071581050811 92476819563187607371576217)
        ·
          refine ⟨69357614672390705528682163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92476819563187607371576217 69357614672390705528682163)
          ·
            refine ⟨104036422008586058293023245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69357614672390705528682163 104036422008586058293023245)
            ·
              refine ⟨39013658253219771859883717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104036422008586058293023245 39013658253219771859883717)
              ·
                refine ⟨7315060922478707223728197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39013658253219771859883717 7315060922478707223728197)
                ·
                  refine ⟨1371573922964757604449037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7315060922478707223728197 1371573922964757604449037)
                  ·
                    refine ⟨514340221111784101668389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1371573922964757604449037 514340221111784101668389)
                    ·
                      rfl

theorem cell22_1502511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 4, 4, 3].length) (baseStart_1502511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1502511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1502511 prefixEnd_1502511 := by exact prefixLift 1502511
  have htrace : WordTrace (prefixWord ++ tailWord_1502511) baseStart_1502511 baseEnd_1502511 := by
    simpa [prefixWord, tailWord_1502511, baseEnd_1502511] using wordTrace_append hprefix tailTrace_1502511
  have hstable : (prefixWord ++ tailWord_1502511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1502511).length < 2 ^ (prefixWord ++ tailWord_1502511).sum := by decide
  have hdescent : baseEnd_1502511 < baseStart_1502511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1502511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1502513 : List Nat := [1, 2, 2, 3, 3, 1, 1, 5, 4]
def baseStart_1502513 : Nat := 118140960795 + 1502513 * 2 ^ 59
def prefixEnd_1502513 : Nat := 4983230072969 + 3 ^ 40 * 1502513 * 2
def baseEnd_1502513 : Nat := 171446968584218921039461

theorem tailTrace_1502513 : CollatzResearch.WordTrace tailWord_1502513 prefixEnd_1502513 171446968584218921039461 := by
  unfold tailWord_1502513
  simp only [CollatzResearch.WordTrace]
  refine ⟨54801151205659484635840193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36534100803772989757226795 54801151205659484635840193)
  ·
    refine ⟨41100863404244613476880145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54801151205659484635840193 41100863404244613476880145)
    ·
      refine ⟨30825647553183460107660109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41100863404244613476880145 30825647553183460107660109)
      ·
        refine ⟨11559617832443797540372541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30825647553183460107660109 11559617832443797540372541)
        ·
          refine ⟨4334856687166424077639703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11559617832443797540372541 4334856687166424077639703)
          ·
            refine ⟨6502285030749636116459555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4334856687166424077639703 6502285030749636116459555)
            ·
              refine ⟨9753427546124454174689333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6502285030749636116459555 9753427546124454174689333)
              ·
                refine ⟨914383832449167578877125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9753427546124454174689333 914383832449167578877125)
                ·
                  refine ⟨171446968584218921039461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 914383832449167578877125 171446968584218921039461)
                  ·
                    rfl

theorem cell22_1502513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 5, 4].length) (baseStart_1502513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1502513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1502513 prefixEnd_1502513 := by exact prefixLift 1502513
  have htrace : WordTrace (prefixWord ++ tailWord_1502513) baseStart_1502513 baseEnd_1502513 := by
    simpa [prefixWord, tailWord_1502513, baseEnd_1502513] using wordTrace_append hprefix tailTrace_1502513
  have hstable : (prefixWord ++ tailWord_1502513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1502513).length < 2 ^ (prefixWord ++ tailWord_1502513).sum := by decide
  have hdescent : baseEnd_1502513 < baseStart_1502513 := by decide
  rcases family_descends (prefixWord ++ tailWord_1502513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1502515 : List Nat := [1, 1, 1, 2, 5, 4, 2, 1, 1, 4]
def baseStart_1502515 : Nat := 118140960795 + 1502515 * 2 ^ 59
def prefixEnd_1502515 : Nat := 4983230072969 + 3 ^ 40 * 1502515 * 2
def baseEnd_1502515 : Nat := 514341590393529424568377

theorem tailTrace_1502515 : CollatzResearch.WordTrace tailWord_1502515 prefixEnd_1502515 514341590393529424568377 := by
  unfold tailWord_1502515
  simp only [CollatzResearch.WordTrace]
  refine ⟨54801224151652238977412999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36534149434434825984941999 54801224151652238977412999)
  ·
    refine ⟨82201836227478358466119499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54801224151652238977412999 82201836227478358466119499)
    ·
      refine ⟨123302754341217537699179249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82201836227478358466119499 123302754341217537699179249)
      ·
        refine ⟨92477065755913153274384437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123302754341217537699179249 92477065755913153274384437)
        ·
          refine ⟨8669724914616858119473541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 92477065755913153274384437 8669724914616858119473541)
          ·
            refine ⟨1625573421490660897401289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8669724914616858119473541 1625573421490660897401289)
            ·
              refine ⟨1219180066117995673050967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1625573421490660897401289 1219180066117995673050967)
              ·
                refine ⟨1828770099176993509576451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1219180066117995673050967 1828770099176993509576451)
                ·
                  refine ⟨2743155148765490264364677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1828770099176993509576451 2743155148765490264364677)
                  ·
                    refine ⟨514341590393529424568377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2743155148765490264364677 514341590393529424568377)
                    ·
                      rfl

theorem cell22_1502515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 2, 1, 1, 4].length) (baseStart_1502515 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1502515 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1502515 prefixEnd_1502515 := by exact prefixLift 1502515
  have htrace : WordTrace (prefixWord ++ tailWord_1502515) baseStart_1502515 baseEnd_1502515 := by
    simpa [prefixWord, tailWord_1502515, baseEnd_1502515] using wordTrace_append hprefix tailTrace_1502515
  have hstable : (prefixWord ++ tailWord_1502515).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1502515).length < 2 ^ (prefixWord ++ tailWord_1502515).sum := by decide
  have hdescent : baseEnd_1502515 < baseStart_1502515 := by decide
  rcases family_descends (prefixWord ++ tailWord_1502515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1502545 : List Nat := [1, 2, 2, 1, 4, 1, 5, 1, 2, 3]
def baseStart_1502545 : Nat := 118140960795 + 1502545 * 2 ^ 59
def prefixEnd_1502545 : Nat := 4983230072969 + 3 ^ 40 * 1502545 * 2
def baseEnd_1502545 : Nat := 514351860006619346318285

theorem tailTrace_1502545 : CollatzResearch.WordTrace tailWord_1502545 prefixEnd_1502545 514351860006619346318285 := by
  unfold tailWord_1502545
  simp only [CollatzResearch.WordTrace]
  refine ⟨54802318341543554101005089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36534878894362369400670059 54802318341543554101005089)
  ·
    refine ⟨41101738756157665575753817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54802318341543554101005089 41101738756157665575753817)
    ·
      refine ⟨30826304067118249181815363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41101738756157665575753817 30826304067118249181815363)
      ·
        refine ⟨46239456100677373772723045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30826304067118249181815363 46239456100677373772723045)
        ·
          refine ⟨8669898018877007582385571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46239456100677373772723045 8669898018877007582385571)
          ·
            refine ⟨13004847028315511373578357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8669898018877007582385571 13004847028315511373578357)
            ·
              refine ⟨1219204408904579191272971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13004847028315511373578357 1219204408904579191272971)
              ·
                refine ⟨1828806613356868786909457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1219204408904579191272971 1828806613356868786909457)
                ·
                  refine ⟨1371604960017651590182093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1828806613356868786909457 1371604960017651590182093)
                  ·
                    refine ⟨514351860006619346318285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1371604960017651590182093 514351860006619346318285)
                    ·
                      rfl

theorem cell22_1502545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 5, 1, 2, 3].length) (baseStart_1502545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1502545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1502545 prefixEnd_1502545 := by exact prefixLift 1502545
  have htrace : WordTrace (prefixWord ++ tailWord_1502545) baseStart_1502545 baseEnd_1502545 := by
    simpa [prefixWord, tailWord_1502545, baseEnd_1502545] using wordTrace_append hprefix tailTrace_1502545
  have hstable : (prefixWord ++ tailWord_1502545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1502545).length < 2 ^ (prefixWord ++ tailWord_1502545).sum := by decide
  have hdescent : baseEnd_1502545 < baseStart_1502545 := by decide
  rcases family_descends (prefixWord ++ tailWord_1502545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1502663 : List Nat := [1, 1, 4, 1, 1, 3, 4, 1, 1, 5]
def baseStart_1502663 : Nat := 118140960795 + 1502663 * 2 ^ 59
def prefixEnd_1502663 : Nat := 4983230072969 + 3 ^ 40 * 1502663 * 2
def baseEnd_1502663 : Nat := 514392253818106371867923

theorem tailTrace_1502663 : CollatzResearch.WordTrace tailWord_1502663 prefixEnd_1502663 514392253818106371867923 := by
  unfold tailWord_1502663
  simp only [CollatzResearch.WordTrace]
  refine ⟨54806622155116060253800643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36537748103410706835867095 54806622155116060253800643)
  ·
    refine ⟨82209933232674090380700965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54806622155116060253800643 82209933232674090380700965)
    ·
      refine ⟨15414362481126391946381431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82209933232674090380700965 15414362481126391946381431)
      ·
        refine ⟨23121543721689587919572147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15414362481126391946381431 23121543721689587919572147)
        ·
          refine ⟨34682315582534381879358221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23121543721689587919572147 34682315582534381879358221)
          ·
            refine ⟨13005868343450393204759333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34682315582534381879358221 13005868343450393204759333)
            ·
              refine ⟨2438600314396948725892375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13005868343450393204759333 2438600314396948725892375)
              ·
                refine ⟨3657900471595423088838563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2438600314396948725892375 3657900471595423088838563)
                ·
                  refine ⟨5486850707393134633257845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3657900471595423088838563 5486850707393134633257845)
                  ·
                    refine ⟨514392253818106371867923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5486850707393134633257845 514392253818106371867923)
                    ·
                      rfl

theorem cell22_1502663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 4, 1, 1, 5].length) (baseStart_1502663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1502663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1502663 prefixEnd_1502663 := by exact prefixLift 1502663
  have htrace : WordTrace (prefixWord ++ tailWord_1502663) baseStart_1502663 baseEnd_1502663 := by
    simpa [prefixWord, tailWord_1502663, baseEnd_1502663] using wordTrace_append hprefix tailTrace_1502663
  have hstable : (prefixWord ++ tailWord_1502663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1502663).length < 2 ^ (prefixWord ++ tailWord_1502663).sum := by decide
  have hdescent : baseEnd_1502663 < baseStart_1502663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1502663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1502693 : List Nat := [1, 3, 1, 5, 1, 2, 9]
def baseStart_1502693 : Nat := 118140960795 + 1502693 * 2 ^ 59
def prefixEnd_1502693 : Nat := 4983230072969 + 3 ^ 40 * 1502693 * 2
def baseEnd_1502693 : Nat := 19051945312266529393253

theorem tailTrace_1502693 : CollatzResearch.WordTrace tailWord_1502693 prefixEnd_1502693 19051945312266529393253 := by
  unfold tailWord_1502693
  simp only [CollatzResearch.WordTrace]
  refine ⟨54807716345007375377392733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36538477563338250251595155 54807716345007375377392733)
  ·
    refine ⟨20552893629377765766522275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54807716345007375377392733 20552893629377765766522275)
    ·
      refine ⟨30829340444066648649783413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20552893629377765766522275 30829340444066648649783413)
      ·
        refine ⟨2890250666631248310917195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30829340444066648649783413 2890250666631248310917195)
        ·
          refine ⟨4335375999946872466375793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2890250666631248310917195 4335375999946872466375793)
          ·
            refine ⟨3251531999960154349781845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4335375999946872466375793 3251531999960154349781845)
            ·
              refine ⟨19051945312266529393253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3251531999960154349781845 19051945312266529393253)
              ·
                rfl

theorem cell22_1502693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 9].length) (baseStart_1502693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1502693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1502693 prefixEnd_1502693 := by exact prefixLift 1502693
  have htrace : WordTrace (prefixWord ++ tailWord_1502693) baseStart_1502693 baseEnd_1502693 := by
    simpa [prefixWord, tailWord_1502693, baseEnd_1502693] using wordTrace_append hprefix tailTrace_1502693
  have hstable : (prefixWord ++ tailWord_1502693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1502693).length < 2 ^ (prefixWord ++ tailWord_1502693).sum := by decide
  have hdescent : baseEnd_1502693 < baseStart_1502693 := by decide
  rcases family_descends (prefixWord ++ tailWord_1502693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1502733 : List Nat := [1, 7, 1, 1, 3, 1, 1, 3, 4]
def baseStart_1502733 : Nat := 118140960795 + 1502733 * 2 ^ 59
def prefixEnd_1502733 : Nat := 4983230072969 + 3 ^ 40 * 1502733 * 2
def baseEnd_1502733 : Nat := 171472072082883174205903

theorem tailTrace_1502733 : CollatzResearch.WordTrace tailWord_1502733 prefixEnd_1502733 171472072082883174205903 := by
  unfold tailWord_1502733
  simp only [CollatzResearch.WordTrace]
  refine ⟨54809175264862462208848853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36539450176574974805899235 54809175264862462208848853)
  ·
    refine ⟨1284590045270213958019895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 54809175264862462208848853 1284590045270213958019895)
    ·
      refine ⟨1926885067905320937029843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1284590045270213958019895 1926885067905320937029843)
      ·
        refine ⟨2890327601857981405544765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1926885067905320937029843 2890327601857981405544765)
        ·
          refine ⟨1083872850696743027079287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2890327601857981405544765 1083872850696743027079287)
          ·
            refine ⟨1625809276045114540618931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1083872850696743027079287 1625809276045114540618931)
            ·
              refine ⟨2438713914067671810928397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1625809276045114540618931 2438713914067671810928397)
              ·
                refine ⟨914517717775376929098149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2438713914067671810928397 914517717775376929098149)
                ·
                  refine ⟨171472072082883174205903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 914517717775376929098149 171472072082883174205903)
                  ·
                    rfl

theorem cell22_1502733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_1502733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1502733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1502733 prefixEnd_1502733 := by exact prefixLift 1502733
  have htrace : WordTrace (prefixWord ++ tailWord_1502733) baseStart_1502733 baseEnd_1502733 := by
    simpa [prefixWord, tailWord_1502733, baseEnd_1502733] using wordTrace_append hprefix tailTrace_1502733
  have hstable : (prefixWord ++ tailWord_1502733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1502733).length < 2 ^ (prefixWord ++ tailWord_1502733).sum := by decide
  have hdescent : baseEnd_1502733 < baseStart_1502733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1502733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1502768 : List Nat := [2, 1, 1, 1, 2, 3, 1, 4, 3, 4]
def baseStart_1502768 : Nat := 118140960795 + 1502768 * 2 ^ 59
def prefixEnd_1502768 : Nat := 4983230072969 + 3 ^ 40 * 1502768 * 2
def baseEnd_1502768 : Nat := 514428197463921097992601

theorem tailTrace_1502768 : CollatzResearch.WordTrace tailWord_1502768 prefixEnd_1502768 514428197463921097992601 := by
  unfold tailWord_1502768
  simp only [CollatzResearch.WordTrace]
  refine ⟨27405225909867831593186479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36540301213157108790915305 27405225909867831593186479)
  ·
    refine ⟨41107838864801747389779719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27405225909867831593186479 41107838864801747389779719)
    ·
      refine ⟨61661758297202621084669579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41107838864801747389779719 61661758297202621084669579)
      ·
        refine ⟨92492637445803931627004369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61661758297202621084669579 92492637445803931627004369)
        ·
          refine ⟨69369478084352948720253277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92492637445803931627004369 69369478084352948720253277)
          ·
            refine ⟨26013554281632355770094979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69369478084352948720253277 26013554281632355770094979)
            ·
              refine ⟨39020331422448533655142469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26013554281632355770094979 39020331422448533655142469)
              ·
                refine ⟨7316312141709100060339213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39020331422448533655142469 7316312141709100060339213)
                ·
                  refine ⟨2743617053140912522627205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7316312141709100060339213 2743617053140912522627205)
                  ·
                    refine ⟨514428197463921097992601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2743617053140912522627205 514428197463921097992601)
                    ·
                      rfl

theorem cell22_1502768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 4, 3, 4].length) (baseStart_1502768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1502768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1502768 prefixEnd_1502768 := by exact prefixLift 1502768
  have htrace : WordTrace (prefixWord ++ tailWord_1502768) baseStart_1502768 baseEnd_1502768 := by
    simpa [prefixWord, tailWord_1502768, baseEnd_1502768] using wordTrace_append hprefix tailTrace_1502768
  have hstable : (prefixWord ++ tailWord_1502768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1502768).length < 2 ^ (prefixWord ++ tailWord_1502768).sum := by decide
  have hdescent : baseEnd_1502768 < baseStart_1502768 := by decide
  rcases family_descends (prefixWord ++ tailWord_1502768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1502785 : List Nat := [1, 2, 5, 1, 1, 1, 3, 1, 3, 4]
def baseStart_1502785 : Nat := 118140960795 + 1502785 * 2 ^ 59
def prefixEnd_1502785 : Nat := 4983230072969 + 3 ^ 40 * 1502785 * 2
def baseEnd_1502785 : Nat := 514434016911338720317549

theorem tailTrace_1502785 : CollatzResearch.WordTrace tailWord_1502785 prefixEnd_1502785 514434016911338720317549 := by
  unfold tailWord_1502785
  simp only [CollatzResearch.WordTrace]
  refine ⟨54811071860674075089741809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36540714573782716726494539 54811071860674075089741809)
  ·
    refine ⟨41108303895505556317306357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54811071860674075089741809 41108303895505556317306357)
    ·
      refine ⟨3853903490203645904747471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 41108303895505556317306357 3853903490203645904747471)
      ·
        refine ⟨5780855235305468857121207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3853903490203645904747471 5780855235305468857121207)
        ·
          refine ⟨8671282852958203285681811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5780855235305468857121207 8671282852958203285681811)
          ·
            refine ⟨13006924279437304928522717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8671282852958203285681811 13006924279437304928522717)
            ·
              refine ⟨4877596604788989348196019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13006924279437304928522717 4877596604788989348196019)
              ·
                refine ⟨7316394907183484022294029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4877596604788989348196019 7316394907183484022294029)
                ·
                  refine ⟨2743648090193806508360261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7316394907183484022294029 2743648090193806508360261)
                  ·
                    refine ⟨514434016911338720317549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2743648090193806508360261 514434016911338720317549)
                    ·
                      rfl

theorem cell22_1502785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_1502785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1502785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1502785 prefixEnd_1502785 := by exact prefixLift 1502785
  have htrace : WordTrace (prefixWord ++ tailWord_1502785) baseStart_1502785 baseEnd_1502785 := by
    simpa [prefixWord, tailWord_1502785, baseEnd_1502785] using wordTrace_append hprefix tailTrace_1502785
  have hstable : (prefixWord ++ tailWord_1502785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1502785).length < 2 ^ (prefixWord ++ tailWord_1502785).sum := by decide
  have hdescent : baseEnd_1502785 < baseStart_1502785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1502785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1502800 : List Nat := [2, 1, 1, 1, 1, 3, 4, 5, 4]
def baseStart_1502800 : Nat := 118140960795 + 1502800 * 2 ^ 59
def prefixEnd_1502800 : Nat := 4983230072969 + 3 ^ 40 * 1502800 * 2
def baseEnd_1502800 : Nat := 171479717239294560397501

theorem tailTrace_1502800 : CollatzResearch.WordTrace tailWord_1502800 prefixEnd_1502800 171479717239294560397501 := by
  unfold tailWord_1502800
  simp only [CollatzResearch.WordTrace]
  refine ⟨27405809477809866325768927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36541079303746488434358569 27405809477809866325768927)
  ·
    refine ⟨41108714216714799488653391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27405809477809866325768927 41108714216714799488653391)
    ·
      refine ⟨61663071325072199232980087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41108714216714799488653391 61663071325072199232980087)
      ·
        refine ⟨92494606987608298849470131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61663071325072199232980087 92494606987608298849470131)
        ·
          refine ⟨138741910481412448274205197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92494606987608298849470131 138741910481412448274205197)
          ·
            refine ⟨52028216430529668102826949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 138741910481412448274205197 52028216430529668102826949)
            ·
              refine ⟨9755290580724312769280053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52028216430529668102826949 9755290580724312769280053)
              ·
                refine ⟨914558491942904322120005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9755290580724312769280053 914558491942904322120005)
                ·
                  refine ⟨171479717239294560397501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 914558491942904322120005 171479717239294560397501)
                  ·
                    rfl

theorem cell22_1502800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 5, 4].length) (baseStart_1502800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1502800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1502800 prefixEnd_1502800 := by exact prefixLift 1502800
  have htrace : WordTrace (prefixWord ++ tailWord_1502800) baseStart_1502800 baseEnd_1502800 := by
    simpa [prefixWord, tailWord_1502800, baseEnd_1502800] using wordTrace_append hprefix tailTrace_1502800
  have hstable : (prefixWord ++ tailWord_1502800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1502800).length < 2 ^ (prefixWord ++ tailWord_1502800).sum := by decide
  have hdescent : baseEnd_1502800 < baseStart_1502800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1502800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1502806 : List Nat := [5, 2, 2, 2, 1, 1, 2, 2, 5]
def baseStart_1502806 : Nat := 118140960795 + 1502806 * 2 ^ 59
def prefixEnd_1502806 : Nat := 4983230072969 + 3 ^ 40 * 1502806 * 2
def baseEnd_1502806 : Nat := 171480401880167221847495

theorem tailTrace_1502806 : CollatzResearch.WordTrace tailWord_1502806 prefixEnd_1502806 171480401880167221847495 := by
  unfold tailWord_1502806
  simp only [CollatzResearch.WordTrace]
  refine ⟨3425739862099874729766017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36541225195731997117504181 3425739862099874729766017)
  ·
    refine ⟨2569304896574906047324513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3425739862099874729766017 2569304896574906047324513)
    ·
      refine ⟨1926978672431179535493385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2569304896574906047324513 1926978672431179535493385)
      ·
        refine ⟨1445234004323384651620039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1926978672431179535493385 1445234004323384651620039)
        ·
          refine ⟨2167851006485076977430059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1445234004323384651620039 2167851006485076977430059)
          ·
            refine ⟨3251776509727615466145089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2167851006485076977430059 3251776509727615466145089)
            ·
              refine ⟨2438832382295711599608817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3251776509727615466145089 2438832382295711599608817)
              ·
                refine ⟨1829124286721783699706613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2438832382295711599608817 1829124286721783699706613)
                ·
                  refine ⟨171480401880167221847495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1829124286721783699706613 171480401880167221847495)
                  ·
                    rfl

theorem cell22_1502806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 2, 2, 5].length) (baseStart_1502806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1502806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1502806 prefixEnd_1502806 := by exact prefixLift 1502806
  have htrace : WordTrace (prefixWord ++ tailWord_1502806) baseStart_1502806 baseEnd_1502806 := by
    simpa [prefixWord, tailWord_1502806, baseEnd_1502806] using wordTrace_append hprefix tailTrace_1502806
  have hstable : (prefixWord ++ tailWord_1502806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1502806).length < 2 ^ (prefixWord ++ tailWord_1502806).sum := by decide
  have hdescent : baseEnd_1502806 < baseStart_1502806 := by decide
  rcases family_descends (prefixWord ++ tailWord_1502806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1502832 : List Nat := [2, 1, 1, 1, 6, 1, 2, 3, 2, 3]
def baseStart_1502832 : Nat := 118140960795 + 1502832 * 2 ^ 59
def prefixEnd_1502832 : Nat := 4983230072969 + 3 ^ 40 * 1502832 * 2
def baseEnd_1502832 : Nat := 514450105971846264392405

theorem tailTrace_1502832 : CollatzResearch.WordTrace tailWord_1502832 prefixEnd_1502832 514450105971846264392405 := by
  unfold tailWord_1502832
  simp only [CollatzResearch.WordTrace]
  refine ⟨27406393045751901058351375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36541857394335868077801833 27406393045751901058351375)
  ·
    refine ⟨41109589568627851587527063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27406393045751901058351375 41109589568627851587527063)
    ·
      refine ⟨61664384352941777381290595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41109589568627851587527063 61664384352941777381290595)
      ·
        refine ⟨92496576529412666071935893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61664384352941777381290595 92496576529412666071935893)
        ·
          refine ⟨4335777024816218722121995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 92496576529412666071935893 4335777024816218722121995)
          ·
            refine ⟨6503665537224328083182993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4335777024816218722121995 6503665537224328083182993)
            ·
              refine ⟨4877749152918246062387245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6503665537224328083182993 4877749152918246062387245)
              ·
                refine ⟨1829155932344342273395217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4877749152918246062387245 1829155932344342273395217)
                ·
                  refine ⟨1371866949258256705046413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1829155932344342273395217 1371866949258256705046413)
                  ·
                    refine ⟨514450105971846264392405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1371866949258256705046413 514450105971846264392405)
                    ·
                      rfl

theorem cell22_1502832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 3, 2, 3].length) (baseStart_1502832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1502832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1502832 prefixEnd_1502832 := by exact prefixLift 1502832
  have htrace : WordTrace (prefixWord ++ tailWord_1502832) baseStart_1502832 baseEnd_1502832 := by
    simpa [prefixWord, tailWord_1502832, baseEnd_1502832] using wordTrace_append hprefix tailTrace_1502832
  have hstable : (prefixWord ++ tailWord_1502832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1502832).length < 2 ^ (prefixWord ++ tailWord_1502832).sum := by decide
  have hdescent : baseEnd_1502832 < baseStart_1502832 := by decide
  rcases family_descends (prefixWord ++ tailWord_1502832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1502860 : List Nat := [2, 2, 1, 2, 1, 1, 3, 2, 5, 3]
def baseStart_1502860 : Nat := 118140960795 + 1502860 * 2 ^ 59
def prefixEnd_1502860 : Nat := 4983230072969 + 3 ^ 40 * 1502860 * 2
def baseEnd_1502860 : Nat := 514459690944063524692319

theorem tailTrace_1502860 : CollatzResearch.WordTrace tailWord_1502860 prefixEnd_1502860 514459690944063524692319 := by
  unfold tailWord_1502860
  simp only [CollatzResearch.WordTrace]
  refine ⟨27406903667701181449361017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36542538223601575265814689 27406903667701181449361017)
  ·
    refine ⟨20555177750775886087020763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27406903667701181449361017 20555177750775886087020763)
    ·
      refine ⟨30832766626163829130531145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20555177750775886087020763 30832766626163829130531145)
      ·
        refine ⟨23124574969622871847898359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30832766626163829130531145 23124574969622871847898359)
        ·
          refine ⟨34686862454434307771847539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23124574969622871847898359 34686862454434307771847539)
          ·
            refine ⟨52030293681651461657771309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34686862454434307771847539 52030293681651461657771309)
            ·
              refine ⟨19511360130619298121664241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52030293681651461657771309 19511360130619298121664241)
              ·
                refine ⟨14633520097964473591248181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19511360130619298121664241 14633520097964473591248181)
                ·
                  refine ⟨1371892509184169399179517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14633520097964473591248181 1371892509184169399179517)
                  ·
                    refine ⟨514459690944063524692319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1371892509184169399179517 514459690944063524692319)
                    ·
                      rfl

theorem cell22_1502860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 5, 3].length) (baseStart_1502860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1502860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1502860 prefixEnd_1502860 := by exact prefixLift 1502860
  have htrace : WordTrace (prefixWord ++ tailWord_1502860) baseStart_1502860 baseEnd_1502860 := by
    simpa [prefixWord, tailWord_1502860, baseEnd_1502860] using wordTrace_append hprefix tailTrace_1502860
  have hstable : (prefixWord ++ tailWord_1502860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1502860).length < 2 ^ (prefixWord ++ tailWord_1502860).sum := by decide
  have hdescent : baseEnd_1502860 < baseStart_1502860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1502860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1502866 : List Nat := [3, 2, 3, 1, 3, 2, 1, 2, 2, 3]
def baseStart_1502866 : Nat := 118140960795 + 1502866 * 2 ^ 59
def prefixEnd_1502866 : Nat := 4983230072969 + 3 ^ 40 * 1502866 * 2
def baseEnd_1502866 : Nat := 514461744866681509042301

theorem tailTrace_1502866 : CollatzResearch.WordTrace tailWord_1502866 prefixEnd_1502866 514461744866681509042301 := by
  unfold tailWord_1502866
  simp only [CollatzResearch.WordTrace]
  refine ⟨13703506543345156480860113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36542684115587083948960301 13703506543345156480860113)
  ·
    refine ⟨10277629907508867360645085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13703506543345156480860113 10277629907508867360645085)
    ·
      refine ⟨3854111215315825260241907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10277629907508867360645085 3854111215315825260241907)
      ·
        refine ⟨5781166822973737890362861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3854111215315825260241907 5781166822973737890362861)
        ·
          refine ⟨2167937558615151708886073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5781166822973737890362861 2167937558615151708886073)
          ·
            refine ⟨1625953168961363781664555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2167937558615151708886073 1625953168961363781664555)
            ·
              refine ⟨2438929753442045672496833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1625953168961363781664555 2438929753442045672496833)
              ·
                refine ⟨1829197315081534254372625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2438929753442045672496833 1829197315081534254372625)
                ·
                  refine ⟨1371897986311150690779469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1829197315081534254372625 1371897986311150690779469)
                  ·
                    refine ⟨514461744866681509042301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1371897986311150690779469 514461744866681509042301)
                    ·
                      rfl

theorem cell22_1502866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 1, 2, 2, 3].length) (baseStart_1502866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1502866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1502866 prefixEnd_1502866 := by exact prefixLift 1502866
  have htrace : WordTrace (prefixWord ++ tailWord_1502866) baseStart_1502866 baseEnd_1502866 := by
    simpa [prefixWord, tailWord_1502866, baseEnd_1502866] using wordTrace_append hprefix tailTrace_1502866
  have hstable : (prefixWord ++ tailWord_1502866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1502866).length < 2 ^ (prefixWord ++ tailWord_1502866).sum := by decide
  have hdescent : baseEnd_1502866 < baseStart_1502866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1502866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1502980 : List Nat := [2, 3, 2, 2, 1, 12]
def baseStart_1502980 : Nat := 118140960795 + 1502980 * 2 ^ 59
def prefixEnd_1502980 : Nat := 4983230072969 + 3 ^ 40 * 1502980 * 2
def baseEnd_1502980 : Nat := 6351861350573126070271

theorem tailTrace_1502980 : CollatzResearch.WordTrace tailWord_1502980 prefixEnd_1502980 6351861350573126070271 := by
  unfold tailWord_1502980
  simp only [CollatzResearch.WordTrace]
  refine ⟨27409092047483811696545197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36545456063311748928726929 27409092047483811696545197)
  ·
    refine ⟨10278409517806429386204449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27409092047483811696545197 10278409517806429386204449)
    ·
      refine ⟨7708807138354822039653337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10278409517806429386204449 7708807138354822039653337)
      ·
        refine ⟨5781605353766116529740003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7708807138354822039653337 5781605353766116529740003)
        ·
          refine ⟨8672408030649174794610005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5781605353766116529740003 8672408030649174794610005)
          ·
            refine ⟨6351861350573126070271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 8672408030649174794610005 6351861350573126070271)
            ·
              rfl

theorem cell22_1502980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 12].length) (baseStart_1502980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1502980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1502980 prefixEnd_1502980 := by exact prefixLift 1502980
  have htrace : WordTrace (prefixWord ++ tailWord_1502980) baseStart_1502980 baseEnd_1502980 := by
    simpa [prefixWord, tailWord_1502980, baseEnd_1502980] using wordTrace_append hprefix tailTrace_1502980
  have hstable : (prefixWord ++ tailWord_1502980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1502980).length < 2 ^ (prefixWord ++ tailWord_1502980).sum := by decide
  have hdescent : baseEnd_1502980 < baseStart_1502980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1502980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1502984 : List Nat := [2, 1, 3, 2, 2, 1, 4, 2, 2, 3]
def baseStart_1502984 : Nat := 118140960795 + 1502984 * 2 ^ 59
def prefixEnd_1502984 : Nat := 4983230072969 + 3 ^ 40 * 1502984 * 2
def baseEnd_1502984 : Nat := 514502138678168534591939

theorem tailTrace_1502984 : CollatzResearch.WordTrace tailWord_1502984 prefixEnd_1502984 514502138678168534591939 := by
  unfold tailWord_1502984
  simp only [CollatzResearch.WordTrace]
  refine ⟨27409164993476566038118003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36545553324635421384157337 27409164993476566038118003)
  ·
    refine ⟨41113747490214849057177005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27409164993476566038118003 41113747490214849057177005)
    ·
      refine ⟨15417655308830568396441377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41113747490214849057177005 15417655308830568396441377)
      ·
        refine ⟨11563241481622926297331033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15417655308830568396441377 11563241481622926297331033)
        ·
          refine ⟨8672431111217194722998275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11563241481622926297331033 8672431111217194722998275)
          ·
            refine ⟨13008646666825792084497413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8672431111217194722998275 13008646666825792084497413)
            ·
              refine ⟨2439121250029836015843265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13008646666825792084497413 2439121250029836015843265)
              ·
                refine ⟨1829340937522377011882449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2439121250029836015843265 1829340937522377011882449)
                ·
                  refine ⟨1372005703141782758911837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1829340937522377011882449 1372005703141782758911837)
                  ·
                    refine ⟨514502138678168534591939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1372005703141782758911837 514502138678168534591939)
                    ·
                      rfl

theorem cell22_1502984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 4, 2, 2, 3].length) (baseStart_1502984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1502984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1502984 prefixEnd_1502984 := by exact prefixLift 1502984
  have htrace : WordTrace (prefixWord ++ tailWord_1502984) baseStart_1502984 baseEnd_1502984 := by
    simpa [prefixWord, tailWord_1502984, baseEnd_1502984] using wordTrace_append hprefix tailTrace_1502984
  have hstable : (prefixWord ++ tailWord_1502984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1502984).length < 2 ^ (prefixWord ++ tailWord_1502984).sum := by decide
  have hdescent : baseEnd_1502984 < baseStart_1502984 := by decide
  rcases family_descends (prefixWord ++ tailWord_1502984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1502986 : List Nat := [3, 1, 2, 2, 1, 5, 2, 2, 4]
def baseStart_1502986 : Nat := 118140960795 + 1502986 * 2 ^ 59
def prefixEnd_1502986 : Nat := 4983230072969 + 3 ^ 40 * 1502986 * 2
def baseEnd_1502986 : Nat := 171500941106347065347311

theorem tailTrace_1502986 : CollatzResearch.WordTrace tailWord_1502986 prefixEnd_1502986 171500941106347065347311 := by
  unfold tailWord_1502986
  simp only [CollatzResearch.WordTrace]
  refine ⟨13704600733236471604452203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36545601955297257611872541 13704600733236471604452203)
  ·
    refine ⟨20556901099854707406678305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13704600733236471604452203 20556901099854707406678305)
    ·
      refine ⟨15417675824891030555008729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20556901099854707406678305 15417675824891030555008729)
      ·
        refine ⟨11563256868668272916256547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15417675824891030555008729 11563256868668272916256547)
        ·
          refine ⟨17344885303002409374384821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11563256868668272916256547 17344885303002409374384821)
          ·
            refine ⟨1626082997156475878848577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17344885303002409374384821 1626082997156475878848577)
            ·
              refine ⟨1219562247867356909136433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1626082997156475878848577 1219562247867356909136433)
              ·
                refine ⟨914671685900517681852325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1219562247867356909136433 914671685900517681852325)
                ·
                  refine ⟨171500941106347065347311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 914671685900517681852325 171500941106347065347311)
                  ·
                    rfl

theorem cell22_1502986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 2, 2, 4].length) (baseStart_1502986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1502986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1502986 prefixEnd_1502986 := by exact prefixLift 1502986
  have htrace : WordTrace (prefixWord ++ tailWord_1502986) baseStart_1502986 baseEnd_1502986 := by
    simpa [prefixWord, tailWord_1502986, baseEnd_1502986] using wordTrace_append hprefix tailTrace_1502986
  have hstable : (prefixWord ++ tailWord_1502986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1502986).length < 2 ^ (prefixWord ++ tailWord_1502986).sum := by decide
  have hdescent : baseEnd_1502986 < baseStart_1502986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1502986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1502997 : List Nat := [1, 3, 2, 1, 2, 5, 1, 7]
def baseStart_1502997 : Nat := 118140960795 + 1502997 * 2 ^ 59
def prefixEnd_1502997 : Nat := 4983230072969 + 3 ^ 40 * 1502997 * 2
def baseEnd_1502997 : Nat := 57167398760426759335211

theorem tailTrace_1502997 : CollatzResearch.WordTrace tailWord_1502997 prefixEnd_1502997 57167398760426759335211 := by
  unfold tailWord_1502997
  simp only [CollatzResearch.WordTrace]
  refine ⟨54818804135906035296459245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36545869423937356864306163 54818804135906035296459245)
  ·
    refine ⟨20557051550964763236172217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54818804135906035296459245 20557051550964763236172217)
    ·
      refine ⟨15417788663223572427129163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20557051550964763236172217 15417788663223572427129163)
      ·
        refine ⟨23126682994835358640693745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15417788663223572427129163 23126682994835358640693745)
        ·
          refine ⟨17345012246126518980520309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23126682994835358640693745 17345012246126518980520309)
          ·
            refine ⟨1626094898074361154423779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17345012246126518980520309 1626094898074361154423779)
            ·
              refine ⟨2439142347111541731635669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1626094898074361154423779 2439142347111541731635669)
              ·
                refine ⟨57167398760426759335211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2439142347111541731635669 57167398760426759335211)
                ·
                  rfl

theorem cell22_1502997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 1, 7].length) (baseStart_1502997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1502997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1502997 prefixEnd_1502997 := by exact prefixLift 1502997
  have htrace : WordTrace (prefixWord ++ tailWord_1502997) baseStart_1502997 baseEnd_1502997 := by
    simpa [prefixWord, tailWord_1502997, baseEnd_1502997] using wordTrace_append hprefix tailTrace_1502997
  have hstable : (prefixWord ++ tailWord_1502997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1502997).length < 2 ^ (prefixWord ++ tailWord_1502997).sum := by decide
  have hdescent : baseEnd_1502997 < baseStart_1502997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1502997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1503057 : List Nat := [1, 2, 2, 1, 5, 1, 2, 1, 2, 5]
def baseStart_1503057 : Nat := 118140960795 + 1503057 * 2 ^ 59
def prefixEnd_1503057 : Nat := 4983230072969 + 3 ^ 40 * 1503057 * 2
def baseEnd_1503057 : Nat := 514527128070020677516715

theorem tailTrace_1503057 : CollatzResearch.WordTrace tailWord_1503057 prefixEnd_1503057 514527128070020677516715 := by
  unfold tailWord_1503057
  simp only [CollatzResearch.WordTrace]
  refine ⟨54820992515688665543643425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36547328343792443695762283 54820992515688665543643425)
  ·
    refine ⟨41115744386766499157732569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54820992515688665543643425 41115744386766499157732569)
    ·
      refine ⟨30836808290074874368299427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41115744386766499157732569 30836808290074874368299427)
      ·
        refine ⟨46255212435112311552449141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30836808290074874368299427 46255212435112311552449141)
        ·
          refine ⟨4336426165791779208042107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46255212435112311552449141 4336426165791779208042107)
          ·
            refine ⟨6504639248687668812063161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4336426165791779208042107 6504639248687668812063161)
            ·
              refine ⟨4878479436515751609047371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6504639248687668812063161 4878479436515751609047371)
              ·
                refine ⟨7317719154773627413571057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4878479436515751609047371 7317719154773627413571057)
                ·
                  refine ⟨5488289366080220560178293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7317719154773627413571057 5488289366080220560178293)
                  ·
                    refine ⟨514527128070020677516715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5488289366080220560178293 514527128070020677516715)
                    ·
                      rfl

theorem cell22_1503057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 1, 2, 5].length) (baseStart_1503057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1503057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1503057 prefixEnd_1503057 := by exact prefixLift 1503057
  have htrace : WordTrace (prefixWord ++ tailWord_1503057) baseStart_1503057 baseEnd_1503057 := by
    simpa [prefixWord, tailWord_1503057, baseEnd_1503057] using wordTrace_append hprefix tailTrace_1503057
  have hstable : (prefixWord ++ tailWord_1503057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1503057).length < 2 ^ (prefixWord ++ tailWord_1503057).sum := by decide
  have hdescent : baseEnd_1503057 < baseStart_1503057 := by decide
  rcases family_descends (prefixWord ++ tailWord_1503057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1503192 : List Nat := [2, 1, 2, 2, 2, 2, 1, 2, 1, 7]
def baseStart_1503192 : Nat := 118140960795 + 1503192 * 2 ^ 59
def prefixEnd_1503192 : Nat := 4983230072969 + 3 ^ 40 * 1503192 * 2
def baseEnd_1503192 : Nat := 514573341328925325391301

theorem tailTrace_1503192 : CollatzResearch.WordTrace tailWord_1503192 prefixEnd_1503192 514573341328925325391301 := by
  unfold tailWord_1503192
  simp only [CollatzResearch.WordTrace]
  refine ⟨27412958185099791799903915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36550610913466389066538553 27412958185099791799903915)
  ·
    refine ⟨41119437277649687699855873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27412958185099791799903915 41119437277649687699855873)
    ·
      refine ⟨30839577958237265774891905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41119437277649687699855873 30839577958237265774891905)
      ·
        refine ⟨23129683468677949331168929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30839577958237265774891905 23129683468677949331168929)
        ·
          refine ⟨17347262601508461998376697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23129683468677949331168929 17347262601508461998376697)
          ·
            refine ⟨13010446951131346498782523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17347262601508461998376697 13010446951131346498782523)
            ·
              refine ⟨19515670426697019748173785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13010446951131346498782523 19515670426697019748173785)
              ·
                refine ⟨14636752820022764811130339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19515670426697019748173785 14636752820022764811130339)
                ·
                  refine ⟨21955129230034147216695509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14636752820022764811130339 21955129230034147216695509)
                  ·
                    refine ⟨514573341328925325391301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21955129230034147216695509 514573341328925325391301)
                    ·
                      rfl

theorem cell22_1503192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 2, 1, 7].length) (baseStart_1503192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1503192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1503192 prefixEnd_1503192 := by exact prefixLift 1503192
  have htrace : WordTrace (prefixWord ++ tailWord_1503192) baseStart_1503192 baseEnd_1503192 := by
    simpa [prefixWord, tailWord_1503192, baseEnd_1503192] using wordTrace_append hprefix tailTrace_1503192
  have hstable : (prefixWord ++ tailWord_1503192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1503192).length < 2 ^ (prefixWord ++ tailWord_1503192).sum := by decide
  have hdescent : baseEnd_1503192 < baseStart_1503192 := by decide
  rcases family_descends (prefixWord ++ tailWord_1503192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1503239 : List Nat := [1, 1, 4, 3, 1, 2, 2, 2, 6]
def baseStart_1503239 : Nat := 118140960795 + 1503239 * 2 ^ 59
def prefixEnd_1503239 : Nat := 4983230072969 + 3 ^ 40 * 1503239 * 2
def baseEnd_1503239 : Nat := 171529810129810956488719

theorem tailTrace_1503239 : CollatzResearch.WordTrace tailWord_1503239 prefixEnd_1503239 171529810129810956488719 := by
  unfold tailWord_1503239
  simp only [CollatzResearch.WordTrace]
  refine ⟨54827630601029310626768771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36551753734019540417845847 54827630601029310626768771)
  ·
    refine ⟨82241445901543965940153157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54827630601029310626768771 82241445901543965940153157)
    ·
      refine ⟨15420271106539493613778717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82241445901543965940153157 15420271106539493613778717)
      ·
        refine ⟨5782601664952310105167019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15420271106539493613778717 5782601664952310105167019)
        ·
          refine ⟨8673902497428465157750529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5782601664952310105167019 8673902497428465157750529)
          ·
            refine ⟨6505426873071348868312897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8673902497428465157750529 6505426873071348868312897)
            ·
              refine ⟨4879070154803511651234673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6505426873071348868312897 4879070154803511651234673)
              ·
                refine ⟨3659302616102633738426005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4879070154803511651234673 3659302616102633738426005)
                ·
                  refine ⟨171529810129810956488719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3659302616102633738426005 171529810129810956488719)
                  ·
                    rfl

theorem cell22_1503239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 2, 6].length) (baseStart_1503239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1503239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1503239 prefixEnd_1503239 := by exact prefixLift 1503239
  have htrace : WordTrace (prefixWord ++ tailWord_1503239) baseStart_1503239 baseEnd_1503239 := by
    simpa [prefixWord, tailWord_1503239, baseEnd_1503239] using wordTrace_append hprefix tailTrace_1503239
  have hstable : (prefixWord ++ tailWord_1503239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1503239).length < 2 ^ (prefixWord ++ tailWord_1503239).sum := by decide
  have hdescent : baseEnd_1503239 < baseStart_1503239 := by decide
  rcases family_descends (prefixWord ++ tailWord_1503239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1503269 : List Nat := [1, 3, 1, 2, 2, 3, 1, 1, 4, 4]
def baseStart_1503269 : Nat := 118140960795 + 1503269 * 2 ^ 59
def prefixEnd_1503269 : Nat := 4983230072969 + 3 ^ 40 * 1503269 * 2
def baseEnd_1503269 : Nat := 514599700002522791216065

theorem tailTrace_1503269 : CollatzResearch.WordTrace tailWord_1503269 prefixEnd_1503269 514599700002522791216065 := by
  unfold tailWord_1503269
  simp only [CollatzResearch.WordTrace]
  refine ⟨54828724790920625750360861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36552483193947083833573907 54828724790920625750360861)
  ·
    refine ⟨20560771796595234656385323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54828724790920625750360861 20560771796595234656385323)
    ·
      refine ⟨30841157694892851984577985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20560771796595234656385323 30841157694892851984577985)
      ·
        refine ⟨23130868271169638988433489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30841157694892851984577985 23130868271169638988433489)
        ·
          refine ⟨17348151203377229241325117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23130868271169638988433489 17348151203377229241325117)
          ·
            refine ⟨6505556701266460965496919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17348151203377229241325117 6505556701266460965496919)
            ·
              refine ⟨9758335051899691448245379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6505556701266460965496919 9758335051899691448245379)
              ·
                refine ⟨14637502577849537172368069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9758335051899691448245379 14637502577849537172368069)
                ·
                  refine ⟨2744531733346788219819013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14637502577849537172368069 2744531733346788219819013)
                  ·
                    refine ⟨514599700002522791216065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2744531733346788219819013 514599700002522791216065)
                    ·
                      rfl

theorem cell22_1503269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 1, 4, 4].length) (baseStart_1503269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1503269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1503269 prefixEnd_1503269 := by exact prefixLift 1503269
  have htrace : WordTrace (prefixWord ++ tailWord_1503269) baseStart_1503269 baseEnd_1503269 := by
    simpa [prefixWord, tailWord_1503269, baseEnd_1503269] using wordTrace_append hprefix tailTrace_1503269
  have hstable : (prefixWord ++ tailWord_1503269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1503269).length < 2 ^ (prefixWord ++ tailWord_1503269).sum := by decide
  have hdescent : baseEnd_1503269 < baseStart_1503269 := by decide
  rcases family_descends (prefixWord ++ tailWord_1503269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1503286 : List Nat := [5, 1, 2, 1, 1, 1, 1, 2, 4, 4]
def baseStart_1503286 : Nat := 118140960795 + 1503286 * 2 ^ 59
def prefixEnd_1503286 : Nat := 4983230072969 + 3 ^ 40 * 1503286 * 2
def baseEnd_1503286 : Nat := 514605519449940413541013

theorem tailTrace_1503286 : CollatzResearch.WordTrace tailWord_1503286 prefixEnd_1503286 514605519449940413541013 := by
  unfold tailWord_1503286
  simp only [CollatzResearch.WordTrace]
  refine ⟨3426834051991189853358107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36552896554572691769153141 3426834051991189853358107)
  ·
    refine ⟨5140251077986784780037161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3426834051991189853358107 5140251077986784780037161)
    ·
      refine ⟨3855188308490088585027871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5140251077986784780037161 3855188308490088585027871)
      ·
        refine ⟨5782782462735132877541807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3855188308490088585027871 5782782462735132877541807)
        ·
          refine ⟨8674173694102699316312711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5782782462735132877541807 8674173694102699316312711)
          ·
            refine ⟨13011260541154048974469067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8674173694102699316312711 13011260541154048974469067)
            ·
              refine ⟨19516890811731073461703601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13011260541154048974469067 19516890811731073461703601)
              ·
                refine ⟨14637668108798305096277701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19516890811731073461703601 14637668108798305096277701)
                ·
                  refine ⟨2744562770399682205552069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14637668108798305096277701 2744562770399682205552069)
                  ·
                    refine ⟨514605519449940413541013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2744562770399682205552069 514605519449940413541013)
                    ·
                      rfl

theorem cell22_1503286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_1503286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1503286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1503286 prefixEnd_1503286 := by exact prefixLift 1503286
  have htrace : WordTrace (prefixWord ++ tailWord_1503286) baseStart_1503286 baseEnd_1503286 := by
    simpa [prefixWord, tailWord_1503286, baseEnd_1503286] using wordTrace_append hprefix tailTrace_1503286
  have hstable : (prefixWord ++ tailWord_1503286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1503286).length < 2 ^ (prefixWord ++ tailWord_1503286).sum := by decide
  have hdescent : baseEnd_1503286 < baseStart_1503286 := by decide
  rcases family_descends (prefixWord ++ tailWord_1503286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1503288 : List Nat := [2, 1, 2, 1, 6, 1, 1, 3, 2, 3]
def baseStart_1503288 : Nat := 118140960795 + 1503288 * 2 ^ 59
def prefixEnd_1503288 : Nat := 4983230072969 + 3 ^ 40 * 1503288 * 2
def baseEnd_1503288 : Nat := 514606204090813074991007

theorem tailTrace_1503288 : CollatzResearch.WordTrace tailWord_1503288 prefixEnd_1503288 514606204090813074991007 := by
  unfold tailWord_1503288
  simp only [CollatzResearch.WordTrace]
  refine ⟨27414708888925895997651259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36552945185234527996868345 27414708888925895997651259)
  ·
    refine ⟨41122063333388843996476889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27414708888925895997651259 41122063333388843996476889)
    ·
      refine ⟨30841547500041632997357667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41122063333388843996476889 30841547500041632997357667)
      ·
        refine ⟨46262321250062449496036501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30841547500041632997357667 46262321250062449496036501)
        ·
          refine ⟨2168546308596677320126711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 46262321250062449496036501 2168546308596677320126711)
          ·
            refine ⟨3252819462895015980190067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2168546308596677320126711 3252819462895015980190067)
            ·
              refine ⟨4879229194342523970285101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3252819462895015980190067 4879229194342523970285101)
              ·
                refine ⟨1829710947878446488856913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4879229194342523970285101 1829710947878446488856913)
                ·
                  refine ⟨1372283210908834866642685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1829710947878446488856913 1372283210908834866642685)
                  ·
                    refine ⟨514606204090813074991007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1372283210908834866642685 514606204090813074991007)
                    ·
                      rfl

theorem cell22_1503288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 3, 2, 3].length) (baseStart_1503288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1503288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1503288 prefixEnd_1503288 := by exact prefixLift 1503288
  have htrace : WordTrace (prefixWord ++ tailWord_1503288) baseStart_1503288 baseEnd_1503288 := by
    simpa [prefixWord, tailWord_1503288, baseEnd_1503288] using wordTrace_append hprefix tailTrace_1503288
  have hstable : (prefixWord ++ tailWord_1503288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1503288).length < 2 ^ (prefixWord ++ tailWord_1503288).sum := by decide
  have hdescent : baseEnd_1503288 < baseStart_1503288 := by decide
  rcases family_descends (prefixWord ++ tailWord_1503288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1503344 : List Nat := [2, 1, 1, 1, 5, 2, 1, 1, 1, 7]
def baseStart_1503344 : Nat := 118140960795 + 1503344 * 2 ^ 59
def prefixEnd_1503344 : Nat := 4983230072969 + 3 ^ 40 * 1503344 * 2
def baseEnd_1503344 : Nat := 514625374035247595590835

theorem tailTrace_1503344 : CollatzResearch.WordTrace tailWord_1503344 prefixEnd_1503344 514625374035247595590835 := by
  unfold tailWord_1503344
  simp only [CollatzResearch.WordTrace]
  refine ⟨27415730132824456779670543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36554306843765942372894057 27415730132824456779670543)
  ·
    refine ⟨41123595199236685169505815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27415730132824456779670543 41123595199236685169505815)
    ·
      refine ⟨61685392798855027754258723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41123595199236685169505815 61685392798855027754258723)
      ·
        refine ⟨92528089198282541631388085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61685392798855027754258723 92528089198282541631388085)
        ·
          refine ⟨8674508362338988277942633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 92528089198282541631388085 8674508362338988277942633)
          ·
            refine ⟨6505881271754241208456975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8674508362338988277942633 6505881271754241208456975)
            ·
              refine ⟨9758821907631361812685463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6505881271754241208456975 9758821907631361812685463)
              ·
                refine ⟨14638232861447042719028195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9758821907631361812685463 14638232861447042719028195)
                ·
                  refine ⟨21957349292170564078542293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14638232861447042719028195 21957349292170564078542293)
                  ·
                    refine ⟨514625374035247595590835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21957349292170564078542293 514625374035247595590835)
                    ·
                      rfl

theorem cell22_1503344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 1, 1, 7].length) (baseStart_1503344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1503344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1503344 prefixEnd_1503344 := by exact prefixLift 1503344
  have htrace : WordTrace (prefixWord ++ tailWord_1503344) baseStart_1503344 baseEnd_1503344 := by
    simpa [prefixWord, tailWord_1503344, baseEnd_1503344] using wordTrace_append hprefix tailTrace_1503344
  have hstable : (prefixWord ++ tailWord_1503344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1503344).length < 2 ^ (prefixWord ++ tailWord_1503344).sum := by decide
  have hdescent : baseEnd_1503344 < baseStart_1503344 := by decide
  rcases family_descends (prefixWord ++ tailWord_1503344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1503346 : List Nat := [3, 2, 1, 2, 2, 2, 2, 3, 5]
def baseStart_1503346 : Nat := 118140960795 + 1503346 * 2 ^ 59
def prefixEnd_1503346 : Nat := 4983230072969 + 3 ^ 40 * 1503346 * 2
def baseEnd_1503346 : Nat := 171542019558706752346943

theorem tailTrace_1503346 : CollatzResearch.WordTrace tailWord_1503346 prefixEnd_1503346 171542019558706752346943 := by
  unfold tailWord_1503346
  simp only [CollatzResearch.WordTrace]
  refine ⟨13707883302910416975228473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36554355474427778600609261 13707883302910416975228473)
  ·
    refine ⟨10280912477182812731421355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13707883302910416975228473 10280912477182812731421355)
    ·
      refine ⟨15421368715774219097132033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10280912477182812731421355 15421368715774219097132033)
      ·
        refine ⟨11566026536830664322849025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15421368715774219097132033 11566026536830664322849025)
        ·
          refine ⟨8674519902622998242136769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11566026536830664322849025 8674519902622998242136769)
          ·
            refine ⟨6505889926967248681602577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8674519902622998242136769 6505889926967248681602577)
            ·
              refine ⟨4879417445225436511201933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6505889926967248681602577 4879417445225436511201933)
              ·
                refine ⟨1829781541959538691700725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4879417445225436511201933 1829781541959538691700725)
                ·
                  refine ⟨171542019558706752346943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1829781541959538691700725 171542019558706752346943)
                  ·
                    rfl

theorem cell22_1503346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 3, 5].length) (baseStart_1503346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1503346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1503346 prefixEnd_1503346 := by exact prefixLift 1503346
  have htrace : WordTrace (prefixWord ++ tailWord_1503346) baseStart_1503346 baseEnd_1503346 := by
    simpa [prefixWord, tailWord_1503346, baseEnd_1503346] using wordTrace_append hprefix tailTrace_1503346
  have hstable : (prefixWord ++ tailWord_1503346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1503346).length < 2 ^ (prefixWord ++ tailWord_1503346).sum := by decide
  have hdescent : baseEnd_1503346 < baseStart_1503346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1503346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1503376 : List Nat := [2, 1, 1, 1, 1, 1, 7, 3, 1, 4]
def baseStart_1503376 : Nat := 118140960795 + 1503376 * 2 ^ 59
def prefixEnd_1503376 : Nat := 4983230072969 + 3 ^ 40 * 1503376 * 2
def baseEnd_1503376 : Nat := 514636328289210178790737

theorem tailTrace_1503376 : CollatzResearch.WordTrace tailWord_1503376 prefixEnd_1503376 514636328289210178790737 := by
  unfold tailWord_1503376
  simp only [CollatzResearch.WordTrace]
  refine ⟨27416313700766491512252991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36555084934355322016337321 27416313700766491512252991)
  ·
    refine ⟨41124470551149737268379487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27416313700766491512252991 41124470551149737268379487)
    ·
      refine ⟨61686705826724605902569231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41124470551149737268379487 61686705826724605902569231)
      ·
        refine ⟨92530058740086908853853847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61686705826724605902569231 92530058740086908853853847)
        ·
          refine ⟨138795088110130363280780771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92530058740086908853853847 138795088110130363280780771)
          ·
            refine ⟨208192632165195544921171157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138795088110130363280780771 208192632165195544921171157)
            ·
              refine ⟨4879514816371770584089949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 208192632165195544921171157 4879514816371770584089949)
              ·
                refine ⟨1829818056139413969033731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4879514816371770584089949 1829818056139413969033731)
                ·
                  refine ⟨2744727084209120953550597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1829818056139413969033731 2744727084209120953550597)
                  ·
                    refine ⟨514636328289210178790737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2744727084209120953550597 514636328289210178790737)
                    ·
                      rfl

theorem cell22_1503376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 3, 1, 4].length) (baseStart_1503376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1503376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1503376 prefixEnd_1503376 := by exact prefixLift 1503376
  have htrace : WordTrace (prefixWord ++ tailWord_1503376) baseStart_1503376 baseEnd_1503376 := by
    simpa [prefixWord, tailWord_1503376, baseEnd_1503376] using wordTrace_append hprefix tailTrace_1503376
  have hstable : (prefixWord ++ tailWord_1503376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1503376).length < 2 ^ (prefixWord ++ tailWord_1503376).sum := by decide
  have hdescent : baseEnd_1503376 < baseStart_1503376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1503376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1503391 : List Nat := [1, 1, 2, 6, 1, 1, 1, 3, 6]
def baseStart_1503391 : Nat := 118140960795 + 1503391 * 2 ^ 59
def prefixEnd_1503391 : Nat := 4983230072969 + 3 ^ 40 * 1503391 * 2
def baseEnd_1503391 : Nat := 171547154365251713221897

theorem tailTrace_1503391 : CollatzResearch.WordTrace tailWord_1503391 prefixEnd_1503391 171547154365251713221897 := by
  unfold tailWord_1503391
  simp only [CollatzResearch.WordTrace]
  refine ⟨54833174496478640586302027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36555449664319093724201351 54833174496478640586302027)
  ·
    refine ⟨82249761744717960879453041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54833174496478640586302027 82249761744717960879453041)
    ·
      refine ⟨61687321308538470659589781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82249761744717960879453041 61687321308538470659589781)
      ·
        refine ⟨2891593186337740812168271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 61687321308538470659589781 2891593186337740812168271)
        ·
          refine ⟨4337389779506611218252407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2891593186337740812168271 4337389779506611218252407)
          ·
            refine ⟨6506084669259916827378611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4337389779506611218252407 6506084669259916827378611)
            ·
              refine ⟨9759127003889875241067917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6506084669259916827378611 9759127003889875241067917)
              ·
                refine ⟨3659672626458703215400469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9759127003889875241067917 3659672626458703215400469)
                ·
                  refine ⟨171547154365251713221897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3659672626458703215400469 171547154365251713221897)
                  ·
                    rfl

theorem cell22_1503391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 3, 6].length) (baseStart_1503391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1503391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1503391 prefixEnd_1503391 := by exact prefixLift 1503391
  have htrace : WordTrace (prefixWord ++ tailWord_1503391) baseStart_1503391 baseEnd_1503391 := by
    simpa [prefixWord, tailWord_1503391, baseEnd_1503391] using wordTrace_append hprefix tailTrace_1503391
  have hstable : (prefixWord ++ tailWord_1503391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1503391).length < 2 ^ (prefixWord ++ tailWord_1503391).sum := by decide
  have hdescent : baseEnd_1503391 < baseStart_1503391 := by decide
  rcases family_descends (prefixWord ++ tailWord_1503391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1503419 : List Nat := [1, 1, 1, 1, 1, 2, 7, 8]
def baseStart_1503419 : Nat := 118140960795 + 1503419 * 2 ^ 59
def prefixEnd_1503419 : Nat := 4983230072969 + 3 ^ 40 * 1503419 * 2
def baseEnd_1503419 : Nat := 57183449785330266662845

theorem tailTrace_1503419 : CollatzResearch.WordTrace tailWord_1503419 prefixEnd_1503419 57183449785330266662845 := by
  unfold tailWord_1503419
  simp only [CollatzResearch.WordTrace]
  refine ⟨54834195740377201368321311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36556130493584800912214207 54834195740377201368321311)
  ·
    refine ⟨82251293610565802052481967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54834195740377201368321311 82251293610565802052481967)
    ·
      refine ⟨123376940415848703078722951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82251293610565802052481967 123376940415848703078722951)
      ·
        refine ⟨185065410623773054618084427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123376940415848703078722951 185065410623773054618084427)
        ·
          refine ⟨277598115935659581927126641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185065410623773054618084427 277598115935659581927126641)
          ·
            refine ⟨208198586951744686445344981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 277598115935659581927126641 208198586951744686445344981)
            ·
              refine ⟨4879654381681516088562773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 208198586951744686445344981 4879654381681516088562773)
              ·
                refine ⟨57183449785330266662845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4879654381681516088562773 57183449785330266662845)
                ·
                  rfl

theorem cell22_1503419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 8].length) (baseStart_1503419 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1503419 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1503419 prefixEnd_1503419 := by exact prefixLift 1503419
  have htrace : WordTrace (prefixWord ++ tailWord_1503419) baseStart_1503419 baseEnd_1503419 := by
    simpa [prefixWord, tailWord_1503419, baseEnd_1503419] using wordTrace_append hprefix tailTrace_1503419
  have hstable : (prefixWord ++ tailWord_1503419).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1503419).length < 2 ^ (prefixWord ++ tailWord_1503419).sum := by decide
  have hdescent : baseEnd_1503419 < baseStart_1503419 := by decide
  rcases family_descends (prefixWord ++ tailWord_1503419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1503421 : List Nat := [1, 4, 1, 2, 1, 1, 1, 5, 2, 4]
def baseStart_1503421 : Nat := 118140960795 + 1503421 * 2 ^ 59
def prefixEnd_1503421 : Nat := 4983230072969 + 3 ^ 40 * 1503421 * 2
def baseEnd_1503421 : Nat := 514651732708845061415599

theorem tailTrace_1503421 : CollatzResearch.WordTrace tailWord_1503421 prefixEnd_1503421 514651732708845061415599 := by
  unfold tailWord_1503421
  simp only [CollatzResearch.WordTrace]
  refine ⟨54834268686369955709894117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36556179124246637139929411 54834268686369955709894117)
  ·
    refine ⟨10281425378694366695605147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54834268686369955709894117 10281425378694366695605147)
    ·
      refine ⟨15422138068041550043407721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10281425378694366695605147 15422138068041550043407721)
      ·
        refine ⟨11566603551031162532555791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15422138068041550043407721 11566603551031162532555791)
        ·
          refine ⟨17349905326546743798833687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11566603551031162532555791 17349905326546743798833687)
          ·
            refine ⟨26024857989820115698250531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17349905326546743798833687 26024857989820115698250531)
            ·
              refine ⟨39037286984730173547375797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26024857989820115698250531 39037286984730173547375797)
              ·
                refine ⟨3659745654818453770066481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39037286984730173547375797 3659745654818453770066481)
                ·
                  refine ⟨2744809241113840327549861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3659745654818453770066481 2744809241113840327549861)
                  ·
                    refine ⟨514651732708845061415599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2744809241113840327549861 514651732708845061415599)
                    ·
                      rfl

theorem cell22_1503421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 5, 2, 4].length) (baseStart_1503421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1503421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1503421 prefixEnd_1503421 := by exact prefixLift 1503421
  have htrace : WordTrace (prefixWord ++ tailWord_1503421) baseStart_1503421 baseEnd_1503421 := by
    simpa [prefixWord, tailWord_1503421, baseEnd_1503421] using wordTrace_append hprefix tailTrace_1503421
  have hstable : (prefixWord ++ tailWord_1503421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1503421).length < 2 ^ (prefixWord ++ tailWord_1503421).sum := by decide
  have hdescent : baseEnd_1503421 < baseStart_1503421 := by decide
  rcases family_descends (prefixWord ++ tailWord_1503421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1503438 : List Nat := [4, 1, 1, 1, 4, 2, 1, 2, 2, 4]
def baseStart_1503438 : Nat := 118140960795 + 1503438 * 2 ^ 59
def prefixEnd_1503438 : Nat := 4983230072969 + 3 ^ 40 * 1503438 * 2
def baseEnd_1503438 : Nat := 514657552156262683740547

theorem tailTrace_1503438 : CollatzResearch.WordTrace tailWord_1503438 prefixEnd_1503438 514657552156262683740547 := by
  unfold tailWord_1503438
  simp only [CollatzResearch.WordTrace]
  refine ⟨6854361090913545951657871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36556592484872245075508645 6854361090913545951657871)
  ·
    refine ⟨10281541636370318927486807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6854361090913545951657871 10281541636370318927486807)
    ·
      refine ⟨15422312454555478391230211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10281541636370318927486807 15422312454555478391230211)
      ·
        refine ⟨23133468681833217586845317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15422312454555478391230211 23133468681833217586845317)
        ·
          refine ⟨4337525377843728297533497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23133468681833217586845317 4337525377843728297533497)
          ·
            refine ⟨3253144033382796223150123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4337525377843728297533497 3253144033382796223150123)
            ·
              refine ⟨4879716050074194334725185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3253144033382796223150123 4879716050074194334725185)
              ·
                refine ⟨3659787037555645751043889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4879716050074194334725185 3659787037555645751043889)
                ·
                  refine ⟨2744840278166734313282917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3659787037555645751043889 2744840278166734313282917)
                  ·
                    refine ⟨514657552156262683740547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2744840278166734313282917 514657552156262683740547)
                    ·
                      rfl

theorem cell22_1503438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 2, 2, 4].length) (baseStart_1503438 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1503438 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1503438 prefixEnd_1503438 := by exact prefixLift 1503438
  have htrace : WordTrace (prefixWord ++ tailWord_1503438) baseStart_1503438 baseEnd_1503438 := by
    simpa [prefixWord, tailWord_1503438, baseEnd_1503438] using wordTrace_append hprefix tailTrace_1503438
  have hstable : (prefixWord ++ tailWord_1503438).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1503438).length < 2 ^ (prefixWord ++ tailWord_1503438).sum := by decide
  have hdescent : baseEnd_1503438 < baseStart_1503438 := by decide
  rcases family_descends (prefixWord ++ tailWord_1503438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1503453 : List Nat := [1, 4, 3, 2, 1, 2, 2, 7]
def baseStart_1503453 : Nat := 118140960795 + 1503453 * 2 ^ 59
def prefixEnd_1503453 : Nat := 4983230072969 + 3 ^ 40 * 1503453 * 2
def baseEnd_1503453 : Nat := 57184742995867516068389

theorem tailTrace_1503453 : CollatzResearch.WordTrace tailWord_1503453 prefixEnd_1503453 57184742995867516068389 := by
  unfold tailWord_1503453
  simp only [CollatzResearch.WordTrace]
  refine ⟨54835435822254025175059013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36556957214836016783372675 54835435822254025175059013)
  ·
    refine ⟨10281644216672629720323565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54835435822254025175059013 10281644216672629720323565)
    ·
      refine ⟨3855616581252236145121337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10281644216672629720323565 3855616581252236145121337)
      ·
        refine ⟨2891712435939177108841003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3855616581252236145121337 2891712435939177108841003)
        ·
          refine ⟨4337568653908765663261505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2891712435939177108841003 4337568653908765663261505)
          ·
            refine ⟨3253176490431574247446129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4337568653908765663261505 3253176490431574247446129)
            ·
              refine ⟨2439882367823680685584597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3253176490431574247446129 2439882367823680685584597)
              ·
                refine ⟨57184742995867516068389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2439882367823680685584597 57184742995867516068389)
                ·
                  rfl

theorem cell22_1503453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 2, 7].length) (baseStart_1503453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1503453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1503453 prefixEnd_1503453 := by exact prefixLift 1503453
  have htrace : WordTrace (prefixWord ++ tailWord_1503453) baseStart_1503453 baseEnd_1503453 := by
    simpa [prefixWord, tailWord_1503453, baseEnd_1503453] using wordTrace_append hprefix tailTrace_1503453
  have hstable : (prefixWord ++ tailWord_1503453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1503453).length < 2 ^ (prefixWord ++ tailWord_1503453).sum := by decide
  have hdescent : baseEnd_1503453 < baseStart_1503453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1503453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1503545 : List Nat := [1, 2, 1, 6, 1, 2, 1, 3, 1, 4]
def baseStart_1503545 : Nat := 118140960795 + 1503545 * 2 ^ 59
def prefixEnd_1503545 : Nat := 4983230072969 + 3 ^ 40 * 1503545 * 2
def baseEnd_1503545 : Nat := 514694180442950071315219

theorem tailTrace_1503545 : CollatzResearch.WordTrace tailWord_1503545 prefixEnd_1503545 514694180442950071315219 := by
  unfold tailWord_1503545
  simp only [CollatzResearch.WordTrace]
  refine ⟨54838791337920724887408089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36559194225280483258272059 54838791337920724887408089)
  ·
    refine ⟨41129093503440543665556067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54838791337920724887408089 41129093503440543665556067)
    ·
      refine ⟨61693640255160815498334101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41129093503440543665556067 61693640255160815498334101)
      ·
        refine ⟨2891889386960663226484411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 61693640255160815498334101 2891889386960663226484411)
        ·
          refine ⟨4337834080440994839726617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2891889386960663226484411 4337834080440994839726617)
          ·
            refine ⟨3253375560330746129794963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4337834080440994839726617 3253375560330746129794963)
            ·
              refine ⟨4880063340496119194692445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3253375560330746129794963 4880063340496119194692445)
              ·
                refine ⟨1830023752686044698009667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4880063340496119194692445 1830023752686044698009667)
                ·
                  refine ⟨2745035629029067047014501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1830023752686044698009667 2745035629029067047014501)
                  ·
                    refine ⟨514694180442950071315219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2745035629029067047014501 514694180442950071315219)
                    ·
                      rfl

theorem cell22_1503545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 3, 1, 4].length) (baseStart_1503545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1503545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1503545 prefixEnd_1503545 := by exact prefixLift 1503545
  have htrace : WordTrace (prefixWord ++ tailWord_1503545) baseStart_1503545 baseEnd_1503545 := by
    simpa [prefixWord, tailWord_1503545, baseEnd_1503545] using wordTrace_append hprefix tailTrace_1503545
  have hstable : (prefixWord ++ tailWord_1503545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1503545).length < 2 ^ (prefixWord ++ tailWord_1503545).sum := by decide
  have hdescent : baseEnd_1503545 < baseStart_1503545 := by decide
  rcases family_descends (prefixWord ++ tailWord_1503545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1503601 : List Nat := [1, 2, 2, 2, 1, 2, 1, 2, 1, 8]
def baseStart_1503601 : Nat := 118140960795 + 1503601 * 2 ^ 59
def prefixEnd_1503601 : Nat := 4983230072969 + 3 ^ 40 * 1503601 * 2
def baseEnd_1503601 : Nat := 514713350387384591915047

theorem tailTrace_1503601 : CollatzResearch.WordTrace tailWord_1503601 prefixEnd_1503601 514713350387384591915047 := by
  unfold tailWord_1503601
  simp only [CollatzResearch.WordTrace]
  refine ⟨54840833825717846451446657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36560555883811897634297771 54840833825717846451446657)
  ·
    refine ⟨41130625369288384838584993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54840833825717846451446657 41130625369288384838584993)
    ·
      refine ⟨30847969026966288628938745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41130625369288384838584993 30847969026966288628938745)
      ·
        refine ⟨23135976770224716471704059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30847969026966288628938745 23135976770224716471704059)
        ·
          refine ⟨34703965155337074707556089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23135976770224716471704059 34703965155337074707556089)
          ·
            refine ⟨26027973866502806030667067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34703965155337074707556089 26027973866502806030667067)
            ·
              refine ⟨39041960799754209046000601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26027973866502806030667067 39041960799754209046000601)
              ·
                refine ⟨29281470599815656784500451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39041960799754209046000601 29281470599815656784500451)
                ·
                  refine ⟨43922205899723485176750677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29281470599815656784500451 43922205899723485176750677)
                  ·
                    refine ⟨514713350387384591915047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 43922205899723485176750677 514713350387384591915047)
                    ·
                      rfl

theorem cell22_1503601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 8].length) (baseStart_1503601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1503601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1503601 prefixEnd_1503601 := by exact prefixLift 1503601
  have htrace : WordTrace (prefixWord ++ tailWord_1503601) baseStart_1503601 baseEnd_1503601 := by
    simpa [prefixWord, tailWord_1503601, baseEnd_1503601] using wordTrace_append hprefix tailTrace_1503601
  have hstable : (prefixWord ++ tailWord_1503601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1503601).length < 2 ^ (prefixWord ++ tailWord_1503601).sum := by decide
  have hdescent : baseEnd_1503601 < baseStart_1503601 := by decide
  rcases family_descends (prefixWord ++ tailWord_1503601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1503626 : List Nat := [3, 1, 2, 5, 1, 2, 2, 1, 2, 3]
def baseStart_1503626 : Nat := 118140960795 + 1503626 * 2 ^ 59
def prefixEnd_1503626 : Nat := 4983230072969 + 3 ^ 40 * 1503626 * 2
def baseEnd_1503626 : Nat := 514721908398292860039971

theorem tailTrace_1503626 : CollatzResearch.WordTrace tailWord_1503626 prefixEnd_1503626 514721908398292860039971 := by
  unfold tailWord_1503626
  simp only [CollatzResearch.WordTrace]
  refine ⟨13710436412656818930276683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36561163767084850480737821 13710436412656818930276683)
  ·
    refine ⟨20565654618985228395415025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13710436412656818930276683 20565654618985228395415025)
    ·
      refine ⟨15424240964238921296561269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20565654618985228395415025 15424240964238921296561269)
      ·
        refine ⟨1446022590397398871552619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15424240964238921296561269 1446022590397398871552619)
        ·
          refine ⟨2169033885596098307328929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1446022590397398871552619 2169033885596098307328929)
          ·
            refine ⟨1626775414197073730496697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2169033885596098307328929 1626775414197073730496697)
            ·
              refine ⟨1220081560647805297872523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1626775414197073730496697 1220081560647805297872523)
              ·
                refine ⟨1830122340971707946808785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1220081560647805297872523 1830122340971707946808785)
                ·
                  refine ⟨1372591755728780960106589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1830122340971707946808785 1372591755728780960106589)
                  ·
                    refine ⟨514721908398292860039971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1372591755728780960106589 514721908398292860039971)
                    ·
                      rfl

theorem cell22_1503626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 2, 1, 2, 3].length) (baseStart_1503626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1503626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1503626 prefixEnd_1503626 := by exact prefixLift 1503626
  have htrace : WordTrace (prefixWord ++ tailWord_1503626) baseStart_1503626 baseEnd_1503626 := by
    simpa [prefixWord, tailWord_1503626, baseEnd_1503626] using wordTrace_append hprefix tailTrace_1503626
  have hstable : (prefixWord ++ tailWord_1503626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1503626).length < 2 ^ (prefixWord ++ tailWord_1503626).sum := by decide
  have hdescent : baseEnd_1503626 < baseStart_1503626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1503626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1503802 : List Nat := [3, 1, 1, 1, 3, 3, 4, 1, 5]
def baseStart_1503802 : Nat := 118140960795 + 1503802 * 2 ^ 59
def prefixEnd_1503802 : Nat := 4983230072969 + 3 ^ 40 * 1503802 * 2
def baseEnd_1503802 : Nat := 171594052265029022546477

theorem tailTrace_1503802 : CollatzResearch.WordTrace tailWord_1503802 prefixEnd_1503802 171594052265029022546477 := by
  unfold tailWord_1503802
  simp only [CollatzResearch.WordTrace]
  refine ⟨13712041224497414444878415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36565443265326438519675773 13712041224497414444878415)
  ·
    refine ⟨20568061836746121667317623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13712041224497414444878415 20568061836746121667317623)
    ·
      refine ⟨30852092755119182500976435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20568061836746121667317623 30852092755119182500976435)
      ·
        refine ⟨46278139132678773751464653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30852092755119182500976435 46278139132678773751464653)
        ·
          refine ⟨17354302174754540156799245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46278139132678773751464653 17354302174754540156799245)
          ·
            refine ⟨6507863315532952558799717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17354302174754540156799245 6507863315532952558799717)
            ·
              refine ⟨1220224371662428604774947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6507863315532952558799717 1220224371662428604774947)
              ·
                refine ⟨1830336557493642907162421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1220224371662428604774947 1830336557493642907162421)
                ·
                  refine ⟨171594052265029022546477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1830336557493642907162421 171594052265029022546477)
                  ·
                    rfl

theorem cell22_1503802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 4, 1, 5].length) (baseStart_1503802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1503802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1503802 prefixEnd_1503802 := by exact prefixLift 1503802
  have htrace : WordTrace (prefixWord ++ tailWord_1503802) baseStart_1503802 baseEnd_1503802 := by
    simpa [prefixWord, tailWord_1503802, baseEnd_1503802] using wordTrace_append hprefix tailTrace_1503802
  have hstable : (prefixWord ++ tailWord_1503802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1503802).length < 2 ^ (prefixWord ++ tailWord_1503802).sum := by decide
  have hdescent : baseEnd_1503802 < baseStart_1503802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1503802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1503877 : List Nat := [1, 3, 1, 1, 4, 2, 3, 1, 2, 4]
def baseStart_1503877 : Nat := 118140960795 + 1503877 * 2 ^ 59
def prefixEnd_1503877 : Nat := 4983230072969 + 3 ^ 40 * 1503877 * 2
def baseEnd_1503877 : Nat := 514807830827811872014201

theorem tailTrace_1503877 : CollatzResearch.WordTrace tailWord_1503877 prefixEnd_1503877 514807830827811872014201 := by
  unfold tailWord_1503877
  simp only [CollatzResearch.WordTrace]
  refine ⟨54850900372717945588493885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36567266915145297058995923 54850900372717945588493885)
  ·
    refine ⟨20569087639769229595685207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54850900372717945588493885 20569087639769229595685207)
    ·
      refine ⟨30853631459653844393527811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20569087639769229595685207 30853631459653844393527811)
      ·
        refine ⟨46280447189480766590291717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30853631459653844393527811 46280447189480766590291717)
        ·
          refine ⟨8677583848027643735679697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46280447189480766590291717 8677583848027643735679697)
          ·
            refine ⟨6508187886020732801759773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8677583848027643735679697 6508187886020732801759773)
            ·
              refine ⟨2440570457257774800659915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6508187886020732801759773 2440570457257774800659915)
              ·
                refine ⟨3660855685886662200989873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2440570457257774800659915 3660855685886662200989873)
                ·
                  refine ⟨2745641764414996650742405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3660855685886662200989873 2745641764414996650742405)
                  ·
                    refine ⟨514807830827811872014201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2745641764414996650742405 514807830827811872014201)
                    ·
                      rfl

theorem cell22_1503877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 3, 1, 2, 4].length) (baseStart_1503877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1503877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1503877 prefixEnd_1503877 := by exact prefixLift 1503877
  have htrace : WordTrace (prefixWord ++ tailWord_1503877) baseStart_1503877 baseEnd_1503877 := by
    simpa [prefixWord, tailWord_1503877, baseEnd_1503877] using wordTrace_append hprefix tailTrace_1503877
  have hstable : (prefixWord ++ tailWord_1503877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1503877).length < 2 ^ (prefixWord ++ tailWord_1503877).sum := by decide
  have hdescent : baseEnd_1503877 < baseStart_1503877 := by decide
  rcases family_descends (prefixWord ++ tailWord_1503877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1503892 : List Nat := [2, 4, 2, 2, 1, 2, 9]
def baseStart_1503892 : Nat := 118140960795 + 1503892 * 2 ^ 59
def prefixEnd_1503892 : Nat := 4983230072969 + 3 ^ 40 * 1503892 * 2
def baseEnd_1503892 : Nat := 19067146875346549366265

theorem tailTrace_1503892 : CollatzResearch.WordTrace tailWord_1503892 prefixEnd_1503892 19067146875346549366265 := by
  unfold tailWord_1503892
  simp only [CollatzResearch.WordTrace]
  refine ⟨27425723733831801575144965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36567631645109068766859953 27425723733831801575144965)
  ·
    refine ⟨5142323200093462795339681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27425723733831801575144965 5142323200093462795339681)
    ·
      refine ⟨3856742400070097096504761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5142323200093462795339681 3856742400070097096504761)
      ·
        refine ⟨2892556800052572822378571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3856742400070097096504761 2892556800052572822378571)
        ·
          refine ⟨4338835200078859233567857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2892556800052572822378571 4338835200078859233567857)
          ·
            refine ⟨3254126400059144425175893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4338835200078859233567857 3254126400059144425175893)
            ·
              refine ⟨19067146875346549366265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3254126400059144425175893 19067146875346549366265)
              ·
                rfl

theorem cell22_1503892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 9].length) (baseStart_1503892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1503892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1503892 prefixEnd_1503892 := by exact prefixLift 1503892
  have htrace : WordTrace (prefixWord ++ tailWord_1503892) baseStart_1503892 baseEnd_1503892 := by
    simpa [prefixWord, tailWord_1503892, baseEnd_1503892] using wordTrace_append hprefix tailTrace_1503892
  have hstable : (prefixWord ++ tailWord_1503892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1503892).length < 2 ^ (prefixWord ++ tailWord_1503892).sum := by decide
  have hdescent : baseEnd_1503892 < baseStart_1503892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1503892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1503971 : List Nat := [1, 1, 1, 7, 1, 3, 2, 1, 5]
def baseStart_1503971 : Nat := 118140960795 + 1503971 * 2 ^ 59
def prefixEnd_1503971 : Nat := 4983230072969 + 3 ^ 40 * 1503971 * 2
def baseEnd_1503971 : Nat := 171613336316275653387971

theorem tailTrace_1503971 : CollatzResearch.WordTrace tailWord_1503971 prefixEnd_1503971 171613336316275653387971 := by
  unfold tailWord_1503971
  simp only [CollatzResearch.WordTrace]
  refine ⟨54854328834377399642415767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36569552556251599761610511 54854328834377399642415767)
  ·
    refine ⟨82281493251566099463623651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54854328834377399642415767 82281493251566099463623651)
    ·
      refine ⟨123422239877349149195435477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82281493251566099463623651 123422239877349149195435477)
      ·
        refine ⟨2892708747125370684268019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 123422239877349149195435477 2892708747125370684268019)
        ·
          refine ⟨4339063120688056026402029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2892708747125370684268019 4339063120688056026402029)
          ·
            refine ⟨1627148670258021009900761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4339063120688056026402029 1627148670258021009900761)
            ·
              refine ⟨1220361502693515757425571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1627148670258021009900761 1220361502693515757425571)
              ·
                refine ⟨1830542254040273636138357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1220361502693515757425571 1830542254040273636138357)
                ·
                  refine ⟨171613336316275653387971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1830542254040273636138357 171613336316275653387971)
                  ·
                    rfl

theorem cell22_1503971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 2, 1, 5].length) (baseStart_1503971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1503971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1503971 prefixEnd_1503971 := by exact prefixLift 1503971
  have htrace : WordTrace (prefixWord ++ tailWord_1503971) baseStart_1503971 baseEnd_1503971 := by
    simpa [prefixWord, tailWord_1503971, baseEnd_1503971] using wordTrace_append hprefix tailTrace_1503971
  have hstable : (prefixWord ++ tailWord_1503971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1503971).length < 2 ^ (prefixWord ++ tailWord_1503971).sum := by decide
  have hdescent : baseEnd_1503971 < baseStart_1503971 := by decide
  rcases family_descends (prefixWord ++ tailWord_1503971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1503995 : List Nat := [1, 1, 1, 1, 1, 3, 1, 2, 5, 6]
def baseStart_1503995 : Nat := 118140960795 + 1503995 * 2 ^ 59
def prefixEnd_1503995 : Nat := 4983230072969 + 3 ^ 40 * 1503995 * 2
def baseEnd_1503995 : Nat := 514848224639298897563839

theorem tailTrace_1503995 : CollatzResearch.WordTrace tailWord_1503995 prefixEnd_1503995 514848224639298897563839 := by
  unfold tailWord_1503995
  simp only [CollatzResearch.WordTrace]
  refine ⟨54855204186290451741289439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36570136124193634494192959 54855204186290451741289439)
  ·
    refine ⟨82282806279435677611934159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54855204186290451741289439 82282806279435677611934159)
    ·
      refine ⟨123424209419153516417901239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82282806279435677611934159 123424209419153516417901239)
      ·
        refine ⟨185136314128730274626851859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123424209419153516417901239 185136314128730274626851859)
        ·
          refine ⟨277704471193095411940277789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185136314128730274626851859 277704471193095411940277789)
          ·
            refine ⟨104139176697410779477604171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 277704471193095411940277789 104139176697410779477604171)
            ·
              refine ⟨156208765046116169216406257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104139176697410779477604171 156208765046116169216406257)
              ·
                refine ⟨117156573784587126912304693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 156208765046116169216406257 117156573784587126912304693)
                ·
                  refine ⟨10983428792305043148028565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 117156573784587126912304693 10983428792305043148028565)
                  ·
                    refine ⟨514848224639298897563839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10983428792305043148028565 514848224639298897563839)
                    ·
                      rfl

theorem cell22_1503995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 5, 6].length) (baseStart_1503995 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1503995 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1503995 prefixEnd_1503995 := by exact prefixLift 1503995
  have htrace : WordTrace (prefixWord ++ tailWord_1503995) baseStart_1503995 baseEnd_1503995 := by
    simpa [prefixWord, tailWord_1503995, baseEnd_1503995] using wordTrace_append hprefix tailTrace_1503995
  have hstable : (prefixWord ++ tailWord_1503995).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1503995).length < 2 ^ (prefixWord ++ tailWord_1503995).sum := by decide
  have hdescent : baseEnd_1503995 < baseStart_1503995 := by decide
  rcases family_descends (prefixWord ++ tailWord_1503995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1503997 : List Nat := [1, 4, 1, 1, 1, 1, 5, 2, 1, 5]
def baseStart_1503997 : Nat := 118140960795 + 1503997 * 2 ^ 59
def prefixEnd_1503997 : Nat := 4983230072969 + 3 ^ 40 * 1503997 * 2
def baseEnd_1503997 : Nat := 514848909280171559013833

theorem tailTrace_1503997 : CollatzResearch.WordTrace tailWord_1503997 prefixEnd_1503997 514848909280171559013833 := by
  unfold tailWord_1503997
  simp only [CollatzResearch.WordTrace]
  refine ⟨54855277132283206082862245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36570184754855470721908163 54855277132283206082862245)
  ·
    refine ⟨10285364462303101140536671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54855277132283206082862245 10285364462303101140536671)
    ·
      refine ⟨15428046693454651710805007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10285364462303101140536671 15428046693454651710805007)
      ·
        refine ⟨23142070040181977566207511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15428046693454651710805007 23142070040181977566207511)
        ·
          refine ⟨34713105060272966349311267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23142070040181977566207511 34713105060272966349311267)
          ·
            refine ⟨52069657590409449523966901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34713105060272966349311267 52069657590409449523966901)
            ·
              refine ⟨4881530399100885892871897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52069657590409449523966901 4881530399100885892871897)
              ·
                refine ⟨3661147799325664419653923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4881530399100885892871897 3661147799325664419653923)
                ·
                  refine ⟨5491721698988496629480885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3661147799325664419653923 5491721698988496629480885)
                  ·
                    refine ⟨514848909280171559013833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5491721698988496629480885 514848909280171559013833)
                    ·
                      rfl

theorem cell22_1503997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 2, 1, 5].length) (baseStart_1503997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1503997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1503997 prefixEnd_1503997 := by exact prefixLift 1503997
  have htrace : WordTrace (prefixWord ++ tailWord_1503997) baseStart_1503997 baseEnd_1503997 := by
    simpa [prefixWord, tailWord_1503997, baseEnd_1503997] using wordTrace_append hprefix tailTrace_1503997
  have hstable : (prefixWord ++ tailWord_1503997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1503997).length < 2 ^ (prefixWord ++ tailWord_1503997).sum := by decide
  have hdescent : baseEnd_1503997 < baseStart_1503997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1503997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1504046 : List Nat := [4, 1, 3, 2, 1, 1, 3, 1, 2, 4]
def baseStart_1504046 : Nat := 118140960795 + 1504046 * 2 ^ 59
def prefixEnd_1504046 : Nat := 4983230072969 + 3 ^ 40 * 1504046 * 2
def baseEnd_1504046 : Nat := 514865682981551764538683

theorem tailTrace_1504046 : CollatzResearch.WordTrace tailWord_1504046 prefixEnd_1504046 514865682981551764538683 := by
  unfold tailWord_1504046
  simp only [CollatzResearch.WordTrace]
  refine ⟨6857133038638210931424499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36571376206070458300930661 6857133038638210931424499)
  ·
    refine ⟨10285699557957316397136749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6857133038638210931424499 10285699557957316397136749)
    ·
      refine ⟨3857137334233993648926281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10285699557957316397136749 3857137334233993648926281)
      ·
        refine ⟨2892853000675495236694711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3857137334233993648926281 2892853000675495236694711)
        ·
          refine ⟨4339279501013242855042067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2892853000675495236694711 4339279501013242855042067)
          ·
            refine ⟨6508919251519864282563101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4339279501013242855042067 6508919251519864282563101)
            ·
              refine ⟨2440844719319949105961163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6508919251519864282563101 2440844719319949105961163)
              ·
                refine ⟨3661267078979923658941745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2440844719319949105961163 3661267078979923658941745)
                ·
                  refine ⟨2745950309234942744206309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3661267078979923658941745 2745950309234942744206309)
                  ·
                    refine ⟨514865682981551764538683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2745950309234942744206309 514865682981551764538683)
                    ·
                      rfl

theorem cell22_1504046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_1504046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1504046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1504046 prefixEnd_1504046 := by exact prefixLift 1504046
  have htrace : WordTrace (prefixWord ++ tailWord_1504046) baseStart_1504046 baseEnd_1504046 := by
    simpa [prefixWord, tailWord_1504046, baseEnd_1504046] using wordTrace_append hprefix tailTrace_1504046
  have hstable : (prefixWord ++ tailWord_1504046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1504046).length < 2 ^ (prefixWord ++ tailWord_1504046).sum := by decide
  have hdescent : baseEnd_1504046 < baseStart_1504046 := by decide
  rcases family_descends (prefixWord ++ tailWord_1504046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1504065 : List Nat := [1, 2, 5, 3, 1, 2, 1, 2, 2, 3]
def baseStart_1504065 : Nat := 118140960795 + 1504065 * 2 ^ 59
def prefixEnd_1504065 : Nat := 4983230072969 + 3 ^ 40 * 1504065 * 2
def baseEnd_1504065 : Nat := 514872187069842048313625

theorem tailTrace_1504065 : CollatzResearch.WordTrace tailWord_1504065 prefixEnd_1504065 514872187069842048313625 := by
  unfold tailWord_1504065
  simp only [CollatzResearch.WordTrace]
  refine ⟨54857757296036853696337649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36571838197357902464225099 54857757296036853696337649)
  ·
    refine ⟨41143317972027640272253237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54857757296036853696337649 41143317972027640272253237)
    ·
      refine ⟨3857186059877591275523741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 41143317972027640272253237 3857186059877591275523741)
      ·
        refine ⟨1446444772454096728321403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3857186059877591275523741 1446444772454096728321403)
        ·
          refine ⟨2169667158681145092482105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1446444772454096728321403 2169667158681145092482105)
          ·
            refine ⟨1627250369010858819361579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2169667158681145092482105 1627250369010858819361579)
            ·
              refine ⟨2440875553516288229042369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1627250369010858819361579 2440875553516288229042369)
              ·
                refine ⟨1830656665137216171781777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2440875553516288229042369 1830656665137216171781777)
                ·
                  refine ⟨1372992498852912128836333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1830656665137216171781777 1372992498852912128836333)
                  ·
                    refine ⟨514872187069842048313625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1372992498852912128836333 514872187069842048313625)
                    ·
                      rfl

theorem cell22_1504065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 1, 2, 2, 3].length) (baseStart_1504065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1504065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1504065 prefixEnd_1504065 := by exact prefixLift 1504065
  have htrace : WordTrace (prefixWord ++ tailWord_1504065) baseStart_1504065 baseEnd_1504065 := by
    simpa [prefixWord, tailWord_1504065, baseEnd_1504065] using wordTrace_append hprefix tailTrace_1504065
  have hstable : (prefixWord ++ tailWord_1504065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1504065).length < 2 ^ (prefixWord ++ tailWord_1504065).sum := by decide
  have hdescent : baseEnd_1504065 < baseStart_1504065 := by decide
  rcases family_descends (prefixWord ++ tailWord_1504065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1504072 : List Nat := [2, 1, 3, 1, 1, 3, 3, 1, 7]
def baseStart_1504072 : Nat := 118140960795 + 1504072 * 2 ^ 59
def prefixEnd_1504072 : Nat := 4983230072969 + 3 ^ 40 * 1504072 * 2
def baseEnd_1504072 : Nat := 171624861104298787796201

theorem tailTrace_1504072 : CollatzResearch.WordTrace tailWord_1504072 prefixEnd_1504072 171624861104298787796201 := by
  unfold tailWord_1504072
  simp only [CollatzResearch.WordTrace]
  refine ⟨27429006303505746945921235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36572008404674329261228313 27429006303505746945921235)
  ·
    refine ⟨41143509455258620418881853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27429006303505746945921235 41143509455258620418881853)
    ·
      refine ⟨15428816045721982657080695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41143509455258620418881853 15428816045721982657080695)
      ·
        refine ⟨23143224068582973985621043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15428816045721982657080695 23143224068582973985621043)
        ·
          refine ⟨34714836102874460978431565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23143224068582973985621043 34714836102874460978431565)
          ·
            refine ⟨13018063538577922866911837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34714836102874460978431565 13018063538577922866911837)
            ·
              refine ⟨4881773826966721075091939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13018063538577922866911837 4881773826966721075091939)
              ·
                refine ⟨7322660740450081612637909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4881773826966721075091939 7322660740450081612637909)
                ·
                  refine ⟨171624861104298787796201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7322660740450081612637909 171624861104298787796201)
                  ·
                    rfl

theorem cell22_1504072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 1, 7].length) (baseStart_1504072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1504072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1504072 prefixEnd_1504072 := by exact prefixLift 1504072
  have htrace : WordTrace (prefixWord ++ tailWord_1504072) baseStart_1504072 baseEnd_1504072 := by
    simpa [prefixWord, tailWord_1504072, baseEnd_1504072] using wordTrace_append hprefix tailTrace_1504072
  have hstable : (prefixWord ++ tailWord_1504072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1504072).length < 2 ^ (prefixWord ++ tailWord_1504072).sum := by decide
  have hdescent : baseEnd_1504072 < baseStart_1504072 := by decide
  rcases family_descends (prefixWord ++ tailWord_1504072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1504076 : List Nat := [2, 2, 1, 3, 3, 2, 2, 1, 3, 3]
def baseStart_1504076 : Nat := 118140960795 + 1504076 * 2 ^ 59
def prefixEnd_1504076 : Nat := 4983230072969 + 3 ^ 40 * 1504076 * 2
def baseEnd_1504076 : Nat := 514875952594641686288591

theorem tailTrace_1504076 : CollatzResearch.WordTrace tailWord_1504076 prefixEnd_1504076 514875952594641686288591 := by
  unfold tailWord_1504076
  simp only [CollatzResearch.WordTrace]
  refine ⟨27429079249498501287494041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36572105665998001716658721 27429079249498501287494041)
  ·
    refine ⟨20571809437123875965620531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27429079249498501287494041 20571809437123875965620531)
    ·
      refine ⟨30857714155685813948430797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20571809437123875965620531 30857714155685813948430797)
      ·
        refine ⟨11571642808382180230661549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30857714155685813948430797 11571642808382180230661549)
        ·
          refine ⟨4339366053143317586498081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11571642808382180230661549 4339366053143317586498081)
          ·
            refine ⟨3254524539857488189873561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4339366053143317586498081 3254524539857488189873561)
            ·
              refine ⟨2440893404893116142405171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3254524539857488189873561 2440893404893116142405171)
              ·
                refine ⟨3661340107339674213607757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2440893404893116142405171 3661340107339674213607757)
                ·
                  refine ⟨1373002540252377830102909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3661340107339674213607757 1373002540252377830102909)
                  ·
                    refine ⟨514875952594641686288591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1373002540252377830102909 514875952594641686288591)
                    ·
                      rfl

theorem cell22_1504076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 2, 1, 3, 3].length) (baseStart_1504076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1504076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1504076 prefixEnd_1504076 := by exact prefixLift 1504076
  have htrace : WordTrace (prefixWord ++ tailWord_1504076) baseStart_1504076 baseEnd_1504076 := by
    simpa [prefixWord, tailWord_1504076, baseEnd_1504076] using wordTrace_append hprefix tailTrace_1504076
  have hstable : (prefixWord ++ tailWord_1504076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1504076).length < 2 ^ (prefixWord ++ tailWord_1504076).sum := by decide
  have hdescent : baseEnd_1504076 < baseStart_1504076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1504076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1504147 : List Nat := [1, 1, 1, 2, 1, 2, 1, 6, 1, 6]
def baseStart_1504147 : Nat := 118140960795 + 1504147 * 2 ^ 59
def prefixEnd_1504147 : Nat := 4983230072969 + 3 ^ 40 * 1504147 * 2
def baseEnd_1504147 : Nat := 514900257345621167763373

theorem tailTrace_1504147 : CollatzResearch.WordTrace tailWord_1504147 prefixEnd_1504147 514900257345621167763373 := by
  unfold tailWord_1504147
  simp only [CollatzResearch.WordTrace]
  refine ⟨54860748081739781700822695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36573832054493187800548463 54860748081739781700822695)
  ·
    refine ⟨82291122122609672551234043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54860748081739781700822695 82291122122609672551234043)
    ·
      refine ⟨123436683183914508826851065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82291122122609672551234043 123436683183914508826851065)
      ·
        refine ⟨92577512387935881620138299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123436683183914508826851065 92577512387935881620138299)
        ·
          refine ⟨138866268581903822430207449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92577512387935881620138299 138866268581903822430207449)
          ·
            refine ⟨104149701436427866822655587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138866268581903822430207449 104149701436427866822655587)
            ·
              refine ⟨156224552154641800233983381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104149701436427866822655587 156224552154641800233983381)
              ·
                refine ⟨7323025882248834385967971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 156224552154641800233983381 7323025882248834385967971)
                ·
                  refine ⟨10984538823373251578951957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7323025882248834385967971 10984538823373251578951957)
                  ·
                    refine ⟨514900257345621167763373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10984538823373251578951957 514900257345621167763373)
                    ·
                      rfl

theorem cell22_1504147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 6, 1, 6].length) (baseStart_1504147 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1504147 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1504147 prefixEnd_1504147 := by exact prefixLift 1504147
  have htrace : WordTrace (prefixWord ++ tailWord_1504147) baseStart_1504147 baseEnd_1504147 := by
    simpa [prefixWord, tailWord_1504147, baseEnd_1504147] using wordTrace_append hprefix tailTrace_1504147
  have hstable : (prefixWord ++ tailWord_1504147).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1504147).length < 2 ^ (prefixWord ++ tailWord_1504147).sum := by decide
  have hdescent : baseEnd_1504147 < baseStart_1504147 := by decide
  rcases family_descends (prefixWord ++ tailWord_1504147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1504239 : List Nat := [1, 1, 2, 1, 4, 3, 1, 2, 2, 5]
def baseStart_1504239 : Nat := 118140960795 + 1504239 * 2 ^ 59
def prefixEnd_1504239 : Nat := 4983230072969 + 3 ^ 40 * 1504239 * 2
def baseEnd_1504239 : Nat := 514931750825763594463091

theorem tailTrace_1504239 : CollatzResearch.WordTrace tailWord_1504239 prefixEnd_1504239 514931750825763594463091 := by
  unfold tailWord_1504239
  simp only [CollatzResearch.WordTrace]
  refine ⟨54864103597406481413171771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36576069064937654275447847 54864103597406481413171771)
  ·
    refine ⟨82296155396109722119757657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54864103597406481413171771 82296155396109722119757657)
    ·
      refine ⟨61722116547082291589818243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82296155396109722119757657 61722116547082291589818243)
      ·
        refine ⟨92583174820623437384727365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61722116547082291589818243 92583174820623437384727365)
        ·
          refine ⟨17359345278866894509636381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92583174820623437384727365 17359345278866894509636381)
          ·
            refine ⟨6509754479575085441113643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17359345278866894509636381 6509754479575085441113643)
            ·
              refine ⟨9764631719362628161670465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6509754479575085441113643 9764631719362628161670465)
              ·
                refine ⟨7323473789521971121252849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9764631719362628161670465 7323473789521971121252849)
                ·
                  refine ⟨5492605342141478340939637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7323473789521971121252849 5492605342141478340939637)
                  ·
                    refine ⟨514931750825763594463091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5492605342141478340939637 514931750825763594463091)
                    ·
                      rfl

theorem cell22_1504239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 2, 2, 5].length) (baseStart_1504239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1504239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1504239 prefixEnd_1504239 := by exact prefixLift 1504239
  have htrace : WordTrace (prefixWord ++ tailWord_1504239) baseStart_1504239 baseEnd_1504239 := by
    simpa [prefixWord, tailWord_1504239, baseEnd_1504239] using wordTrace_append hprefix tailTrace_1504239
  have hstable : (prefixWord ++ tailWord_1504239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1504239).length < 2 ^ (prefixWord ++ tailWord_1504239).sum := by decide
  have hdescent : baseEnd_1504239 < baseStart_1504239 := by decide
  rcases family_descends (prefixWord ++ tailWord_1504239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1504241 : List Nat := [1, 2, 2, 2, 4, 1, 3, 2, 5]
def baseStart_1504241 : Nat := 118140960795 + 1504241 * 2 ^ 59
def prefixEnd_1504241 : Nat := 4983230072969 + 3 ^ 40 * 1504241 * 2
def baseEnd_1504241 : Nat := 171644145155545418637695

theorem tailTrace_1504241 : CollatzResearch.WordTrace tailWord_1504241 prefixEnd_1504241 171644145155545418637695 := by
  unfold tailWord_1504241
  simp only [CollatzResearch.WordTrace]
  refine ⟨54864176543399235754744577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36576117695599490503163051 54864176543399235754744577)
  ·
    refine ⟨41148132407549426816058433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54864176543399235754744577 41148132407549426816058433)
    ·
      refine ⟨30861099305662070112043825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41148132407549426816058433 30861099305662070112043825)
      ·
        refine ⟨23145824479246552584032869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30861099305662070112043825 23145824479246552584032869)
        ·
          refine ⟨4339842089858728609506163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23145824479246552584032869 4339842089858728609506163)
          ·
            refine ⟨6509763134788092914259245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4339842089858728609506163 6509763134788092914259245)
            ·
              refine ⟨2441161175545534842847217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6509763134788092914259245 2441161175545534842847217)
              ·
                refine ⟨1830870881659151132135413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2441161175545534842847217 1830870881659151132135413)
                ·
                  refine ⟨171644145155545418637695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1830870881659151132135413 171644145155545418637695)
                  ·
                    rfl

theorem cell22_1504241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 3, 2, 5].length) (baseStart_1504241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1504241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1504241 prefixEnd_1504241 := by exact prefixLift 1504241
  have htrace : WordTrace (prefixWord ++ tailWord_1504241) baseStart_1504241 baseEnd_1504241 := by
    simpa [prefixWord, tailWord_1504241, baseEnd_1504241] using wordTrace_append hprefix tailTrace_1504241
  have hstable : (prefixWord ++ tailWord_1504241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1504241).length < 2 ^ (prefixWord ++ tailWord_1504241).sum := by decide
  have hdescent : baseEnd_1504241 < baseStart_1504241 := by decide
  rcases family_descends (prefixWord ++ tailWord_1504241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1504314 : List Nat := [3, 1, 1, 1, 3, 1, 3, 9]
def baseStart_1504314 : Nat := 118140960795 + 1504314 * 2 ^ 59
def prefixEnd_1504314 : Nat := 4983230072969 + 3 ^ 40 * 1504314 * 2
def baseEnd_1504314 : Nat := 57217491650943155426429

theorem tailTrace_1504314 : CollatzResearch.WordTrace tailWord_1504314 prefixEnd_1504314 57217491650943155426429 := by
  unfold tailWord_1504314
  simp only [CollatzResearch.WordTrace]
  refine ⟨13716709768033692305537999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36577892714756512814767997 13716709768033692305537999)
  ·
    refine ⟨20575064652050538458306999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13716709768033692305537999 20575064652050538458306999)
    ·
      refine ⟨30862596978075807687460499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20575064652050538458306999 30862596978075807687460499)
      ·
        refine ⟨46293895467113711531190749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30862596978075807687460499 46293895467113711531190749)
        ·
          refine ⟨17360210800167641824196531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46293895467113711531190749 17360210800167641824196531)
          ·
            refine ⟨26040316200251462736294797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17360210800167641824196531 26040316200251462736294797)
            ·
              refine ⟨9765118575094298526110549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26040316200251462736294797 9765118575094298526110549)
              ·
                refine ⟨57217491650943155426429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9765118575094298526110549 57217491650943155426429)
                ·
                  rfl

theorem cell22_1504314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 9].length) (baseStart_1504314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1504314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1504314 prefixEnd_1504314 := by exact prefixLift 1504314
  have htrace : WordTrace (prefixWord ++ tailWord_1504314) baseStart_1504314 baseEnd_1504314 := by
    simpa [prefixWord, tailWord_1504314, baseEnd_1504314] using wordTrace_append hprefix tailTrace_1504314
  have hstable : (prefixWord ++ tailWord_1504314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1504314).length < 2 ^ (prefixWord ++ tailWord_1504314).sum := by decide
  have hdescent : baseEnd_1504314 < baseStart_1504314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1504314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1504333 : List Nat := [1, 6, 1, 1, 1, 2, 1, 3, 2, 4]
def baseStart_1504333 : Nat := 118140960795 + 1504333 * 2 ^ 59
def prefixEnd_1504333 : Nat := 4983230072969 + 3 ^ 40 * 1504333 * 2
def baseEnd_1504333 : Nat := 514963928946778682612803

theorem tailTrace_1504333 : CollatzResearch.WordTrace tailWord_1504333 prefixEnd_1504333 514963928946778682612803 := by
  unfold tailWord_1504333
  simp only [CollatzResearch.WordTrace]
  refine ⟨54867532059065935467093653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36578354706043956978062435 54867532059065935467093653)
  ·
    refine ⟨2571915565268715725020015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 54867532059065935467093653 2571915565268715725020015)
    ·
      refine ⟨3857873347903073587530023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2571915565268715725020015 3857873347903073587530023)
      ·
        refine ⟨5786810021854610381295035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3857873347903073587530023 5786810021854610381295035)
        ·
          refine ⟨8680215032781915571942553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5786810021854610381295035 8680215032781915571942553)
          ·
            refine ⟨6510161274586436678956915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8680215032781915571942553 6510161274586436678956915)
            ·
              refine ⟨9765241911879655018435373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6510161274586436678956915 9765241911879655018435373)
              ·
                refine ⟨3661965716954870631913265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9765241911879655018435373 3661965716954870631913265)
                ·
                  refine ⟨2746474287716152973934949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3661965716954870631913265 2746474287716152973934949)
                  ·
                    refine ⟨514963928946778682612803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2746474287716152973934949 514963928946778682612803)
                    ·
                      rfl

theorem cell22_1504333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_1504333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1504333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1504333 prefixEnd_1504333 := by exact prefixLift 1504333
  have htrace : WordTrace (prefixWord ++ tailWord_1504333) baseStart_1504333 baseEnd_1504333 := by
    simpa [prefixWord, tailWord_1504333, baseEnd_1504333] using wordTrace_append hprefix tailTrace_1504333
  have hstable : (prefixWord ++ tailWord_1504333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1504333).length < 2 ^ (prefixWord ++ tailWord_1504333).sum := by decide
  have hdescent : baseEnd_1504333 < baseStart_1504333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1504333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1504346 : List Nat := [3, 1, 1, 2, 1, 1, 2, 1, 7, 3]
def baseStart_1504346 : Nat := 118140960795 + 1504346 * 2 ^ 59
def prefixEnd_1504346 : Nat := 4983230072969 + 3 ^ 40 * 1504346 * 2
def baseEnd_1504346 : Nat := 514968379112450982037763

theorem tailTrace_1504346 : CollatzResearch.WordTrace tailWord_1504346 prefixEnd_1504346 514968379112450982037763 := by
  unfold tailWord_1504346
  simp only [CollatzResearch.WordTrace]
  refine ⟨13717001552004709671829223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36578670805345892458211261 13717001552004709671829223)
  ·
    refine ⟨20575502328007064507743835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13717001552004709671829223 20575502328007064507743835)
    ·
      refine ⟨30863253492010596761615753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20575502328007064507743835 30863253492010596761615753)
      ·
        refine ⟨23147440119007947571211815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30863253492010596761615753 23147440119007947571211815)
        ·
          refine ⟨34721160178511921356817723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23147440119007947571211815 34721160178511921356817723)
          ·
            refine ⟨52081740267767882035226585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34721160178511921356817723 52081740267767882035226585)
            ·
              refine ⟨39061305200825911526419939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52081740267767882035226585 39061305200825911526419939)
              ·
                refine ⟨58591957801238867289629909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39061305200825911526419939 58591957801238867289629909)
                ·
                  refine ⟨1373249010966535952100701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 58591957801238867289629909 1373249010966535952100701)
                  ·
                    refine ⟨514968379112450982037763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1373249010966535952100701 514968379112450982037763)
                    ·
                      rfl

theorem cell22_1504346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 7, 3].length) (baseStart_1504346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1504346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1504346 prefixEnd_1504346 := by exact prefixLift 1504346
  have htrace : WordTrace (prefixWord ++ tailWord_1504346) baseStart_1504346 baseEnd_1504346 := by
    simpa [prefixWord, tailWord_1504346, baseEnd_1504346] using wordTrace_append hprefix tailTrace_1504346
  have hstable : (prefixWord ++ tailWord_1504346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1504346).length < 2 ^ (prefixWord ++ tailWord_1504346).sum := by decide
  have hdescent : baseEnd_1504346 < baseStart_1504346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1504346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1504376 : List Nat := [2, 1, 2, 1, 1, 1, 6, 3, 5]
def baseStart_1504376 : Nat := 118140960795 + 1504376 * 2 ^ 59
def prefixEnd_1504376 : Nat := 4983230072969 + 3 ^ 40 * 1504376 * 2
def baseEnd_1504376 : Nat := 171659549575180301262557

theorem tailTrace_1504376 : CollatzResearch.WordTrace tailWord_1504376 prefixEnd_1504376 171659549575180301262557 := by
  unfold tailWord_1504376
  simp only [CollatzResearch.WordTrace]
  refine ⟨27434550198955076905454491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36579400265273435873939321 27434550198955076905454491)
  ·
    refine ⟨41151825298432615358181737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27434550198955076905454491 41151825298432615358181737)
    ·
      refine ⟨30863868973824461518636303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41151825298432615358181737 30863868973824461518636303)
      ·
        refine ⟨46295803460736692277954455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30863868973824461518636303 46295803460736692277954455)
        ·
          refine ⟨69443705191105038416931683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46295803460736692277954455 69443705191105038416931683)
          ·
            refine ⟨104165557786657557625397525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69443705191105038416931683 104165557786657557625397525)
            ·
              refine ⟨4882760521249573013690509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 104165557786657557625397525 4882760521249573013690509)
              ·
                refine ⟨1831035195468589880133941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4882760521249573013690509 1831035195468589880133941)
                ·
                  refine ⟨171659549575180301262557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1831035195468589880133941 171659549575180301262557)
                  ·
                    rfl

theorem cell22_1504376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 3, 5].length) (baseStart_1504376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1504376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1504376 prefixEnd_1504376 := by exact prefixLift 1504376
  have htrace : WordTrace (prefixWord ++ tailWord_1504376) baseStart_1504376 baseEnd_1504376 := by
    simpa [prefixWord, tailWord_1504376, baseEnd_1504376] using wordTrace_append hprefix tailTrace_1504376
  have hstable : (prefixWord ++ tailWord_1504376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1504376).length < 2 ^ (prefixWord ++ tailWord_1504376).sum := by decide
  have hdescent : baseEnd_1504376 < baseStart_1504376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1504376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1504410 : List Nat := [3, 1, 1, 5, 1, 3, 1, 2, 5]
def baseStart_1504410 : Nat := 118140960795 + 1504410 * 2 ^ 59
def prefixEnd_1504410 : Nat := 4983230072969 + 3 ^ 40 * 1504410 * 2
def baseEnd_1504410 : Nat := 171663429206792049479189

theorem tailTrace_1504410 : CollatzResearch.WordTrace tailWord_1504410 prefixEnd_1504410 171663429206792049479189 := by
  unfold tailWord_1504410
  simp only [CollatzResearch.WordTrace]
  refine ⟨13717585119946744404411671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36580226986524651745097789 13717585119946744404411671)
  ·
    refine ⟨20576377679920116606617507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13717585119946744404411671 20576377679920116606617507)
    ·
      refine ⟨30864566519880174909926261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20576377679920116606617507 30864566519880174909926261)
      ·
        refine ⟨2893553111238766397805587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30864566519880174909926261 2893553111238766397805587)
        ·
          refine ⟨4340329666858149596708381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2893553111238766397805587 4340329666858149596708381)
          ·
            refine ⟨1627623625071806098765643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4340329666858149596708381 1627623625071806098765643)
            ·
              refine ⟨2441435437607709148148465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1627623625071806098765643 2441435437607709148148465)
              ·
                refine ⟨1831076578205781861111349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2441435437607709148148465 1831076578205781861111349)
                ·
                  refine ⟨171663429206792049479189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1831076578205781861111349 171663429206792049479189)
                  ·
                    rfl

theorem cell22_1504410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 1, 2, 5].length) (baseStart_1504410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1504410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1504410 prefixEnd_1504410 := by exact prefixLift 1504410
  have htrace : WordTrace (prefixWord ++ tailWord_1504410) baseStart_1504410 baseEnd_1504410 := by
    simpa [prefixWord, tailWord_1504410, baseEnd_1504410] using wordTrace_append hprefix tailTrace_1504410
  have hstable : (prefixWord ++ tailWord_1504410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1504410).length < 2 ^ (prefixWord ++ tailWord_1504410).sum := by decide
  have hdescent : baseEnd_1504410 < baseStart_1504410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1504410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1504421 : List Nat := [1, 3, 1, 2, 1, 4, 1, 3, 6]
def baseStart_1504421 : Nat := 118140960795 + 1504421 * 2 ^ 59
def prefixEnd_1504421 : Nat := 4983230072969 + 3 ^ 40 * 1504421 * 2
def baseEnd_1504421 : Nat := 171664684381725262137511

theorem tailTrace_1504421 : CollatzResearch.WordTrace tailWord_1504421 prefixEnd_1504421 171664684381725262137511 := by
  unfold tailWord_1504421
  simp only [CollatzResearch.WordTrace]
  refine ⟨54870741682747126496297117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36580494455164750997531411 54870741682747126496297117)
  ·
    refine ⟨20576528131030172436111419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54870741682747126496297117 20576528131030172436111419)
    ·
      refine ⟨30864792196545258654167129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20576528131030172436111419 30864792196545258654167129)
      ·
        refine ⟨23148594147408943990625347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30864792196545258654167129 23148594147408943990625347)
        ·
          refine ⟨34722891221113415985938021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23148594147408943990625347 34722891221113415985938021)
          ·
            refine ⟨6510542103958765497363379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34722891221113415985938021 6510542103958765497363379)
            ·
              refine ⟨9765813155938148246045069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6510542103958765497363379 9765813155938148246045069)
              ·
                refine ⟨3662179933476805592266901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9765813155938148246045069 3662179933476805592266901)
                ·
                  refine ⟨171664684381725262137511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3662179933476805592266901 171664684381725262137511)
                  ·
                    rfl

theorem cell22_1504421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 3, 6].length) (baseStart_1504421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1504421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1504421 prefixEnd_1504421 := by exact prefixLift 1504421
  have htrace : WordTrace (prefixWord ++ tailWord_1504421) baseStart_1504421 baseEnd_1504421 := by
    simpa [prefixWord, tailWord_1504421, baseEnd_1504421] using wordTrace_append hprefix tailTrace_1504421
  have hstable : (prefixWord ++ tailWord_1504421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1504421).length < 2 ^ (prefixWord ++ tailWord_1504421).sum := by decide
  have hdescent : baseEnd_1504421 < baseStart_1504421 := by decide
  rcases family_descends (prefixWord ++ tailWord_1504421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1504472 : List Nat := [2, 1, 2, 2, 5, 1, 3, 2, 4]
def baseStart_1504472 : Nat := 118140960795 + 1504472 * 2 ^ 59
def prefixEnd_1504472 : Nat := 4983230072969 + 3 ^ 40 * 1504472 * 2
def baseEnd_1504472 : Nat := 171670503829142884462459

theorem tailTrace_1504472 : CollatzResearch.WordTrace tailWord_1504472 prefixEnd_1504472 171670503829142884462459 := by
  unfold tailWord_1504472
  simp only [CollatzResearch.WordTrace]
  refine ⟨27436300902781181103201835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36581734537041574804269113 27436300902781181103201835)
  ·
    refine ⟨41154451354171771654802753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27436300902781181103201835 41154451354171771654802753)
    ·
      refine ⟨30865838515628828741102065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41154451354171771654802753 30865838515628828741102065)
      ·
        refine ⟨23149378886721621555826549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30865838515628828741102065 23149378886721621555826549)
        ·
          refine ⟨2170254270630152020858739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23149378886721621555826549 2170254270630152020858739)
          ·
            refine ⟨3255381405945228031288109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2170254270630152020858739 3255381405945228031288109)
            ·
              refine ⟨1220768027229460511733041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3255381405945228031288109 1220768027229460511733041)
              ·
                refine ⟨915576020422095383799781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1220768027229460511733041 915576020422095383799781)
                ·
                  refine ⟨171670503829142884462459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 915576020422095383799781 171670503829142884462459)
                  ·
                    rfl

theorem cell22_1504472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 3, 2, 4].length) (baseStart_1504472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1504472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1504472 prefixEnd_1504472 := by exact prefixLift 1504472
  have htrace : WordTrace (prefixWord ++ tailWord_1504472) baseStart_1504472 baseEnd_1504472 := by
    simpa [prefixWord, tailWord_1504472, baseEnd_1504472] using wordTrace_append hprefix tailTrace_1504472
  have hstable : (prefixWord ++ tailWord_1504472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1504472).length < 2 ^ (prefixWord ++ tailWord_1504472).sum := by decide
  have hdescent : baseEnd_1504472 < baseStart_1504472 := by decide
  rcases family_descends (prefixWord ++ tailWord_1504472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1504487 : List Nat := [1, 1, 5, 3, 2, 1, 1, 3, 2, 3]
def baseStart_1504487 : Nat := 118140960795 + 1504487 * 2 ^ 59
def prefixEnd_1504487 : Nat := 4983230072969 + 3 ^ 40 * 1504487 * 2
def baseEnd_1504487 : Nat := 515016646293973614262331

theorem tailTrace_1504487 : CollatzResearch.WordTrace tailWord_1504487 prefixEnd_1504487 515016646293973614262331 := by
  unfold tailWord_1504487
  simp only [CollatzResearch.WordTrace]
  refine ⟨54873148900508019768199715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36582099267005346512133143 54873148900508019768199715)
  ·
    refine ⟨82309723350762029652299573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54873148900508019768199715 82309723350762029652299573)
    ·
      refine ⟨7716536564133940279903085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 82309723350762029652299573 7716536564133940279903085)
      ·
        refine ⟨2893701211550227604963657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7716536564133940279903085 2893701211550227604963657)
        ·
          refine ⟨2170275908662670703722743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2893701211550227604963657 2170275908662670703722743)
          ·
            refine ⟨3255413862994006055584115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2170275908662670703722743 3255413862994006055584115)
            ·
              refine ⟨4883120794491009083376173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3255413862994006055584115 4883120794491009083376173)
              ·
                refine ⟨1831170297934128406266065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4883120794491009083376173 1831170297934128406266065)
                ·
                  refine ⟨1373377723450596304699549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1831170297934128406266065 1373377723450596304699549)
                  ·
                    refine ⟨515016646293973614262331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1373377723450596304699549 515016646293973614262331)
                    ·
                      rfl

theorem cell22_1504487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 3, 2, 3].length) (baseStart_1504487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1504487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1504487 prefixEnd_1504487 := by exact prefixLift 1504487
  have htrace : WordTrace (prefixWord ++ tailWord_1504487) baseStart_1504487 baseEnd_1504487 := by
    simpa [prefixWord, tailWord_1504487, baseEnd_1504487] using wordTrace_append hprefix tailTrace_1504487
  have hstable : (prefixWord ++ tailWord_1504487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1504487).length < 2 ^ (prefixWord ++ tailWord_1504487).sum := by decide
  have hdescent : baseEnd_1504487 < baseStart_1504487 := by decide
  rcases family_descends (prefixWord ++ tailWord_1504487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1504571 : List Nat := [1, 1, 1, 1, 1, 2, 1, 1, 4, 9]
def baseStart_1504571 : Nat := 118140960795 + 1504571 * 2 ^ 59
def prefixEnd_1504571 : Nat := 4983230072969 + 3 ^ 40 * 1504571 * 2
def baseEnd_1504571 : Nat := 515045401210625395162073

theorem tailTrace_1504571 : CollatzResearch.WordTrace tailWord_1504571 prefixEnd_1504571 515045401210625395162073 := by
  unfold tailWord_1504571
  simp only [CollatzResearch.WordTrace]
  refine ⟨54876212632203702114257567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36584141754802468076171711 54876212632203702114257567)
  ·
    refine ⟨82314318948305553171386351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54876212632203702114257567 82314318948305553171386351)
    ·
      refine ⟨123471478422458329757079527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82314318948305553171386351 123471478422458329757079527)
      ·
        refine ⟨185207217633687494635619291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123471478422458329757079527 185207217633687494635619291)
        ·
          refine ⟨277810826450531241953428937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185207217633687494635619291 277810826450531241953428937)
          ·
            refine ⟨208358119837898431465071703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 277810826450531241953428937 208358119837898431465071703)
            ·
              refine ⟨312537179756847647197607555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 208358119837898431465071703 312537179756847647197607555)
              ·
                refine ⟨468805769635271470796411333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 312537179756847647197607555 468805769635271470796411333)
                ·
                  refine ⟨87901081806613400774327125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 468805769635271470796411333 87901081806613400774327125)
                  ·
                    refine ⟨515045401210625395162073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 87901081806613400774327125 515045401210625395162073)
                    ·
                      rfl

theorem cell22_1504571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 9].length) (baseStart_1504571 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1504571 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1504571 prefixEnd_1504571 := by exact prefixLift 1504571
  have htrace : WordTrace (prefixWord ++ tailWord_1504571) baseStart_1504571 baseEnd_1504571 := by
    simpa [prefixWord, tailWord_1504571, baseEnd_1504571] using wordTrace_append hprefix tailTrace_1504571
  have hstable : (prefixWord ++ tailWord_1504571).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1504571).length < 2 ^ (prefixWord ++ tailWord_1504571).sum := by decide
  have hdescent : baseEnd_1504571 < baseStart_1504571 := by decide
  rcases family_descends (prefixWord ++ tailWord_1504571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1504575 : List Nat := [1, 1, 2, 2, 4, 3, 1, 3, 1, 4]
def baseStart_1504575 : Nat := 118140960795 + 1504575 * 2 ^ 59
def prefixEnd_1504575 : Nat := 4983230072969 + 3 ^ 40 * 1504575 * 2
def baseEnd_1504575 : Nat := 515046770492370718062061

theorem tailTrace_1504575 : CollatzResearch.WordTrace tailWord_1504575 prefixEnd_1504575 515046770492370718062061 := by
  unfold tailWord_1504575
  simp only [CollatzResearch.WordTrace]
  refine ⟨54876358524189210797403179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36584239016126140531602119 54876358524189210797403179)
  ·
    refine ⟨82314537786283816196104769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54876358524189210797403179 82314537786283816196104769)
    ·
      refine ⟨61735903339712862147078577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82314537786283816196104769 61735903339712862147078577)
      ·
        refine ⟨46301927504784646610308933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61735903339712862147078577 46301927504784646610308933)
        ·
          refine ⟨8681611407147121239432925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46301927504784646610308933 8681611407147121239432925)
          ·
            refine ⟨3255604277680170464787347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8681611407147121239432925 3255604277680170464787347)
            ·
              refine ⟨4883406416520255697181021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3255604277680170464787347 4883406416520255697181021)
              ·
                refine ⟨1831277406195095886442883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4883406416520255697181021 1831277406195095886442883)
                ·
                  refine ⟨2746916109292643829664325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1831277406195095886442883 2746916109292643829664325)
                  ·
                    refine ⟨515046770492370718062061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2746916109292643829664325 515046770492370718062061)
                    ·
                      rfl

theorem cell22_1504575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 3, 1, 4].length) (baseStart_1504575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1504575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1504575 prefixEnd_1504575 := by exact prefixLift 1504575
  have htrace : WordTrace (prefixWord ++ tailWord_1504575) baseStart_1504575 baseEnd_1504575 := by
    simpa [prefixWord, tailWord_1504575, baseEnd_1504575] using wordTrace_append hprefix tailTrace_1504575
  have hstable : (prefixWord ++ tailWord_1504575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1504575).length < 2 ^ (prefixWord ++ tailWord_1504575).sum := by decide
  have hdescent : baseEnd_1504575 < baseStart_1504575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1504575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1504590 : List Nat := [4, 1, 1, 1, 1, 1, 3, 6, 4]
def baseStart_1504590 : Nat := 118140960795 + 1504590 * 2 ^ 59
def prefixEnd_1504590 : Nat := 4983230072969 + 3 ^ 40 * 1504590 * 2
def baseEnd_1504590 : Nat := 171683968432971892979005

theorem tailTrace_1504590 : CollatzResearch.WordTrace tailWord_1504590 prefixEnd_1504590 171683968432971892979005 := by
  unfold tailWord_1504590
  simp only [CollatzResearch.WordTrace]
  refine ⟨6859613202391858544899903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36584603746089912239466149 6859613202391858544899903)
  ·
    refine ⟨10289419803587787817349855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6859613202391858544899903 10289419803587787817349855)
    ·
      refine ⟨15434129705381681726024783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10289419803587787817349855 15434129705381681726024783)
      ·
        refine ⟨23151194558072522589037175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15434129705381681726024783 23151194558072522589037175)
        ·
          refine ⟨34726791837108783883555763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23151194558072522589037175 34726791837108783883555763)
          ·
            refine ⟨52090187755663175825333645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34726791837108783883555763 52090187755663175825333645)
            ·
              refine ⟨19533820408373690934500117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52090187755663175825333645 19533820408373690934500117)
              ·
                refine ⟨915647831642516762554693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 19533820408373690934500117 915647831642516762554693)
                ·
                  refine ⟨171683968432971892979005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 915647831642516762554693 171683968432971892979005)
                  ·
                    rfl

theorem cell22_1504590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 6, 4].length) (baseStart_1504590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1504590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1504590 prefixEnd_1504590 := by exact prefixLift 1504590
  have htrace : WordTrace (prefixWord ++ tailWord_1504590) baseStart_1504590 baseEnd_1504590 := by
    simpa [prefixWord, tailWord_1504590, baseEnd_1504590] using wordTrace_append hprefix tailTrace_1504590
  have hstable : (prefixWord ++ tailWord_1504590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1504590).length < 2 ^ (prefixWord ++ tailWord_1504590).sum := by decide
  have hdescent : baseEnd_1504590 < baseStart_1504590 := by decide
  rcases family_descends (prefixWord ++ tailWord_1504590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1504697 : List Nat := [1, 2, 1, 4, 4, 1, 2, 2, 5]
def baseStart_1504697 : Nat := 118140960795 + 1504697 * 2 ^ 59
def prefixEnd_1504697 : Nat := 4983230072969 + 3 ^ 40 * 1504697 * 2
def baseEnd_1504697 : Nat := 171696177861867688837229

theorem tailTrace_1504697 : CollatzResearch.WordTrace tailWord_1504697 prefixEnd_1504697 171696177861867688837229 := by
  unfold tailWord_1504697
  simp only [CollatzResearch.WordTrace]
  refine ⟨54880808229747225633344345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36587205486498150422229563 54880808229747225633344345)
  ·
    refine ⟨41160606172310419225008259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54880808229747225633344345 41160606172310419225008259)
    ·
      refine ⟨61740909258465628837512389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41160606172310419225008259 61740909258465628837512389)
      ·
        refine ⟨11576420485962305407033573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61740909258465628837512389 11576420485962305407033573)
        ·
          refine ⟨2170578841117932263818795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11576420485962305407033573 2170578841117932263818795)
          ·
            refine ⟨3255868261676898395728193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2170578841117932263818795 3255868261676898395728193)
            ·
              refine ⟨2441901196257673796796145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3255868261676898395728193 2441901196257673796796145)
              ·
                refine ⟨1831425897193255347597109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2441901196257673796796145 1831425897193255347597109)
                ·
                  refine ⟨171696177861867688837229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1831425897193255347597109 171696177861867688837229)
                  ·
                    rfl

theorem cell22_1504697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 2, 2, 5].length) (baseStart_1504697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1504697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1504697 prefixEnd_1504697 := by exact prefixLift 1504697
  have htrace : WordTrace (prefixWord ++ tailWord_1504697) baseStart_1504697 baseEnd_1504697 := by
    simpa [prefixWord, tailWord_1504697, baseEnd_1504697] using wordTrace_append hprefix tailTrace_1504697
  have hstable : (prefixWord ++ tailWord_1504697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1504697).length < 2 ^ (prefixWord ++ tailWord_1504697).sum := by decide
  have hdescent : baseEnd_1504697 < baseStart_1504697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1504697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1504725 : List Nat := [1, 3, 2, 3, 1, 1, 3, 2, 6]
def baseStart_1504725 : Nat := 118140960795 + 1504725 * 2 ^ 59
def prefixEnd_1504725 : Nat := 4983230072969 + 3 ^ 40 * 1504725 * 2
def baseEnd_1504725 : Nat := 171699372852606775603867

theorem tailTrace_1504725 : CollatzResearch.WordTrace tailWord_1504725 prefixEnd_1504725 171699372852606775603867 := by
  unfold tailWord_1504725
  simp only [CollatzResearch.WordTrace]
  refine ⟨54881829473645786415363629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36587886315763857610242419 54881829473645786415363629)
  ·
    refine ⟨20580686052617169905761361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54881829473645786415363629 20580686052617169905761361)
    ·
      refine ⟨15435514539462877429321021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20580686052617169905761361 15435514539462877429321021)
      ·
        refine ⟨5788317952298579035995383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15435514539462877429321021 5788317952298579035995383)
        ·
          refine ⟨8682476928447868553993075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5788317952298579035995383 8682476928447868553993075)
          ·
            refine ⟨13023715392671802830989613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8682476928447868553993075 13023715392671802830989613)
            ·
              refine ⟨4883893272251926061621105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13023715392671802830989613 4883893272251926061621105)
              ·
                refine ⟨3662919954188944546215829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4883893272251926061621105 3662919954188944546215829)
                ·
                  refine ⟨171699372852606775603867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3662919954188944546215829 171699372852606775603867)
                  ·
                    rfl

theorem cell22_1504725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 2, 6].length) (baseStart_1504725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1504725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1504725 prefixEnd_1504725 := by exact prefixLift 1504725
  have htrace : WordTrace (prefixWord ++ tailWord_1504725) baseStart_1504725 baseEnd_1504725 := by
    simpa [prefixWord, tailWord_1504725, baseEnd_1504725] using wordTrace_append hprefix tailTrace_1504725
  have hstable : (prefixWord ++ tailWord_1504725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1504725).length < 2 ^ (prefixWord ++ tailWord_1504725).sum := by decide
  have hdescent : baseEnd_1504725 < baseStart_1504725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1504725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1504787 : List Nat := [1, 1, 1, 2, 1, 8, 2, 6]
def baseStart_1504787 : Nat := 118140960795 + 1504787 * 2 ^ 59
def prefixEnd_1504787 : Nat := 4983230072969 + 3 ^ 40 * 1504787 * 2
def baseEnd_1504787 : Nat := 57235482491652536862379

theorem tailTrace_1504787 : CollatzResearch.WordTrace tailWord_1504787 prefixEnd_1504787 57235482491652536862379 := by
  unfold tailWord_1504787
  simp only [CollatzResearch.WordTrace]
  refine ⟨54884090799421171004120615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36589393866280780669413743 54884090799421171004120615)
  ·
    refine ⟨82326136199131756506180923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54884090799421171004120615 82326136199131756506180923)
    ·
      refine ⟨123489204298697634759271385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82326136199131756506180923 123489204298697634759271385)
      ·
        refine ⟨92616903224023226069453539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123489204298697634759271385 92616903224023226069453539)
        ·
          refine ⟨138925354836034839104180309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92616903224023226069453539 138925354836034839104180309)
          ·
            refine ⟨1628031501984783270752113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 138925354836034839104180309 1628031501984783270752113)
            ·
              refine ⟨1221023626488587453064085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1628031501984783270752113 1221023626488587453064085)
              ·
                refine ⟨57235482491652536862379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1221023626488587453064085 57235482491652536862379)
                ·
                  rfl

theorem cell22_1504787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 2, 6].length) (baseStart_1504787 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1504787 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1504787 prefixEnd_1504787 := by exact prefixLift 1504787
  have htrace : WordTrace (prefixWord ++ tailWord_1504787) baseStart_1504787 baseEnd_1504787 := by
    simpa [prefixWord, tailWord_1504787, baseEnd_1504787] using wordTrace_append hprefix tailTrace_1504787
  have hstable : (prefixWord ++ tailWord_1504787).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1504787).length < 2 ^ (prefixWord ++ tailWord_1504787).sum := by decide
  have hdescent : baseEnd_1504787 < baseStart_1504787 := by decide
  rcases family_descends (prefixWord ++ tailWord_1504787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1504802 : List Nat := [3, 3, 1, 1, 1, 1, 2, 2, 5, 3]
def baseStart_1504802 : Nat := 118140960795 + 1504802 * 2 ^ 59
def prefixEnd_1504802 : Nat := 4983230072969 + 3 ^ 40 * 1504802 * 2
def baseEnd_1504802 : Nat := 515124477231417792636365

theorem tailTrace_1504802 : CollatzResearch.WordTrace tailWord_1504802 prefixEnd_1504802 515124477231417792636365 := by
  unfold tailWord_1504802
  simp only [CollatzResearch.WordTrace]
  refine ⟨13721159473591707141479165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36589758596244552377277773 13721159473591707141479165)
  ·
    refine ⟨5145434802596890178054687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13721159473591707141479165 5145434802596890178054687)
    ·
      refine ⟨7718152203895335267082031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5145434802596890178054687 7718152203895335267082031)
      ·
        refine ⟨11577228305843002900623047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7718152203895335267082031 11577228305843002900623047)
        ·
          refine ⟨17365842458764504350934571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11577228305843002900623047 17365842458764504350934571)
          ·
            refine ⟨26048763688146756526401857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17365842458764504350934571 26048763688146756526401857)
            ·
              refine ⟨19536572766110067394801393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26048763688146756526401857 19536572766110067394801393)
              ·
                refine ⟨14652429574582550546101045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19536572766110067394801393 14652429574582550546101045)
                ·
                  refine ⟨1373665272617114113696973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14652429574582550546101045 1373665272617114113696973)
                  ·
                    refine ⟨515124477231417792636365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1373665272617114113696973 515124477231417792636365)
                    ·
                      rfl

theorem cell22_1504802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 2, 5, 3].length) (baseStart_1504802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1504802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1504802 prefixEnd_1504802 := by exact prefixLift 1504802
  have htrace : WordTrace (prefixWord ++ tailWord_1504802) baseStart_1504802 baseEnd_1504802 := by
    simpa [prefixWord, tailWord_1504802, baseEnd_1504802] using wordTrace_append hprefix tailTrace_1504802
  have hstable : (prefixWord ++ tailWord_1504802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1504802).length < 2 ^ (prefixWord ++ tailWord_1504802).sum := by decide
  have hdescent : baseEnd_1504802 < baseStart_1504802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1504802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1504819 : List Nat := [1, 1, 1, 2, 4, 5, 1, 1, 3, 3]
def baseStart_1504819 : Nat := 118140960795 + 1504819 * 2 ^ 59
def prefixEnd_1504819 : Nat := 4983230072969 + 3 ^ 40 * 1504819 * 2
def baseEnd_1504819 : Nat := 515130296678835414961313

theorem tailTrace_1504819 : CollatzResearch.WordTrace tailWord_1504819 prefixEnd_1504819 515130296678835414961313 := by
  unfold tailWord_1504819
  simp only [CollatzResearch.WordTrace]
  refine ⟨54885257935305240469285511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36590171956870160312857007 54885257935305240469285511)
  ·
    refine ⟨82327886902957860703928267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54885257935305240469285511 82327886902957860703928267)
    ·
      refine ⟨123491830354436791055892401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82327886902957860703928267 123491830354436791055892401)
      ·
        refine ⟨92618872765827593291919301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123491830354436791055892401 92618872765827593291919301)
        ·
          refine ⟨17366038643592673742234869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92618872765827593291919301 17366038643592673742234869)
          ·
            refine ⟨1628066122836813163334519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17366038643592673742234869 1628066122836813163334519)
            ·
              refine ⟨2442099184255219745001779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1628066122836813163334519 2442099184255219745001779)
              ·
                refine ⟨3663148776382829617502669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2442099184255219745001779 3663148776382829617502669)
                ·
                  refine ⟨1373680791143561106563501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3663148776382829617502669 1373680791143561106563501)
                  ·
                    refine ⟨515130296678835414961313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1373680791143561106563501 515130296678835414961313)
                    ·
                      rfl

theorem cell22_1504819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 1, 1, 3, 3].length) (baseStart_1504819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1504819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1504819 prefixEnd_1504819 := by exact prefixLift 1504819
  have htrace : WordTrace (prefixWord ++ tailWord_1504819) baseStart_1504819 baseEnd_1504819 := by
    simpa [prefixWord, tailWord_1504819, baseEnd_1504819] using wordTrace_append hprefix tailTrace_1504819
  have hstable : (prefixWord ++ tailWord_1504819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1504819).length < 2 ^ (prefixWord ++ tailWord_1504819).sum := by decide
  have hdescent : baseEnd_1504819 < baseStart_1504819 := by decide
  rcases family_descends (prefixWord ++ tailWord_1504819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1504892 : List Nat := [2, 2, 2, 1, 1, 2, 1, 2, 6, 3]
def baseStart_1504892 : Nat := 118140960795 + 1504892 * 2 ^ 59
def prefixEnd_1504892 : Nat := 4983230072969 + 3 ^ 40 * 1504892 * 2
def baseEnd_1504892 : Nat := 515155286070687557886089

theorem tailTrace_1504892 : CollatzResearch.WordTrace tailWord_1504892 prefixEnd_1504892 515155286070687557886089 := by
  unfold tailWord_1504892
  simp only [CollatzResearch.WordTrace]
  refine ⟨27443960232020386968346465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36591946976027182624461953 27443960232020386968346465)
  ·
    refine ⟨20582970174015290226259849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27443960232020386968346465 20582970174015290226259849)
    ·
      refine ⟨15437227630511467669694887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20582970174015290226259849 15437227630511467669694887)
      ·
        refine ⟨23155841445767201504542331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15437227630511467669694887 23155841445767201504542331)
        ·
          refine ⟨34733762168650802256813497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23155841445767201504542331 34733762168650802256813497)
          ·
            refine ⟨26050321626488101692610123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34733762168650802256813497 26050321626488101692610123)
            ·
              refine ⟨39075482439732152538915185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26050321626488101692610123 39075482439732152538915185)
              ·
                refine ⟨29306611829799114404186389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39075482439732152538915185 29306611829799114404186389)
                ·
                  refine ⟨1373747429521833487696237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 29306611829799114404186389 1373747429521833487696237)
                  ·
                    refine ⟨515155286070687557886089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1373747429521833487696237 515155286070687557886089)
                    ·
                      rfl

theorem cell22_1504892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 6, 3].length) (baseStart_1504892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1504892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1504892 prefixEnd_1504892 := by exact prefixLift 1504892
  have htrace : WordTrace (prefixWord ++ tailWord_1504892) baseStart_1504892 baseEnd_1504892 := by
    simpa [prefixWord, tailWord_1504892, baseEnd_1504892] using wordTrace_append hprefix tailTrace_1504892
  have hstable : (prefixWord ++ tailWord_1504892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1504892).length < 2 ^ (prefixWord ++ tailWord_1504892).sum := by decide
  have hdescent : baseEnd_1504892 < baseStart_1504892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1504892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1504905 : List Nat := [1, 2, 1, 1, 4, 1, 2, 10]
def baseStart_1504905 : Nat := 118140960795 + 1504905 * 2 ^ 59
def prefixEnd_1504905 : Nat := 4983230072969 + 3 ^ 40 * 1504905 * 2
def baseEnd_1504905 : Nat := 57239970692928873034561

theorem tailTrace_1504905 : CollatzResearch.WordTrace tailWord_1504905 prefixEnd_1504905 57239970692928873034561 := by
  unfold tailWord_1504905
  simp only [CollatzResearch.WordTrace]
  refine ⟨54888394612993677156916169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36592263075329118104610779 54888394612993677156916169)
  ·
    refine ⟨41166295959745257867687127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54888394612993677156916169 41166295959745257867687127)
    ·
      refine ⟨61749443939617886801530691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41166295959745257867687127 61749443939617886801530691)
      ·
        refine ⟨92624165909426830202296037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61749443939617886801530691 92624165909426830202296037)
        ·
          refine ⟨17367031108017530662930507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92624165909426830202296037 17367031108017530662930507)
          ·
            refine ⟨26050546662026295994395761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17367031108017530662930507 26050546662026295994395761)
            ·
              refine ⟨19537909996519721995796821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26050546662026295994395761 19537909996519721995796821)
              ·
                refine ⟨57239970692928873034561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 19537909996519721995796821 57239970692928873034561)
                ·
                  rfl

theorem cell22_1504905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 10].length) (baseStart_1504905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1504905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1504905 prefixEnd_1504905 := by exact prefixLift 1504905
  have htrace : WordTrace (prefixWord ++ tailWord_1504905) baseStart_1504905 baseEnd_1504905 := by
    simpa [prefixWord, tailWord_1504905, baseEnd_1504905] using wordTrace_append hprefix tailTrace_1504905
  have hstable : (prefixWord ++ tailWord_1504905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1504905).length < 2 ^ (prefixWord ++ tailWord_1504905).sum := by decide
  have hdescent : baseEnd_1504905 < baseStart_1504905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1504905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1504926 : List Nat := [4, 3, 1, 1, 1, 3, 1, 1, 4, 3]
def baseStart_1504926 : Nat := 118140960795 + 1504926 * 2 ^ 59
def prefixEnd_1504926 : Nat := 4983230072969 + 3 ^ 40 * 1504926 * 2
def baseEnd_1504926 : Nat := 515166924965522802535985

theorem tailTrace_1504926 : CollatzResearch.WordTrace tailWord_1504926 prefixEnd_1504926 515166924965522802535985 := by
  unfold tailWord_1504926
  simp only [CollatzResearch.WordTrace]
  refine ⟨6861145068239699717928829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36592773697278398495620421 6861145068239699717928829)
  ·
    refine ⟨2572929400589887394223311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6861145068239699717928829 2572929400589887394223311)
    ·
      refine ⟨3859394100884831091334967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2572929400589887394223311 3859394100884831091334967)
      ·
        refine ⟨5789091151327246637002451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3859394100884831091334967 5789091151327246637002451)
        ·
          refine ⟨8683636726990869955503677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5789091151327246637002451 8683636726990869955503677)
          ·
            refine ⟨3256363772621576233313879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8683636726990869955503677 3256363772621576233313879)
            ·
              refine ⟨4884545658932364349970819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3256363772621576233313879 4884545658932364349970819)
              ·
                refine ⟨7326818488398546524956229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4884545658932364349970819 7326818488398546524956229)
                ·
                  refine ⟨1373778466574727473429293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7326818488398546524956229 1373778466574727473429293)
                  ·
                    refine ⟨515166924965522802535985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1373778466574727473429293 515166924965522802535985)
                    ·
                      rfl

theorem cell22_1504926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 1, 4, 3].length) (baseStart_1504926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1504926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1504926 prefixEnd_1504926 := by exact prefixLift 1504926
  have htrace : WordTrace (prefixWord ++ tailWord_1504926) baseStart_1504926 baseEnd_1504926 := by
    simpa [prefixWord, tailWord_1504926, baseEnd_1504926] using wordTrace_append hprefix tailTrace_1504926
  have hstable : (prefixWord ++ tailWord_1504926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1504926).length < 2 ^ (prefixWord ++ tailWord_1504926).sum := by decide
  have hdescent : baseEnd_1504926 < baseStart_1504926 := by decide
  rcases family_descends (prefixWord ++ tailWord_1504926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1504954 : List Nat := [3, 1, 1, 1, 2, 4, 2, 2, 3, 3]
def baseStart_1504954 : Nat := 118140960795 + 1504954 * 2 ^ 59
def prefixEnd_1504954 : Nat := 4983230072969 + 3 ^ 40 * 1504954 * 2
def baseEnd_1504954 : Nat := 515176509937740062835899

theorem tailTrace_1504954 : CollatzResearch.WordTrace tailWord_1504954 prefixEnd_1504954 515176509937740062835899 := by
  unfold tailWord_1504954
  simp only [CollatzResearch.WordTrace]
  refine ⟨13722545447454039631362479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36593454526544105683633277 13722545447454039631362479)
  ·
    refine ⟨20583818171181059447043719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13722545447454039631362479 20583818171181059447043719)
    ·
      refine ⟨30875727256771589170565579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20583818171181059447043719 30875727256771589170565579)
      ·
        refine ⟨46313590885157383755848369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30875727256771589170565579 46313590885157383755848369)
        ·
          refine ⟨34735193163868037816886277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46313590885157383755848369 34735193163868037816886277)
          ·
            refine ⟨6512848718225257090666177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34735193163868037816886277 6512848718225257090666177)
            ·
              refine ⟨4884636538668942817999633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6512848718225257090666177 4884636538668942817999633)
              ·
                refine ⟨3663477404001707113499725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4884636538668942817999633 3663477404001707113499725)
                ·
                  refine ⟨1373804026500640167562397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3663477404001707113499725 1373804026500640167562397)
                  ·
                    refine ⟨515176509937740062835899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1373804026500640167562397 515176509937740062835899)
                    ·
                      rfl

theorem cell22_1504954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 2, 3, 3].length) (baseStart_1504954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1504954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1504954 prefixEnd_1504954 := by exact prefixLift 1504954
  have htrace : WordTrace (prefixWord ++ tailWord_1504954) baseStart_1504954 baseEnd_1504954 := by
    simpa [prefixWord, tailWord_1504954, baseEnd_1504954] using wordTrace_append hprefix tailTrace_1504954
  have hstable : (prefixWord ++ tailWord_1504954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1504954).length < 2 ^ (prefixWord ++ tailWord_1504954).sum := by decide
  have hdescent : baseEnd_1504954 < baseStart_1504954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1504954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1504962 : List Nat := [3, 5, 1, 2, 1, 2, 1, 3, 4]
def baseStart_1504962 : Nat := 118140960795 + 1504962 * 2 ^ 59
def prefixEnd_1504962 : Nat := 4983230072969 + 3 ^ 40 * 1504962 * 2
def baseEnd_1504962 : Nat := 171726416167076902878625

theorem tailTrace_1504962 : CollatzResearch.WordTrace tailWord_1504962 prefixEnd_1504962 171726416167076902878625 := by
  unfold tailWord_1504962
  simp only [CollatzResearch.WordTrace]
  refine ⟨13722618393446793972935285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36593649049191450594494093 13722618393446793972935285)
  ·
    refine ⟨1286495474385636934962683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13722618393446793972935285 1286495474385636934962683)
    ·
      refine ⟨1929743211578455402444025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1286495474385636934962683 1929743211578455402444025)
      ·
        refine ⟨1447307408683841551833019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1929743211578455402444025 1447307408683841551833019)
        ·
          refine ⟨2170961113025762327749529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1447307408683841551833019 2170961113025762327749529)
          ·
            refine ⟨1628220834769321745812147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2170961113025762327749529 1628220834769321745812147)
            ·
              refine ⟨2442331252153982618718221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1628220834769321745812147 2442331252153982618718221)
              ·
                refine ⟨915874219557743482019333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2442331252153982618718221 915874219557743482019333)
                ·
                  refine ⟨171726416167076902878625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 915874219557743482019333 171726416167076902878625)
                  ·
                    rfl

theorem cell22_1504962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_1504962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1504962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1504962 prefixEnd_1504962 := by exact prefixLift 1504962
  have htrace : WordTrace (prefixWord ++ tailWord_1504962) baseStart_1504962 baseEnd_1504962 := by
    simpa [prefixWord, tailWord_1504962, baseEnd_1504962] using wordTrace_append hprefix tailTrace_1504962
  have hstable : (prefixWord ++ tailWord_1504962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1504962).length < 2 ^ (prefixWord ++ tailWord_1504962).sum := by decide
  have hdescent : baseEnd_1504962 < baseStart_1504962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1504962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1505027 : List Nat := [1, 1, 1, 3, 2, 2, 3, 1, 3, 5]
def baseStart_1505027 : Nat := 118140960795 + 1505027 * 2 ^ 59
def prefixEnd_1505027 : Nat := 4983230072969 + 3 ^ 40 * 1505027 * 2
def baseEnd_1505027 : Nat := 515201499329592205760675

theorem tailTrace_1505027 : CollatzResearch.WordTrace tailWord_1505027 prefixEnd_1505027 515201499329592205760675 := by
  unfold tailWord_1505027
  simp only [CollatzResearch.WordTrace]
  refine ⟨54892844318551691992857335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36595229545701127995238223 54892844318551691992857335)
  ·
    refine ⟨82339266477827537989286003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54892844318551691992857335 82339266477827537989286003)
    ·
      refine ⟨123508899716741306983929005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82339266477827537989286003 123508899716741306983929005)
      ·
        refine ⟨46315837393777990118973377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123508899716741306983929005 46315837393777990118973377)
        ·
          refine ⟨34736878045333492589230033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46315837393777990118973377 34736878045333492589230033)
          ·
            refine ⟨26052658534000119441922525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34736878045333492589230033 26052658534000119441922525)
            ·
              refine ⟨9769746950250044790720947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26052658534000119441922525 9769746950250044790720947)
              ·
                refine ⟨14654620425375067186081421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9769746950250044790720947 14654620425375067186081421)
                ·
                  refine ⟨5495482659515650194780533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14654620425375067186081421 5495482659515650194780533)
                  ·
                    refine ⟨515201499329592205760675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5495482659515650194780533 515201499329592205760675)
                    ·
                      rfl

theorem cell22_1505027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 1, 3, 5].length) (baseStart_1505027 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1505027 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1505027 prefixEnd_1505027 := by exact prefixLift 1505027
  have htrace : WordTrace (prefixWord ++ tailWord_1505027) baseStart_1505027 baseEnd_1505027 := by
    simpa [prefixWord, tailWord_1505027, baseEnd_1505027] using wordTrace_append hprefix tailTrace_1505027
  have hstable : (prefixWord ++ tailWord_1505027).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1505027).length < 2 ^ (prefixWord ++ tailWord_1505027).sum := by decide
  have hdescent : baseEnd_1505027 < baseStart_1505027 := by decide
  rcases family_descends (prefixWord ++ tailWord_1505027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1505061 : List Nat := [1, 3, 1, 2, 3, 2, 2, 3, 2, 3]
def baseStart_1505061 : Nat := 118140960795 + 1505061 * 2 ^ 59
def prefixEnd_1505061 : Nat := 4983230072969 + 3 ^ 40 * 1505061 * 2
def baseEnd_1505061 : Nat := 515213138224427450410571

theorem tailTrace_1505061 : CollatzResearch.WordTrace tailWord_1505061 prefixEnd_1505061 515213138224427450410571 := by
  unfold tailWord_1505061
  simp only [CollatzResearch.WordTrace]
  refine ⟨54894084400428515799595037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36596056266952343866396691 54894084400428515799595037)
  ·
    refine ⟨20585281650160693424848139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54894084400428515799595037 20585281650160693424848139)
    ·
      refine ⟨30877922475241040137272209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20585281650160693424848139 30877922475241040137272209)
      ·
        refine ⟨23158441856430780102954157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30877922475241040137272209 23158441856430780102954157)
        ·
          refine ⟨8684415696161542538607809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23158441856430780102954157 8684415696161542538607809)
          ·
            refine ⟨6513311772121156903955857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8684415696161542538607809 6513311772121156903955857)
            ·
              refine ⟨4884983829090867677966893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6513311772121156903955857 4884983829090867677966893)
              ·
                refine ⟨1831868935909075379237585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4884983829090867677966893 1831868935909075379237585)
                ·
                  refine ⟨1373901701931806534428189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1831868935909075379237585 1373901701931806534428189)
                  ·
                    refine ⟨515213138224427450410571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1373901701931806534428189 515213138224427450410571)
                    ·
                      rfl

theorem cell22_1505061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 3, 2, 3].length) (baseStart_1505061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1505061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1505061 prefixEnd_1505061 := by exact prefixLift 1505061
  have htrace : WordTrace (prefixWord ++ tailWord_1505061) baseStart_1505061 baseEnd_1505061 := by
    simpa [prefixWord, tailWord_1505061, baseEnd_1505061] using wordTrace_append hprefix tailTrace_1505061
  have hstable : (prefixWord ++ tailWord_1505061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1505061).length < 2 ^ (prefixWord ++ tailWord_1505061).sum := by decide
  have hdescent : baseEnd_1505061 < baseStart_1505061 := by decide
  rcases family_descends (prefixWord ++ tailWord_1505061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1505076 : List Nat := [2, 5, 1, 1, 2, 2, 1, 1, 1, 6]
def baseStart_1505076 : Nat := 118140960795 + 1505076 * 2 ^ 59
def prefixEnd_1505076 : Nat := 4983230072969 + 3 ^ 40 * 1505076 * 2
def baseEnd_1505076 : Nat := 515218273030972411285525

theorem tailTrace_1505076 : CollatzResearch.WordTrace tailWord_1505076 prefixEnd_1505076 515218273030972411285525 := by
  unfold tailWord_1505076
  simp only [CollatzResearch.WordTrace]
  refine ⟨27447315747687086680695541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36596420996916115574260721 27447315747687086680695541)
  ·
    refine ⟨2573185851345664376315207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27447315747687086680695541 2573185851345664376315207)
    ·
      refine ⟨3859778777018496564472811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2573185851345664376315207 3859778777018496564472811)
      ·
        refine ⟨5789668165527744846709217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3859778777018496564472811 5789668165527744846709217)
        ·
          refine ⟨4342251124145808635031913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5789668165527744846709217 4342251124145808635031913)
          ·
            refine ⟨3256688343109356476273935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4342251124145808635031913 3256688343109356476273935)
            ·
              refine ⟨4885032514664034714410903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3256688343109356476273935 4885032514664034714410903)
              ·
                refine ⟨7327548771996052071616355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4885032514664034714410903 7327548771996052071616355)
                ·
                  refine ⟨10991323157994078107424533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7327548771996052071616355 10991323157994078107424533)
                  ·
                    refine ⟨515218273030972411285525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10991323157994078107424533 515218273030972411285525)
                    ·
                      rfl

theorem cell22_1505076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_1505076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1505076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1505076 prefixEnd_1505076 := by exact prefixLift 1505076
  have htrace : WordTrace (prefixWord ++ tailWord_1505076) baseStart_1505076 baseEnd_1505076 := by
    simpa [prefixWord, tailWord_1505076, baseEnd_1505076] using wordTrace_append hprefix tailTrace_1505076
  have hstable : (prefixWord ++ tailWord_1505076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1505076).length < 2 ^ (prefixWord ++ tailWord_1505076).sum := by decide
  have hdescent : baseEnd_1505076 < baseStart_1505076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1505076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1505106 : List Nat := [3, 2, 2, 1, 1, 3, 1, 3, 3, 3]
def baseStart_1505106 : Nat := 118140960795 + 1505106 * 2 ^ 59
def prefixEnd_1505106 : Nat := 4983230072969 + 3 ^ 40 * 1505106 * 2
def baseEnd_1505106 : Nat := 515228542644062333035433

theorem tailTrace_1505106 : CollatzResearch.WordTrace tailWord_1505106 prefixEnd_1505106 515228542644062333035433 := by
  unfold tailWord_1505106
  simp only [CollatzResearch.WordTrace]
  refine ⟨13723931421316372121245793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36597150456843658989988781 13723931421316372121245793)
  ·
    refine ⟨10292948565987279090934345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13723931421316372121245793 10292948565987279090934345)
    ·
      refine ⟨7719711424490459318200759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10292948565987279090934345 7719711424490459318200759)
      ·
        refine ⟨11579567136735688977301139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7719711424490459318200759 11579567136735688977301139)
        ·
          refine ⟨17369350705103533465951709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11579567136735688977301139 17369350705103533465951709)
          ·
            refine ⟨6513506514413825049731891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17369350705103533465951709 6513506514413825049731891)
            ·
              refine ⟨9770259771620737574597837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6513506514413825049731891 9770259771620737574597837)
              ·
                refine ⟨3663847414357776590474189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9770259771620737574597837 3663847414357776590474189)
                ·
                  refine ⟨1373942780384166221427821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3663847414357776590474189 1373942780384166221427821)
                  ·
                    refine ⟨515228542644062333035433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1373942780384166221427821 515228542644062333035433)
                    ·
                      rfl

theorem cell22_1505106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 3, 3, 3].length) (baseStart_1505106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1505106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1505106 prefixEnd_1505106 := by exact prefixLift 1505106
  have htrace : WordTrace (prefixWord ++ tailWord_1505106) baseStart_1505106 baseEnd_1505106 := by
    simpa [prefixWord, tailWord_1505106, baseEnd_1505106] using wordTrace_append hprefix tailTrace_1505106
  have hstable : (prefixWord ++ tailWord_1505106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1505106).length < 2 ^ (prefixWord ++ tailWord_1505106).sum := by decide
  have hdescent : baseEnd_1505106 < baseStart_1505106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1505106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1505149 : List Nat := [1, 4, 1, 1, 2, 1, 1, 2, 5, 4]
def baseStart_1505149 : Nat := 118140960795 + 1505149 * 2 ^ 59
def prefixEnd_1505149 : Nat := 4983230072969 + 3 ^ 40 * 1505149 * 2
def baseEnd_1505149 : Nat := 515243262422824554210301

theorem tailTrace_1505149 : CollatzResearch.WordTrace tailWord_1505149 prefixEnd_1505149 515243262422824554210301 := by
  unfold tailWord_1505149
  simp only [CollatzResearch.WordTrace]
  refine ⟨54897294024109706828798501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36598196016073137885865667 54897294024109706828798501)
  ·
    refine ⟨10293242629520570030399719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54897294024109706828798501 10293242629520570030399719)
    ·
      refine ⟨15439863944280855045599579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10293242629520570030399719 15439863944280855045599579)
      ·
        refine ⟨23159795916421282568399369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15439863944280855045599579 23159795916421282568399369)
        ·
          refine ⟨17369846937315961926299527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23159795916421282568399369 17369846937315961926299527)
          ·
            refine ⟨26054770405973942889449291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17369846937315961926299527 26054770405973942889449291)
            ·
              refine ⟨39082155608960914334173937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26054770405973942889449291 39082155608960914334173937)
              ·
                refine ⟨29311616706720685750630453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39082155608960914334173937 29311616706720685750630453)
                ·
                  refine ⟨2747964066255064289121605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29311616706720685750630453 2747964066255064289121605)
                  ·
                    refine ⟨515243262422824554210301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2747964066255064289121605 515243262422824554210301)
                    ·
                      rfl

theorem cell22_1505149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 5, 4].length) (baseStart_1505149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1505149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1505149 prefixEnd_1505149 := by exact prefixLift 1505149
  have htrace : WordTrace (prefixWord ++ tailWord_1505149) baseStart_1505149 baseEnd_1505149 := by
    simpa [prefixWord, tailWord_1505149, baseEnd_1505149] using wordTrace_append hprefix tailTrace_1505149
  have hstable : (prefixWord ++ tailWord_1505149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1505149).length < 2 ^ (prefixWord ++ tailWord_1505149).sum := by decide
  have hdescent : baseEnd_1505149 < baseStart_1505149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1505149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1505170 : List Nat := [3, 2, 3, 2, 1, 3, 2, 1, 5]
def baseStart_1505170 : Nat := 118140960795 + 1505170 * 2 ^ 59
def prefixEnd_1505170 : Nat := 4983230072969 + 3 ^ 40 * 1505170 * 2
def baseEnd_1505170 : Nat := 171750150383995833145079

theorem tailTrace_1505170 : CollatzResearch.WordTrace tailWord_1505170 prefixEnd_1505170 171750150383995833145079 := by
  unfold tailWord_1505170
  simp only [CollatzResearch.WordTrace]
  refine ⟨13724514989258406853828241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36598706638022418276875309 13724514989258406853828241)
  ·
    refine ⟨10293386241943805140371181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13724514989258406853828241 10293386241943805140371181)
    ·
      refine ⟨3860019840728926927639193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10293386241943805140371181 3860019840728926927639193)
      ·
        refine ⟨2895014880546695195729395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3860019840728926927639193 2895014880546695195729395)
        ·
          refine ⟨4342522320820042793594093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2895014880546695195729395 4342522320820042793594093)
          ·
            refine ⟨1628445870307516047597785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4342522320820042793594093 1628445870307516047597785)
            ·
              refine ⟨1221334402730637035698339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1628445870307516047597785 1221334402730637035698339)
              ·
                refine ⟨1832001604095955553547509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1221334402730637035698339 1832001604095955553547509)
                ·
                  refine ⟨171750150383995833145079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1832001604095955553547509 171750150383995833145079)
                  ·
                    rfl

theorem cell22_1505170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 2, 1, 5].length) (baseStart_1505170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1505170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1505170 prefixEnd_1505170 := by exact prefixLift 1505170
  have htrace : WordTrace (prefixWord ++ tailWord_1505170) baseStart_1505170 baseEnd_1505170 := by
    simpa [prefixWord, tailWord_1505170, baseEnd_1505170] using wordTrace_append hprefix tailTrace_1505170
  have hstable : (prefixWord ++ tailWord_1505170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1505170).length < 2 ^ (prefixWord ++ tailWord_1505170).sum := by decide
  have hdescent : baseEnd_1505170 < baseStart_1505170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1505170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1505213 : List Nat := [1, 4, 1, 2, 3, 1, 1, 4, 2, 3]
def baseStart_1505213 : Nat := 118140960795 + 1505213 * 2 ^ 59
def prefixEnd_1505213 : Nat := 4983230072969 + 3 ^ 40 * 1505213 * 2
def baseEnd_1505213 : Nat := 515265170930749720610105

theorem tailTrace_1505213 : CollatzResearch.WordTrace tailWord_1505213 prefixEnd_1505213 515265170930749720610105 := by
  unfold tailWord_1505213
  simp only [CollatzResearch.WordTrace]
  refine ⟨54899628295877845759128293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36599752197251897172752195 54899628295877845759128293)
  ·
    refine ⟨10293680305477096079836555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54899628295877845759128293 10293680305477096079836555)
    ·
      refine ⟨15440520458215644119754833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10293680305477096079836555 15440520458215644119754833)
      ·
        refine ⟨11580390343661733089816125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15440520458215644119754833 11580390343661733089816125)
        ·
          refine ⟨4342646378873149908681047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11580390343661733089816125 4342646378873149908681047)
          ·
            refine ⟨6513969568309724863021571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4342646378873149908681047 6513969568309724863021571)
            ·
              refine ⟨9770954352464587294532357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6513969568309724863021571 9770954352464587294532357)
              ·
                refine ⟨1832053941087110117724817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9770954352464587294532357 1832053941087110117724817)
                ·
                  refine ⟨1374040455815332588293613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1832053941087110117724817 1374040455815332588293613)
                  ·
                    refine ⟨515265170930749720610105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1374040455815332588293613 515265170930749720610105)
                    ·
                      rfl

theorem cell22_1505213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 4, 2, 3].length) (baseStart_1505213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1505213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1505213 prefixEnd_1505213 := by exact prefixLift 1505213
  have htrace : WordTrace (prefixWord ++ tailWord_1505213) baseStart_1505213 baseEnd_1505213 := by
    simpa [prefixWord, tailWord_1505213, baseEnd_1505213] using wordTrace_append hprefix tailTrace_1505213
  have hstable : (prefixWord ++ tailWord_1505213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1505213).length < 2 ^ (prefixWord ++ tailWord_1505213).sum := by decide
  have hdescent : baseEnd_1505213 < baseStart_1505213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1505213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1505239 : List Nat := [1, 1, 3, 2, 1, 1, 3, 2, 2, 6]
def baseStart_1505239 : Nat := 118140960795 + 1505239 * 2 ^ 59
def prefixEnd_1505239 : Nat := 4983230072969 + 3 ^ 40 * 1505239 * 2
def baseEnd_1505239 : Nat := 515274071262094319460025

theorem tailTrace_1505239 : CollatzResearch.WordTrace tailWord_1505239 prefixEnd_1505239 515274071262094319460025 := by
  unfold tailWord_1505239
  simp only [CollatzResearch.WordTrace]
  refine ⟨54900576593783652199574771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36600384395855768133049847 54900576593783652199574771)
  ·
    refine ⟨82350864890675478299362157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54900576593783652199574771 82350864890675478299362157)
    ·
      refine ⟨30881574334003304362260809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82350864890675478299362157 30881574334003304362260809)
      ·
        refine ⟨23161180750502478271695607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30881574334003304362260809 23161180750502478271695607)
        ·
          refine ⟨34741771125753717407543411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23161180750502478271695607 34741771125753717407543411)
          ·
            refine ⟨52112656688630576111315117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34741771125753717407543411 52112656688630576111315117)
            ·
              refine ⟨19542246258236466041743169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52112656688630576111315117 19542246258236466041743169)
              ·
                refine ⟨14656684693677349531307377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19542246258236466041743169 14656684693677349531307377)
                ·
                  refine ⟨10992513520258012148480533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14656684693677349531307377 10992513520258012148480533)
                  ·
                    refine ⟨515274071262094319460025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10992513520258012148480533 515274071262094319460025)
                    ·
                      rfl

theorem cell22_1505239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 2, 2, 6].length) (baseStart_1505239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1505239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1505239 prefixEnd_1505239 := by exact prefixLift 1505239
  have htrace : WordTrace (prefixWord ++ tailWord_1505239) baseStart_1505239 baseEnd_1505239 := by
    simpa [prefixWord, tailWord_1505239, baseEnd_1505239] using wordTrace_append hprefix tailTrace_1505239
  have hstable : (prefixWord ++ tailWord_1505239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1505239).length < 2 ^ (prefixWord ++ tailWord_1505239).sum := by decide
  have hdescent : baseEnd_1505239 < baseStart_1505239 := by decide
  rcases family_descends (prefixWord ++ tailWord_1505239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1505245 : List Nat := [1, 4, 3, 1, 3, 2, 1, 1, 2, 4]
def baseStart_1505245 : Nat := 118140960795 + 1505245 * 2 ^ 59
def prefixEnd_1505245 : Nat := 4983230072969 + 3 ^ 40 * 1505245 * 2
def baseEnd_1505245 : Nat := 515276125184712303810007

theorem tailTrace_1505245 : CollatzResearch.WordTrace tailWord_1505245 prefixEnd_1505245 515276125184712303810007 := by
  unfold tailWord_1505245
  simp only [CollatzResearch.WordTrace]
  refine ⟨54900795431761915224293189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36600530287841276816195459 54900795431761915224293189)
  ·
    refine ⟨10293899143455359104554973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54900795431761915224293189 10293899143455359104554973)
    ·
      refine ⟨3860212178795759664208115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10293899143455359104554973 3860212178795759664208115)
      ·
        refine ⟨5790318268193639496312173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3860212178795759664208115 5790318268193639496312173)
        ·
          refine ⟨2171369350572614811117065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5790318268193639496312173 2171369350572614811117065)
          ·
            refine ⟨1628527012929461108337799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2171369350572614811117065 1628527012929461108337799)
            ·
              refine ⟨2442790519394191662506699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1628527012929461108337799 2442790519394191662506699)
              ·
                refine ⟨3664185779091287493760049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2442790519394191662506699 3664185779091287493760049)
                ·
                  refine ⟨2748139334318465620320037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3664185779091287493760049 2748139334318465620320037)
                  ·
                    refine ⟨515276125184712303810007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2748139334318465620320037 515276125184712303810007)
                    ·
                      rfl

theorem cell22_1505245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 1, 1, 2, 4].length) (baseStart_1505245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1505245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1505245 prefixEnd_1505245 := by exact prefixLift 1505245
  have htrace : WordTrace (prefixWord ++ tailWord_1505245) baseStart_1505245 baseEnd_1505245 := by
    simpa [prefixWord, tailWord_1505245, baseEnd_1505245] using wordTrace_append hprefix tailTrace_1505245
  have hstable : (prefixWord ++ tailWord_1505245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1505245).length < 2 ^ (prefixWord ++ tailWord_1505245).sum := by decide
  have hdescent : baseEnd_1505245 < baseStart_1505245 := by decide
  rcases family_descends (prefixWord ++ tailWord_1505245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1505288 : List Nat := [2, 1, 3, 2, 1, 2, 5, 1, 5]
def baseStart_1505288 : Nat := 118140960795 + 1505288 * 2 ^ 59
def prefixEnd_1505288 : Nat := 4983230072969 + 3 ^ 40 * 1505288 * 2
def baseEnd_1505288 : Nat := 171763614987824841661625

theorem tailTrace_1505288 : CollatzResearch.WordTrace tailWord_1505288 prefixEnd_1505288 171763614987824841661625 := by
  unfold tailWord_1505288
  simp only [CollatzResearch.WordTrace]
  refine ⟨27451181885303066784054259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36601575847070755712072345 27451181885303066784054259)
  ·
    refine ⟨41176772827954600176081389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27451181885303066784054259 41176772827954600176081389)
    ·
      refine ⟨15441289810482975066030521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41176772827954600176081389 15441289810482975066030521)
      ·
        refine ⟨11580967357862231299522891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15441289810482975066030521 11580967357862231299522891)
        ·
          refine ⟨17371451036793346949284337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11580967357862231299522891 17371451036793346949284337)
          ·
            refine ⟨13028588277595010211963253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17371451036793346949284337 13028588277595010211963253)
            ·
              refine ⟨1221430151024532207371555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13028588277595010211963253 1221430151024532207371555)
              ·
                refine ⟨1832145226536798311057333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1221430151024532207371555 1832145226536798311057333)
                ·
                  refine ⟨171763614987824841661625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1832145226536798311057333 171763614987824841661625)
                  ·
                    rfl

theorem cell22_1505288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 5, 1, 5].length) (baseStart_1505288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1505288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1505288 prefixEnd_1505288 := by exact prefixLift 1505288
  have htrace : WordTrace (prefixWord ++ tailWord_1505288) baseStart_1505288 baseEnd_1505288 := by
    simpa [prefixWord, tailWord_1505288, baseEnd_1505288] using wordTrace_append hprefix tailTrace_1505288
  have hstable : (prefixWord ++ tailWord_1505288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1505288).length < 2 ^ (prefixWord ++ tailWord_1505288).sum := by decide
  have hdescent : baseEnd_1505288 < baseStart_1505288 := by decide
  rcases family_descends (prefixWord ++ tailWord_1505288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1505333 : List Nat := [1, 3, 3, 1, 1, 1, 2, 6, 4]
def baseStart_1505333 : Nat := 118140960795 + 1505333 * 2 ^ 59
def prefixEnd_1505333 : Nat := 4983230072969 + 3 ^ 40 * 1505333 * 2
def baseEnd_1505333 : Nat := 171768749794369802536579

theorem tailTrace_1505333 : CollatzResearch.WordTrace tailWord_1505333 prefixEnd_1505333 171768749794369802536579 := by
  unfold tailWord_1505333
  simp only [CollatzResearch.WordTrace]
  refine ⟨54904005055443106253496653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36602670036962070835664435 54904005055443106253496653)
  ·
    refine ⟨20589001895791164845061245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54904005055443106253496653 20589001895791164845061245)
    ·
      refine ⟨7720875710921686816897967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20589001895791164845061245 7720875710921686816897967)
      ·
        refine ⟨11581313566382530225346951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7720875710921686816897967 11581313566382530225346951)
        ·
          refine ⟨17371970349573795338020427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11581313566382530225346951 17371970349573795338020427)
          ·
            refine ⟨26057955524360693007030641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17371970349573795338020427 26057955524360693007030641)
            ·
              refine ⟨19543466643270519755272981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26057955524360693007030641 19543466643270519755272981)
              ·
                refine ⟨916099998903305613528421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 19543466643270519755272981 916099998903305613528421)
                ·
                  refine ⟨171768749794369802536579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 916099998903305613528421 171768749794369802536579)
                  ·
                    rfl

theorem cell22_1505333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 6, 4].length) (baseStart_1505333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1505333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1505333 prefixEnd_1505333 := by exact prefixLift 1505333
  have htrace : WordTrace (prefixWord ++ tailWord_1505333) baseStart_1505333 baseEnd_1505333 := by
    simpa [prefixWord, tailWord_1505333, baseEnd_1505333] using wordTrace_append hprefix tailTrace_1505333
  have hstable : (prefixWord ++ tailWord_1505333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1505333).length < 2 ^ (prefixWord ++ tailWord_1505333).sum := by decide
  have hdescent : baseEnd_1505333 < baseStart_1505333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1505333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1505378 : List Nat := [3, 3, 2, 2, 2, 10]
def baseStart_1505378 : Nat := 118140960795 + 1505378 * 2 ^ 59
def prefixEnd_1505378 : Nat := 4983230072969 + 3 ^ 40 * 1505378 * 2
def baseEnd_1505378 : Nat := 6361995725959806052279

theorem tailTrace_1505378 : CollatzResearch.WordTrace tailWord_1505378 prefixEnd_1505378 6361995725959806052279 := by
  unfold tailWord_1505378
  simp only [CollatzResearch.WordTrace]
  refine ⟨13726411585070019734721197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36603764226853385959256525 13726411585070019734721197)
  ·
    refine ⟨5147404344401257400520449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13726411585070019734721197 5147404344401257400520449)
    ·
      refine ⟨3860553258300943050390337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5147404344401257400520449 3860553258300943050390337)
      ·
        refine ⟨2895414943725707287792753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3860553258300943050390337 2895414943725707287792753)
        ·
          refine ⟨2171561207794280465844565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2895414943725707287792753 2171561207794280465844565)
          ·
            refine ⟨6361995725959806052279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2171561207794280465844565 6361995725959806052279)
            ·
              rfl

theorem cell22_1505378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 10].length) (baseStart_1505378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1505378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1505378 prefixEnd_1505378 := by exact prefixLift 1505378
  have htrace : WordTrace (prefixWord ++ tailWord_1505378) baseStart_1505378 baseEnd_1505378 := by
    simpa [prefixWord, tailWord_1505378, baseEnd_1505378] using wordTrace_append hprefix tailTrace_1505378
  have hstable : (prefixWord ++ tailWord_1505378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1505378).length < 2 ^ (prefixWord ++ tailWord_1505378).sum := by decide
  have hdescent : baseEnd_1505378 < baseStart_1505378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1505378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1505391 : List Nat := [1, 1, 2, 1, 3, 4, 1, 1, 2, 6]
def baseStart_1505391 : Nat := 118140960795 + 1505391 * 2 ^ 59
def prefixEnd_1505391 : Nat := 4983230072969 + 3 ^ 40 * 1505391 * 2
def baseEnd_1505391 : Nat := 515326103968416589659559

theorem tailTrace_1505391 : CollatzResearch.WordTrace tailWord_1505391 prefixEnd_1505391 515326103968416589659559 := by
  unfold tailWord_1505391
  simp only [CollatzResearch.WordTrace]
  refine ⟨54906120489232982159108027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36604080326155321439405351 54906120489232982159108027)
  ·
    refine ⟨82359180733849473238662041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54906120489232982159108027 82359180733849473238662041)
    ·
      refine ⟨61769385550387104928996531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82359180733849473238662041 61769385550387104928996531)
      ·
        refine ⟨92654078325580657393494797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61769385550387104928996531 92654078325580657393494797)
        ·
          refine ⟨34745279372092746522560549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92654078325580657393494797 34745279372092746522560549)
          ·
            refine ⟨6514739882267389972980103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34745279372092746522560549 6514739882267389972980103)
            ·
              refine ⟨9772109823401084959470155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6514739882267389972980103 9772109823401084959470155)
              ·
                refine ⟨14658164735101627439205233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9772109823401084959470155 14658164735101627439205233)
                ·
                  refine ⟨10993623551326220579403925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14658164735101627439205233 10993623551326220579403925)
                  ·
                    refine ⟨515326103968416589659559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10993623551326220579403925 515326103968416589659559)
                    ·
                      rfl

theorem cell22_1505391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 1, 2, 6].length) (baseStart_1505391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1505391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1505391 prefixEnd_1505391 := by exact prefixLift 1505391
  have htrace : WordTrace (prefixWord ++ tailWord_1505391) baseStart_1505391 baseEnd_1505391 := by
    simpa [prefixWord, tailWord_1505391, baseEnd_1505391] using wordTrace_append hprefix tailTrace_1505391
  have hstable : (prefixWord ++ tailWord_1505391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1505391).length < 2 ^ (prefixWord ++ tailWord_1505391).sum := by decide
  have hdescent : baseEnd_1505391 < baseStart_1505391 := by decide
  rcases family_descends (prefixWord ++ tailWord_1505391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1505393 : List Nat := [1, 2, 2, 2, 1, 1, 4, 3, 3, 3]
def baseStart_1505393 : Nat := 118140960795 + 1505393 * 2 ^ 59
def prefixEnd_1505393 : Nat := 4983230072969 + 3 ^ 40 * 1505393 * 2
def baseEnd_1505393 : Nat := 515326788609289251109553

theorem tailTrace_1505393 : CollatzResearch.WordTrace tailWord_1505393 prefixEnd_1505393 515326788609289251109553 := by
  unfold tailWord_1505393
  simp only [CollatzResearch.WordTrace]
  refine ⟨54906193435225736500680833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36604128956817157667120555 54906193435225736500680833)
  ·
    refine ⟨41179645076419302375510625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54906193435225736500680833 41179645076419302375510625)
    ·
      refine ⟨30884733807314476781632969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41179645076419302375510625 30884733807314476781632969)
      ·
        refine ⟨23163550355485857586224727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30884733807314476781632969 23163550355485857586224727)
        ·
          refine ⟨34745325533228786379337091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23163550355485857586224727 34745325533228786379337091)
          ·
            refine ⟨52117988299843179569005637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34745325533228786379337091 52117988299843179569005637)
            ·
              refine ⟨9772122806220596169188557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52117988299843179569005637 9772122806220596169188557)
              ·
                refine ⟨3664546052332723563445709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9772122806220596169188557 3664546052332723563445709)
                ·
                  refine ⟨1374204769624771336292141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3664546052332723563445709 1374204769624771336292141)
                  ·
                    refine ⟨515326788609289251109553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1374204769624771336292141 515326788609289251109553)
                    ·
                      rfl

theorem cell22_1505393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 3, 3, 3].length) (baseStart_1505393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1505393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1505393 prefixEnd_1505393 := by exact prefixLift 1505393
  have htrace : WordTrace (prefixWord ++ tailWord_1505393) baseStart_1505393 baseEnd_1505393 := by
    simpa [prefixWord, tailWord_1505393, baseEnd_1505393] using wordTrace_append hprefix tailTrace_1505393
  have hstable : (prefixWord ++ tailWord_1505393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1505393).length < 2 ^ (prefixWord ++ tailWord_1505393).sum := by decide
  have hdescent : baseEnd_1505393 < baseStart_1505393 := by decide
  rcases family_descends (prefixWord ++ tailWord_1505393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1505440 : List Nat := [2, 1, 1, 4, 2, 4, 1, 2, 5]
def baseStart_1505440 : Nat := 118140960795 + 1505440 * 2 ^ 59
def prefixEnd_1505440 : Nat := 4983230072969 + 3 ^ 40 * 1505440 * 2
def baseEnd_1505440 : Nat := 171780959223265598394803

theorem tailTrace_1505440 : CollatzResearch.WordTrace tailWord_1505440 prefixEnd_1505440 171780959223265598394803 := by
  unfold tailWord_1505440
  simp only [CollatzResearch.WordTrace]
  refine ⟨27453953833027731763820887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36605271777370309018427849 27453953833027731763820887)
  ·
    refine ⟨41180930749541597645731331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27453953833027731763820887 41180930749541597645731331)
    ·
      refine ⟨61771396124312396468596997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41180930749541597645731331 61771396124312396468596997)
      ·
        refine ⟨11582136773308574337861937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61771396124312396468596997 11582136773308574337861937)
        ·
          refine ⟨8686602579981430753396453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11582136773308574337861937 8686602579981430753396453)
          ·
            refine ⟨1628737983746518266261835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8686602579981430753396453 1628737983746518266261835)
            ·
              refine ⟨2443106975619777399392753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1628737983746518266261835 2443106975619777399392753)
              ·
                refine ⟨1832330231714833049544565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2443106975619777399392753 1832330231714833049544565)
                ·
                  refine ⟨171780959223265598394803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1832330231714833049544565 171780959223265598394803)
                  ·
                    rfl

theorem cell22_1505440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 1, 2, 5].length) (baseStart_1505440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1505440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1505440 prefixEnd_1505440 := by exact prefixLift 1505440
  have htrace : WordTrace (prefixWord ++ tailWord_1505440) baseStart_1505440 baseEnd_1505440 := by
    simpa [prefixWord, tailWord_1505440, baseEnd_1505440] using wordTrace_append hprefix tailTrace_1505440
  have hstable : (prefixWord ++ tailWord_1505440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1505440).length < 2 ^ (prefixWord ++ tailWord_1505440).sum := by decide
  have hdescent : baseEnd_1505440 < baseStart_1505440 := by decide
  rcases family_descends (prefixWord ++ tailWord_1505440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1505457 : List Nat := [1, 2, 2, 5, 2, 1, 3, 1, 5]
def baseStart_1505457 : Nat := 118140960795 + 1505457 * 2 ^ 59
def prefixEnd_1505457 : Nat := 4983230072969 + 3 ^ 40 * 1505457 * 2
def baseEnd_1505457 : Nat := 171782899039071472503119

theorem tailTrace_1505457 : CollatzResearch.WordTrace tailWord_1505457 prefixEnd_1505457 171782899039071472503119 := by
  unfold tailWord_1505457
  simp only [CollatzResearch.WordTrace]
  refine ⟨54908527706993875431010625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36605685137995916954007083 54908527706993875431010625)
  ·
    refine ⟨41181395780245406573257969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54908527706993875431010625 41181395780245406573257969)
    ·
      refine ⟨30886046835184054929943477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41181395780245406573257969 30886046835184054929943477)
      ·
        refine ⟨2895566890798505149682201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30886046835184054929943477 2895566890798505149682201)
        ·
          refine ⟨2171675168098878862261651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2895566890798505149682201 2171675168098878862261651)
          ·
            refine ⟨3257512752148318293392477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2171675168098878862261651 3257512752148318293392477)
            ·
              refine ⟨1221567282055619360022179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3257512752148318293392477 1221567282055619360022179)
              ·
                refine ⟨1832350923083429040033269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1221567282055619360022179 1832350923083429040033269)
                ·
                  refine ⟨171782899039071472503119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1832350923083429040033269 171782899039071472503119)
                  ·
                    rfl

theorem cell22_1505457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 3, 1, 5].length) (baseStart_1505457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1505457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1505457 prefixEnd_1505457 := by exact prefixLift 1505457
  have htrace : WordTrace (prefixWord ++ tailWord_1505457) baseStart_1505457 baseEnd_1505457 := by
    simpa [prefixWord, tailWord_1505457, baseEnd_1505457] using wordTrace_append hprefix tailTrace_1505457
  have hstable : (prefixWord ++ tailWord_1505457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1505457).length < 2 ^ (prefixWord ++ tailWord_1505457).sum := by decide
  have hdescent : baseEnd_1505457 < baseStart_1505457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1505457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1505483 : List Nat := [1, 1, 1, 1, 3, 2, 3, 1, 6, 3]
def baseStart_1505483 : Nat := 118140960795 + 1505483 * 2 ^ 59
def prefixEnd_1505483 : Nat := 4983230072969 + 3 ^ 40 * 1505483 * 2
def baseEnd_1505483 : Nat := 515357597448559016359277

theorem tailTrace_1505483 : CollatzResearch.WordTrace tailWord_1505483 prefixEnd_1505483 515357597448559016359277 := by
  unfold tailWord_1505483
  simp only [CollatzResearch.WordTrace]
  refine ⟨54909476004899681871457103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36606317336599787914304735 54909476004899681871457103)
  ·
    refine ⟨82364214007349522807185655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54909476004899681871457103 82364214007349522807185655)
    ·
      refine ⟨123546321011024284210778483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82364214007349522807185655 123546321011024284210778483)
      ·
        refine ⟨185319481516536426316167725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123546321011024284210778483 185319481516536426316167725)
        ·
          refine ⟨69494805568701159868562897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 185319481516536426316167725 69494805568701159868562897)
          ·
            refine ⟨52121104176525869901422173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69494805568701159868562897 52121104176525869901422173)
            ·
              refine ⟨19545414066197201213033315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52121104176525869901422173 19545414066197201213033315)
              ·
                refine ⟨29318121099295801819549973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19545414066197201213033315 29318121099295801819549973)
                ·
                  refine ⟨1374286926529490710291405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 29318121099295801819549973 1374286926529490710291405)
                  ·
                    refine ⟨515357597448559016359277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1374286926529490710291405 515357597448559016359277)
                    ·
                      rfl

theorem cell22_1505483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 6, 3].length) (baseStart_1505483 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1505483 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1505483 prefixEnd_1505483 := by exact prefixLift 1505483
  have htrace : WordTrace (prefixWord ++ tailWord_1505483) baseStart_1505483 baseEnd_1505483 := by
    simpa [prefixWord, tailWord_1505483, baseEnd_1505483] using wordTrace_append hprefix tailTrace_1505483
  have hstable : (prefixWord ++ tailWord_1505483).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1505483).length < 2 ^ (prefixWord ++ tailWord_1505483).sum := by decide
  have hdescent : baseEnd_1505483 < baseStart_1505483 := by decide
  rcases family_descends (prefixWord ++ tailWord_1505483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1505498 : List Nat := [3, 1, 1, 2, 2, 1, 3, 1, 4, 4]
def baseStart_1505498 : Nat := 118140960795 + 1505498 * 2 ^ 59
def prefixEnd_1505498 : Nat := 4983230072969 + 3 ^ 40 * 1505498 * 2
def baseEnd_1505498 : Nat := 515362732255103977234231

theorem tailTrace_1505498 : CollatzResearch.WordTrace tailWord_1505498 prefixEnd_1505498 515362732255103977234231 := by
  unfold tailWord_1505498
  simp only [CollatzResearch.WordTrace]
  refine ⟨13727505774961334858313287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36606682066563559622168765 13727505774961334858313287)
  ·
    refine ⟨20591258662442002287469931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13727505774961334858313287 20591258662442002287469931)
    ·
      refine ⟨30886887993663003431204897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20591258662442002287469931 30886887993663003431204897)
      ·
        refine ⟨23165165995247252573403673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30886887993663003431204897 23165165995247252573403673)
        ·
          refine ⟨17373874496435439430052755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23165165995247252573403673 17373874496435439430052755)
          ·
            refine ⟨26060811744653159145079133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17373874496435439430052755 26060811744653159145079133)
            ·
              refine ⟨9772804404244934679404675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26060811744653159145079133 9772804404244934679404675)
              ·
                refine ⟨14659206606367402019107013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9772804404244934679404675 14659206606367402019107013)
                ·
                  refine ⟨2748601238693887878582565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14659206606367402019107013 2748601238693887878582565)
                  ·
                    refine ⟨515362732255103977234231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2748601238693887878582565 515362732255103977234231)
                    ·
                      rfl

theorem cell22_1505498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 1, 4, 4].length) (baseStart_1505498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1505498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1505498 prefixEnd_1505498 := by exact prefixLift 1505498
  have htrace : WordTrace (prefixWord ++ tailWord_1505498) baseStart_1505498 baseEnd_1505498 := by
    simpa [prefixWord, tailWord_1505498, baseEnd_1505498] using wordTrace_append hprefix tailTrace_1505498
  have hstable : (prefixWord ++ tailWord_1505498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1505498).length < 2 ^ (prefixWord ++ tailWord_1505498).sum := by decide
  have hdescent : baseEnd_1505498 < baseStart_1505498 := by decide
  rcases family_descends (prefixWord ++ tailWord_1505498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1505620 : List Nat := [2, 4, 1, 1, 2, 2, 1, 3, 6]
def baseStart_1505620 : Nat := 118140960795 + 1505620 * 2 ^ 59
def prefixEnd_1505620 : Nat := 4983230072969 + 3 ^ 40 * 1505620 * 2
def baseEnd_1505620 : Nat := 171801498449445441894619

theorem tailTrace_1505620 : CollatzResearch.WordTrace tailWord_1505620 prefixEnd_1505620 171801498449445441894619 := by
  unfold tailWord_1505620
  simp only [CollatzResearch.WordTrace]
  refine ⟨27457236402701677134597157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36609648536935569512796209 27457236402701677134597157)
  ·
    refine ⟨5148231825506564462736967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27457236402701677134597157 5148231825506564462736967)
    ·
      refine ⟨7722347738259846694105451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5148231825506564462736967 7722347738259846694105451)
      ·
        refine ⟨11583521607389770041158177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7722347738259846694105451 11583521607389770041158177)
        ·
          refine ⟨8687641205542327530868633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11583521607389770041158177 8687641205542327530868633)
          ·
            refine ⟨6515730904156745648151475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8687641205542327530868633 6515730904156745648151475)
            ·
              refine ⟨9773596356235118472227213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6515730904156745648151475 9773596356235118472227213)
              ·
                refine ⟨3665098633588169427085205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9773596356235118472227213 3665098633588169427085205)
                ·
                  refine ⟨171801498449445441894619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3665098633588169427085205 171801498449445441894619)
                  ·
                    rfl

theorem cell22_1505620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 3, 6].length) (baseStart_1505620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1505620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1505620 prefixEnd_1505620 := by exact prefixLift 1505620
  have htrace : WordTrace (prefixWord ++ tailWord_1505620) baseStart_1505620 baseEnd_1505620 := by
    simpa [prefixWord, tailWord_1505620, baseEnd_1505620] using wordTrace_append hprefix tailTrace_1505620
  have hstable : (prefixWord ++ tailWord_1505620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1505620).length < 2 ^ (prefixWord ++ tailWord_1505620).sum := by decide
  have hdescent : baseEnd_1505620 < baseStart_1505620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1505620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1505650 : List Nat := [3, 2, 1, 2, 1, 3, 2, 1, 1, 6]
def baseStart_1505650 : Nat := 118140960795 + 1505650 * 2 ^ 59
def prefixEnd_1505650 : Nat := 4983230072969 + 3 ^ 40 * 1505650 * 2
def baseEnd_1505650 : Nat := 515414764961426247433765

theorem tailTrace_1505650 : CollatzResearch.WordTrace tailWord_1505650 prefixEnd_1505650 515414764961426247433765 := by
  unfold tailWord_1505650
  simp only [CollatzResearch.WordTrace]
  refine ⟨13728891748823667348196601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36610377996863112928524269 13728891748823667348196601)
  ·
    refine ⟨10296668811617750511147451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13728891748823667348196601 10296668811617750511147451)
    ·
      refine ⟨15445003217426625766721177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10296668811617750511147451 15445003217426625766721177)
      ·
        refine ⟨11583752413069969325040883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15445003217426625766721177 11583752413069969325040883)
        ·
          refine ⟨17375628619604953987561325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11583752413069969325040883 17375628619604953987561325)
          ·
            refine ⟨6515860732351857745335497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17375628619604953987561325 6515860732351857745335497)
            ·
              refine ⟨4886895549263893309001623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6515860732351857745335497 4886895549263893309001623)
              ·
                refine ⟨7330343323895839963502435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4886895549263893309001623 7330343323895839963502435)
                ·
                  refine ⟨10995514985843759945253653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7330343323895839963502435 10995514985843759945253653)
                  ·
                    refine ⟨515414764961426247433765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10995514985843759945253653 515414764961426247433765)
                    ·
                      rfl

theorem cell22_1505650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 1, 1, 6].length) (baseStart_1505650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1505650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1505650 prefixEnd_1505650 := by exact prefixLift 1505650
  have htrace : WordTrace (prefixWord ++ tailWord_1505650) baseStart_1505650 baseEnd_1505650 := by
    simpa [prefixWord, tailWord_1505650, baseEnd_1505650] using wordTrace_append hprefix tailTrace_1505650
  have hstable : (prefixWord ++ tailWord_1505650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1505650).length < 2 ^ (prefixWord ++ tailWord_1505650).sum := by decide
  have hdescent : baseEnd_1505650 < baseStart_1505650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1505650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1505663 : List Nat := [1, 1, 2, 2, 1, 1, 2, 2, 1, 9]
def baseStart_1505663 : Nat := 118140960795 + 1505663 * 2 ^ 59
def prefixEnd_1505663 : Nat := 4983230072969 + 3 ^ 40 * 1505663 * 2
def baseEnd_1505663 : Nat := 515419215127098546858725

theorem tailTrace_1505663 : CollatzResearch.WordTrace tailWord_1505663 prefixEnd_1505663 515419215127098546858725 := by
  unfold tailWord_1505663
  simp only [CollatzResearch.WordTrace]
  refine ⟨54916041144247572613009643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36610694096165048408673095 54916041144247572613009643)
  ·
    refine ⟨82374061716371358919514465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54916041144247572613009643 82374061716371358919514465)
    ·
      refine ⟨61780546287278519189635849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82374061716371358919514465 61780546287278519189635849)
      ·
        refine ⟨46335409715458889392226887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61780546287278519189635849 46335409715458889392226887)
        ·
          refine ⟨69503114573188334088340331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46335409715458889392226887 69503114573188334088340331)
          ·
            refine ⟨104254671859782501132510497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69503114573188334088340331 104254671859782501132510497)
            ·
              refine ⟨78191003894836875849382873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104254671859782501132510497 78191003894836875849382873)
              ·
                refine ⟨58643252921127656887037155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78191003894836875849382873 58643252921127656887037155)
                ·
                  refine ⟨87964879381691485330555733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58643252921127656887037155 87964879381691485330555733)
                  ·
                    refine ⟨515419215127098546858725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 87964879381691485330555733 515419215127098546858725)
                    ·
                      rfl

theorem cell22_1505663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 9].length) (baseStart_1505663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1505663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1505663 prefixEnd_1505663 := by exact prefixLift 1505663
  have htrace : WordTrace (prefixWord ++ tailWord_1505663) baseStart_1505663 baseEnd_1505663 := by
    simpa [prefixWord, tailWord_1505663, baseEnd_1505663] using wordTrace_append hprefix tailTrace_1505663
  have hstable : (prefixWord ++ tailWord_1505663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1505663).length < 2 ^ (prefixWord ++ tailWord_1505663).sum := by decide
  have hdescent : baseEnd_1505663 < baseStart_1505663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1505663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1505665 : List Nat := [1, 2, 4, 3, 1, 1, 10]
def baseStart_1505665 : Nat := 118140960795 + 1505665 * 2 ^ 59
def prefixEnd_1505665 : Nat := 4983230072969 + 3 ^ 40 * 1505665 * 2
def baseEnd_1505665 : Nat := 19089625917332266974397

theorem tailTrace_1505665 : CollatzResearch.WordTrace tailWord_1505665 prefixEnd_1505665 19089625917332266974397 := by
  unfold tailWord_1505665
  simp only [CollatzResearch.WordTrace]
  refine ⟨54916114090240326954582449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36610742726826884636388299 54916114090240326954582449)
  ·
    refine ⟨41187085567680245215936837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54916114090240326954582449 41187085567680245215936837)
    ·
      refine ⟨7722578543940045977988157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41187085567680245215936837 7722578543940045977988157)
      ·
        refine ⟨2895966953977517241745559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7722578543940045977988157 2895966953977517241745559)
        ·
          refine ⟨4343950430966275862618339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2895966953977517241745559 4343950430966275862618339)
          ·
            refine ⟨6515925646449413793927509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4343950430966275862618339 6515925646449413793927509)
            ·
              refine ⟨19089625917332266974397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 6515925646449413793927509 19089625917332266974397)
              ·
                rfl

theorem cell22_1505665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 10].length) (baseStart_1505665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1505665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1505665 prefixEnd_1505665 := by exact prefixLift 1505665
  have htrace : WordTrace (prefixWord ++ tailWord_1505665) baseStart_1505665 baseEnd_1505665 := by
    simpa [prefixWord, tailWord_1505665, baseEnd_1505665] using wordTrace_append hprefix tailTrace_1505665
  have hstable : (prefixWord ++ tailWord_1505665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1505665).length < 2 ^ (prefixWord ++ tailWord_1505665).sum := by decide
  have hdescent : baseEnd_1505665 < baseStart_1505665 := by decide
  rcases family_descends (prefixWord ++ tailWord_1505665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1505667 : List Nat := [1, 1, 1, 3, 6, 1, 1, 2, 2, 4]
def baseStart_1505667 : Nat := 118140960795 + 1505667 * 2 ^ 59
def prefixEnd_1505667 : Nat := 4983230072969 + 3 ^ 40 * 1505667 * 2
def baseEnd_1505667 : Nat := 515420584408843869758713

theorem tailTrace_1505667 : CollatzResearch.WordTrace tailWord_1505667 prefixEnd_1505667 515420584408843869758713 := by
  unfold tailWord_1505667
  simp only [CollatzResearch.WordTrace]
  refine ⟨54916187036233081296155255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36610791357488720864103503 54916187036233081296155255)
  ·
    refine ⟨82374280554349621944232883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54916187036233081296155255 82374280554349621944232883)
    ·
      refine ⟨123561420831524432916349325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82374280554349621944232883 123561420831524432916349325)
      ·
        refine ⟨46335532811821662343630997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123561420831524432916349325 46335532811821662343630997)
        ·
          refine ⟨2171978100554140422357703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 46335532811821662343630997 2171978100554140422357703)
          ·
            refine ⟨3257967150831210633536555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2171978100554140422357703 3257967150831210633536555)
            ·
              refine ⟨4886950726246815950304833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3257967150831210633536555 4886950726246815950304833)
              ·
                refine ⟨3665213044685111962728625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4886950726246815950304833 3665213044685111962728625)
                ·
                  refine ⟨2748909783513833972046469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3665213044685111962728625 2748909783513833972046469)
                  ·
                    refine ⟨515420584408843869758713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2748909783513833972046469 515420584408843869758713)
                    ·
                      rfl

theorem cell22_1505667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 2, 2, 4].length) (baseStart_1505667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1505667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1505667 prefixEnd_1505667 := by exact prefixLift 1505667
  have htrace : WordTrace (prefixWord ++ tailWord_1505667) baseStart_1505667 baseEnd_1505667 := by
    simpa [prefixWord, tailWord_1505667, baseEnd_1505667] using wordTrace_append hprefix tailTrace_1505667
  have hstable : (prefixWord ++ tailWord_1505667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1505667).length < 2 ^ (prefixWord ++ tailWord_1505667).sum := by decide
  have hdescent : baseEnd_1505667 < baseStart_1505667 := by decide
  rcases family_descends (prefixWord ++ tailWord_1505667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1505680 : List Nat := [2, 1, 1, 1, 1, 1, 2, 1, 9, 3]
def baseStart_1505680 : Nat := 118140960795 + 1505680 * 2 ^ 59
def prefixEnd_1505680 : Nat := 4983230072969 + 3 ^ 40 * 1505680 * 2
def baseEnd_1505680 : Nat := 515425034574516169183673

theorem tailTrace_1505680 : CollatzResearch.WordTrace tailWord_1505680 prefixEnd_1505680 515425034574516169183673 := by
  unfold tailWord_1505680
  simp only [CollatzResearch.WordTrace]
  refine ⟨27458330592592992258189247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36611107456790656344252329 27458330592592992258189247)
  ·
    refine ⟨41187495888889488387283871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27458330592592992258189247 41187495888889488387283871)
    ·
      refine ⟨61781243833334232580925807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41187495888889488387283871 61781243833334232580925807)
      ·
        refine ⟨92671865750001348871388711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61781243833334232580925807 92671865750001348871388711)
        ·
          refine ⟨139007798625002023307083067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92671865750001348871388711 139007798625002023307083067)
          ·
            refine ⟨208511697937503034960624601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139007798625002023307083067 208511697937503034960624601)
            ·
              refine ⟨156383773453127276220468451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 208511697937503034960624601 156383773453127276220468451)
              ·
                refine ⟨234575660179690914330702677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 156383773453127276220468451 234575660179690914330702677)
                ·
                  refine ⟨1374466758865376451156461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 234575660179690914330702677 1374466758865376451156461)
                  ·
                    refine ⟨515425034574516169183673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1374466758865376451156461 515425034574516169183673)
                    ·
                      rfl

theorem cell22_1505680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 9, 3].length) (baseStart_1505680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1505680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1505680 prefixEnd_1505680 := by exact prefixLift 1505680
  have htrace : WordTrace (prefixWord ++ tailWord_1505680) baseStart_1505680 baseEnd_1505680 := by
    simpa [prefixWord, tailWord_1505680, baseEnd_1505680] using wordTrace_append hprefix tailTrace_1505680
  have hstable : (prefixWord ++ tailWord_1505680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1505680).length < 2 ^ (prefixWord ++ tailWord_1505680).sum := by decide
  have hdescent : baseEnd_1505680 < baseStart_1505680 := by decide
  rcases family_descends (prefixWord ++ tailWord_1505680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1505714 : List Nat := [3, 2, 1, 1, 1, 1, 4, 5, 1, 3]
def baseStart_1505714 : Nat := 118140960795 + 1505714 * 2 ^ 59
def prefixEnd_1505714 : Nat := 4983230072969 + 3 ^ 40 * 1505714 * 2
def baseEnd_1505714 : Nat := 515436673469351413833569

theorem tailTrace_1505714 : CollatzResearch.WordTrace tailWord_1505714 prefixEnd_1505714 515436673469351413833569 := by
  unfold tailWord_1505714
  simp only [CollatzResearch.WordTrace]
  refine ⟨13729475316765702080779049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36611934178041872215410797 13729475316765702080779049)
  ·
    refine ⟨10297106487574276560584287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13729475316765702080779049 10297106487574276560584287)
    ·
      refine ⟨15445659731361414840876431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10297106487574276560584287 15445659731361414840876431)
      ·
        refine ⟨23168489597042122261314647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15445659731361414840876431 23168489597042122261314647)
        ·
          refine ⟨34752734395563183391971971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23168489597042122261314647 34752734395563183391971971)
          ·
            refine ⟨52129101593344775087957957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34752734395563183391971971 52129101593344775087957957)
            ·
              refine ⟨9774206548752145328992117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52129101593344775087957957 9774206548752145328992117)
              ·
                refine ⟨916331863945513624593011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9774206548752145328992117 916331863945513624593011)
                ·
                  refine ⟨1374497795918270436889517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 916331863945513624593011 1374497795918270436889517)
                  ·
                    refine ⟨515436673469351413833569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1374497795918270436889517 515436673469351413833569)
                    ·
                      rfl

theorem cell22_1505714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 5, 1, 3].length) (baseStart_1505714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1505714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1505714 prefixEnd_1505714 := by exact prefixLift 1505714
  have htrace : WordTrace (prefixWord ++ tailWord_1505714) baseStart_1505714 baseEnd_1505714 := by
    simpa [prefixWord, tailWord_1505714, baseEnd_1505714] using wordTrace_append hprefix tailTrace_1505714
  have hstable : (prefixWord ++ tailWord_1505714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1505714).length < 2 ^ (prefixWord ++ tailWord_1505714).sum := by decide
  have hdescent : baseEnd_1505714 < baseStart_1505714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1505714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1505757 : List Nat := [1, 4, 3, 1, 1, 1, 1, 3, 3, 4]
def baseStart_1505757 : Nat := 118140960795 + 1505757 * 2 ^ 59
def prefixEnd_1505757 : Nat := 4983230072969 + 3 ^ 40 * 1505757 * 2
def baseEnd_1505757 : Nat := 515451393248113635008437

theorem tailTrace_1505757 : CollatzResearch.WordTrace tailWord_1505757 prefixEnd_1505757 515451393248113635008437 := by
  unfold tailWord_1505757
  simp only [CollatzResearch.WordTrace]
  refine ⟨54919469605907026666931525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36612979737271351111287683 54919469605907026666931525)
  ·
    refine ⟨10297400551107567500049661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54919469605907026666931525 10297400551107567500049661)
    ·
      refine ⟨3861525206665337812518623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10297400551107567500049661 3861525206665337812518623)
      ·
        refine ⟨5792287809998006718777935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3861525206665337812518623 5792287809998006718777935)
        ·
          refine ⟨8688431714997010078166903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5792287809998006718777935 8688431714997010078166903)
          ·
            refine ⟨13032647572495515117250355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8688431714997010078166903 13032647572495515117250355)
            ·
              refine ⟨19548971358743272675875533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13032647572495515117250355 19548971358743272675875533)
              ·
                refine ⟨7330864259528727253453325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19548971358743272675875533 7330864259528727253453325)
                ·
                  refine ⟨2749074097323272720044997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7330864259528727253453325 2749074097323272720044997)
                  ·
                    refine ⟨515451393248113635008437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2749074097323272720044997 515451393248113635008437)
                    ·
                      rfl

theorem cell22_1505757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_1505757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1505757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1505757 prefixEnd_1505757 := by exact prefixLift 1505757
  have htrace : WordTrace (prefixWord ++ tailWord_1505757) baseStart_1505757 baseEnd_1505757 := by
    simpa [prefixWord, tailWord_1505757, baseEnd_1505757] using wordTrace_append hprefix tailTrace_1505757
  have hstable : (prefixWord ++ tailWord_1505757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1505757).length < 2 ^ (prefixWord ++ tailWord_1505757).sum := by decide
  have hdescent : baseEnd_1505757 < baseStart_1505757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1505757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1505774 : List Nat := [4, 1, 2, 1, 2, 3, 1, 3, 1, 4]
def baseStart_1505774 : Nat := 118140960795 + 1505774 * 2 ^ 59
def prefixEnd_1505774 : Nat := 4983230072969 + 3 ^ 40 * 1505774 * 2
def baseEnd_1505774 : Nat := 515457212695531257333385

theorem tailTrace_1505774 : CollatzResearch.WordTrace tailWord_1505774 prefixEnd_1505774 515457212695531257333385 := by
  unfold tailWord_1505774
  simp only [CollatzResearch.WordTrace]
  refine ⟨6865011205855679821287547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36613393097896959046866917 6865011205855679821287547)
  ·
    refine ⟨10297516808783519731931321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6865011205855679821287547 10297516808783519731931321)
    ·
      refine ⟨7723137606587639798948491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10297516808783519731931321 7723137606587639798948491)
      ·
        refine ⟨11584706409881459698422737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7723137606587639798948491 11584706409881459698422737)
        ·
          refine ⟨8688529807411094773817053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11584706409881459698422737 8688529807411094773817053)
          ·
            refine ⟨3258198677779160540181395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8688529807411094773817053 3258198677779160540181395)
            ·
              refine ⟨4887298016668740810272093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3258198677779160540181395 4887298016668740810272093)
              ·
                refine ⟨1832736756250777803852035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4887298016668740810272093 1832736756250777803852035)
                ·
                  refine ⟨2749105134376166705778053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1832736756250777803852035 2749105134376166705778053)
                  ·
                    refine ⟨515457212695531257333385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2749105134376166705778053 515457212695531257333385)
                    ·
                      rfl

theorem cell22_1505774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 3, 1, 4].length) (baseStart_1505774 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1505774 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1505774 prefixEnd_1505774 := by exact prefixLift 1505774
  have htrace : WordTrace (prefixWord ++ tailWord_1505774) baseStart_1505774 baseEnd_1505774 := by
    simpa [prefixWord, tailWord_1505774, baseEnd_1505774] using wordTrace_append hprefix tailTrace_1505774
  have hstable : (prefixWord ++ tailWord_1505774).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1505774).length < 2 ^ (prefixWord ++ tailWord_1505774).sum := by decide
  have hdescent : baseEnd_1505774 < baseStart_1505774 := by decide
  rcases family_descends (prefixWord ++ tailWord_1505774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1505800 : List Nat := [2, 1, 3, 2, 1, 1, 1, 11]
def baseStart_1505800 : Nat := 118140960795 + 1505800 * 2 ^ 59
def prefixEnd_1505800 : Nat := 4983230072969 + 3 ^ 40 * 1505800 * 2
def baseEnd_1505800 : Nat := 57274012558541761798145

theorem tailTrace_1505800 : CollatzResearch.WordTrace tailWord_1505800 prefixEnd_1505800 57274012558541761798145 := by
  unfold tailWord_1505800
  simp only [CollatzResearch.WordTrace]
  refine ⟨27460518972375622505373427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36614025296500830007164569 27460518972375622505373427)
  ·
    refine ⟨41190778458563433758060141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27460518972375622505373427 41190778458563433758060141)
    ·
      refine ⟨15446541921961287659272553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41190778458563433758060141 15446541921961287659272553)
      ·
        refine ⟨11584906441470965744454415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15446541921961287659272553 11584906441470965744454415)
        ·
          refine ⟨17377359662206448616681623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11584906441470965744454415 17377359662206448616681623)
          ·
            refine ⟨26066039493309672925022435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17377359662206448616681623 26066039493309672925022435)
            ·
              refine ⟨39099059239964509387533653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26066039493309672925022435 39099059239964509387533653)
              ·
                refine ⟨57274012558541761798145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 39099059239964509387533653 57274012558541761798145)
                ·
                  rfl

theorem cell22_1505800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 11].length) (baseStart_1505800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1505800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1505800 prefixEnd_1505800 := by exact prefixLift 1505800
  have htrace : WordTrace (prefixWord ++ tailWord_1505800) baseStart_1505800 baseEnd_1505800 := by
    simpa [prefixWord, tailWord_1505800, baseEnd_1505800] using wordTrace_append hprefix tailTrace_1505800
  have hstable : (prefixWord ++ tailWord_1505800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1505800).length < 2 ^ (prefixWord ++ tailWord_1505800).sum := by decide
  have hdescent : baseEnd_1505800 < baseStart_1505800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1505800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1505804 : List Nat := [2, 2, 1, 2, 4, 3, 1, 1, 1, 5]
def baseStart_1505804 : Nat := 118140960795 + 1505804 * 2 ^ 59
def prefixEnd_1505804 : Nat := 4983230072969 + 3 ^ 40 * 1505804 * 2
def baseEnd_1505804 : Nat := 515467482308621179083293

theorem tailTrace_1505804 : CollatzResearch.WordTrace tailWord_1505804 prefixEnd_1505804 515467482308621179083293 := by
  unfold tailWord_1505804
  simp only [CollatzResearch.WordTrace]
  refine ⟨27460591918368376846946233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36614122557824502462594977 27460591918368376846946233)
  ·
    refine ⟨20595443938776282635209675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27460591918368376846946233 20595443938776282635209675)
    ·
      refine ⟨30893165908164423952814513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20595443938776282635209675 30893165908164423952814513)
      ·
        refine ⟨23169874431123317964610885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30893165908164423952814513 23169874431123317964610885)
        ·
          refine ⟨4344351455835622118364541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23169874431123317964610885 4344351455835622118364541)
          ·
            refine ⟨1629131795938358294386703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4344351455835622118364541 1629131795938358294386703)
            ·
              refine ⟨2443697693907537441580055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1629131795938358294386703 2443697693907537441580055)
              ·
                refine ⟨3665546540861306162370083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2443697693907537441580055 3665546540861306162370083)
                ·
                  refine ⟨5498319811291959243555125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3665546540861306162370083 5498319811291959243555125)
                  ·
                    refine ⟨515467482308621179083293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5498319811291959243555125 515467482308621179083293)
                    ·
                      rfl

theorem cell22_1505804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 1, 1, 1, 5].length) (baseStart_1505804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1505804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1505804 prefixEnd_1505804 := by exact prefixLift 1505804
  have htrace : WordTrace (prefixWord ++ tailWord_1505804) baseStart_1505804 baseEnd_1505804 := by
    simpa [prefixWord, tailWord_1505804, baseEnd_1505804] using wordTrace_append hprefix tailTrace_1505804
  have hstable : (prefixWord ++ tailWord_1505804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1505804).length < 2 ^ (prefixWord ++ tailWord_1505804).sum := by decide
  have hdescent : baseEnd_1505804 < baseStart_1505804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1505804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1505896 : List Nat := [2, 1, 4, 3, 2, 1, 2, 2, 5]
def baseStart_1505896 : Nat := 118140960795 + 1505896 * 2 ^ 59
def prefixEnd_1505896 : Nat := 4983230072969 + 3 ^ 40 * 1505896 * 2
def baseEnd_1505896 : Nat := 171832991929587868594337

theorem tailTrace_1505896 : CollatzResearch.WordTrace tailWord_1505896 prefixEnd_1505896 171832991929587868594337 := by
  unfold tailWord_1505896
  simp only [CollatzResearch.WordTrace]
  refine ⟨27462269676201726703120771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36616359568268968937494361 27462269676201726703120771)
  ·
    refine ⟨41193404514302590054681157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27462269676201726703120771 41193404514302590054681157)
    ·
      refine ⟨7723763346431735635252717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41193404514302590054681157 7723763346431735635252717)
      ·
        refine ⟨2896411254911900863219769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7723763346431735635252717 2896411254911900863219769)
        ·
          refine ⟨2172308441183925647414827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2896411254911900863219769 2172308441183925647414827)
          ·
            refine ⟨3258462661775888471122241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2172308441183925647414827 3258462661775888471122241)
            ·
              refine ⟨2443846996331916353341681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3258462661775888471122241 2443846996331916353341681)
              ·
                refine ⟨1832885247248937265006261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2443846996331916353341681 1832885247248937265006261)
                ·
                  refine ⟨171832991929587868594337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1832885247248937265006261 171832991929587868594337)
                  ·
                    rfl

theorem cell22_1505896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 2, 2, 5].length) (baseStart_1505896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1505896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1505896 prefixEnd_1505896 := by exact prefixLift 1505896
  have htrace : WordTrace (prefixWord ++ tailWord_1505896) baseStart_1505896 baseEnd_1505896 := by
    simpa [prefixWord, tailWord_1505896, baseEnd_1505896] using wordTrace_append hprefix tailTrace_1505896
  have hstable : (prefixWord ++ tailWord_1505896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1505896).length < 2 ^ (prefixWord ++ tailWord_1505896).sum := by decide
  have hdescent : baseEnd_1505896 < baseStart_1505896 := by decide
  rcases family_descends (prefixWord ++ tailWord_1505896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1505924 : List Nat := [2, 3, 2, 1, 3, 2, 1, 2, 6]
def baseStart_1505924 : Nat := 118140960795 + 1505924 * 2 ^ 59
def prefixEnd_1505924 : Nat := 4983230072969 + 3 ^ 40 * 1505924 * 2
def baseEnd_1505924 : Nat := 171836186920326955360975

theorem tailTrace_1505924 : CollatzResearch.WordTrace tailWord_1505924 prefixEnd_1505924 171836186920326955360975 := by
  unfold tailWord_1505924
  simp only [CollatzResearch.WordTrace]
  refine ⟨27462780298151007094130413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36617040397534676125507217 27462780298151007094130413)
  ·
    refine ⟨10298542611806627660298905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27462780298151007094130413 10298542611806627660298905)
    ·
      refine ⟨7723906958854970745224179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10298542611806627660298905 7723906958854970745224179)
      ·
        refine ⟨11585860438282456117836269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7723906958854970745224179 11585860438282456117836269)
        ·
          refine ⟨4344697664355921044188601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11585860438282456117836269 4344697664355921044188601)
          ·
            refine ⟨3258523248266940783141451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4344697664355921044188601 3258523248266940783141451)
            ·
              refine ⟨4887784872400411174712177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3258523248266940783141451 4887784872400411174712177)
              ·
                refine ⟨3665838654300308381034133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4887784872400411174712177 3665838654300308381034133)
                ·
                  refine ⟨171836186920326955360975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3665838654300308381034133 171836186920326955360975)
                  ·
                    rfl

theorem cell22_1505924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 2, 6].length) (baseStart_1505924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1505924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1505924 prefixEnd_1505924 := by exact prefixLift 1505924
  have htrace : WordTrace (prefixWord ++ tailWord_1505924) baseStart_1505924 baseEnd_1505924 := by
    simpa [prefixWord, tailWord_1505924, baseEnd_1505924] using wordTrace_append hprefix tailTrace_1505924
  have hstable : (prefixWord ++ tailWord_1505924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1505924).length < 2 ^ (prefixWord ++ tailWord_1505924).sum := by decide
  have hdescent : baseEnd_1505924 < baseStart_1505924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1505924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1506027 : List Nat := [1, 1, 1, 1, 2, 4, 1, 1, 2, 8]
def baseStart_1506027 : Nat := 118140960795 + 1506027 * 2 ^ 59
def prefixEnd_1506027 : Nat := 4983230072969 + 3 ^ 40 * 1506027 * 2
def baseEnd_1506027 : Nat := 515543819765922930757609

theorem tailTrace_1506027 : CollatzResearch.WordTrace tailWord_1506027 prefixEnd_1506027 515543819765922930757609 := by
  unfold tailWord_1506027
  simp only [CollatzResearch.WordTrace]
  refine ⟨54929317314928862779260335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36619544876619241852840223 54929317314928862779260335)
  ·
    refine ⟨82393975972393294168890503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54929317314928862779260335 82393975972393294168890503)
    ·
      refine ⟨123590963958589941253335755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82393975972393294168890503 123590963958589941253335755)
      ·
        refine ⟨185386445937884911880003633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123590963958589941253335755 185386445937884911880003633)
        ·
          refine ⟨139039834453413683910002725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 185386445937884911880003633 139039834453413683910002725)
          ·
            refine ⟨26069968960015065733125511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 139039834453413683910002725 26069968960015065733125511)
            ·
              refine ⟨39104953440022598599688267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26069968960015065733125511 39104953440022598599688267)
              ·
                refine ⟨58657430160033897899532401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39104953440022598599688267 58657430160033897899532401)
                ·
                  refine ⟨43993072620025423424649301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58657430160033897899532401 43993072620025423424649301)
                  ·
                    refine ⟨515543819765922930757609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 43993072620025423424649301 515543819765922930757609)
                    ·
                      rfl

theorem cell22_1506027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 8].length) (baseStart_1506027 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1506027 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1506027 prefixEnd_1506027 := by exact prefixLift 1506027
  have htrace : WordTrace (prefixWord ++ tailWord_1506027) baseStart_1506027 baseEnd_1506027 := by
    simpa [prefixWord, tailWord_1506027, baseEnd_1506027] using wordTrace_append hprefix tailTrace_1506027
  have hstable : (prefixWord ++ tailWord_1506027).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1506027).length < 2 ^ (prefixWord ++ tailWord_1506027).sum := by decide
  have hdescent : baseEnd_1506027 < baseStart_1506027 := by decide
  rcases family_descends (prefixWord ++ tailWord_1506027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1506029 : List Nat := [1, 5, 1, 2, 1, 1, 2, 1, 1, 7]
def baseStart_1506029 : Nat := 118140960795 + 1506029 * 2 ^ 59
def prefixEnd_1506029 : Nat := 4983230072969 + 3 ^ 40 * 1506029 * 2
def baseEnd_1506029 : Nat := 515544504406795592207603

theorem tailTrace_1506029 : CollatzResearch.WordTrace tailWord_1506029 prefixEnd_1506029 515544504406795592207603 := by
  unfold tailWord_1506029
  simp only [CollatzResearch.WordTrace]
  refine ⟨54929390260921617120833141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36619593507281078080555427 54929390260921617120833141)
  ·
    refine ⟨5149630336961401605078107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 54929390260921617120833141 5149630336961401605078107)
    ·
      refine ⟨7724445505442102407617161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5149630336961401605078107 7724445505442102407617161)
      ·
        refine ⟨5793334129081576805712871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7724445505442102407617161 5793334129081576805712871)
        ·
          refine ⟨8690001193622365208569307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5793334129081576805712871 8690001193622365208569307)
          ·
            refine ⟨13035001790433547812853961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8690001193622365208569307 13035001790433547812853961)
            ·
              refine ⟨9776251342825160859640471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13035001790433547812853961 9776251342825160859640471)
              ·
                refine ⟨14664377014237741289460707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9776251342825160859640471 14664377014237741289460707)
                ·
                  refine ⟨21996565521356611934191061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14664377014237741289460707 21996565521356611934191061)
                  ·
                    refine ⟨515544504406795592207603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21996565521356611934191061 515544504406795592207603)
                    ·
                      rfl

theorem cell22_1506029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 1, 1, 7].length) (baseStart_1506029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1506029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1506029 prefixEnd_1506029 := by exact prefixLift 1506029
  have htrace : WordTrace (prefixWord ++ tailWord_1506029) baseStart_1506029 baseEnd_1506029 := by
    simpa [prefixWord, tailWord_1506029, baseEnd_1506029] using wordTrace_append hprefix tailTrace_1506029
  have hstable : (prefixWord ++ tailWord_1506029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1506029).length < 2 ^ (prefixWord ++ tailWord_1506029).sum := by decide
  have hdescent : baseEnd_1506029 < baseStart_1506029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1506029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1506031 : List Nat := [1, 1, 2, 1, 5, 2, 4, 1, 5]
def baseStart_1506031 : Nat := 118140960795 + 1506031 * 2 ^ 59
def prefixEnd_1506031 : Nat := 4983230072969 + 3 ^ 40 * 1506031 * 2
def baseEnd_1506031 : Nat := 171848396349222751219199

theorem tailTrace_1506031 : CollatzResearch.WordTrace tailWord_1506031 prefixEnd_1506031 171848396349222751219199 := by
  unfold tailWord_1506031
  simp only [CollatzResearch.WordTrace]
  refine ⟨54929463206914371462405947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36619642137942914308270631 54929463206914371462405947)
  ·
    refine ⟨82394194810371557193608921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54929463206914371462405947 82394194810371557193608921)
    ·
      refine ⟨61795646107778667895206691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82394194810371557193608921 61795646107778667895206691)
      ·
        refine ⟨92693469161668001842810037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61795646107778667895206691 92693469161668001842810037)
        ·
          refine ⟨8690012733906375172763441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 92693469161668001842810037 8690012733906375172763441)
          ·
            refine ⟨6517509550429781379572581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8690012733906375172763441 6517509550429781379572581)
            ·
              refine ⟨1222033040705584008669859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6517509550429781379572581 1222033040705584008669859)
              ·
                refine ⟨1833049561058376013004789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1222033040705584008669859 1833049561058376013004789)
                ·
                  refine ⟨171848396349222751219199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1833049561058376013004789 171848396349222751219199)
                  ·
                    rfl

theorem cell22_1506031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 4, 1, 5].length) (baseStart_1506031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1506031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1506031 prefixEnd_1506031 := by exact prefixLift 1506031
  have htrace : WordTrace (prefixWord ++ tailWord_1506031) baseStart_1506031 baseEnd_1506031 := by
    simpa [prefixWord, tailWord_1506031, baseEnd_1506031] using wordTrace_append hprefix tailTrace_1506031
  have hstable : (prefixWord ++ tailWord_1506031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1506031).length < 2 ^ (prefixWord ++ tailWord_1506031).sum := by decide
  have hdescent : baseEnd_1506031 < baseStart_1506031 := by decide
  rcases family_descends (prefixWord ++ tailWord_1506031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1506074 : List Nat := [3, 1, 1, 3, 2, 1, 1, 2, 3, 5]
def baseStart_1506074 : Nat := 118140960795 + 1506074 * 2 ^ 59
def prefixEnd_1506074 : Nat := 4983230072969 + 3 ^ 40 * 1506074 * 2
def baseEnd_1506074 : Nat := 515559908826430474832465

theorem tailTrace_1506074 : CollatzResearch.WordTrace tailWord_1506074 prefixEnd_1506074 515559908826430474832465 := by
  unfold tailWord_1506074
  simp only [CollatzResearch.WordTrace]
  refine ⟨13732757886439647451555319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36620687697172393204147517 13732757886439647451555319)
  ·
    refine ⟨20599136829659471177332979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13732757886439647451555319 20599136829659471177332979)
    ·
      refine ⟨30898705244489206765999469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20599136829659471177332979 30898705244489206765999469)
      ·
        refine ⟨11587014466683452537249801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30898705244489206765999469 11587014466683452537249801)
        ·
          refine ⟨8690260850012589402937351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11587014466683452537249801 8690260850012589402937351)
          ·
            refine ⟨13035391275018884104406027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8690260850012589402937351 13035391275018884104406027)
            ·
              refine ⟨19553086912528326156609041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13035391275018884104406027 19553086912528326156609041)
              ·
                refine ⟨14664815184396244617456781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19553086912528326156609041 14664815184396244617456781)
                ·
                  refine ⟨5499305694148591731546293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14664815184396244617456781 5499305694148591731546293)
                  ·
                    refine ⟨515559908826430474832465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5499305694148591731546293 515559908826430474832465)
                    ·
                      rfl

theorem cell22_1506074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 2, 3, 5].length) (baseStart_1506074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1506074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1506074 prefixEnd_1506074 := by exact prefixLift 1506074
  have htrace : WordTrace (prefixWord ++ tailWord_1506074) baseStart_1506074 baseEnd_1506074 := by
    simpa [prefixWord, tailWord_1506074, baseEnd_1506074] using wordTrace_append hprefix tailTrace_1506074
  have hstable : (prefixWord ++ tailWord_1506074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1506074).length < 2 ^ (prefixWord ++ tailWord_1506074).sum := by decide
  have hdescent : baseEnd_1506074 < baseStart_1506074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1506074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1506106 : List Nat := [3, 1, 1, 1, 6, 1, 1, 1, 1, 6]
def baseStart_1506106 : Nat := 118140960795 + 1506106 * 2 ^ 59
def prefixEnd_1506106 : Nat := 4983230072969 + 3 ^ 40 * 1506106 * 2
def baseEnd_1506106 : Nat := 515570863080393058032367

theorem tailTrace_1506106 : CollatzResearch.WordTrace tailWord_1506106 prefixEnd_1506106 515570863080393058032367 := by
  unfold tailWord_1506106
  simp only [CollatzResearch.WordTrace]
  refine ⟨13733049670410664817846543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36621465787761772847590781 13733049670410664817846543)
  ·
    refine ⟨20599574505615997226769815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13733049670410664817846543 20599574505615997226769815)
    ·
      refine ⟨30899361758423995840154723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20599574505615997226769815 30899361758423995840154723)
      ·
        refine ⟨46349042637635993760232085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30899361758423995840154723 46349042637635993760232085)
        ·
          refine ⟨2172611373639187207510879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 46349042637635993760232085 2172611373639187207510879)
          ·
            refine ⟨3258917060458780811266319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2172611373639187207510879 3258917060458780811266319)
            ·
              refine ⟨4888375590688171216899479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3258917060458780811266319 4888375590688171216899479)
              ·
                refine ⟨7332563386032256825349219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4888375590688171216899479 7332563386032256825349219)
                ·
                  refine ⟨10998845079048385238023829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7332563386032256825349219 10998845079048385238023829)
                  ·
                    refine ⟨515570863080393058032367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10998845079048385238023829 515570863080393058032367)
                    ·
                      rfl

theorem cell22_1506106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 1, 1, 6].length) (baseStart_1506106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1506106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1506106 prefixEnd_1506106 := by exact prefixLift 1506106
  have htrace : WordTrace (prefixWord ++ tailWord_1506106) baseStart_1506106 baseEnd_1506106 := by
    simpa [prefixWord, tailWord_1506106, baseEnd_1506106] using wordTrace_append hprefix tailTrace_1506106
  have hstable : (prefixWord ++ tailWord_1506106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1506106).length < 2 ^ (prefixWord ++ tailWord_1506106).sum := by decide
  have hdescent : baseEnd_1506106 < baseStart_1506106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1506106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1506110 : List Nat := [4, 2, 1, 2, 3, 1, 2, 3, 4]
def baseStart_1506110 : Nat := 118140960795 + 1506110 * 2 ^ 59
def prefixEnd_1506110 : Nat := 4983230072969 + 3 ^ 40 * 1506110 * 2
def baseEnd_1506110 : Nat := 171857410787379460310785

theorem tailTrace_1506110 : CollatzResearch.WordTrace tailWord_1506110 prefixEnd_1506110 171857410787379460310785 := by
  unfold tailWord_1506110
  simp only [CollatzResearch.WordTrace]
  refine ⟨6866543071703520994316473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36621563049085445303021189 6866543071703520994316473)
  ·
    refine ⟨5149907303777640745737355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6866543071703520994316473 5149907303777640745737355)
    ·
      refine ⟨7724860955666461118606033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5149907303777640745737355 7724860955666461118606033)
      ·
        refine ⟨5793645716749845838954525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7724860955666461118606033 5793645716749845838954525)
        ·
          refine ⟨2172617143781192189607947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5793645716749845838954525 2172617143781192189607947)
          ·
            refine ⟨3258925715671788284411921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2172617143781192189607947 3258925715671788284411921)
            ·
              refine ⟨2444194286753841213308941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3258925715671788284411921 2444194286753841213308941)
              ·
                refine ⟨916572857532690454990853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2444194286753841213308941 916572857532690454990853)
                ·
                  refine ⟨171857410787379460310785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 916572857532690454990853 171857410787379460310785)
                  ·
                    rfl

theorem cell22_1506110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 2, 3, 4].length) (baseStart_1506110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1506110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1506110 prefixEnd_1506110 := by exact prefixLift 1506110
  have htrace : WordTrace (prefixWord ++ tailWord_1506110) baseStart_1506110 baseEnd_1506110 := by
    simpa [prefixWord, tailWord_1506110, baseEnd_1506110] using wordTrace_append hprefix tailTrace_1506110
  have hstable : (prefixWord ++ tailWord_1506110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1506110).length < 2 ^ (prefixWord ++ tailWord_1506110).sum := by decide
  have hdescent : baseEnd_1506110 < baseStart_1506110 := by decide
  rcases family_descends (prefixWord ++ tailWord_1506110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1506125 : List Nat := [1, 6, 1, 2, 2, 1, 1, 1, 4, 3]
def baseStart_1506125 : Nat := 118140960795 + 1506125 * 2 ^ 59
def prefixEnd_1506125 : Nat := 4983230072969 + 3 ^ 40 * 1506125 * 2
def baseEnd_1506125 : Nat := 515577367168683341807309

theorem tailTrace_1506125 : CollatzResearch.WordTrace tailWord_1506125 prefixEnd_1506125 515577367168683341807309 := by
  unfold tailWord_1506125
  simp only [CollatzResearch.WordTrace]
  refine ⟨54932891668573825516327829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36621927779049217010885219 54932891668573825516327829)
  ·
    refine ⟨2574979296964398071077867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 54932891668573825516327829 2574979296964398071077867)
    ·
      refine ⟨3862468945446597106616801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2574979296964398071077867 3862468945446597106616801)
      ·
        refine ⟨2896851709084947829962601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3862468945446597106616801 2896851709084947829962601)
        ·
          refine ⟨2172638781813710872471951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2896851709084947829962601 2172638781813710872471951)
          ·
            refine ⟨3258958172720566308707927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2172638781813710872471951 3258958172720566308707927)
            ·
              refine ⟨4888437259080849463061891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3258958172720566308707927 4888437259080849463061891)
              ·
                refine ⟨7332655888621274194592837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4888437259080849463061891 7332655888621274194592837)
                ·
                  refine ⟨1374872979116488911486157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7332655888621274194592837 1374872979116488911486157)
                  ·
                    refine ⟨515577367168683341807309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1374872979116488911486157 515577367168683341807309)
                    ·
                      rfl

theorem cell22_1506125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 1, 4, 3].length) (baseStart_1506125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1506125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1506125 prefixEnd_1506125 := by exact prefixLift 1506125
  have htrace : WordTrace (prefixWord ++ tailWord_1506125) baseStart_1506125 baseEnd_1506125 := by
    simpa [prefixWord, tailWord_1506125, baseEnd_1506125] using wordTrace_append hprefix tailTrace_1506125
  have hstable : (prefixWord ++ tailWord_1506125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1506125).length < 2 ^ (prefixWord ++ tailWord_1506125).sum := by decide
  have hdescent : baseEnd_1506125 < baseStart_1506125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1506125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1506260 : List Nat := [2, 4, 1, 2, 1, 2, 2, 3, 2, 3]
def baseStart_1506260 : Nat := 118140960795 + 1506260 * 2 ^ 59
def prefixEnd_1506260 : Nat := 4983230072969 + 3 ^ 40 * 1506260 * 2
def baseEnd_1506260 : Nat := 515623580427587989681895

theorem tailTrace_1506260 : CollatzResearch.WordTrace tailWord_1506260 prefixEnd_1506260 515623580427587989681895 := by
  unfold tailWord_1506260
  simp only [CollatzResearch.WordTrace]
  refine ⟨27468907761542371786246117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36625210348723162381661489 27468907761542371786246117)
  ·
    refine ⟨5150420205289194709921147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27468907761542371786246117 5150420205289194709921147)
    ·
      refine ⟨7725630307933792064881721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5150420205289194709921147 7725630307933792064881721)
      ·
        refine ⟨5794222730950344048661291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7725630307933792064881721 5794222730950344048661291)
        ·
          refine ⟨8691334096425516072991937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5794222730950344048661291 8691334096425516072991937)
          ·
            refine ⟨6518500572319137054743953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8691334096425516072991937 6518500572319137054743953)
            ·
              refine ⟨4888875429239352791057965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6518500572319137054743953 4888875429239352791057965)
              ·
                refine ⟨1833328285964757296646737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4888875429239352791057965 1833328285964757296646737)
                ·
                  refine ⟨1374996214473567972485053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1833328285964757296646737 1374996214473567972485053)
                  ·
                    refine ⟨515623580427587989681895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1374996214473567972485053 515623580427587989681895)
                    ·
                      rfl

theorem cell22_1506260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 3, 2, 3].length) (baseStart_1506260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1506260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1506260 prefixEnd_1506260 := by exact prefixLift 1506260
  have htrace : WordTrace (prefixWord ++ tailWord_1506260) baseStart_1506260 baseEnd_1506260 := by
    simpa [prefixWord, tailWord_1506260, baseEnd_1506260] using wordTrace_append hprefix tailTrace_1506260
  have hstable : (prefixWord ++ tailWord_1506260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1506260).length < 2 ^ (prefixWord ++ tailWord_1506260).sum := by decide
  have hdescent : baseEnd_1506260 < baseStart_1506260 := by decide
  rcases family_descends (prefixWord ++ tailWord_1506260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1506305 : List Nat := [1, 2, 4, 1, 2, 3, 2, 1, 3, 3]
def baseStart_1506305 : Nat := 118140960795 + 1506305 * 2 ^ 59
def prefixEnd_1506305 : Nat := 4983230072969 + 3 ^ 40 * 1506305 * 2
def baseEnd_1506305 : Nat := 515638984847222872306757

theorem tailTrace_1506305 : CollatzResearch.WordTrace tailWord_1506305 prefixEnd_1506305 515638984847222872306757 := by
  unfold tailWord_1506305
  simp only [CollatzResearch.WordTrace]
  refine ⟨54939456807921716257880369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36626304538614477505253579 54939456807921716257880369)
  ·
    refine ⟨41204592605941287193410277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54939456807921716257880369 41204592605941287193410277)
    ·
      refine ⟨7725861113613991348764427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41204592605941287193410277 7725861113613991348764427)
      ·
        refine ⟨11588791670420987023146641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7725861113613991348764427 11588791670420987023146641)
        ·
          refine ⟨8691593752815740267359981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11588791670420987023146641 8691593752815740267359981)
          ·
            refine ⟨3259347657305902600259993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8691593752815740267359981 3259347657305902600259993)
            ·
              refine ⟨2444510742979426950194995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3259347657305902600259993 2444510742979426950194995)
              ·
                refine ⟨3666766114469140425292493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2444510742979426950194995 3666766114469140425292493)
                ·
                  refine ⟨1375037292925927659484685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3666766114469140425292493 1375037292925927659484685)
                  ·
                    refine ⟨515638984847222872306757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1375037292925927659484685 515638984847222872306757)
                    ·
                      rfl

theorem cell22_1506305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 2, 1, 3, 3].length) (baseStart_1506305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1506305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1506305 prefixEnd_1506305 := by exact prefixLift 1506305
  have htrace : WordTrace (prefixWord ++ tailWord_1506305) baseStart_1506305 baseEnd_1506305 := by
    simpa [prefixWord, tailWord_1506305, baseEnd_1506305] using wordTrace_append hprefix tailTrace_1506305
  have hstable : (prefixWord ++ tailWord_1506305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1506305).length < 2 ^ (prefixWord ++ tailWord_1506305).sum := by decide
  have hdescent : baseEnd_1506305 < baseStart_1506305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1506305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1506331 : List Nat := [1, 1, 1, 1, 1, 1, 3, 2, 7, 4]
def baseStart_1506331 : Nat := 118140960795 + 1506331 * 2 ^ 59
def prefixEnd_1506331 : Nat := 4983230072969 + 3 ^ 40 * 1506331 * 2
def baseEnd_1506331 : Nat := 515647885178567471156677

theorem tailTrace_1506331 : CollatzResearch.WordTrace tailWord_1506331 prefixEnd_1506331 515647885178567471156677 := by
  unfold tailWord_1506331
  simp only [CollatzResearch.WordTrace]
  refine ⟨54940405105827522698326847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36626936737218348465551231 54940405105827522698326847)
  ·
    refine ⟨82410607658741284047490271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54940405105827522698326847 82410607658741284047490271)
    ·
      refine ⟨123615911488111926071235407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82410607658741284047490271 123615911488111926071235407)
      ·
        refine ⟨185423867232167889106853111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123615911488111926071235407 185423867232167889106853111)
        ·
          refine ⟨278135800848251833660279667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185423867232167889106853111 278135800848251833660279667)
          ·
            refine ⟨417203701272377750490419501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 278135800848251833660279667 417203701272377750490419501)
            ·
              refine ⟨156451387977141656433907313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 417203701272377750490419501 156451387977141656433907313)
              ·
                refine ⟨117338540982856242325430485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 156451387977141656433907313 117338540982856242325430485)
                ·
                  refine ⟨2750122054285693179502277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 117338540982856242325430485 2750122054285693179502277)
                  ·
                    refine ⟨515647885178567471156677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2750122054285693179502277 515647885178567471156677)
                    ·
                      rfl

theorem cell22_1506331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 7, 4].length) (baseStart_1506331 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1506331 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1506331 prefixEnd_1506331 := by exact prefixLift 1506331
  have htrace : WordTrace (prefixWord ++ tailWord_1506331) baseStart_1506331 baseEnd_1506331 := by
    simpa [prefixWord, tailWord_1506331, baseEnd_1506331] using wordTrace_append hprefix tailTrace_1506331
  have hstable : (prefixWord ++ tailWord_1506331).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1506331).length < 2 ^ (prefixWord ++ tailWord_1506331).sum := by decide
  have hdescent : baseEnd_1506331 < baseStart_1506331 := by decide
  rcases family_descends (prefixWord ++ tailWord_1506331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1506348 : List Nat := [2, 2, 1, 1, 1, 2, 3, 5, 1, 4]
def baseStart_1506348 : Nat := 118140960795 + 1506348 * 2 ^ 59
def prefixEnd_1506348 : Nat := 4983230072969 + 3 ^ 40 * 1506348 * 2
def baseEnd_1506348 : Nat := 515653704625985093481625

theorem tailTrace_1506348 : CollatzResearch.WordTrace tailWord_1506348 prefixEnd_1506348 515653704625985093481625 := by
  unfold tailWord_1506348
  simp only [CollatzResearch.WordTrace]
  refine ⟨27470512573382967300847849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36627350097843956401130465 27470512573382967300847849)
  ·
    refine ⟨20602884430037225475635887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27470512573382967300847849 20602884430037225475635887)
    ·
      refine ⟨30904326645055838213453831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20602884430037225475635887 30904326645055838213453831)
      ·
        refine ⟨46356489967583757320180747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30904326645055838213453831 46356489967583757320180747)
        ·
          refine ⟨69534734951375635980271121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46356489967583757320180747 69534734951375635980271121)
          ·
            refine ⟨52151051213531726985203341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69534734951375635980271121 52151051213531726985203341)
            ·
              refine ⟨19556644205074397619451253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52151051213531726985203341 19556644205074397619451253)
              ·
                refine ⟨1833435394225724776823555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19556644205074397619451253 1833435394225724776823555)
                ·
                  refine ⟨2750153091338587165235333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1833435394225724776823555 2750153091338587165235333)
                  ·
                    refine ⟨515653704625985093481625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2750153091338587165235333 515653704625985093481625)
                    ·
                      rfl

theorem cell22_1506348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 4].length) (baseStart_1506348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1506348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1506348 prefixEnd_1506348 := by exact prefixLift 1506348
  have htrace : WordTrace (prefixWord ++ tailWord_1506348) baseStart_1506348 baseEnd_1506348 := by
    simpa [prefixWord, tailWord_1506348, baseEnd_1506348] using wordTrace_append hprefix tailTrace_1506348
  have hstable : (prefixWord ++ tailWord_1506348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1506348).length < 2 ^ (prefixWord ++ tailWord_1506348).sum := by decide
  have hdescent : baseEnd_1506348 < baseStart_1506348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1506348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1506356 : List Nat := [2, 5, 1, 2, 1, 2, 3, 2, 1, 3]
def baseStart_1506356 : Nat := 118140960795 + 1506356 * 2 ^ 59
def prefixEnd_1506356 : Nat := 4983230072969 + 3 ^ 40 * 1506356 * 2
def baseEnd_1506356 : Nat := 515656443189475739281601

theorem tailTrace_1506356 : CollatzResearch.WordTrace tailWord_1506356 prefixEnd_1506356 515656443189475739281601 := by
  unfold tailWord_1506356
  simp only [CollatzResearch.WordTrace]
  refine ⟨27470658465368475983993461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36627544620491301311991281 27470658465368475983993461)
  ·
    refine ⟨2575374231128294623499387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27470658465368475983993461 2575374231128294623499387)
    ·
      refine ⟨3863061346692441935249081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2575374231128294623499387 3863061346692441935249081)
      ·
        refine ⟨2897296010019331451436811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3863061346692441935249081 2897296010019331451436811)
        ·
          refine ⟨4345944015028997177155217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2897296010019331451436811 4345944015028997177155217)
          ·
            refine ⟨3259458011271747882866413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4345944015028997177155217 3259458011271747882866413)
            ·
              refine ⟨1222296754226905456074905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3259458011271747882866413 1222296754226905456074905)
              ·
                refine ⟨916722565670179092056179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1222296754226905456074905 916722565670179092056179)
                ·
                  refine ⟨1375083848505268638084269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 916722565670179092056179 1375083848505268638084269)
                  ·
                    refine ⟨515656443189475739281601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1375083848505268638084269 515656443189475739281601)
                    ·
                      rfl

theorem cell22_1506356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 3, 2, 1, 3].length) (baseStart_1506356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1506356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1506356 prefixEnd_1506356 := by exact prefixLift 1506356
  have htrace : WordTrace (prefixWord ++ tailWord_1506356) baseStart_1506356 baseEnd_1506356 := by
    simpa [prefixWord, tailWord_1506356, baseEnd_1506356] using wordTrace_append hprefix tailTrace_1506356
  have hstable : (prefixWord ++ tailWord_1506356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1506356).length < 2 ^ (prefixWord ++ tailWord_1506356).sum := by decide
  have hdescent : baseEnd_1506356 < baseStart_1506356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1506356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1506369 : List Nat := [1, 2, 5, 1, 4, 1, 2, 1, 5]
def baseStart_1506369 : Nat := 118140960795 + 1506369 * 2 ^ 59
def prefixEnd_1506369 : Nat := 4983230072969 + 3 ^ 40 * 1506369 * 2
def baseEnd_1506369 : Nat := 171886964451716012902187

theorem tailTrace_1506369 : CollatzResearch.WordTrace tailWord_1506369 prefixEnd_1506369 171886964451716012902187 := by
  unfold tailWord_1506369
  simp only [CollatzResearch.WordTrace]
  refine ⟨54941791079689855188210161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36627860719793236792140107 54941791079689855188210161)
  ·
    refine ⟨41206343309767391391157621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54941791079689855188210161 41206343309767391391157621)
    ·
      refine ⟨3863094685290692942921027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 41206343309767391391157621 3863094685290692942921027)
      ·
        refine ⟨5794642027936039414381541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3863094685290692942921027 5794642027936039414381541)
        ·
          refine ⟨1086495380238007390196539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5794642027936039414381541 1086495380238007390196539)
          ·
            refine ⟨1629743070357011085294809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1086495380238007390196539 1629743070357011085294809)
            ·
              refine ⟨1222307302767758313971107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1629743070357011085294809 1222307302767758313971107)
              ·
                refine ⟨1833460954151637470956661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1222307302767758313971107 1833460954151637470956661)
                ·
                  refine ⟨171886964451716012902187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1833460954151637470956661 171886964451716012902187)
                  ·
                    rfl

theorem cell22_1506369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 2, 1, 5].length) (baseStart_1506369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1506369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1506369 prefixEnd_1506369 := by exact prefixLift 1506369
  have htrace : WordTrace (prefixWord ++ tailWord_1506369) baseStart_1506369 baseEnd_1506369 := by
    simpa [prefixWord, tailWord_1506369, baseEnd_1506369] using wordTrace_append hprefix tailTrace_1506369
  have hstable : (prefixWord ++ tailWord_1506369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1506369).length < 2 ^ (prefixWord ++ tailWord_1506369).sum := by decide
  have hdescent : baseEnd_1506369 < baseStart_1506369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1506369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1506408 : List Nat := [2, 1, 4, 4, 11]
def baseStart_1506408 : Nat := 118140960795 + 1506408 * 2 ^ 59
def prefixEnd_1506408 : Nat := 4983230072969 + 3 ^ 40 * 1506408 * 2
def baseEnd_1506408 : Nat := 2122116229844300152187

theorem tailTrace_1506408 : CollatzResearch.WordTrace tailWord_1506408 prefixEnd_1506408 2122116229844300152187 := by
  unfold tailWord_1506408
  simp only [CollatzResearch.WordTrace]
  refine ⟨27471606763274282424439939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36628809017699043232586585 27471606763274282424439939)
  ·
    refine ⟨41207410144911423636659909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27471606763274282424439939 41207410144911423636659909)
    ·
      refine ⟨7726389402170891931873733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41207410144911423636659909 7726389402170891931873733)
      ·
        refine ⟨1448698012907042237226325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7726389402170891931873733 1448698012907042237226325)
        ·
          refine ⟨2122116229844300152187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 1448698012907042237226325 2122116229844300152187)
          ·
            rfl

theorem cell22_1506408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 11].length) (baseStart_1506408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1506408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1506408 prefixEnd_1506408 := by exact prefixLift 1506408
  have htrace : WordTrace (prefixWord ++ tailWord_1506408) baseStart_1506408 baseEnd_1506408 := by
    simpa [prefixWord, tailWord_1506408, baseEnd_1506408] using wordTrace_append hprefix tailTrace_1506408
  have hstable : (prefixWord ++ tailWord_1506408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1506408).length < 2 ^ (prefixWord ++ tailWord_1506408).sum := by decide
  have hdescent : baseEnd_1506408 < baseStart_1506408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1506408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1506410 : List Nat := [3, 1, 3, 2, 2, 1, 2, 2, 2, 4]
def baseStart_1506410 : Nat := 118140960795 + 1506410 * 2 ^ 59
def prefixEnd_1506410 : Nat := 4983230072969 + 3 ^ 40 * 1506410 * 2
def baseEnd_1506410 : Nat := 515674928493037598431435

theorem tailTrace_1506410 : CollatzResearch.WordTrace tailWord_1506410 prefixEnd_1506410 515674928493037598431435 := by
  unfold tailWord_1506410
  simp only [CollatzResearch.WordTrace]
  refine ⟨13735821618135329797613171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36628857648360879460301789 13735821618135329797613171)
  ·
    refine ⟨20603732427202994696419757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13735821618135329797613171 20603732427202994696419757)
    ·
      refine ⟨7726399660201123011157409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20603732427202994696419757 7726399660201123011157409)
      ·
        refine ⟨5794799745150842258368057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7726399660201123011157409 5794799745150842258368057)
        ·
          refine ⟨4346099808863131693776043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5794799745150842258368057 4346099808863131693776043)
          ·
            refine ⟨6519149713294697540664065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4346099808863131693776043 6519149713294697540664065)
            ·
              refine ⟨4889362284971023155498049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6519149713294697540664065 4889362284971023155498049)
              ·
                refine ⟨3667021713728267366623537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4889362284971023155498049 3667021713728267366623537)
                ·
                  refine ⟨2750266285296200524967653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3667021713728267366623537 2750266285296200524967653)
                  ·
                    refine ⟨515674928493037598431435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2750266285296200524967653 515674928493037598431435)
                    ·
                      rfl

theorem cell22_1506410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 2, 2, 4].length) (baseStart_1506410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1506410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1506410 prefixEnd_1506410 := by exact prefixLift 1506410
  have htrace : WordTrace (prefixWord ++ tailWord_1506410) baseStart_1506410 baseEnd_1506410 := by
    simpa [prefixWord, tailWord_1506410, baseEnd_1506410] using wordTrace_append hprefix tailTrace_1506410
  have hstable : (prefixWord ++ tailWord_1506410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1506410).length < 2 ^ (prefixWord ++ tailWord_1506410).sum := by decide
  have hdescent : baseEnd_1506410 < baseStart_1506410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1506410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1506414 : List Nat := [4, 1, 2, 2, 1, 4, 2, 2, 4]
def baseStart_1506414 : Nat := 118140960795 + 1506414 * 2 ^ 59
def prefixEnd_1506414 : Nat := 4983230072969 + 3 ^ 40 * 1506414 * 2
def baseEnd_1506414 : Nat := 171892099258260973777141

theorem tailTrace_1506414 : CollatzResearch.WordTrace tailWord_1506414 prefixEnd_1506414 171892099258260973777141 := by
  unfold tailWord_1506414
  simp only [CollatzResearch.WordTrace]
  refine ⟨6867929045565853484199787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36628954909684551915732197 6867929045565853484199787)
  ·
    refine ⟨10301893568348780226299681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6867929045565853484199787 10301893568348780226299681)
    ·
      refine ⟨7726420176261585169724761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10301893568348780226299681 7726420176261585169724761)
      ·
        refine ⟨5794815132196188877293571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7726420176261585169724761 5794815132196188877293571)
        ·
          refine ⟨8692222698294283315940357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5794815132196188877293571 8692222698294283315940357)
          ·
            refine ⟨1629791755930178121738817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8692222698294283315940357 1629791755930178121738817)
            ·
              refine ⟨1222343816947633591304113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1629791755930178121738817 1222343816947633591304113)
              ·
                refine ⟨916757862710725193478085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1222343816947633591304113 916757862710725193478085)
                ·
                  refine ⟨171892099258260973777141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 916757862710725193478085 171892099258260973777141)
                  ·
                    rfl

theorem cell22_1506414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 2, 2, 4].length) (baseStart_1506414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1506414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1506414 prefixEnd_1506414 := by exact prefixLift 1506414
  have htrace : WordTrace (prefixWord ++ tailWord_1506414) baseStart_1506414 baseEnd_1506414 := by
    simpa [prefixWord, tailWord_1506414, baseEnd_1506414] using wordTrace_append hprefix tailTrace_1506414
  have hstable : (prefixWord ++ tailWord_1506414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1506414).length < 2 ^ (prefixWord ++ tailWord_1506414).sum := by decide
  have hdescent : baseEnd_1506414 < baseStart_1506414 := by decide
  rcases family_descends (prefixWord ++ tailWord_1506414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1506425 : List Nat := [1, 2, 1, 3, 5, 2, 1, 7]
def baseStart_1506425 : Nat := 118140960795 + 1506425 * 2 ^ 59
def prefixEnd_1506425 : Nat := 4983230072969 + 3 ^ 40 * 1506425 * 2
def baseEnd_1506425 : Nat := 57297784811064728811821

theorem tailTrace_1506425 : CollatzResearch.WordTrace tailWord_1506425 prefixEnd_1506425 57297784811064728811821 := by
  unfold tailWord_1506425
  simp only [CollatzResearch.WordTrace]
  refine ⟨54943833567486976752248729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36629222378324651168165819 54943833567486976752248729)
  ·
    refine ⟨41207875175615232564186547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54943833567486976752248729 41207875175615232564186547)
    ·
      refine ⟨61811812763422848846279821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41207875175615232564186547 61811812763422848846279821)
      ·
        refine ⟨23179429786283568317354933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61811812763422848846279821 23179429786283568317354933)
        ·
          refine ⟨2173071542464084529752025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23179429786283568317354933 2173071542464084529752025)
          ·
            refine ⟨1629803656848063397314019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2173071542464084529752025 1629803656848063397314019)
            ·
              refine ⟨2444705485272095095971029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1629803656848063397314019 2444705485272095095971029)
              ·
                refine ⟨57297784811064728811821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2444705485272095095971029 57297784811064728811821)
                ·
                  rfl

theorem cell22_1506425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 1, 7].length) (baseStart_1506425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1506425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1506425 prefixEnd_1506425 := by exact prefixLift 1506425
  have htrace : WordTrace (prefixWord ++ tailWord_1506425) baseStart_1506425 baseEnd_1506425 := by
    simpa [prefixWord, tailWord_1506425, baseEnd_1506425] using wordTrace_append hprefix tailTrace_1506425
  have hstable : (prefixWord ++ tailWord_1506425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1506425).length < 2 ^ (prefixWord ++ tailWord_1506425).sum := by decide
  have hdescent : baseEnd_1506425 < baseStart_1506425 := by decide
  rcases family_descends (prefixWord ++ tailWord_1506425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1506474 : List Nat := [3, 1, 5, 1, 1, 2, 2, 1, 3, 3]
def baseStart_1506474 : Nat := 118140960795 + 1506474 * 2 ^ 59
def prefixEnd_1506474 : Nat := 4983230072969 + 3 ^ 40 * 1506474 * 2
def baseEnd_1506474 : Nat := 515696837000962764831239

theorem tailTrace_1506474 : CollatzResearch.WordTrace tailWord_1506474 prefixEnd_1506474 515696837000962764831239 := by
  unfold tailWord_1506474
  simp only [CollatzResearch.WordTrace]
  refine ⟨13736405186077364530195619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36630413829539638747188317 13736405186077364530195619)
  ·
    refine ⟨20604607779116046795293429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13736405186077364530195619 20604607779116046795293429)
    ·
      refine ⟨1931681979292129387058759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20604607779116046795293429 1931681979292129387058759)
      ·
        refine ⟨2897522968938194080588139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1931681979292129387058759 2897522968938194080588139)
        ·
          refine ⟨4346284453407291120882209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2897522968938194080588139 4346284453407291120882209)
          ·
            refine ⟨3259713340055468340661657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4346284453407291120882209 3259713340055468340661657)
            ·
              refine ⟨2444785005041601255496243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3259713340055468340661657 2444785005041601255496243)
              ·
                refine ⟨3667177507562401883244365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2444785005041601255496243 3667177507562401883244365)
                ·
                  refine ⟨1375191565335900706216637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3667177507562401883244365 1375191565335900706216637)
                  ·
                    refine ⟨515696837000962764831239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1375191565335900706216637 515696837000962764831239)
                    ·
                      rfl

theorem cell22_1506474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_1506474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1506474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1506474 prefixEnd_1506474 := by exact prefixLift 1506474
  have htrace : WordTrace (prefixWord ++ tailWord_1506474) baseStart_1506474 baseEnd_1506474 := by
    simpa [prefixWord, tailWord_1506474, baseEnd_1506474] using wordTrace_append hprefix tailTrace_1506474
  have hstable : (prefixWord ++ tailWord_1506474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1506474).length < 2 ^ (prefixWord ++ tailWord_1506474).sum := by decide
  have hdescent : baseEnd_1506474 < baseStart_1506474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1506474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1506483 : List Nat := [1, 1, 1, 2, 3, 2, 2, 1, 5, 4]
def baseStart_1506483 : Nat := 118140960795 + 1506483 * 2 ^ 59
def prefixEnd_1506483 : Nat := 4983230072969 + 3 ^ 40 * 1506483 * 2
def baseEnd_1506483 : Nat := 515699917884889741356211

theorem tailTrace_1506483 : CollatzResearch.WordTrace tailWord_1506483 prefixEnd_1506483 515699917884889741356211 := by
  unfold tailWord_1506483
  simp only [CollatzResearch.WordTrace]
  refine ⟨54945949001276852657860103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36630632667517901771906735 54945949001276852657860103)
  ·
    refine ⟨82418923501915278986790155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54945949001276852657860103 82418923501915278986790155)
    ·
      refine ⟨123628385252872918480185233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82418923501915278986790155 123628385252872918480185233)
      ·
        refine ⟨92721288939654688860138925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123628385252872918480185233 92721288939654688860138925)
        ·
          refine ⟨34770483352370508322552097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92721288939654688860138925 34770483352370508322552097)
          ·
            refine ⟨26077862514277881241914073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34770483352370508322552097 26077862514277881241914073)
            ·
              refine ⟨19558396885708410931435555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26077862514277881241914073 19558396885708410931435555)
              ·
                refine ⟨29337595328562616397153333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19558396885708410931435555 29337595328562616397153333)
                ·
                  refine ⟨2750399562052745287233125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29337595328562616397153333 2750399562052745287233125)
                  ·
                    refine ⟨515699917884889741356211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2750399562052745287233125 515699917884889741356211)
                    ·
                      rfl

theorem cell22_1506483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 5, 4].length) (baseStart_1506483 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1506483 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1506483 prefixEnd_1506483 := by exact prefixLift 1506483
  have htrace : WordTrace (prefixWord ++ tailWord_1506483) baseStart_1506483 baseEnd_1506483 := by
    simpa [prefixWord, tailWord_1506483, baseEnd_1506483] using wordTrace_append hprefix tailTrace_1506483
  have hstable : (prefixWord ++ tailWord_1506483).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1506483).length < 2 ^ (prefixWord ++ tailWord_1506483).sum := by decide
  have hdescent : baseEnd_1506483 < baseStart_1506483 := by decide
  rcases family_descends (prefixWord ++ tailWord_1506483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1506513 : List Nat := [1, 2, 2, 1, 2, 2, 1, 3, 3, 5]
def baseStart_1506513 : Nat := 118140960795 + 1506513 * 2 ^ 59
def prefixEnd_1506513 : Nat := 4983230072969 + 3 ^ 40 * 1506513 * 2
def baseEnd_1506513 : Nat := 515710187497979663106119

theorem tailTrace_1506513 : CollatzResearch.WordTrace tailWord_1506513 prefixEnd_1506513 515710187497979663106119 := by
  unfold tailWord_1506513
  simp only [CollatzResearch.WordTrace]
  refine ⟨54947043191168167781452193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36631362127445445187634795 54947043191168167781452193)
  ·
    refine ⟨41210282393376125836089145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54947043191168167781452193 41210282393376125836089145)
    ·
      refine ⟨30907711795032094377066859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41210282393376125836089145 30907711795032094377066859)
      ·
        refine ⟨46361567692548141565600289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30907711795032094377066859 46361567692548141565600289)
        ·
          refine ⟨34771175769411106174200217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46361567692548141565600289 34771175769411106174200217)
          ·
            refine ⟨26078381827058329630650163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34771175769411106174200217 26078381827058329630650163)
            ·
              refine ⟨39117572740587494445975245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26078381827058329630650163 39117572740587494445975245)
              ·
                refine ⟨14669089777720310417240717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39117572740587494445975245 14669089777720310417240717)
                ·
                  refine ⟨5500908666645116406465269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14669089777720310417240717 5500908666645116406465269)
                  ·
                    refine ⟨515710187497979663106119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5500908666645116406465269 515710187497979663106119)
                    ·
                      rfl

theorem cell22_1506513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 3, 3, 5].length) (baseStart_1506513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1506513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1506513 prefixEnd_1506513 := by exact prefixLift 1506513
  have htrace : WordTrace (prefixWord ++ tailWord_1506513) baseStart_1506513 baseEnd_1506513 := by
    simpa [prefixWord, tailWord_1506513, baseEnd_1506513] using wordTrace_append hprefix tailTrace_1506513
  have hstable : (prefixWord ++ tailWord_1506513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1506513).length < 2 ^ (prefixWord ++ tailWord_1506513).sum := by decide
  have hdescent : baseEnd_1506513 < baseStart_1506513 := by decide
  rcases family_descends (prefixWord ++ tailWord_1506513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1506517 : List Nat := [1, 3, 2, 4, 1, 1, 2, 3, 1, 4]
def baseStart_1506517 : Nat := 118140960795 + 1506517 * 2 ^ 59
def prefixEnd_1506517 : Nat := 4983230072969 + 3 ^ 40 * 1506517 * 2
def baseEnd_1506517 : Nat := 515711556779724986006107

theorem tailTrace_1506517 : CollatzResearch.WordTrace tailWord_1506517 prefixEnd_1506517 515711556779724986006107 := by
  unfold tailWord_1506517
  simp only [CollatzResearch.WordTrace]
  refine ⟨54947189083153676464597805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36631459388769117643065203 54947189083153676464597805)
  ·
    refine ⟨20605195906182628674224177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54947189083153676464597805 20605195906182628674224177)
    ·
      refine ⟨15453896929636971505668133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20605195906182628674224177 15453896929636971505668133)
      ·
        refine ⟨2897605674306932157312775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15453896929636971505668133 2897605674306932157312775)
        ·
          refine ⟨4346408511460398235969163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2897605674306932157312775 4346408511460398235969163)
          ·
            refine ⟨6519612767190597353953745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4346408511460398235969163 6519612767190597353953745)
            ·
              refine ⟨4889709575392948015465309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6519612767190597353953745 4889709575392948015465309)
              ·
                refine ⟨1833641090772355505799491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4889709575392948015465309 1833641090772355505799491)
                ·
                  refine ⟨2750461636158533258699237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1833641090772355505799491 2750461636158533258699237)
                  ·
                    refine ⟨515711556779724986006107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2750461636158533258699237 515711556779724986006107)
                    ·
                      rfl

theorem cell22_1506517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 3, 1, 4].length) (baseStart_1506517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1506517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1506517 prefixEnd_1506517 := by exact prefixLift 1506517
  have htrace : WordTrace (prefixWord ++ tailWord_1506517) baseStart_1506517 baseEnd_1506517 := by
    simpa [prefixWord, tailWord_1506517, baseEnd_1506517] using wordTrace_append hprefix tailTrace_1506517
  have hstable : (prefixWord ++ tailWord_1506517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1506517).length < 2 ^ (prefixWord ++ tailWord_1506517).sum := by decide
  have hdescent : baseEnd_1506517 < baseStart_1506517 := by decide
  rcases family_descends (prefixWord ++ tailWord_1506517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1506547 : List Nat := [1, 1, 1, 2, 2, 6, 1, 3, 2, 3]
def baseStart_1506547 : Nat := 118140960795 + 1506547 * 2 ^ 59
def prefixEnd_1506547 : Nat := 4983230072969 + 3 ^ 40 * 1506547 * 2
def baseEnd_1506547 : Nat := 515721826392814907756015

theorem tailTrace_1506547 : CollatzResearch.WordTrace tailWord_1506547 prefixEnd_1506547 515721826392814907756015 := by
  unfold tailWord_1506547
  simp only [CollatzResearch.WordTrace]
  refine ⟨54948283273044991588189895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36632188848696661058793263 54948283273044991588189895)
  ·
    refine ⟨82422424909567487382284843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54948283273044991588189895 82422424909567487382284843)
    ·
      refine ⟨123633637364351231073427265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82422424909567487382284843 123633637364351231073427265)
      ·
        refine ⟨92725228023263423305070449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123633637364351231073427265 92725228023263423305070449)
        ·
          refine ⟨69543921017447567478802837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92725228023263423305070449 69543921017447567478802837)
          ·
            refine ⟨3259871297692854725568883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 69543921017447567478802837 3259871297692854725568883)
            ·
              refine ⟨4889806946539282088353325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3259871297692854725568883 4889806946539282088353325)
              ·
                refine ⟨1833677604952230783132497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4889806946539282088353325 1833677604952230783132497)
                ·
                  refine ⟨1375258203714173087349373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1833677604952230783132497 1375258203714173087349373)
                  ·
                    refine ⟨515721826392814907756015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1375258203714173087349373 515721826392814907756015)
                    ·
                      rfl

theorem cell22_1506547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 3, 2, 3].length) (baseStart_1506547 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1506547 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1506547 prefixEnd_1506547 := by exact prefixLift 1506547
  have htrace : WordTrace (prefixWord ++ tailWord_1506547) baseStart_1506547 baseEnd_1506547 := by
    simpa [prefixWord, tailWord_1506547, baseEnd_1506547] using wordTrace_append hprefix tailTrace_1506547
  have hstable : (prefixWord ++ tailWord_1506547).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1506547).length < 2 ^ (prefixWord ++ tailWord_1506547).sum := by decide
  have hdescent : baseEnd_1506547 < baseStart_1506547 := by decide
  rcases family_descends (prefixWord ++ tailWord_1506547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1506594 : List Nat := [3, 3, 1, 1, 5, 1, 1, 7]
def baseStart_1506594 : Nat := 118140960795 + 1506594 * 2 ^ 59
def prefixEnd_1506594 : Nat := 4983230072969 + 3 ^ 40 * 1506594 * 2
def baseEnd_1506594 : Nat := 57304212828146939092319

theorem tailTrace_1506594 : CollatzResearch.WordTrace tailWord_1506594 prefixEnd_1506594 57304212828146939092319 := by
  unfold tailWord_1506594
  simp only [CollatzResearch.WordTrace]
  refine ⟨13737499375968679653787709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36633331669249812410100557 13737499375968679653787709)
  ·
    refine ⟨5151562265988254870170391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13737499375968679653787709 5151562265988254870170391)
    ·
      refine ⟨7727343398982382305255587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5151562265988254870170391 7727343398982382305255587)
      ·
        refine ⟨11591015098473573457883381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7727343398982382305255587 11591015098473573457883381)
        ·
          refine ⟨1086657665481897511676567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11591015098473573457883381 1086657665481897511676567)
          ·
            refine ⟨1629986498222846267514851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1086657665481897511676567 1629986498222846267514851)
            ·
              refine ⟨2444979747334269401272277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1629986498222846267514851 2444979747334269401272277)
              ·
                refine ⟨57304212828146939092319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2444979747334269401272277 57304212828146939092319)
                ·
                  rfl

theorem cell22_1506594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 1, 7].length) (baseStart_1506594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1506594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1506594 prefixEnd_1506594 := by exact prefixLift 1506594
  have htrace : WordTrace (prefixWord ++ tailWord_1506594) baseStart_1506594 baseEnd_1506594 := by
    simpa [prefixWord, tailWord_1506594, baseEnd_1506594] using wordTrace_append hprefix tailTrace_1506594
  have hstable : (prefixWord ++ tailWord_1506594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1506594).length < 2 ^ (prefixWord ++ tailWord_1506594).sum := by decide
  have hdescent : baseEnd_1506594 < baseStart_1506594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1506594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1506650 : List Nat := [3, 1, 1, 2, 1, 2, 3, 3, 6]
def baseStart_1506650 : Nat := 118140960795 + 1506650 * 2 ^ 59
def prefixEnd_1506650 : Nat := 4983230072969 + 3 ^ 40 * 1506650 * 2
def baseEnd_1506650 : Nat := 171919028465918990810233

theorem tailTrace_1506650 : CollatzResearch.WordTrace tailWord_1506650 prefixEnd_1506650 171919028465918990810233 := by
  unfold tailWord_1506650
  simp only [CollatzResearch.WordTrace]
  refine ⟨13738009997917960044797351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36634693327781226786126269 13738009997917960044797351)
  ·
    refine ⟨20607014996876940067196027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13738009997917960044797351 20607014996876940067196027)
    ·
      refine ⟨30910522495315410100794041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20607014996876940067196027 30910522495315410100794041)
      ·
        refine ⟨23182891871486557575595531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30910522495315410100794041 23182891871486557575595531)
        ·
          refine ⟨34774337807229836363393297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23182891871486557575595531 34774337807229836363393297)
          ·
            refine ⟨26080753355422377272544973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34774337807229836363393297 26080753355422377272544973)
            ·
              refine ⟨9780282508283391477204365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26080753355422377272544973 9780282508283391477204365)
              ·
                refine ⟨3667605940606271803951637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9780282508283391477204365 3667605940606271803951637)
                ·
                  refine ⟨171919028465918990810233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3667605940606271803951637 171919028465918990810233)
                  ·
                    rfl

theorem cell22_1506650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 3, 6].length) (baseStart_1506650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1506650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1506650 prefixEnd_1506650 := by exact prefixLift 1506650
  have htrace : WordTrace (prefixWord ++ tailWord_1506650) baseStart_1506650 baseEnd_1506650 := by
    simpa [prefixWord, tailWord_1506650, baseEnd_1506650] using wordTrace_append hprefix tailTrace_1506650
  have hstable : (prefixWord ++ tailWord_1506650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1506650).length < 2 ^ (prefixWord ++ tailWord_1506650).sum := by decide
  have hdescent : baseEnd_1506650 < baseStart_1506650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1506650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1506665 : List Nat := [1, 2, 1, 1, 1, 3, 2, 5, 1, 5]
def baseStart_1506665 : Nat := 118140960795 + 1506665 * 2 ^ 59
def prefixEnd_1506665 : Nat := 4983230072969 + 3 ^ 40 * 1506665 * 2
def baseEnd_1506665 : Nat := 515762220204301933305653

theorem tailTrace_1506665 : CollatzResearch.WordTrace tailWord_1506665 prefixEnd_1506665 515762220204301933305653 := by
  unfold tailWord_1506665
  simp only [CollatzResearch.WordTrace]
  refine ⟨54952587086617497740985449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36635058057744998493990299 54952587086617497740985449)
  ·
    refine ⟨41214440314963123305739087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54952587086617497740985449 41214440314963123305739087)
    ·
      refine ⟨61821660472444684958608631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41214440314963123305739087 61821660472444684958608631)
      ·
        refine ⟨92732490708667027437912947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61821660472444684958608631 92732490708667027437912947)
        ·
          refine ⟨139098736063000541156869421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92732490708667027437912947 139098736063000541156869421)
          ·
            refine ⟨52162026023625202933826033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 139098736063000541156869421 52162026023625202933826033)
            ·
              refine ⟨39121519517718902200369525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52162026023625202933826033 39121519517718902200369525)
              ·
                refine ⟨3667642454786147081284643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39121519517718902200369525 3667642454786147081284643)
                ·
                  refine ⟨5501463682179220621926965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3667642454786147081284643 5501463682179220621926965)
                  ·
                    refine ⟨515762220204301933305653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5501463682179220621926965 515762220204301933305653)
                    ·
                      rfl

theorem cell22_1506665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 5, 1, 5].length) (baseStart_1506665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1506665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1506665 prefixEnd_1506665 := by exact prefixLift 1506665
  have htrace : WordTrace (prefixWord ++ tailWord_1506665) baseStart_1506665 baseEnd_1506665 := by
    simpa [prefixWord, tailWord_1506665, baseEnd_1506665] using wordTrace_append hprefix tailTrace_1506665
  have hstable : (prefixWord ++ tailWord_1506665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1506665).length < 2 ^ (prefixWord ++ tailWord_1506665).sum := by decide
  have hdescent : baseEnd_1506665 < baseStart_1506665 := by decide
  rcases family_descends (prefixWord ++ tailWord_1506665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1506669 : List Nat := [1, 5, 1, 1, 1, 4, 2, 2, 1, 4]
def baseStart_1506669 : Nat := 118140960795 + 1506669 * 2 ^ 59
def prefixEnd_1506669 : Nat := 4983230072969 + 3 ^ 40 * 1506669 * 2
def baseEnd_1506669 : Nat := 515763589486047256205641

theorem tailTrace_1506669 : CollatzResearch.WordTrace tailWord_1506669 prefixEnd_1506669 515763589486047256205641 := by
  unfold tailWord_1506669
  simp only [CollatzResearch.WordTrace]
  refine ⟨54952732978603006424131061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36635155319068670949420707 54952732978603006424131061)
  ·
    refine ⟨5151818716744031852262287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 54952732978603006424131061 5151818716744031852262287)
    ·
      refine ⟨7727728075116047778393431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5151818716744031852262287 7727728075116047778393431)
      ·
        refine ⟨11591592112674071667590147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7727728075116047778393431 11591592112674071667590147)
        ·
          refine ⟨17387388169011107501385221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11591592112674071667590147 17387388169011107501385221)
          ·
            refine ⟨3260135281689582656509729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17387388169011107501385221 3260135281689582656509729)
            ·
              refine ⟨2445101461267186992382297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3260135281689582656509729 2445101461267186992382297)
              ·
                refine ⟨1833826095950390244286723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2445101461267186992382297 1833826095950390244286723)
                ·
                  refine ⟨2750739143925585366430085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1833826095950390244286723 2750739143925585366430085)
                  ·
                    refine ⟨515763589486047256205641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2750739143925585366430085 515763589486047256205641)
                    ·
                      rfl

theorem cell22_1506669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 2, 2, 1, 4].length) (baseStart_1506669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1506669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1506669 prefixEnd_1506669 := by exact prefixLift 1506669
  have htrace : WordTrace (prefixWord ++ tailWord_1506669) baseStart_1506669 baseEnd_1506669 := by
    simpa [prefixWord, tailWord_1506669, baseEnd_1506669] using wordTrace_append hprefix tailTrace_1506669
  have hstable : (prefixWord ++ tailWord_1506669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1506669).length < 2 ^ (prefixWord ++ tailWord_1506669).sum := by decide
  have hdescent : baseEnd_1506669 < baseStart_1506669 := by decide
  rcases family_descends (prefixWord ++ tailWord_1506669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1506680 : List Nat := [2, 1, 2, 1, 1, 1, 1, 1, 8, 4]
def baseStart_1506680 : Nat := 118140960795 + 1506680 * 2 ^ 59
def prefixEnd_1506680 : Nat := 4983230072969 + 3 ^ 40 * 1506680 * 2
def baseEnd_1506680 : Nat := 515767355010846894180607

theorem tailTrace_1506680 : CollatzResearch.WordTrace tailWord_1506680 prefixEnd_1506680 515767355010846894180607 := by
  unfold tailWord_1506680
  simp only [CollatzResearch.WordTrace]
  refine ⟨27476567090781577651390747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36635422787708770201854329 27476567090781577651390747)
  ·
    refine ⟨41214850636172366477086121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27476567090781577651390747 41214850636172366477086121)
    ·
      refine ⟨30911137977129274857814591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41214850636172366477086121 30911137977129274857814591)
      ·
        refine ⟨46366706965693912286721887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30911137977129274857814591 46366706965693912286721887)
        ·
          refine ⟨69550060448540868430082831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46366706965693912286721887 69550060448540868430082831)
          ·
            refine ⟨104325090672811302645124247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69550060448540868430082831 104325090672811302645124247)
            ·
              refine ⟨156487636009216953967686371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104325090672811302645124247 156487636009216953967686371)
              ·
                refine ⟨234731454013825430951529557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 156487636009216953967686371 234731454013825430951529557)
                ·
                  refine ⟨2750759226724516768963237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 234731454013825430951529557 2750759226724516768963237)
                  ·
                    refine ⟨515767355010846894180607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2750759226724516768963237 515767355010846894180607)
                    ·
                      rfl

theorem cell22_1506680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 8, 4].length) (baseStart_1506680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1506680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1506680 prefixEnd_1506680 := by exact prefixLift 1506680
  have htrace : WordTrace (prefixWord ++ tailWord_1506680) baseStart_1506680 baseEnd_1506680 := by
    simpa [prefixWord, tailWord_1506680, baseEnd_1506680] using wordTrace_append hprefix tailTrace_1506680
  have hstable : (prefixWord ++ tailWord_1506680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1506680).length < 2 ^ (prefixWord ++ tailWord_1506680).sum := by decide
  have hdescent : baseEnd_1506680 < baseStart_1506680 := by decide
  rcases family_descends (prefixWord ++ tailWord_1506680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1506695 : List Nat := [1, 1, 4, 2, 2, 2, 10]
def baseStart_1506695 : Nat := 118140960795 + 1506695 * 2 ^ 59
def prefixEnd_1506695 : Nat := 4983230072969 + 3 ^ 40 * 1506695 * 2
def baseEnd_1506695 : Nat := 19102684808051550187243

theorem tailTrace_1506695 : CollatzResearch.WordTrace tailWord_1506695 prefixEnd_1506695 19102684808051550187243 := by
  unfold tailWord_1506695
  simp only [CollatzResearch.WordTrace]
  refine ⟨54953681276508812864577539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36635787517672541909718359 54953681276508812864577539)
  ·
    refine ⟨82430521914763219296866309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54953681276508812864577539 82430521914763219296866309)
    ·
      refine ⟨15455722859018103618162433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82430521914763219296866309 15455722859018103618162433)
      ·
        refine ⟨11591792144263577713621825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15455722859018103618162433 11591792144263577713621825)
        ·
          refine ⟨8693844108197683285216369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11591792144263577713621825 8693844108197683285216369)
          ·
            refine ⟨6520383081148262463912277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8693844108197683285216369 6520383081148262463912277)
            ·
              refine ⟨19102684808051550187243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 6520383081148262463912277 19102684808051550187243)
              ·
                rfl

theorem cell22_1506695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 10].length) (baseStart_1506695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1506695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1506695 prefixEnd_1506695 := by exact prefixLift 1506695
  have htrace : WordTrace (prefixWord ++ tailWord_1506695) baseStart_1506695 baseEnd_1506695 := by
    simpa [prefixWord, tailWord_1506695, baseEnd_1506695] using wordTrace_append hprefix tailTrace_1506695
  have hstable : (prefixWord ++ tailWord_1506695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1506695).length < 2 ^ (prefixWord ++ tailWord_1506695).sum := by decide
  have hdescent : baseEnd_1506695 < baseStart_1506695 := by decide
  rcases family_descends (prefixWord ++ tailWord_1506695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1506725 : List Nat := [1, 3, 1, 2, 1, 1, 2, 1, 4, 6]
def baseStart_1506725 : Nat := 118140960795 + 1506725 * 2 ^ 59
def prefixEnd_1506725 : Nat := 4983230072969 + 3 ^ 40 * 1506725 * 2
def baseEnd_1506725 : Nat := 515782759430481776805469

theorem tailTrace_1506725 : CollatzResearch.WordTrace tailWord_1506725 prefixEnd_1506725 515782759430481776805469 := by
  unfold tailWord_1506725
  simp only [CollatzResearch.WordTrace]
  refine ⟨54954775466400127988169629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36636516977600085325446419 54954775466400127988169629)
  ·
    refine ⟨20608040799900047995563611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54954775466400127988169629 20608040799900047995563611)
    ·
      refine ⟨30912061199850071993345417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20608040799900047995563611 30912061199850071993345417)
      ·
        refine ⟨23184045899887553995009063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30912061199850071993345417 23184045899887553995009063)
        ·
          refine ⟨34776068849831330992513595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23184045899887553995009063 34776068849831330992513595)
          ·
            refine ⟨52164103274746996488770393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34776068849831330992513595 52164103274746996488770393)
            ·
              refine ⟨39123077456060247366577795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52164103274746996488770393 39123077456060247366577795)
              ·
                refine ⟨58684616184090371049866693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39123077456060247366577795 58684616184090371049866693)
                ·
                  refine ⟨11003365534516944571850005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58684616184090371049866693 11003365534516944571850005)
                  ·
                    refine ⟨515782759430481776805469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11003365534516944571850005 515782759430481776805469)
                    ·
                      rfl

theorem cell22_1506725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 4, 6].length) (baseStart_1506725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1506725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1506725 prefixEnd_1506725 := by exact prefixLift 1506725
  have htrace : WordTrace (prefixWord ++ tailWord_1506725) baseStart_1506725 baseEnd_1506725 := by
    simpa [prefixWord, tailWord_1506725, baseEnd_1506725] using wordTrace_append hprefix tailTrace_1506725
  have hstable : (prefixWord ++ tailWord_1506725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1506725).length < 2 ^ (prefixWord ++ tailWord_1506725).sum := by decide
  have hdescent : baseEnd_1506725 < baseStart_1506725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1506725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1506846 : List Nat := [4, 3, 3, 1, 2, 1, 1, 3, 1, 3]
def baseStart_1506846 : Nat := 118140960795 + 1506846 * 2 ^ 59
def prefixEnd_1506846 : Nat := 4983230072969 + 3 ^ 40 * 1506846 * 2
def baseEnd_1506846 : Nat := 515824180203277794530099

theorem tailTrace_1506846 : CollatzResearch.WordTrace tailWord_1506846 prefixEnd_1506846 515824180203277794530099 := by
  unfold tailWord_1506846
  simp only [CollatzResearch.WordTrace]
  refine ⟨6869898587370220706665549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36639459132641177102216261 6869898587370220706665549)
  ·
    refine ⟨2576211970263832764999581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6869898587370220706665549 2576211970263832764999581)
    ·
      refine ⟨966079488848937286874843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2576211970263832764999581 966079488848937286874843)
      ·
        refine ⟨1449119233273405930312265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 966079488848937286874843 1449119233273405930312265)
        ·
          refine ⟨1086839424955054447734199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1449119233273405930312265 1086839424955054447734199)
          ·
            refine ⟨1630259137432581671601299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1086839424955054447734199 1630259137432581671601299)
            ·
              refine ⟨2445388706148872507401949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1630259137432581671601299 2445388706148872507401949)
              ·
                refine ⟨917020764805827190275731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2445388706148872507401949 917020764805827190275731)
                ·
                  refine ⟨1375531147208740785413597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 917020764805827190275731 1375531147208740785413597)
                  ·
                    refine ⟨515824180203277794530099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1375531147208740785413597 515824180203277794530099)
                    ·
                      rfl

theorem cell22_1506846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_1506846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1506846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1506846 prefixEnd_1506846 := by exact prefixLift 1506846
  have htrace : WordTrace (prefixWord ++ tailWord_1506846) baseStart_1506846 baseEnd_1506846 := by
    simpa [prefixWord, tailWord_1506846, baseEnd_1506846] using wordTrace_append hprefix tailTrace_1506846
  have hstable : (prefixWord ++ tailWord_1506846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1506846).length < 2 ^ (prefixWord ++ tailWord_1506846).sum := by decide
  have hdescent : baseEnd_1506846 < baseStart_1506846 := by decide
  rcases family_descends (prefixWord ++ tailWord_1506846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1506870 : List Nat := [5, 1, 2, 1, 3, 1, 3, 2, 4]
def baseStart_1506870 : Nat := 118140960795 + 1506870 * 2 ^ 59
def prefixEnd_1506870 : Nat := 4983230072969 + 3 ^ 40 * 1506870 * 2
def baseEnd_1506870 : Nat := 171944131964583243976675

theorem tailTrace_1506870 : CollatzResearch.WordTrace tailWord_1506870 prefixEnd_1506870 171944131964583243976675 := by
  unfold tailWord_1506870
  simp only [CollatzResearch.WordTrace]
  refine ⟨3435004003179676109512379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36640042700583211834798709 3435004003179676109512379)
  ·
    refine ⟨5152506004769514164268569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3435004003179676109512379 5152506004769514164268569)
    ·
      refine ⟨3864379503577135623201427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5152506004769514164268569 3864379503577135623201427)
      ·
        refine ⟨5796569255365703434802141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3864379503577135623201427 5796569255365703434802141)
        ·
          refine ⟨2173713470762138788050803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5796569255365703434802141 2173713470762138788050803)
          ·
            refine ⟨3260570206143208182076205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2173713470762138788050803 3260570206143208182076205)
            ·
              refine ⟨1222713827303703068278577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3260570206143208182076205 1222713827303703068278577)
              ·
                refine ⟨917035370477777301208933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1222713827303703068278577 917035370477777301208933)
                ·
                  refine ⟨171944131964583243976675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 917035370477777301208933 171944131964583243976675)
                  ·
                    rfl

theorem cell22_1506870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 3, 2, 4].length) (baseStart_1506870 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1506870 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1506870 prefixEnd_1506870 := by exact prefixLift 1506870
  have htrace : WordTrace (prefixWord ++ tailWord_1506870) baseStart_1506870 baseEnd_1506870 := by
    simpa [prefixWord, tailWord_1506870, baseEnd_1506870] using wordTrace_append hprefix tailTrace_1506870
  have hstable : (prefixWord ++ tailWord_1506870).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1506870).length < 2 ^ (prefixWord ++ tailWord_1506870).sum := by decide
  have hdescent : baseEnd_1506870 < baseStart_1506870 := by decide
  rcases family_descends (prefixWord ++ tailWord_1506870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1506930 : List Nat := [3, 2, 1, 2, 3, 1, 4, 2, 1, 3]
def baseStart_1506930 : Nat := 118140960795 + 1506930 * 2 ^ 59
def prefixEnd_1506930 : Nat := 4983230072969 + 3 ^ 40 * 1506930 * 2
def baseEnd_1506930 : Nat := 515852935119929575429841

theorem tailTrace_1506930 : CollatzResearch.WordTrace tailWord_1506930 prefixEnd_1506930 515852935119929575429841 := by
  unfold tailWord_1506930
  simp only [CollatzResearch.WordTrace]
  refine ⟨13740563107664361999845561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36641501620438298666254829 13740563107664361999845561)
  ·
    refine ⟨10305422330748271499884171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13740563107664361999845561 10305422330748271499884171)
    ·
      refine ⟨15458133496122407249826257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10305422330748271499884171 15458133496122407249826257)
      ·
        refine ⟨11593600122091805437369693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15458133496122407249826257 11593600122091805437369693)
        ·
          refine ⟨4347600045784427039013635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11593600122091805437369693 4347600045784427039013635)
          ·
            refine ⟨6521400068676640558520453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4347600045784427039013635 6521400068676640558520453)
            ·
              refine ⟨1222762512876870104722585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6521400068676640558520453 1222762512876870104722585)
              ·
                refine ⟨917071884657652578541939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1222762512876870104722585 917071884657652578541939)
                ·
                  refine ⟨1375607826986478867812909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 917071884657652578541939 1375607826986478867812909)
                  ·
                    refine ⟨515852935119929575429841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1375607826986478867812909 515852935119929575429841)
                    ·
                      rfl

theorem cell22_1506930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 4, 2, 1, 3].length) (baseStart_1506930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1506930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1506930 prefixEnd_1506930 := by exact prefixLift 1506930
  have htrace : WordTrace (prefixWord ++ tailWord_1506930) baseStart_1506930 baseEnd_1506930 := by
    simpa [prefixWord, tailWord_1506930, baseEnd_1506930] using wordTrace_append hprefix tailTrace_1506930
  have hstable : (prefixWord ++ tailWord_1506930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1506930).length < 2 ^ (prefixWord ++ tailWord_1506930).sum := by decide
  have hdescent : baseEnd_1506930 < baseStart_1506930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1506930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1506954 : List Nat := [3, 1, 2, 3, 2, 1, 1, 1, 8]
def baseStart_1506954 : Nat := 118140960795 + 1506954 * 2 ^ 59
def prefixEnd_1506954 : Nat := 4983230072969 + 3 ^ 40 * 1506954 * 2
def baseEnd_1506954 : Nat := 171953716936800504276589

theorem tailTrace_1506954 : CollatzResearch.WordTrace tailWord_1506954 prefixEnd_1506954 171953716936800504276589 := by
  unfold tailWord_1506954
  simp only [CollatzResearch.WordTrace]
  refine ⟨13740781945642625024563979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36642085188380333398837277 13740781945642625024563979)
  ·
    refine ⟨20611172918463937536845969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13740781945642625024563979 20611172918463937536845969)
    ·
      refine ⟨15458379688847953152634477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20611172918463937536845969 15458379688847953152634477)
      ·
        refine ⟨5796892383317982432237929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15458379688847953152634477 5796892383317982432237929)
        ·
          refine ⟨4347669287488486824178447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5796892383317982432237929 4347669287488486824178447)
          ·
            refine ⟨6521503931232730236267671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4347669287488486824178447 6521503931232730236267671)
            ·
              refine ⟨9782255896849095354401507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6521503931232730236267671 9782255896849095354401507)
              ·
                refine ⟨14673383845273643031602261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9782255896849095354401507 14673383845273643031602261)
                ·
                  refine ⟨171953716936800504276589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14673383845273643031602261 171953716936800504276589)
                  ·
                    rfl

theorem cell22_1506954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 1, 8].length) (baseStart_1506954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1506954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1506954 prefixEnd_1506954 := by exact prefixLift 1506954
  have htrace : WordTrace (prefixWord ++ tailWord_1506954) baseStart_1506954 baseEnd_1506954 := by
    simpa [prefixWord, tailWord_1506954, baseEnd_1506954] using wordTrace_append hprefix tailTrace_1506954
  have hstable : (prefixWord ++ tailWord_1506954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1506954).length < 2 ^ (prefixWord ++ tailWord_1506954).sum := by decide
  have hdescent : baseEnd_1506954 < baseStart_1506954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1506954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1507044 : List Nat := [2, 3, 1, 1, 1, 3, 1, 3, 7]
def baseStart_1507044 : Nat := 118140960795 + 1507044 * 2 ^ 59
def prefixEnd_1507044 : Nat := 4983230072969 + 3 ^ 40 * 1507044 * 2
def baseEnd_1507044 : Nat := 171963986549890426026497

theorem tailTrace_1507044 : CollatzResearch.WordTrace tailWord_1507044 prefixEnd_1507044 171963986549890426026497 := by
  unfold tailWord_1507044
  simp only [CollatzResearch.WordTrace]
  refine ⟨27483205176122222734516093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36644273568162963646021457 27483205176122222734516093)
  ·
    refine ⟨10306201941045833525443535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27483205176122222734516093 10306201941045833525443535)
    ·
      refine ⟨15459302911568750288165303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10306201941045833525443535 15459302911568750288165303)
      ·
        refine ⟨23188954367353125432247955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15459302911568750288165303 23188954367353125432247955)
        ·
          refine ⟨34783431551029688148371933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23188954367353125432247955 34783431551029688148371933)
          ·
            refine ⟨13043786831636133055639475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34783431551029688148371933 13043786831636133055639475)
            ·
              refine ⟨19565680247454199583459213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13043786831636133055639475 19565680247454199583459213)
              ·
                refine ⟨7337130092795324843797205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19565680247454199583459213 7337130092795324843797205)
                ·
                  refine ⟨171963986549890426026497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7337130092795324843797205 171963986549890426026497)
                  ·
                    rfl

theorem cell22_1507044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 3, 7].length) (baseStart_1507044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1507044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1507044 prefixEnd_1507044 := by exact prefixLift 1507044
  have htrace : WordTrace (prefixWord ++ tailWord_1507044) baseStart_1507044 baseEnd_1507044 := by
    simpa [prefixWord, tailWord_1507044, baseEnd_1507044] using wordTrace_append hprefix tailTrace_1507044
  have hstable : (prefixWord ++ tailWord_1507044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1507044).length < 2 ^ (prefixWord ++ tailWord_1507044).sum := by decide
  have hdescent : baseEnd_1507044 < baseStart_1507044 := by decide
  rcases family_descends (prefixWord ++ tailWord_1507044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1507048 : List Nat := [2, 1, 4, 1, 3, 1, 3, 1, 3, 3]
def baseStart_1507048 : Nat := 118140960795 + 1507048 * 2 ^ 59
def prefixEnd_1507048 : Nat := 4983230072969 + 3 ^ 40 * 1507048 * 2
def baseEnd_1507048 : Nat := 515893328931416600979479

theorem tailTrace_1507048 : CollatzResearch.WordTrace tailWord_1507048 prefixEnd_1507048 515893328931416600979479 := by
  unfold tailWord_1507048
  simp only [CollatzResearch.WordTrace]
  refine ⟨27483278122114977076088899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36644370829486636101451865 27483278122114977076088899)
  ·
    refine ⟨41224917183172465614133349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27483278122114977076088899 41224917183172465614133349)
    ·
      refine ⟨7729671971844837302650003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41224917183172465614133349 7729671971844837302650003)
      ·
        refine ⟨11594507957767255953975005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7729671971844837302650003 11594507957767255953975005)
        ·
          refine ⟨4347940484162720982740627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11594507957767255953975005 4347940484162720982740627)
          ·
            refine ⟨6521910726244081474110941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4347940484162720982740627 6521910726244081474110941)
            ·
              refine ⟨2445716522341530552791603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6521910726244081474110941 2445716522341530552791603)
              ·
                refine ⟨3668574783512295829187405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2445716522341530552791603 3668574783512295829187405)
                ·
                  refine ⟨1375715543817110935945277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3668574783512295829187405 1375715543817110935945277)
                  ·
                    refine ⟨515893328931416600979479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1375715543817110935945277 515893328931416600979479)
                    ·
                      rfl

theorem cell22_1507048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 3, 1, 3, 3].length) (baseStart_1507048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1507048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1507048 prefixEnd_1507048 := by exact prefixLift 1507048
  have htrace : WordTrace (prefixWord ++ tailWord_1507048) baseStart_1507048 baseEnd_1507048 := by
    simpa [prefixWord, tailWord_1507048, baseEnd_1507048] using wordTrace_append hprefix tailTrace_1507048
  have hstable : (prefixWord ++ tailWord_1507048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1507048).length < 2 ^ (prefixWord ++ tailWord_1507048).sum := by decide
  have hdescent : baseEnd_1507048 < baseStart_1507048 := by decide
  rcases family_descends (prefixWord ++ tailWord_1507048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1507059 : List Nat := [1, 1, 1, 2, 2, 3, 2, 3, 2, 5]
def baseStart_1507059 : Nat := 118140960795 + 1507059 * 2 ^ 59
def prefixEnd_1507059 : Nat := 4983230072969 + 3 ^ 40 * 1507059 * 2
def baseEnd_1507059 : Nat := 515897094456216238954445

theorem tailTrace_1507059 : CollatzResearch.WordTrace tailWord_1507059 prefixEnd_1507059 515897094456216238954445 := by
  unfold tailWord_1507059
  simp only [CollatzResearch.WordTrace]
  refine ⟨54966957447190103030828231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36644638298126735353885487 54966957447190103030828231)
  ·
    refine ⟨82450436170785154546242347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54966957447190103030828231 82450436170785154546242347)
    ·
      refine ⟨123675654256177731819363521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82450436170785154546242347 123675654256177731819363521)
      ·
        refine ⟨92756740692133298864522641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123675654256177731819363521 92756740692133298864522641)
        ·
          refine ⟨69567555519099974148391981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92756740692133298864522641 69567555519099974148391981)
          ·
            refine ⟨26087833319662490305646993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69567555519099974148391981 26087833319662490305646993)
            ·
              refine ⟨19565874989746867729235245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26087833319662490305646993 19565874989746867729235245)
              ·
                refine ⟨7337203121155075398463217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19565874989746867729235245 7337203121155075398463217)
                ·
                  refine ⟨5502902340866306548847413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7337203121155075398463217 5502902340866306548847413)
                  ·
                    refine ⟨515897094456216238954445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5502902340866306548847413 515897094456216238954445)
                    ·
                      rfl

theorem cell22_1507059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 3, 2, 5].length) (baseStart_1507059 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1507059 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1507059 prefixEnd_1507059 := by exact prefixLift 1507059
  have htrace : WordTrace (prefixWord ++ tailWord_1507059) baseStart_1507059 baseEnd_1507059 := by
    simpa [prefixWord, tailWord_1507059, baseEnd_1507059] using wordTrace_append hprefix tailTrace_1507059
  have hstable : (prefixWord ++ tailWord_1507059).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1507059).length < 2 ^ (prefixWord ++ tailWord_1507059).sum := by decide
  have hdescent : baseEnd_1507059 < baseStart_1507059 := by decide
  rcases family_descends (prefixWord ++ tailWord_1507059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1507106 : List Nat := [3, 3, 1, 1, 2, 1, 2, 3, 6]
def baseStart_1507106 : Nat := 118140960795 + 1507106 * 2 ^ 59
def prefixEnd_1507106 : Nat := 4983230072969 + 3 ^ 40 * 1507106 * 2
def baseEnd_1507106 : Nat := 171971061172241261009767

theorem tailTrace_1507106 : CollatzResearch.WordTrace tailWord_1507106 prefixEnd_1507106 171971061172241261009767 := by
  unfold tailWord_1507106
  simp only [CollatzResearch.WordTrace]
  refine ⟨13742167919504957514447293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36645781118679886705192781 13742167919504957514447293)
  ·
    refine ⟨5153312969814359067917735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13742167919504957514447293 5153312969814359067917735)
    ·
      refine ⟨7729969454721538601876603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5153312969814359067917735 7729969454721538601876603)
      ·
        refine ⟨11594954182082307902814905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7729969454721538601876603 11594954182082307902814905)
        ·
          refine ⟨8696215636561730927111179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11594954182082307902814905 8696215636561730927111179)
          ·
            refine ⟨13044323454842596390666769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8696215636561730927111179 13044323454842596390666769)
            ·
              refine ⟨9783242591131947293000077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13044323454842596390666769 9783242591131947293000077)
              ·
                refine ⟨3668715971674480234875029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9783242591131947293000077 3668715971674480234875029)
                ·
                  refine ⟨171971061172241261009767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3668715971674480234875029 171971061172241261009767)
                  ·
                    rfl

theorem cell22_1507106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 3, 6].length) (baseStart_1507106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1507106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1507106 prefixEnd_1507106 := by exact prefixLift 1507106
  have htrace : WordTrace (prefixWord ++ tailWord_1507106) baseStart_1507106 baseEnd_1507106 := by
    simpa [prefixWord, tailWord_1507106, baseEnd_1507106] using wordTrace_append hprefix tailTrace_1507106
  have hstable : (prefixWord ++ tailWord_1507106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1507106).length < 2 ^ (prefixWord ++ tailWord_1507106).sum := by decide
  have hdescent : baseEnd_1507106 < baseStart_1507106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1507106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1507119 : List Nat := [1, 1, 2, 1, 2, 1, 2, 3, 3, 6]
def baseStart_1507119 : Nat := 118140960795 + 1507119 * 2 ^ 59
def prefixEnd_1507119 : Nat := 4983230072969 + 3 ^ 40 * 1507119 * 2
def baseEnd_1507119 : Nat := 515917633682396082454261

theorem tailTrace_1507119 : CollatzResearch.WordTrace tailWord_1507119 prefixEnd_1507119 515917633682396082454261 := by
  unfold tailWord_1507119
  simp only [CollatzResearch.WordTrace]
  refine ⟨54969145826972733278012411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36646097217981822185341607 54969145826972733278012411)
  ·
    refine ⟨82453718740459099917018617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54969145826972733278012411 82453718740459099917018617)
    ·
      refine ⟨61840289055344324937763963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82453718740459099917018617 61840289055344324937763963)
      ·
        refine ⟨92760433583016487406645945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61840289055344324937763963 92760433583016487406645945)
        ·
          refine ⟨69570325187262365554984459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92760433583016487406645945 69570325187262365554984459)
          ·
            refine ⟨104355487780893548332476689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69570325187262365554984459 104355487780893548332476689)
            ·
              refine ⟨78266615835670161249357517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104355487780893548332476689 78266615835670161249357517)
              ·
                refine ⟨29349980938376310468509069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78266615835670161249357517 29349980938376310468509069)
                ·
                  refine ⟨11006242851891116425690901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29349980938376310468509069 11006242851891116425690901)
                  ·
                    refine ⟨515917633682396082454261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11006242851891116425690901 515917633682396082454261)
                    ·
                      rfl

theorem cell22_1507119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 3, 6].length) (baseStart_1507119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1507119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1507119 prefixEnd_1507119 := by exact prefixLift 1507119
  have htrace : WordTrace (prefixWord ++ tailWord_1507119) baseStart_1507119 baseEnd_1507119 := by
    simpa [prefixWord, tailWord_1507119, baseEnd_1507119] using wordTrace_append hprefix tailTrace_1507119
  have hstable : (prefixWord ++ tailWord_1507119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1507119).length < 2 ^ (prefixWord ++ tailWord_1507119).sum := by decide
  have hdescent : baseEnd_1507119 < baseStart_1507119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1507119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1507121 : List Nat := [1, 2, 2, 3, 2, 2, 1, 3, 1, 5]
def baseStart_1507121 : Nat := 118140960795 + 1507121 * 2 ^ 59
def prefixEnd_1507121 : Nat := 4983230072969 + 3 ^ 40 * 1507121 * 2
def baseEnd_1507121 : Nat := 515918318323268743904255

theorem tailTrace_1507121 : CollatzResearch.WordTrace tailWord_1507121 prefixEnd_1507121 515918318323268743904255 := by
  unfold tailWord_1507121
  simp only [CollatzResearch.WordTrace]
  refine ⟨54969218772965487619585217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36646145848643658413056811 54969218772965487619585217)
  ·
    refine ⟨41226914079724115714688913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54969218772965487619585217 41226914079724115714688913)
    ·
      refine ⟨30920185559793086786016685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41226914079724115714688913 30920185559793086786016685)
      ·
        refine ⟨11595069584922407544756257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30920185559793086786016685 11595069584922407544756257)
        ·
          refine ⟨8696302188691805658567193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11595069584922407544756257 8696302188691805658567193)
          ·
            refine ⟨6522226641518854243925395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8696302188691805658567193 6522226641518854243925395)
            ·
              refine ⟨9783339962278281365888093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6522226641518854243925395 9783339962278281365888093)
              ·
                refine ⟨3668752485854355512208035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9783339962278281365888093 3668752485854355512208035)
                ·
                  refine ⟨5503128728781533268312053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3668752485854355512208035 5503128728781533268312053)
                  ·
                    refine ⟨515918318323268743904255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5503128728781533268312053 515918318323268743904255)
                    ·
                      rfl

theorem cell22_1507121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 3, 1, 5].length) (baseStart_1507121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1507121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1507121 prefixEnd_1507121 := by exact prefixLift 1507121
  have htrace : WordTrace (prefixWord ++ tailWord_1507121) baseStart_1507121 baseEnd_1507121 := by
    simpa [prefixWord, tailWord_1507121, baseEnd_1507121] using wordTrace_append hprefix tailTrace_1507121
  have hstable : (prefixWord ++ tailWord_1507121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1507121).length < 2 ^ (prefixWord ++ tailWord_1507121).sum := by decide
  have hdescent : baseEnd_1507121 < baseStart_1507121 := by decide
  rcases family_descends (prefixWord ++ tailWord_1507121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1507142 : List Nat := [6, 1, 1, 2, 1, 2, 1, 3, 1, 4]
def baseStart_1507142 : Nat := 118140960795 + 1507142 * 2 ^ 59
def prefixEnd_1507142 : Nat := 4983230072969 + 3 ^ 40 * 1507142 * 2
def baseEnd_1507142 : Nat := 515925507052431689129191

theorem tailTrace_1507142 : CollatzResearch.WordTrace tailWord_1507142 prefixEnd_1507142 515925507052431689129191 := by
  unfold tailWord_1507142
  simp only [CollatzResearch.WordTrace]
  refine ⟨1717812022059044006440615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 36646656470592938804066453 1717812022059044006440615)
  ·
    refine ⟨2576718033088566009660923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1717812022059044006440615 2576718033088566009660923)
    ·
      refine ⟨3865077049632849014491385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2576718033088566009660923 3865077049632849014491385)
      ·
        refine ⟨2898807787224636760868539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3865077049632849014491385 2898807787224636760868539)
        ·
          refine ⟨4348211680836955141302809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2898807787224636760868539 4348211680836955141302809)
          ·
            refine ⟨3261158760627716355977107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4348211680836955141302809 3261158760627716355977107)
            ·
              refine ⟨4891738140941574533965661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3261158760627716355977107 4891738140941574533965661)
              ·
                refine ⟨1834401802853090450237123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4891738140941574533965661 1834401802853090450237123)
                ·
                  refine ⟨2751602704279635675355685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1834401802853090450237123 2751602704279635675355685)
                  ·
                    refine ⟨515925507052431689129191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2751602704279635675355685 515925507052431689129191)
                    ·
                      rfl

theorem cell22_1507142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_1507142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1507142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1507142 prefixEnd_1507142 := by exact prefixLift 1507142
  have htrace : WordTrace (prefixWord ++ tailWord_1507142) baseStart_1507142 baseEnd_1507142 := by
    simpa [prefixWord, tailWord_1507142, baseEnd_1507142] using wordTrace_append hprefix tailTrace_1507142
  have hstable : (prefixWord ++ tailWord_1507142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1507142).length < 2 ^ (prefixWord ++ tailWord_1507142).sum := by decide
  have hdescent : baseEnd_1507142 < baseStart_1507142 := by decide
  rcases family_descends (prefixWord ++ tailWord_1507142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1507172 : List Nat := [2, 3, 1, 1, 5, 1, 3, 1, 2, 3]
def baseStart_1507172 : Nat := 118140960795 + 1507172 * 2 ^ 59
def prefixEnd_1507172 : Nat := 4983230072969 + 3 ^ 40 * 1507172 * 2
def baseEnd_1507172 : Nat := 515935776665521610879099

theorem tailTrace_1507172 : CollatzResearch.WordTrace tailWord_1507172 prefixEnd_1507172 515935776665521610879099 := by
  unfold tailWord_1507172
  simp only [CollatzResearch.WordTrace]
  refine ⟨27485539447890361664845885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36647385930520482219794513 27485539447890361664845885)
  ·
    refine ⟨10307077292958885624317207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27485539447890361664845885 10307077292958885624317207)
    ·
      refine ⟨15460615939438328436475811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10307077292958885624317207 15460615939438328436475811)
      ·
        refine ⟨23190923909157492654713717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15460615939438328436475811 23190923909157492654713717)
        ·
          refine ⟨2174149116483514936379411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23190923909157492654713717 2174149116483514936379411)
          ·
            refine ⟨3261223674725272404569117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2174149116483514936379411 3261223674725272404569117)
            ·
              refine ⟨1222958878021977151713419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3261223674725272404569117 1222958878021977151713419)
              ·
                refine ⟨1834438317032965727570129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1222958878021977151713419 1834438317032965727570129)
                ·
                  refine ⟨1375828737774724295677597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1834438317032965727570129 1375828737774724295677597)
                  ·
                    refine ⟨515935776665521610879099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1375828737774724295677597 515935776665521610879099)
                    ·
                      rfl

theorem cell22_1507172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 3, 1, 2, 3].length) (baseStart_1507172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1507172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1507172 prefixEnd_1507172 := by exact prefixLift 1507172
  have htrace : WordTrace (prefixWord ++ tailWord_1507172) baseStart_1507172 baseEnd_1507172 := by
    simpa [prefixWord, tailWord_1507172, baseEnd_1507172] using wordTrace_append hprefix tailTrace_1507172
  have hstable : (prefixWord ++ tailWord_1507172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1507172).length < 2 ^ (prefixWord ++ tailWord_1507172).sum := by decide
  have hdescent : baseEnd_1507172 < baseStart_1507172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1507172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1507181 : List Nat := [1, 5, 1, 1, 1, 1, 2, 2, 2, 6]
def baseStart_1507181 : Nat := 118140960795 + 1507181 * 2 ^ 59
def prefixEnd_1507181 : Nat := 4983230072969 + 3 ^ 40 * 1507181 * 2
def baseEnd_1507181 : Nat := 515938857549448587404071

theorem tailTrace_1507181 : CollatzResearch.WordTrace tailWord_1507181 prefixEnd_1507181 515938857549448587404071 := by
  unfold tailWord_1507181
  simp only [CollatzResearch.WordTrace]
  refine ⟨54971407152748117866769397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36647604768498745244512931 54971407152748117866769397)
  ·
    refine ⟨5153569420570136050009631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 54971407152748117866769397 5153569420570136050009631)
    ·
      refine ⟨7730354130855204075014447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5153569420570136050009631 7730354130855204075014447)
      ·
        refine ⟨11595531196282806112521671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7730354130855204075014447 11595531196282806112521671)
        ·
          refine ⟨17393296794424209168782507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11595531196282806112521671 17393296794424209168782507)
          ·
            refine ⟨26089945191636313753173761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17393296794424209168782507 26089945191636313753173761)
            ·
              refine ⟨19567458893727235314880321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26089945191636313753173761 19567458893727235314880321)
              ·
                refine ⟨14675594170295426486160241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19567458893727235314880321 14675594170295426486160241)
                ·
                  refine ⟨11006695627721569864620181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14675594170295426486160241 11006695627721569864620181)
                  ·
                    refine ⟨515938857549448587404071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11006695627721569864620181 515938857549448587404071)
                    ·
                      rfl

theorem cell22_1507181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 2, 2, 6].length) (baseStart_1507181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1507181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1507181 prefixEnd_1507181 := by exact prefixLift 1507181
  have htrace : WordTrace (prefixWord ++ tailWord_1507181) baseStart_1507181 baseEnd_1507181 := by
    simpa [prefixWord, tailWord_1507181, baseEnd_1507181] using wordTrace_append hprefix tailTrace_1507181
  have hstable : (prefixWord ++ tailWord_1507181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1507181).length < 2 ^ (prefixWord ++ tailWord_1507181).sum := by decide
  have hdescent : baseEnd_1507181 < baseStart_1507181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1507181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1507271 : List Nat := [1, 1, 4, 1, 1, 2, 1, 2, 3, 6]
def baseStart_1507271 : Nat := 118140960795 + 1507271 * 2 ^ 59
def prefixEnd_1507271 : Nat := 4983230072969 + 3 ^ 40 * 1507271 * 2
def baseEnd_1507271 : Nat := 515969666388718352653795

theorem tailTrace_1507271 : CollatzResearch.WordTrace tailWord_1507271 prefixEnd_1507271 515969666388718352653795 := by
  unfold tailWord_1507271
  simp only [CollatzResearch.WordTrace]
  refine ⟨54974689722422063237545667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36649793148281375491697111 54974689722422063237545667)
  ·
    refine ⟨82462034583633094856318501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54974689722422063237545667 82462034583633094856318501)
    ·
      refine ⟨15461631484431205285559719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82462034583633094856318501 15461631484431205285559719)
      ·
        refine ⟨23192447226646807928339579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15461631484431205285559719 23192447226646807928339579)
        ·
          refine ⟨34788670839970211892509369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23192447226646807928339579 34788670839970211892509369)
          ·
            refine ⟨26091503129977658919382027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34788670839970211892509369 26091503129977658919382027)
            ·
              refine ⟨39137254694966488379073041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26091503129977658919382027 39137254694966488379073041)
              ·
                refine ⟨29352941021224866284304781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39137254694966488379073041 29352941021224866284304781)
                ·
                  refine ⟨11007352882959324856614293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29352941021224866284304781 11007352882959324856614293)
                  ·
                    refine ⟨515969666388718352653795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11007352882959324856614293 515969666388718352653795)
                    ·
                      rfl

theorem cell22_1507271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 3, 6].length) (baseStart_1507271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1507271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1507271 prefixEnd_1507271 := by exact prefixLift 1507271
  have htrace : WordTrace (prefixWord ++ tailWord_1507271) baseStart_1507271 baseEnd_1507271 := by
    simpa [prefixWord, tailWord_1507271, baseEnd_1507271] using wordTrace_append hprefix tailTrace_1507271
  have hstable : (prefixWord ++ tailWord_1507271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1507271).length < 2 ^ (prefixWord ++ tailWord_1507271).sum := by decide
  have hdescent : baseEnd_1507271 < baseStart_1507271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1507271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1507290 : List Nat := [3, 1, 1, 2, 5, 1, 2, 1, 1, 5]
def baseStart_1507290 : Nat := 118140960795 + 1507290 * 2 ^ 59
def prefixEnd_1507290 : Nat := 4983230072969 + 3 ^ 40 * 1507290 * 2
def baseEnd_1507290 : Nat := 515976170477008636428737

theorem tailTrace_1507290 : CollatzResearch.WordTrace tailWord_1507290 prefixEnd_1507290 515976170477008636428737 := by
  unfold tailWord_1507290
  simp only [CollatzResearch.WordTrace]
  refine ⟨13743845677338307370621831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36650255139568819654991549 13743845677338307370621831)
  ·
    refine ⟨20615768516007461055932747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13743845677338307370621831 20615768516007461055932747)
    ·
      refine ⟨30923652774011191583899121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20615768516007461055932747 30923652774011191583899121)
      ·
        refine ⟨23192739580508393687924341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30923652774011191583899121 23192739580508393687924341)
        ·
          refine ⟨2174319335672661908242907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23192739580508393687924341 2174319335672661908242907)
          ·
            refine ⟨3261479003508992862364361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2174319335672661908242907 3261479003508992862364361)
            ·
              refine ⟨2446109252631744646773271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3261479003508992862364361 2446109252631744646773271)
              ·
                refine ⟨3669163878947616970159907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2446109252631744646773271 3669163878947616970159907)
                ·
                  refine ⟨5503745818421425455239861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3669163878947616970159907 5503745818421425455239861)
                  ·
                    refine ⟨515976170477008636428737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5503745818421425455239861 515976170477008636428737)
                    ·
                      rfl

theorem cell22_1507290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 2, 1, 1, 5].length) (baseStart_1507290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1507290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1507290 prefixEnd_1507290 := by exact prefixLift 1507290
  have htrace : WordTrace (prefixWord ++ tailWord_1507290) baseStart_1507290 baseEnd_1507290 := by
    simpa [prefixWord, tailWord_1507290, baseEnd_1507290] using wordTrace_append hprefix tailTrace_1507290
  have hstable : (prefixWord ++ tailWord_1507290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1507290).length < 2 ^ (prefixWord ++ tailWord_1507290).sum := by decide
  have hdescent : baseEnd_1507290 < baseStart_1507290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1507290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1507309 : List Nat := [1, 5, 1, 4, 1, 1, 2, 3, 4]
def baseStart_1507309 : Nat := 118140960795 + 1507309 * 2 ^ 59
def prefixEnd_1507309 : Nat := 4983230072969 + 3 ^ 40 * 1507309 * 2
def baseEnd_1507309 : Nat := 171994224855099640067893

theorem tailTrace_1507309 : CollatzResearch.WordTrace tailWord_1507309 prefixEnd_1507309 171994224855099640067893 := by
  unfold tailWord_1507309
  simp only [CollatzResearch.WordTrace]
  refine ⟨54976075696284395727428981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36650717130856263818285987 54976075696284395727428981)
  ·
    refine ⟨5154007096526662099446467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 54976075696284395727428981 5154007096526662099446467)
    ·
      refine ⟨7731010644789993149169701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5154007096526662099446467 7731010644789993149169701)
      ·
        refine ⟨1449564495898123715469319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7731010644789993149169701 1449564495898123715469319)
        ·
          refine ⟨2174346743847185573203979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1449564495898123715469319 2174346743847185573203979)
          ·
            refine ⟨3261520115770778359805969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2174346743847185573203979 3261520115770778359805969)
            ·
              refine ⟨2446140086828083769854477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3261520115770778359805969 2446140086828083769854477)
              ·
                refine ⟨917302532560531413695429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2446140086828083769854477 917302532560531413695429)
                ·
                  refine ⟨171994224855099640067893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 917302532560531413695429 171994224855099640067893)
                  ·
                    rfl

theorem cell22_1507309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 2, 3, 4].length) (baseStart_1507309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1507309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1507309 prefixEnd_1507309 := by exact prefixLift 1507309
  have htrace : WordTrace (prefixWord ++ tailWord_1507309) baseStart_1507309 baseEnd_1507309 := by
    simpa [prefixWord, tailWord_1507309, baseEnd_1507309] using wordTrace_append hprefix tailTrace_1507309
  have hstable : (prefixWord ++ tailWord_1507309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1507309).length < 2 ^ (prefixWord ++ tailWord_1507309).sum := by decide
  have hdescent : baseEnd_1507309 < baseStart_1507309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1507309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1507335 : List Nat := [1, 1, 4, 3, 1, 2, 1, 3, 3, 3]
def baseStart_1507335 : Nat := 118140960795 + 1507335 * 2 ^ 59
def prefixEnd_1507335 : Nat := 4983230072969 + 3 ^ 40 * 1507335 * 2
def baseEnd_1507335 : Nat := 515991574896643519053599

theorem tailTrace_1507335 : CollatzResearch.WordTrace tailWord_1507335 prefixEnd_1507335 515991574896643519053599 := by
  unfold tailWord_1507335
  simp only [CollatzResearch.WordTrace]
  refine ⟨54977023994190202167875459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36651349329460134778583639 54977023994190202167875459)
  ·
    refine ⟨82465535991285303251813189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54977023994190202167875459 82465535991285303251813189)
    ·
      refine ⟨15462287998365994359714973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82465535991285303251813189 15462287998365994359714973)
      ·
        refine ⟨5798357999387247884893115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15462287998365994359714973 5798357999387247884893115)
        ·
          refine ⟨8697536999080871827339673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5798357999387247884893115 8697536999080871827339673)
          ·
            refine ⟨6523152749310653870504755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8697536999080871827339673 6523152749310653870504755)
            ·
              refine ⟨9784729123965980805757133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6523152749310653870504755 9784729123965980805757133)
              ·
                refine ⟨3669273421487242802158925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9784729123965980805757133 3669273421487242802158925)
                ·
                  refine ⟨1375977533057716050809597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3669273421487242802158925 1375977533057716050809597)
                  ·
                    refine ⟨515991574896643519053599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1375977533057716050809597 515991574896643519053599)
                    ·
                      rfl

theorem cell22_1507335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 3, 3, 3].length) (baseStart_1507335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1507335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1507335 prefixEnd_1507335 := by exact prefixLift 1507335
  have htrace : WordTrace (prefixWord ++ tailWord_1507335) baseStart_1507335 baseEnd_1507335 := by
    simpa [prefixWord, tailWord_1507335, baseEnd_1507335] using wordTrace_append hprefix tailTrace_1507335
  have hstable : (prefixWord ++ tailWord_1507335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1507335).length < 2 ^ (prefixWord ++ tailWord_1507335).sum := by decide
  have hdescent : baseEnd_1507335 < baseStart_1507335 := by decide
  rcases family_descends (prefixWord ++ tailWord_1507335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1507341 : List Nat := [1, 7, 1, 2, 1, 2, 1, 1, 1, 5]
def baseStart_1507341 : Nat := 118140960795 + 1507341 * 2 ^ 59
def prefixEnd_1507341 : Nat := 4983230072969 + 3 ^ 40 * 1507341 * 2
def baseEnd_1507341 : Nat := 515993628819261503403581

theorem tailTrace_1507341 : CollatzResearch.WordTrace tailWord_1507341 prefixEnd_1507341 515993628819261503403581 := by
  unfold tailWord_1507341
  simp only [CollatzResearch.WordTrace]
  refine ⟨54977242832168465192593877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36651495221445643461729251 54977242832168465192593877)
  ·
    refine ⟨1288529128878948402951419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 54977242832168465192593877 1288529128878948402951419)
    ·
      refine ⟨1932793693318422604427129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1288529128878948402951419 1932793693318422604427129)
      ·
        refine ⟨1449595269988816953320347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1932793693318422604427129 1449595269988816953320347)
        ·
          refine ⟨2174392904983225429980521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1449595269988816953320347 2174392904983225429980521)
          ·
            refine ⟨1630794678737419072485391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2174392904983225429980521 1630794678737419072485391)
            ·
              refine ⟨2446192018106128608728087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1630794678737419072485391 2446192018106128608728087)
              ·
                refine ⟨3669288027159192913092131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2446192018106128608728087 3669288027159192913092131)
                ·
                  refine ⟨5503932040738789369638197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3669288027159192913092131 5503932040738789369638197)
                  ·
                    refine ⟨515993628819261503403581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5503932040738789369638197 515993628819261503403581)
                    ·
                      rfl

theorem cell22_1507341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_1507341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1507341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1507341 prefixEnd_1507341 := by exact prefixLift 1507341
  have htrace : WordTrace (prefixWord ++ tailWord_1507341) baseStart_1507341 baseEnd_1507341 := by
    simpa [prefixWord, tailWord_1507341, baseEnd_1507341] using wordTrace_append hprefix tailTrace_1507341
  have hstable : (prefixWord ++ tailWord_1507341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1507341).length < 2 ^ (prefixWord ++ tailWord_1507341).sum := by decide
  have hdescent : baseEnd_1507341 < baseStart_1507341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1507341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1507440 : List Nat := [2, 1, 1, 1, 5, 2, 2, 2, 2, 4]
def baseStart_1507440 : Nat := 118140960795 + 1507440 * 2 ^ 59
def prefixEnd_1507440 : Nat := 4983230072969 + 3 ^ 40 * 1507440 * 2
def baseEnd_1507440 : Nat := 516027518542458245178277

theorem tailTrace_1507440 : CollatzResearch.WordTrace tailWord_1507440 prefixEnd_1507440 516027518542458245178277 := by
  unfold tailWord_1507440
  simp only [CollatzResearch.WordTrace]
  refine ⟨27490426829404902550223887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36653902439206536733631849 27490426829404902550223887)
  ·
    refine ⟨41235640244107353825335831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27490426829404902550223887 41235640244107353825335831)
    ·
      refine ⟨61853460366161030738003747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41235640244107353825335831 61853460366161030738003747)
      ·
        refine ⟨92780190549241546107005621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61853460366161030738003747 92780190549241546107005621)
        ·
          refine ⟨8698142863991394947531777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 92780190549241546107005621 8698142863991394947531777)
          ·
            refine ⟨6523607147993546210648833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8698142863991394947531777 6523607147993546210648833)
            ·
              refine ⟨4892705360995159657986625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6523607147993546210648833 4892705360995159657986625)
              ·
                refine ⟨3669529020746369743489969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4892705360995159657986625 3669529020746369743489969)
                ·
                  refine ⟨2752146765559777307617477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3669529020746369743489969 2752146765559777307617477)
                  ·
                    refine ⟨516027518542458245178277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2752146765559777307617477 516027518542458245178277)
                    ·
                      rfl

theorem cell22_1507440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 2, 2, 4].length) (baseStart_1507440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1507440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1507440 prefixEnd_1507440 := by exact prefixLift 1507440
  have htrace : WordTrace (prefixWord ++ tailWord_1507440) baseStart_1507440 baseEnd_1507440 := by
    simpa [prefixWord, tailWord_1507440, baseEnd_1507440] using wordTrace_append hprefix tailTrace_1507440
  have hstable : (prefixWord ++ tailWord_1507440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1507440).length < 2 ^ (prefixWord ++ tailWord_1507440).sum := by decide
  have hdescent : baseEnd_1507440 < baseStart_1507440 := by decide
  rcases family_descends (prefixWord ++ tailWord_1507440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1507442 : List Nat := [3, 2, 1, 2, 2, 2, 1, 4, 2, 3]
def baseStart_1507442 : Nat := 118140960795 + 1507442 * 2 ^ 59
def prefixEnd_1507442 : Nat := 4983230072969 + 3 ^ 40 * 1507442 * 2
def baseEnd_1507442 : Nat := 516028203183330906628271

theorem tailTrace_1507442 : CollatzResearch.WordTrace tailWord_1507442 prefixEnd_1507442 516028203183330906628271 := by
  unfold tailWord_1507442
  simp only [CollatzResearch.WordTrace]
  refine ⟨13745231651200639860505145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36653951069868372961347053 13745231651200639860505145)
  ·
    refine ⟨10308923738400479895378859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13745231651200639860505145 10308923738400479895378859)
    ·
      refine ⟨15463385607600719843068289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10308923738400479895378859 15463385607600719843068289)
      ·
        refine ⟨11597539205700539882301217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15463385607600719843068289 11597539205700539882301217)
        ·
          refine ⟨8698154404275404911725913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11597539205700539882301217 8698154404275404911725913)
          ·
            refine ⟨6523615803206553683794435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8698154404275404911725913 6523615803206553683794435)
            ·
              refine ⟨9785423704809830525691653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6523615803206553683794435 9785423704809830525691653)
              ·
                refine ⟨1834766944651843223567185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9785423704809830525691653 1834766944651843223567185)
                ·
                  refine ⟨1376075208488882417675389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1834766944651843223567185 1376075208488882417675389)
                  ·
                    refine ⟨516028203183330906628271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1376075208488882417675389 516028203183330906628271)
                    ·
                      rfl

theorem cell22_1507442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 4, 2, 3].length) (baseStart_1507442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1507442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1507442 prefixEnd_1507442 := by exact prefixLift 1507442
  have htrace : WordTrace (prefixWord ++ tailWord_1507442) baseStart_1507442 baseEnd_1507442 := by
    simpa [prefixWord, tailWord_1507442, baseEnd_1507442] using wordTrace_append hprefix tailTrace_1507442
  have hstable : (prefixWord ++ tailWord_1507442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1507442).length < 2 ^ (prefixWord ++ tailWord_1507442).sum := by decide
  have hdescent : baseEnd_1507442 < baseStart_1507442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1507442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1507592 : List Nat := [2, 1, 3, 2, 3, 1, 1, 3, 2, 4]
def baseStart_1507592 : Nat := 118140960795 + 1507592 * 2 ^ 59
def prefixEnd_1507592 : Nat := 4983230072969 + 3 ^ 40 * 1507592 * 2
def baseEnd_1507592 : Nat := 516079551248780515377811

theorem tailTrace_1507592 : CollatzResearch.WordTrace tailWord_1507592 prefixEnd_1507592 516079551248780515377811 := by
  unfold tailWord_1507592
  simp only [CollatzResearch.WordTrace]
  refine ⟨27493198777129567529990515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36657598369506090039987353 27493198777129567529990515)
  ·
    refine ⟨41239798165694351294985773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27493198777129567529990515 41239798165694351294985773)
    ·
      refine ⟨15464924312135381735619665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41239798165694351294985773 15464924312135381735619665)
      ·
        refine ⟨11598693234101536301714749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15464924312135381735619665 11598693234101536301714749)
        ·
          refine ⟨4349509962788076113143031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11598693234101536301714749 4349509962788076113143031)
          ·
            refine ⟨6524264944182114169714547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4349509962788076113143031 6524264944182114169714547)
            ·
              refine ⟨9786397416273171254571821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6524264944182114169714547 9786397416273171254571821)
              ·
                refine ⟨3669899031102439220464433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9786397416273171254571821 3669899031102439220464433)
                ·
                  refine ⟨2752424273326829415348325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3669899031102439220464433 2752424273326829415348325)
                  ·
                    refine ⟨516079551248780515377811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2752424273326829415348325 516079551248780515377811)
                    ·
                      rfl

theorem cell22_1507592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 3, 2, 4].length) (baseStart_1507592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1507592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1507592 prefixEnd_1507592 := by exact prefixLift 1507592
  have htrace : WordTrace (prefixWord ++ tailWord_1507592) baseStart_1507592 baseEnd_1507592 := by
    simpa [prefixWord, tailWord_1507592, baseEnd_1507592] using wordTrace_append hprefix tailTrace_1507592
  have hstable : (prefixWord ++ tailWord_1507592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1507592).length < 2 ^ (prefixWord ++ tailWord_1507592).sum := by decide
  have hdescent : baseEnd_1507592 < baseStart_1507592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1507592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
