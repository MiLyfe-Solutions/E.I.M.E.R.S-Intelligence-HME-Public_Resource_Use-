import V185TrunkScan23Chunk0761

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4506118 : List Nat := [6, 2, 1, 1, 1, 1, 3, 2, 6]
def baseStart_4506118 : Nat := 118140960795 + 4506118 * 2 ^ 59
def prefixEnd_4506118 : Nat := 4983230072969 + 3 ^ 40 * 4506118 * 2
def baseEnd_4506118 : Nat := 257089379986300669589083

theorem tailTrace_4506118 : CollatzResearch.WordTrace tailWord_4506118 prefixEnd_4506118 257089379986300669589083 := by
  unfold tailWord_4506118
  simp only [CollatzResearch.WordTrace]
  refine ⟨5135988296534735766556969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 109567750326074363019882005 5135988296534735766556969)
  ·
    refine ⟨3851991222401051824917727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5135988296534735766556969 3851991222401051824917727)
    ·
      refine ⟨5777986833601577737376591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3851991222401051824917727 5777986833601577737376591)
      ·
        refine ⟨8666980250402366606064887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5777986833601577737376591 8666980250402366606064887)
        ·
          refine ⟨13000470375603549909097331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8666980250402366606064887 13000470375603549909097331)
          ·
            refine ⟨19500705563405324863645997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13000470375603549909097331 19500705563405324863645997)
            ·
              refine ⟨7312764586276996823867249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19500705563405324863645997 7312764586276996823867249)
              ·
                refine ⟨5484573439707747617900437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7312764586276996823867249 5484573439707747617900437)
                ·
                  refine ⟨257089379986300669589083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5484573439707747617900437 257089379986300669589083)
                  ·
                    rfl

theorem cell23_4506118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 3, 2, 6].length) (baseStart_4506118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4506118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4506118 prefixEnd_4506118 := by exact prefixLift 4506118
  have htrace : WordTrace (prefixWord ++ tailWord_4506118) baseStart_4506118 baseEnd_4506118 := by
    simpa [prefixWord, tailWord_4506118, baseEnd_4506118] using wordTrace_append hprefix tailTrace_4506118
  have hstable : (prefixWord ++ tailWord_4506118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4506118).length < 2 ^ (prefixWord ++ tailWord_4506118).sum := by decide
  have hdescent : baseEnd_4506118 < baseStart_4506118 := by decide
  rcases family_descends (prefixWord ++ tailWord_4506118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4506147 : List Nat := [1, 1, 1, 4, 4, 2, 1, 1, 1, 1, 6]
def baseStart_4506147 : Nat := 118140960795 + 4506147 * 2 ^ 59
def prefixEnd_4506147 : Nat := 4983230072969 + 3 ^ 40 * 4506147 * 2
def baseEnd_4506147 : Nat := 2313819310815686412839113

theorem tailTrace_4506147 : CollatzResearch.WordTrace tailWord_4506147 prefixEnd_4506147 2313819310815686412839113 := by
  unfold tailWord_4506147
  simp only [CollatzResearch.WordTrace]
  refine ⟨164352683206006482482628695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109568455470670988321752463 164352683206006482482628695)
  ·
    refine ⟨246529024809009723723943043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164352683206006482482628695 246529024809009723723943043)
    ·
      refine ⟨369793537213514585585914565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 246529024809009723723943043 369793537213514585585914565)
      ·
        refine ⟨69336288227533984797358981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 369793537213514585585914565 69336288227533984797358981)
        ·
          refine ⟨13000554042662622149504809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69336288227533984797358981 13000554042662622149504809)
          ·
            refine ⟨9750415531996966612128607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13000554042662622149504809 9750415531996966612128607)
            ·
              refine ⟨14625623297995449918192911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9750415531996966612128607 14625623297995449918192911)
              ·
                refine ⟨21938434946993174877289367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14625623297995449918192911 21938434946993174877289367)
                ·
                  refine ⟨32907652420489762315934051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21938434946993174877289367 32907652420489762315934051)
                  ·
                    refine ⟨49361478630734643473901077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32907652420489762315934051 49361478630734643473901077)
                    ·
                      refine ⟨2313819310815686412839113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49361478630734643473901077 2313819310815686412839113)
                      ·
                        rfl

theorem cell23_4506147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 1, 1, 1, 6].length) (baseStart_4506147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4506147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4506147 prefixEnd_4506147 := by exact prefixLift 4506147
  have htrace : WordTrace (prefixWord ++ tailWord_4506147) baseStart_4506147 baseEnd_4506147 := by
    simpa [prefixWord, tailWord_4506147, baseEnd_4506147] using wordTrace_append hprefix tailTrace_4506147
  have hstable : (prefixWord ++ tailWord_4506147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4506147).length < 2 ^ (prefixWord ++ tailWord_4506147).sum := by decide
  have hdescent : baseEnd_4506147 < baseStart_4506147 := by decide
  rcases family_descends (prefixWord ++ tailWord_4506147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4506167 : List Nat := [1, 1, 3, 1, 2, 3, 2, 1, 3, 3, 3]
def baseStart_4506167 : Nat := 118140960795 + 4506167 * 2 ^ 59
def prefixEnd_4506167 : Nat := 4983230072969 + 3 ^ 40 * 4506167 * 2
def baseEnd_4506167 : Nat := 2313829580428776334589021

theorem tailTrace_4506167 : CollatzResearch.WordTrace tailWord_4506167 prefixEnd_4506167 2313829580428776334589021 := by
  unfold tailWord_4506167
  simp only [CollatzResearch.WordTrace]
  refine ⟨164353412665934025898356755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109568941777289350598904503 164353412665934025898356755)
  ·
    refine ⟨246530118998901038847535133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164353412665934025898356755 246530118998901038847535133)
    ·
      refine ⟨92448794624587889567825675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 246530118998901038847535133 92448794624587889567825675)
      ·
        refine ⟨138673191936881834351738513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92448794624587889567825675 138673191936881834351738513)
        ·
          refine ⟨104004893952661375763803885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 138673191936881834351738513 104004893952661375763803885)
          ·
            refine ⟨39001835232248015911426457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 104004893952661375763803885 39001835232248015911426457)
            ·
              refine ⟨29251376424186011933569843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39001835232248015911426457 29251376424186011933569843)
              ·
                refine ⟨43877064636279017900354765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29251376424186011933569843 43877064636279017900354765)
                ·
                  refine ⟨16453899238604631712633037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43877064636279017900354765 16453899238604631712633037)
                  ·
                    refine ⟨6170212214476736892237389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16453899238604631712633037 6170212214476736892237389)
                    ·
                      refine ⟨2313829580428776334589021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6170212214476736892237389 2313829580428776334589021)
                      ·
                        rfl

theorem cell23_4506167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 1, 3, 3, 3].length) (baseStart_4506167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4506167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4506167 prefixEnd_4506167 := by exact prefixLift 4506167
  have htrace : WordTrace (prefixWord ++ tailWord_4506167) baseStart_4506167 baseEnd_4506167 := by
    simpa [prefixWord, tailWord_4506167, baseEnd_4506167] using wordTrace_append hprefix tailTrace_4506167
  have hstable : (prefixWord ++ tailWord_4506167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4506167).length < 2 ^ (prefixWord ++ tailWord_4506167).sum := by decide
  have hdescent : baseEnd_4506167 < baseStart_4506167 := by decide
  rcases family_descends (prefixWord ++ tailWord_4506167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4506244 : List Nat := [2, 3, 2, 1, 3, 1, 1, 1, 2, 4, 3]
def baseStart_4506244 : Nat := 118140960795 + 4506244 * 2 ^ 59
def prefixEnd_4506244 : Nat := 4983230072969 + 3 ^ 40 * 4506244 * 2
def baseEnd_4506244 : Nat := 2313869118439172533326167

theorem tailTrace_4506244 : CollatzResearch.WordTrace tailWord_4506244 prefixEnd_4506244 2313869118439172533326167 := by
  unfold tailWord_4506244
  simp only [CollatzResearch.WordTrace]
  refine ⟨82178110543327534024454893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109570814057770045365939857 82178110543327534024454893)
  ·
    refine ⟨30816791453747825259170585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82178110543327534024454893 30816791453747825259170585)
    ·
      refine ⟨23112593590310868944377939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30816791453747825259170585 23112593590310868944377939)
      ·
        refine ⟨34668890385466303416566909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23112593590310868944377939 34668890385466303416566909)
        ·
          refine ⟨13000833894549863781212591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34668890385466303416566909 13000833894549863781212591)
          ·
            refine ⟨19501250841824795671818887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13000833894549863781212591 19501250841824795671818887)
            ·
              refine ⟨29251876262737193507728331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19501250841824795671818887 29251876262737193507728331)
              ·
                refine ⟨43877814394105790261592497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29251876262737193507728331 43877814394105790261592497)
                ·
                  refine ⟨32908360795579342696194373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43877814394105790261592497 32908360795579342696194373)
                  ·
                    refine ⟨6170317649171126755536445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32908360795579342696194373 6170317649171126755536445)
                    ·
                      refine ⟨2313869118439172533326167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6170317649171126755536445 2313869118439172533326167)
                      ·
                        rfl

theorem cell23_4506244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 1, 2, 4, 3].length) (baseStart_4506244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4506244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4506244 prefixEnd_4506244 := by exact prefixLift 4506244
  have htrace : WordTrace (prefixWord ++ tailWord_4506244) baseStart_4506244 baseEnd_4506244 := by
    simpa [prefixWord, tailWord_4506244, baseEnd_4506244] using wordTrace_append hprefix tailTrace_4506244
  have hstable : (prefixWord ++ tailWord_4506244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4506244).length < 2 ^ (prefixWord ++ tailWord_4506244).sum := by decide
  have hdescent : baseEnd_4506244 < baseStart_4506244 := by decide
  rcases family_descends (prefixWord ++ tailWord_4506244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4506247 : List Nat := [1, 1, 4, 2, 1, 2, 2, 3, 7]
def baseStart_4506247 : Nat := 118140960795 + 4506247 * 2 ^ 59
def prefixEnd_4506247 : Nat := 4983230072969 + 3 ^ 40 * 4506247 * 2
def baseEnd_4506247 : Nat := 257096739875681780176517

theorem tailTrace_4506247 : CollatzResearch.WordTrace tailWord_4506247 prefixEnd_4506247 257096739875681780176517 := by
  unfold tailWord_4506247
  simp only [CollatzResearch.WordTrace]
  refine ⟨164356330505644199561268995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109570887003762799707512663 164356330505644199561268995)
  ·
    refine ⟨246534495758466299341903493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164356330505644199561268995 246534495758466299341903493)
    ·
      refine ⟨46225217954712431126606905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 246534495758466299341903493 46225217954712431126606905)
      ·
        refine ⟨34668913466034323344955179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46225217954712431126606905 34668913466034323344955179)
        ·
          refine ⟨52003370199051485017432769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34668913466034323344955179 52003370199051485017432769)
          ·
            refine ⟨39002527649288613763074577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52003370199051485017432769 39002527649288613763074577)
            ·
              refine ⟨29251895736966460322305933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39002527649288613763074577 29251895736966460322305933)
              ·
                refine ⟨10969460901362422620864725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29251895736966460322305933 10969460901362422620864725)
                ·
                  refine ⟨257096739875681780176517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10969460901362422620864725 257096739875681780176517)
                  ·
                    rfl

theorem cell23_4506247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 3, 7].length) (baseStart_4506247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4506247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4506247 prefixEnd_4506247 := by exact prefixLift 4506247
  have htrace : WordTrace (prefixWord ++ tailWord_4506247) baseStart_4506247 baseEnd_4506247 := by
    simpa [prefixWord, tailWord_4506247, baseEnd_4506247] using wordTrace_append hprefix tailTrace_4506247
  have hstable : (prefixWord ++ tailWord_4506247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4506247).length < 2 ^ (prefixWord ++ tailWord_4506247).sum := by decide
  have hdescent : baseEnd_4506247 < baseStart_4506247 := by decide
  rcases family_descends (prefixWord ++ tailWord_4506247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4506254 : List Nat := [4, 1, 1, 3, 1, 1, 3, 1, 2, 2, 4]
def baseStart_4506254 : Nat := 118140960795 + 4506254 * 2 ^ 59
def prefixEnd_4506254 : Nat := 4983230072969 + 3 ^ 40 * 4506254 * 2
def baseEnd_4506254 : Nat := 2313874253245717494201121

theorem tailTrace_4506254 : CollatzResearch.WordTrace tailWord_4506254 prefixEnd_4506254 2313874253245717494201121 := by
  unfold tailWord_4506254
  simp only [CollatzResearch.WordTrace]
  refine ⟨20544573227077354969596727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109571057211079226504515877 20544573227077354969596727)
  ·
    refine ⟨30816859840616032454395091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20544573227077354969596727 30816859840616032454395091)
    ·
      refine ⟨46225289760924048681592637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30816859840616032454395091 46225289760924048681592637)
      ·
        refine ⟨17334483660346518255597239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46225289760924048681592637 17334483660346518255597239)
        ·
          refine ⟨26001725490519777383395859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17334483660346518255597239 26001725490519777383395859)
          ·
            refine ⟨39002588235779666075093789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26001725490519777383395859 39002588235779666075093789)
            ·
              refine ⟨14625970588417374778160171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39002588235779666075093789 14625970588417374778160171)
              ·
                refine ⟨21938955882626062167240257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14625970588417374778160171 21938955882626062167240257)
                ·
                  refine ⟨16454216911969546625430193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21938955882626062167240257 16454216911969546625430193)
                  ·
                    refine ⟨12340662683977159969072645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16454216911969546625430193 12340662683977159969072645)
                    ·
                      refine ⟨2313874253245717494201121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12340662683977159969072645 2313874253245717494201121)
                      ·
                        rfl

theorem cell23_4506254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_4506254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4506254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4506254 prefixEnd_4506254 := by exact prefixLift 4506254
  have htrace : WordTrace (prefixWord ++ tailWord_4506254) baseStart_4506254 baseEnd_4506254 := by
    simpa [prefixWord, tailWord_4506254, baseEnd_4506254] using wordTrace_append hprefix tailTrace_4506254
  have hstable : (prefixWord ++ tailWord_4506254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4506254).length < 2 ^ (prefixWord ++ tailWord_4506254).sum := by decide
  have hdescent : baseEnd_4506254 < baseStart_4506254 := by decide
  rcases family_descends (prefixWord ++ tailWord_4506254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4506258 : List Nat := [3, 2, 3, 1, 2, 2, 2, 1, 1, 4, 2]
def baseStart_4506258 : Nat := 118140960795 + 4506258 * 2 ^ 59
def prefixEnd_4506258 : Nat := 4983230072969 + 3 ^ 40 * 4506258 * 2
def baseEnd_4506258 : Nat := 2313876307168335478551103

theorem tailTrace_4506258 : CollatzResearch.WordTrace tailWord_4506258 prefixEnd_4506258 2313876307168335478551103 := by
  unfold tailWord_4506258
  simp only [CollatzResearch.WordTrace]
  refine ⟨41089182927151087109979857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109571154472402898959946285 41089182927151087109979857)
  ·
    refine ⟨30816887195363315332484893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41089182927151087109979857 30816887195363315332484893)
    ·
      refine ⟨11556332698261243249681835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30816887195363315332484893 11556332698261243249681835)
      ·
        refine ⟨17334499047391864874522753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11556332698261243249681835 17334499047391864874522753)
        ·
          refine ⟨13000874285543898655892065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17334499047391864874522753 13000874285543898655892065)
          ·
            refine ⟨9750655714157923991919049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13000874285543898655892065 9750655714157923991919049)
            ·
              refine ⟨7312991785618442993939287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9750655714157923991919049 7312991785618442993939287)
              ·
                refine ⟨10969487678427664490908931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7312991785618442993939287 10969487678427664490908931)
                ·
                  refine ⟨16454231517641496736363397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10969487678427664490908931 16454231517641496736363397)
                  ·
                    refine ⟨3085168409557780638068137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16454231517641496736363397 3085168409557780638068137)
                    ·
                      refine ⟨2313876307168335478551103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3085168409557780638068137 2313876307168335478551103)
                      ·
                        rfl

theorem cell23_4506258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 2, 1, 1, 4, 2].length) (baseStart_4506258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4506258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4506258 prefixEnd_4506258 := by exact prefixLift 4506258
  have htrace : WordTrace (prefixWord ++ tailWord_4506258) baseStart_4506258 baseEnd_4506258 := by
    simpa [prefixWord, tailWord_4506258, baseEnd_4506258] using wordTrace_append hprefix tailTrace_4506258
  have hstable : (prefixWord ++ tailWord_4506258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4506258).length < 2 ^ (prefixWord ++ tailWord_4506258).sum := by decide
  have hdescent : baseEnd_4506258 < baseStart_4506258 := by decide
  rcases family_descends (prefixWord ++ tailWord_4506258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4506279 : List Nat := [1, 1, 6, 3, 2, 1, 2, 1, 1, 3, 2]
def baseStart_4506279 : Nat := 118140960795 + 4506279 * 2 ^ 59
def prefixEnd_4506279 : Nat := 4983230072969 + 3 ^ 40 * 4506279 * 2
def baseEnd_4506279 : Nat := 2313887090262079896388507

theorem tailTrace_4506279 : CollatzResearch.WordTrace tailWord_4506279 prefixEnd_4506279 2313887090262079896388507 := by
  unfold tailWord_4506279
  simp only [CollatzResearch.WordTrace]
  refine ⟨164357497641528269026433891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109571665094352179350955927 164357497641528269026433891)
  ·
    refine ⟨246536246462292403539650837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164357497641528269026433891 246536246462292403539650837)
    ·
      refine ⟨11556386552919956415921133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 246536246462292403539650837 11556386552919956415921133)
      ·
        refine ⟨4333644957344983655970425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11556386552919956415921133 4333644957344983655970425)
        ·
          refine ⟨3250233718008737741977819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4333644957344983655970425 3250233718008737741977819)
          ·
            refine ⟨4875350577013106612966729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3250233718008737741977819 4875350577013106612966729)
            ·
              refine ⟨3656512932759829959725047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4875350577013106612966729 3656512932759829959725047)
              ·
                refine ⟨5484769399139744939587571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3656512932759829959725047 5484769399139744939587571)
                ·
                  refine ⟨8227154098709617409381357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5484769399139744939587571 8227154098709617409381357)
                  ·
                    refine ⟨3085182787016106528518009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8227154098709617409381357 3085182787016106528518009)
                    ·
                      refine ⟨2313887090262079896388507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3085182787016106528518009 2313887090262079896388507)
                      ·
                        rfl

theorem cell23_4506279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_4506279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4506279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4506279 prefixEnd_4506279 := by exact prefixLift 4506279
  have htrace : WordTrace (prefixWord ++ tailWord_4506279) baseStart_4506279 baseEnd_4506279 := by
    simpa [prefixWord, tailWord_4506279, baseEnd_4506279] using wordTrace_append hprefix tailTrace_4506279
  have hstable : (prefixWord ++ tailWord_4506279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4506279).length < 2 ^ (prefixWord ++ tailWord_4506279).sum := by decide
  have hdescent : baseEnd_4506279 < baseStart_4506279 := by decide
  rcases family_descends (prefixWord ++ tailWord_4506279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4506314 : List Nat := [3, 1, 2, 1, 4, 1, 1, 2, 1, 3, 4]
def baseStart_4506314 : Nat := 118140960795 + 4506314 * 2 ^ 59
def prefixEnd_4506314 : Nat := 4983230072969 + 3 ^ 40 * 4506314 * 2
def baseEnd_4506314 : Nat := 2313905062084987259450845

theorem tailTrace_4506314 : CollatzResearch.WordTrace tailWord_4506314 prefixEnd_4506314 2313905062084987259450845 := by
  unfold tailWord_4506314
  simp only [CollatzResearch.WordTrace]
  refine ⟨41089693549100367500989499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109572516130934313335971997 41089693549100367500989499)
  ·
    refine ⟨61634540323650551251484249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41089693549100367500989499 61634540323650551251484249)
    ·
      refine ⟨46225905242737913438613187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61634540323650551251484249 46225905242737913438613187)
      ·
        refine ⟨69338857864106870157919781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46225905242737913438613187 69338857864106870157919781)
        ·
          refine ⟨13001035849520038154609959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69338857864106870157919781 13001035849520038154609959)
          ·
            refine ⟨19501553774280057231914939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13001035849520038154609959 19501553774280057231914939)
            ·
              refine ⟨29252330661420085847872409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19501553774280057231914939 29252330661420085847872409)
              ·
                refine ⟨21939247996065064385904307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29252330661420085847872409 21939247996065064385904307)
                ·
                  refine ⟨32908871994097596578856461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21939247996065064385904307 32908871994097596578856461)
                  ·
                    refine ⟨12340826997786598717071173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32908871994097596578856461 12340826997786598717071173)
                    ·
                      refine ⟨2313905062084987259450845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12340826997786598717071173 2313905062084987259450845)
                      ·
                        rfl

theorem cell23_4506314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 2, 1, 3, 4].length) (baseStart_4506314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4506314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4506314 prefixEnd_4506314 := by exact prefixLift 4506314
  have htrace : WordTrace (prefixWord ++ tailWord_4506314) baseStart_4506314 baseEnd_4506314 := by
    simpa [prefixWord, tailWord_4506314, baseEnd_4506314] using wordTrace_append hprefix tailTrace_4506314
  have hstable : (prefixWord ++ tailWord_4506314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4506314).length < 2 ^ (prefixWord ++ tailWord_4506314).sum := by decide
  have hdescent : baseEnd_4506314 < baseStart_4506314 := by decide
  rcases family_descends (prefixWord ++ tailWord_4506314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4506351 : List Nat := [1, 1, 2, 1, 5, 3, 1, 2, 2, 2, 3]
def baseStart_4506351 : Nat := 118140960795 + 4506351 * 2 ^ 59
def prefixEnd_4506351 : Nat := 4983230072969 + 3 ^ 40 * 4506351 * 2
def baseEnd_4506351 : Nat := 2313924060869203614688175

theorem tailTrace_4506351 : CollatzResearch.WordTrace tailWord_4506351 prefixEnd_4506351 2313924060869203614688175 := by
  unfold tailWord_4506351
  simp only [CollatzResearch.WordTrace]
  refine ⟨164360123697267425323054907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109573415798178283548703271 164360123697267425323054907)
  ·
    refine ⟨246540185545901137984582361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164360123697267425323054907 246540185545901137984582361)
    ·
      refine ⟨184905139159425853488436771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 246540185545901137984582361 184905139159425853488436771)
      ·
        refine ⟨277357708739138780232655157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184905139159425853488436771 277357708739138780232655157)
        ·
          refine ⟨26002285194294260646811421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 277357708739138780232655157 26002285194294260646811421)
          ·
            refine ⟨9750856947860347742554283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26002285194294260646811421 9750856947860347742554283)
            ·
              refine ⟨14626285421790521613831425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9750856947860347742554283 14626285421790521613831425)
              ·
                refine ⟨10969714066342891210373569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14626285421790521613831425 10969714066342891210373569)
                ·
                  refine ⟨8227285549757168407780177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10969714066342891210373569 8227285549757168407780177)
                  ·
                    refine ⟨6170464162317876305835133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8227285549757168407780177 6170464162317876305835133)
                    ·
                      refine ⟨2313924060869203614688175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6170464162317876305835133 2313924060869203614688175)
                      ·
                        rfl

theorem cell23_4506351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 2, 2, 2, 3].length) (baseStart_4506351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4506351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4506351 prefixEnd_4506351 := by exact prefixLift 4506351
  have htrace : WordTrace (prefixWord ++ tailWord_4506351) baseStart_4506351 baseEnd_4506351 := by
    simpa [prefixWord, tailWord_4506351, baseEnd_4506351] using wordTrace_append hprefix tailTrace_4506351
  have hstable : (prefixWord ++ tailWord_4506351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4506351).length < 2 ^ (prefixWord ++ tailWord_4506351).sum := by decide
  have hdescent : baseEnd_4506351 < baseStart_4506351 := by decide
  rcases family_descends (prefixWord ++ tailWord_4506351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4506354 : List Nat := [3, 2, 1, 3, 1, 2, 2, 1, 8]
def baseStart_4506354 : Nat := 118140960795 + 4506354 * 2 ^ 59
def prefixEnd_4506354 : Nat := 4983230072969 + 3 ^ 40 * 4506354 * 2
def baseEnd_4506354 : Nat := 257102844590129678105629

theorem tailTrace_4506354 : CollatzResearch.WordTrace tailWord_4506354 prefixEnd_4506354 257102844590129678105629 := by
  unfold tailWord_4506354
  simp only [CollatzResearch.WordTrace]
  refine ⟨41090058279064139208853529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109573488744171037890276077 41090058279064139208853529)
  ·
    refine ⟨30817543709298104406640147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41090058279064139208853529 30817543709298104406640147)
    ·
      refine ⟨46226315563947156609960221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30817543709298104406640147 46226315563947156609960221)
      ·
        refine ⟨17334868336480183728735083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46226315563947156609960221 17334868336480183728735083)
        ·
          refine ⟨26002302504720275593102625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17334868336480183728735083 26002302504720275593102625)
          ·
            refine ⟨19501726878540206694826969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26002302504720275593102625 19501726878540206694826969)
            ·
              refine ⟨14626295158905155021120227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19501726878540206694826969 14626295158905155021120227)
              ·
                refine ⟨21939442738357732531680341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14626295158905155021120227 21939442738357732531680341)
                ·
                  refine ⟨257102844590129678105629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21939442738357732531680341 257102844590129678105629)
                  ·
                    rfl

theorem cell23_4506354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 1, 8].length) (baseStart_4506354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4506354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4506354 prefixEnd_4506354 := by exact prefixLift 4506354
  have htrace : WordTrace (prefixWord ++ tailWord_4506354) baseStart_4506354 baseEnd_4506354 := by
    simpa [prefixWord, tailWord_4506354, baseEnd_4506354] using wordTrace_append hprefix tailTrace_4506354
  have hstable : (prefixWord ++ tailWord_4506354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4506354).length < 2 ^ (prefixWord ++ tailWord_4506354).sum := by decide
  have hdescent : baseEnd_4506354 < baseStart_4506354 := by decide
  rcases family_descends (prefixWord ++ tailWord_4506354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4506367 : List Nat := [1, 1, 2, 2, 1, 3, 1, 1, 2, 9]
def baseStart_4506367 : Nat := 118140960795 + 4506367 * 2 ^ 59
def prefixEnd_4506367 : Nat := 4983230072969 + 3 ^ 40 * 4506367 * 2
def baseEnd_4506367 : Nat := 771310758853225184029367

theorem tailTrace_4506367 : CollatzResearch.WordTrace tailWord_4506367 prefixEnd_4506367 771310758853225184029367 := by
  unfold tailWord_4506367
  simp only [CollatzResearch.WordTrace]
  refine ⟨164360707265209460055637355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109573804843472973370424903 164360707265209460055637355)
  ·
    refine ⟨246541060897814190083456033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164360707265209460055637355 246541060897814190083456033)
    ·
      refine ⟨184905795673360642562592025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 246541060897814190083456033 184905795673360642562592025)
      ·
        refine ⟨138679346755020481921944019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 184905795673360642562592025 138679346755020481921944019)
        ·
          refine ⟨208019020132530722882916029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138679346755020481921944019 208019020132530722882916029)
          ·
            refine ⟨78007132549699021081093511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 208019020132530722882916029 78007132549699021081093511)
            ·
              refine ⟨117010698824548531621640267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78007132549699021081093511 117010698824548531621640267)
              ·
                refine ⟨175516048236822797432460401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 117010698824548531621640267 175516048236822797432460401)
                ·
                  refine ⟨131637036177617098074345301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 175516048236822797432460401 131637036177617098074345301)
                  ·
                    refine ⟨771310758853225184029367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 131637036177617098074345301 771310758853225184029367)
                    ·
                      rfl

theorem cell23_4506367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 9].length) (baseStart_4506367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4506367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4506367 prefixEnd_4506367 := by exact prefixLift 4506367
  have htrace : WordTrace (prefixWord ++ tailWord_4506367) baseStart_4506367 baseEnd_4506367 := by
    simpa [prefixWord, tailWord_4506367, baseEnd_4506367] using wordTrace_append hprefix tailTrace_4506367
  have hstable : (prefixWord ++ tailWord_4506367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4506367).length < 2 ^ (prefixWord ++ tailWord_4506367).sum := by decide
  have hdescent : baseEnd_4506367 < baseStart_4506367 := by decide
  rcases family_descends (prefixWord ++ tailWord_4506367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4506408 : List Nat := [2, 1, 5, 1, 1, 1, 1, 4, 2, 3, 2]
def baseStart_4506408 : Nat := 118140960795 + 4506408 * 2 ^ 59
def prefixEnd_4506408 : Nat := 4983230072969 + 3 ^ 40 * 4506408 * 2
def baseEnd_4506408 : Nat := 2313953329266509891675413

theorem tailTrace_4506408 : CollatzResearch.WordTrace tailWord_4506408 prefixEnd_4506408 2313953329266509891675413 := by
  unfold tailWord_4506408
  simp only [CollatzResearch.WordTrace]
  refine ⟨82181101329030462028939939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109574801772040616038586585 82181101329030462028939939)
  ·
    refine ⟨123271651993545693043409909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82181101329030462028939939 123271651993545693043409909)
    ·
      refine ⟨11556717374394908722819679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 123271651993545693043409909 11556717374394908722819679)
      ·
        refine ⟨17335076061592363084229519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11556717374394908722819679 17335076061592363084229519)
        ·
          refine ⟨26002614092388544626344279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17335076061592363084229519 26002614092388544626344279)
          ·
            refine ⟨39003921138582816939516419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26002614092388544626344279 39003921138582816939516419)
            ·
              refine ⟨58505881707874225409274629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39003921138582816939516419 58505881707874225409274629)
              ·
                refine ⟨10969852820226417264238993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58505881707874225409274629 10969852820226417264238993)
                ·
                  refine ⟨8227389615169812948179245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10969852820226417264238993 8227389615169812948179245)
                  ·
                    refine ⟨3085271105688679855567217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8227389615169812948179245 3085271105688679855567217)
                    ·
                      refine ⟨2313953329266509891675413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3085271105688679855567217 2313953329266509891675413)
                      ·
                        rfl

theorem cell23_4506408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 4, 2, 3, 2].length) (baseStart_4506408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4506408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4506408 prefixEnd_4506408 := by exact prefixLift 4506408
  have htrace : WordTrace (prefixWord ++ tailWord_4506408) baseStart_4506408 baseEnd_4506408 := by
    simpa [prefixWord, tailWord_4506408, baseEnd_4506408] using wordTrace_append hprefix tailTrace_4506408
  have hstable : (prefixWord ++ tailWord_4506408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4506408).length < 2 ^ (prefixWord ++ tailWord_4506408).sum := by decide
  have hdescent : baseEnd_4506408 < baseStart_4506408 := by decide
  rcases family_descends (prefixWord ++ tailWord_4506408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4506421 : List Nat := [1, 3, 3, 1, 3, 1, 1, 2, 3, 1, 4]
def baseStart_4506421 : Nat := 118140960795 + 4506421 * 2 ^ 59
def prefixEnd_4506421 : Nat := 4983230072969 + 3 ^ 40 * 4506421 * 2
def baseEnd_4506421 : Nat := 2313960004515018340812853

theorem tailTrace_4506421 : CollatzResearch.WordTrace tailWord_4506421 prefixEnd_4506421 2313960004515018340812853 := by
  unfold tailWord_4506421
  simp only [CollatzResearch.WordTrace]
  refine ⟨164362676807013827278103117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109575117871342551518735411 164362676807013827278103117)
  ·
    refine ⟨61636003802630185229288669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 164362676807013827278103117 61636003802630185229288669)
    ·
      refine ⟨23113501425986319460983251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61636003802630185229288669 23113501425986319460983251)
      ·
        refine ⟨34670252138979479191474877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23113501425986319460983251 34670252138979479191474877)
        ·
          refine ⟨13001344552117304696803079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34670252138979479191474877 13001344552117304696803079)
          ·
            refine ⟨19502016828175957045204619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13001344552117304696803079 19502016828175957045204619)
            ·
              refine ⟨29253025242263935567806929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19502016828175957045204619 29253025242263935567806929)
              ·
                refine ⟨21939768931697951675855197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29253025242263935567806929 21939768931697951675855197)
                ·
                  refine ⟨8227413349386731878445699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21939768931697951675855197 8227413349386731878445699)
                  ·
                    refine ⟨12341120024080097817668549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8227413349386731878445699 12341120024080097817668549)
                    ·
                      refine ⟨2313960004515018340812853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12341120024080097817668549 2313960004515018340812853)
                      ·
                        rfl

theorem cell23_4506421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 2, 3, 1, 4].length) (baseStart_4506421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4506421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4506421 prefixEnd_4506421 := by exact prefixLift 4506421
  have htrace : WordTrace (prefixWord ++ tailWord_4506421) baseStart_4506421 baseEnd_4506421 := by
    simpa [prefixWord, tailWord_4506421, baseEnd_4506421] using wordTrace_append hprefix tailTrace_4506421
  have hstable : (prefixWord ++ tailWord_4506421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4506421).length < 2 ^ (prefixWord ++ tailWord_4506421).sum := by decide
  have hdescent : baseEnd_4506421 < baseStart_4506421 := by decide
  rcases family_descends (prefixWord ++ tailWord_4506421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4506424 : List Nat := [2, 1, 2, 1, 3, 2, 2, 1, 3, 1, 5]
def baseStart_4506424 : Nat := 118140960795 + 4506424 * 2 ^ 59
def prefixEnd_4506424 : Nat := 4983230072969 + 3 ^ 40 * 4506424 * 2
def baseEnd_4506424 : Nat := 2313961544956981829075339

theorem tailTrace_4506424 : CollatzResearch.WordTrace tailWord_4506424 prefixEnd_4506424 2313961544956981829075339 := by
  unfold tailWord_4506424
  simp only [CollatzResearch.WordTrace]
  refine ⟨82181393113001479395231163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109575190817335305860308217 82181393113001479395231163)
  ·
    refine ⟨123272089669502219092846745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82181393113001479395231163 123272089669502219092846745)
    ·
      refine ⟨92454067252126664319635059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123272089669502219092846745 92454067252126664319635059)
      ·
        refine ⟨138681100878189996479452589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92454067252126664319635059 138681100878189996479452589)
        ·
          refine ⟨52005412829321248679794721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 138681100878189996479452589 52005412829321248679794721)
          ·
            refine ⟨39004059621990936509846041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52005412829321248679794721 39004059621990936509846041)
            ·
              refine ⟨29253044716493202382384531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39004059621990936509846041 29253044716493202382384531)
              ·
                refine ⟨43879567074739803573576797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29253044716493202382384531 43879567074739803573576797)
                ·
                  refine ⟨16454837653027426340091299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43879567074739803573576797 16454837653027426340091299)
                  ·
                    refine ⟨24682256479541139510136949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16454837653027426340091299 24682256479541139510136949)
                    ·
                      refine ⟨2313961544956981829075339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24682256479541139510136949 2313961544956981829075339)
                      ·
                        rfl

theorem cell23_4506424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 1, 3, 1, 5].length) (baseStart_4506424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4506424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4506424 prefixEnd_4506424 := by exact prefixLift 4506424
  have htrace : WordTrace (prefixWord ++ tailWord_4506424) baseStart_4506424 baseEnd_4506424 := by
    simpa [prefixWord, tailWord_4506424, baseEnd_4506424] using wordTrace_append hprefix tailTrace_4506424
  have hstable : (prefixWord ++ tailWord_4506424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4506424).length < 2 ^ (prefixWord ++ tailWord_4506424).sum := by decide
  have hdescent : baseEnd_4506424 < baseStart_4506424 := by decide
  rcases family_descends (prefixWord ++ tailWord_4506424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4506431 : List Nat := [1, 1, 2, 2, 5, 2, 2, 1, 1, 6]
def baseStart_4506431 : Nat := 118140960795 + 4506431 * 2 ^ 59
def prefixEnd_4506431 : Nat := 4983230072969 + 3 ^ 40 * 4506431 * 2
def baseEnd_4506431 : Nat := 771321713107187767229269

theorem tailTrace_4506431 : CollatzResearch.WordTrace tailWord_4506431 prefixEnd_4506431 771321713107187767229269 := by
  unfold tailWord_4506431
  simp only [CollatzResearch.WordTrace]
  refine ⟨164363041536977598985967147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109575361024651732657311431 164363041536977598985967147)
  ·
    refine ⟨246544562305466398478950721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164363041536977598985967147 246544562305466398478950721)
    ·
      refine ⟨184908421729099798859213041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 246544562305466398478950721 184908421729099798859213041)
      ·
        refine ⟨138681316296824849144409781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 184908421729099798859213041 138681316296824849144409781)
        ·
          refine ⟨13001373402827329607288417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 138681316296824849144409781 13001373402827329607288417)
          ·
            refine ⟨9751030052120497205466313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13001373402827329607288417 9751030052120497205466313)
            ·
              refine ⟨7313272539090372904099735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9751030052120497205466313 7313272539090372904099735)
              ·
                refine ⟨10969908808635559356149603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7313272539090372904099735 10969908808635559356149603)
                ·
                  refine ⟨16454863212953339034224405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10969908808635559356149603 16454863212953339034224405)
                  ·
                    refine ⟨771321713107187767229269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16454863212953339034224405 771321713107187767229269)
                    ·
                      rfl

theorem cell23_4506431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 2, 1, 1, 6].length) (baseStart_4506431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4506431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4506431 prefixEnd_4506431 := by exact prefixLift 4506431
  have htrace : WordTrace (prefixWord ++ tailWord_4506431) baseStart_4506431 baseEnd_4506431 := by
    simpa [prefixWord, tailWord_4506431, baseEnd_4506431] using wordTrace_append hprefix tailTrace_4506431
  have hstable : (prefixWord ++ tailWord_4506431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4506431).length < 2 ^ (prefixWord ++ tailWord_4506431).sum := by decide
  have hdescent : baseEnd_4506431 < baseStart_4506431 := by decide
  rcases family_descends (prefixWord ++ tailWord_4506431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4506441 : List Nat := [1, 2, 1, 1, 2, 5, 2, 1, 3, 2, 3]
def baseStart_4506441 : Nat := 118140960795 + 4506441 * 2 ^ 59
def prefixEnd_4506441 : Nat := 4983230072969 + 3 ^ 40 * 4506441 * 2
def baseEnd_4506441 : Nat := 2313970274128108262562761

theorem tailTrace_4506441 : CollatzResearch.WordTrace tailWord_4506441 prefixEnd_4506441 2313970274128108262562761 := by
  unfold tailWord_4506441
  simp only [CollatzResearch.WordTrace]
  refine ⟨164363406266941370693831177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109575604177960913795887451 164363406266941370693831177)
  ·
    refine ⟨123272554700206028020373383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164363406266941370693831177 123272554700206028020373383)
    ·
      refine ⟨184908832050309042030560075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123272554700206028020373383 184908832050309042030560075)
      ·
        refine ⟨277363248075463563045840113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184908832050309042030560075 277363248075463563045840113)
        ·
          refine ⟨208022436056597672284380085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 277363248075463563045840113 208022436056597672284380085)
          ·
            refine ⟨19502103380306031776660633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 208022436056597672284380085 19502103380306031776660633)
            ·
              refine ⟨14626577535229523832495475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19502103380306031776660633 14626577535229523832495475)
              ·
                refine ⟨21939866302844285748743213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14626577535229523832495475 21939866302844285748743213)
                ·
                  refine ⟨8227449863566607155778705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21939866302844285748743213 8227449863566607155778705)
                  ·
                    refine ⟨6170587397674955366834029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8227449863566607155778705 6170587397674955366834029)
                    ·
                      refine ⟨2313970274128108262562761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6170587397674955366834029 2313970274128108262562761)
                      ·
                        rfl

theorem cell23_4506441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 1, 3, 2, 3].length) (baseStart_4506441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4506441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4506441 prefixEnd_4506441 := by exact prefixLift 4506441
  have htrace : WordTrace (prefixWord ++ tailWord_4506441) baseStart_4506441 baseEnd_4506441 := by
    simpa [prefixWord, tailWord_4506441, baseEnd_4506441] using wordTrace_append hprefix tailTrace_4506441
  have hstable : (prefixWord ++ tailWord_4506441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4506441).length < 2 ^ (prefixWord ++ tailWord_4506441).sum := by decide
  have hdescent : baseEnd_4506441 < baseStart_4506441 := by decide
  rcases family_descends (prefixWord ++ tailWord_4506441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4506452 : List Nat := [2, 4, 1, 1, 5, 1, 2, 1, 1, 5]
def baseStart_4506452 : Nat := 118140960795 + 4506452 * 2 ^ 59
def prefixEnd_4506452 : Nat := 4983230072969 + 3 ^ 40 * 4506452 * 2
def baseEnd_4506452 : Nat := 771325307471769239841737

theorem tailTrace_4506452 : CollatzResearch.WordTrace tailWord_4506452 prefixEnd_4506452 771325307471769239841737 := by
  unfold tailWord_4506452
  simp only [CollatzResearch.WordTrace]
  refine ⟨82181903734950759786240805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109575871646601013048321073 82181903734950759786240805)
  ·
    refine ⟨15409106950303267459920151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82181903734950759786240805 15409106950303267459920151)
    ·
      refine ⟨23113660425454901189880227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15409106950303267459920151 23113660425454901189880227)
      ·
        refine ⟨34670490638182351784820341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23113660425454901189880227 34670490638182351784820341)
        ·
          refine ⟨3250358497329595479826907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 34670490638182351784820341 3250358497329595479826907)
          ·
            refine ⟨4875537745994393219740361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3250358497329595479826907 4875537745994393219740361)
            ·
              refine ⟨3656653309495794914805271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4875537745994393219740361 3656653309495794914805271)
              ·
                refine ⟨5484979964243692372207907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3656653309495794914805271 5484979964243692372207907)
                ·
                  refine ⟨8227469946365538558311861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5484979964243692372207907 8227469946365538558311861)
                  ·
                    refine ⟨771325307471769239841737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8227469946365538558311861 771325307471769239841737)
                    ·
                      rfl

theorem cell23_4506452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 2, 1, 1, 5].length) (baseStart_4506452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4506452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4506452 prefixEnd_4506452 := by exact prefixLift 4506452
  have htrace : WordTrace (prefixWord ++ tailWord_4506452) baseStart_4506452 baseEnd_4506452 := by
    simpa [prefixWord, tailWord_4506452, baseEnd_4506452] using wordTrace_append hprefix tailTrace_4506452
  have hstable : (prefixWord ++ tailWord_4506452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4506452).length < 2 ^ (prefixWord ++ tailWord_4506452).sum := by decide
  have hdescent : baseEnd_4506452 < baseStart_4506452 := by decide
  rcases family_descends (prefixWord ++ tailWord_4506452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4506455 : List Nat := [1, 1, 3, 2, 4, 3, 2, 1, 1, 1, 4]
def baseStart_4506455 : Nat := 118140960795 + 4506455 * 2 ^ 59
def prefixEnd_4506455 : Nat := 4983230072969 + 3 ^ 40 * 4506455 * 2
def baseEnd_4506455 : Nat := 2313977462857271207787697

theorem tailTrace_4506455 : CollatzResearch.WordTrace tailWord_4506455 prefixEnd_4506455 2313977462857271207787697 := by
  unfold tailWord_4506455
  simp only [CollatzResearch.WordTrace]
  refine ⟨164363916888890651084840819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109575944592593767389893879 164363916888890651084840819)
  ·
    refine ⟨246545875333335976627261229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164363916888890651084840819 246545875333335976627261229)
    ·
      refine ⟨92454703250000991235222961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 246545875333335976627261229 92454703250000991235222961)
      ·
        refine ⟨69341027437500743426417221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92454703250000991235222961 69341027437500743426417221)
        ·
          refine ⟨13001442644531389392453229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69341027437500743426417221 13001442644531389392453229)
          ·
            refine ⟨4875540991699271022169961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13001442644531389392453229 4875540991699271022169961)
            ·
              refine ⟨3656655743774453266627471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4875540991699271022169961 3656655743774453266627471)
              ·
                refine ⟨5484983615661679899941207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3656655743774453266627471 5484983615661679899941207)
                ·
                  refine ⟨8227475423492519849911811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5484983615661679899941207 8227475423492519849911811)
                  ·
                    refine ⟨12341213135238779774867717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8227475423492519849911811 12341213135238779774867717)
                    ·
                      refine ⟨2313977462857271207787697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12341213135238779774867717 2313977462857271207787697)
                      ·
                        rfl

theorem cell23_4506455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 2, 1, 1, 1, 4].length) (baseStart_4506455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4506455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4506455 prefixEnd_4506455 := by exact prefixLift 4506455
  have htrace : WordTrace (prefixWord ++ tailWord_4506455) baseStart_4506455 baseEnd_4506455 := by
    simpa [prefixWord, tailWord_4506455, baseEnd_4506455] using wordTrace_append hprefix tailTrace_4506455
  have hstable : (prefixWord ++ tailWord_4506455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4506455).length < 2 ^ (prefixWord ++ tailWord_4506455).sum := by decide
  have hdescent : baseEnd_4506455 < baseStart_4506455 := by decide
  rcases family_descends (prefixWord ++ tailWord_4506455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4506458 : List Nat := [3, 1, 1, 2, 1, 5, 1, 3, 1, 2, 3]
def baseStart_4506458 : Nat := 118140960795 + 4506458 * 2 ^ 59
def prefixEnd_4506458 : Nat := 4983230072969 + 3 ^ 40 * 4506458 * 2
def baseEnd_4506458 : Nat := 2313979003299234696050183

theorem tailTrace_4506458 : CollatzResearch.WordTrace tailWord_4506458 prefixEnd_4506458 2313979003299234696050183 := by
  unfold tailWord_4506458
  simp only [CollatzResearch.WordTrace]
  refine ⟨41091006576969945649300007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109576017538586521731466685 41091006576969945649300007)
  ·
    refine ⟨61636509865454918473950011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41091006576969945649300007 61636509865454918473950011)
    ·
      refine ⟨92454764798182377710925017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61636509865454918473950011 92454764798182377710925017)
      ·
        refine ⟨69341073598636783283193763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92454764798182377710925017 69341073598636783283193763)
        ·
          refine ⟨104011610397955174924790645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69341073598636783283193763 104011610397955174924790645)
          ·
            refine ⟨9751088474808297649199123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 104011610397955174924790645 9751088474808297649199123)
            ·
              refine ⟨14626632712212446473798685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9751088474808297649199123 14626632712212446473798685)
              ·
                refine ⟨5484987267079667427674507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14626632712212446473798685 5484987267079667427674507)
                ·
                  refine ⟨8227480900619501141511761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5484987267079667427674507 8227480900619501141511761)
                  ·
                    refine ⟨6170610675464625856133821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8227480900619501141511761 6170610675464625856133821)
                    ·
                      refine ⟨2313979003299234696050183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6170610675464625856133821 2313979003299234696050183)
                      ·
                        rfl

theorem cell23_4506458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 3, 1, 2, 3].length) (baseStart_4506458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4506458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4506458 prefixEnd_4506458 := by exact prefixLift 4506458
  have htrace : WordTrace (prefixWord ++ tailWord_4506458) baseStart_4506458 baseEnd_4506458 := by
    simpa [prefixWord, tailWord_4506458, baseEnd_4506458] using wordTrace_append hprefix tailTrace_4506458
  have hstable : (prefixWord ++ tailWord_4506458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4506458).length < 2 ^ (prefixWord ++ tailWord_4506458).sum := by decide
  have hdescent : baseEnd_4506458 < baseStart_4506458 := by decide
  rcases family_descends (prefixWord ++ tailWord_4506458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4506472 : List Nat := [2, 1, 4, 2, 1, 2, 2, 4, 1, 2, 2]
def baseStart_4506472 : Nat := 118140960795 + 4506472 * 2 ^ 59
def prefixEnd_4506472 : Nat := 4983230072969 + 3 ^ 40 * 4506472 * 2
def baseEnd_4506472 : Nat := 2313986192028397641275119

theorem tailTrace_4506472 : CollatzResearch.WordTrace tailWord_4506472 prefixEnd_4506472 2313986192028397641275119 := by
  unfold tailWord_4506472
  simp only [CollatzResearch.WordTrace]
  refine ⟨82182268464914531494104835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109576357953219375325473113 82182268464914531494104835)
  ·
    refine ⟨123273402697371797241157253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82182268464914531494104835 123273402697371797241157253)
    ·
      refine ⟨23113763005757211982716985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 123273402697371797241157253 23113763005757211982716985)
      ·
        refine ⟨17335322254317908987037739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23113763005757211982716985 17335322254317908987037739)
        ·
          refine ⟨26002983381476863480556609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17335322254317908987037739 26002983381476863480556609)
          ·
            refine ⟨19502237536107647610417457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26002983381476863480556609 19502237536107647610417457)
            ·
              refine ⟨14626678152080735707813093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19502237536107647610417457 14626678152080735707813093)
              ·
                refine ⟨2742502153515137945214955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14626678152080735707813093 2742502153515137945214955)
                ·
                  refine ⟨4113753230272706917822433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2742502153515137945214955 4113753230272706917822433)
                  ·
                    refine ⟨3085314922704530188366825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4113753230272706917822433 3085314922704530188366825)
                    ·
                      refine ⟨2313986192028397641275119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3085314922704530188366825 2313986192028397641275119)
                      ·
                        rfl

theorem cell23_4506472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 4, 1, 2, 2].length) (baseStart_4506472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4506472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4506472 prefixEnd_4506472 := by exact prefixLift 4506472
  have htrace : WordTrace (prefixWord ++ tailWord_4506472) baseStart_4506472 baseEnd_4506472 := by
    simpa [prefixWord, tailWord_4506472, baseEnd_4506472] using wordTrace_append hprefix tailTrace_4506472
  have hstable : (prefixWord ++ tailWord_4506472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4506472).length < 2 ^ (prefixWord ++ tailWord_4506472).sum := by decide
  have hdescent : baseEnd_4506472 < baseStart_4506472 := by decide
  rcases family_descends (prefixWord ++ tailWord_4506472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4506585 : List Nat := [1, 2, 1, 2, 5, 1, 4, 2, 5]
def baseStart_4506585 : Nat := 118140960795 + 4506585 * 2 ^ 59
def prefixEnd_4506585 : Nat := 4983230072969 + 3 ^ 40 * 4506585 * 2
def baseEnd_4506585 : Nat := 257116023926928411018011

theorem tailTrace_4506585 : CollatzResearch.WordTrace tailWord_4506585 prefixEnd_4506585 257116023926928411018011 := by
  unfold tailWord_4506585
  simp only [CollatzResearch.WordTrace]
  refine ⟨164368658378419683287073209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109579105585613122191382139 164368658378419683287073209)
  ·
    refine ⟨123276493783814762465304907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164368658378419683287073209 123276493783814762465304907)
    ·
      refine ⟨184914740675722143697957361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123276493783814762465304907 184914740675722143697957361)
      ·
        refine ⟨138686055506791607773468021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 184914740675722143697957361 138686055506791607773468021)
        ·
          refine ⟨13001817703761713228762627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 138686055506791607773468021 13001817703761713228762627)
          ·
            refine ⟨19502726555642569843143941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13001817703761713228762627 19502726555642569843143941)
            ·
              refine ⟨3656761229182981845589489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19502726555642569843143941 3656761229182981845589489)
              ·
                refine ⟨2742570921887236384192117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3656761229182981845589489 2742570921887236384192117)
                ·
                  refine ⟨257116023926928411018011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2742570921887236384192117 257116023926928411018011)
                  ·
                    rfl

theorem cell23_4506585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 4, 2, 5].length) (baseStart_4506585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4506585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4506585 prefixEnd_4506585 := by exact prefixLift 4506585
  have htrace : WordTrace (prefixWord ++ tailWord_4506585) baseStart_4506585 baseEnd_4506585 := by
    simpa [prefixWord, tailWord_4506585, baseEnd_4506585] using wordTrace_append hprefix tailTrace_4506585
  have hstable : (prefixWord ++ tailWord_4506585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4506585).length < 2 ^ (prefixWord ++ tailWord_4506585).sum := by decide
  have hdescent : baseEnd_4506585 < baseStart_4506585 := by decide
  rcases family_descends (prefixWord ++ tailWord_4506585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4506631 : List Nat := [1, 1, 4, 3, 1, 1, 1, 1, 1, 3, 6]
def baseStart_4506631 : Nat := 118140960795 + 4506631 * 2 ^ 59
def prefixEnd_4506631 : Nat := 4983230072969 + 3 ^ 40 * 4506631 * 2
def baseEnd_4506631 : Nat := 2314067835452462519186887

theorem tailTrace_4506631 : CollatzResearch.WordTrace tailWord_4506631 prefixEnd_4506631 2314067835452462519186887 := by
  unfold tailWord_4506631
  simp only [CollatzResearch.WordTrace]
  refine ⟨164370336136253033143247747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109580224090835355428831831 164370336136253033143247747)
  ·
    refine ⟨246555504204379549714871621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164370336136253033143247747 246555504204379549714871621)
    ·
      refine ⟨46229157038321165571538429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 246555504204379549714871621 46229157038321165571538429)
      ·
        refine ⟨17335933889370437089326911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46229157038321165571538429 17335933889370437089326911)
        ·
          refine ⟨26003900834055655633990367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17335933889370437089326911 26003900834055655633990367)
          ·
            refine ⟨39005851251083483450985551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26003900834055655633990367 39005851251083483450985551)
            ·
              refine ⟨58508776876625225176478327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39005851251083483450985551 58508776876625225176478327)
              ·
                refine ⟨87763165314937837764717491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58508776876625225176478327 87763165314937837764717491)
                ·
                  refine ⟨131644747972406756647076237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 87763165314937837764717491 131644747972406756647076237)
                  ·
                    refine ⟨49366780489652533742653589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 131644747972406756647076237 49366780489652533742653589)
                    ·
                      refine ⟨2314067835452462519186887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49366780489652533742653589 2314067835452462519186887)
                      ·
                        rfl

theorem cell23_4506631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_4506631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4506631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4506631 prefixEnd_4506631 := by exact prefixLift 4506631
  have htrace : WordTrace (prefixWord ++ tailWord_4506631) baseStart_4506631 baseEnd_4506631 := by
    simpa [prefixWord, tailWord_4506631, baseEnd_4506631] using wordTrace_append hprefix tailTrace_4506631
  have hstable : (prefixWord ++ tailWord_4506631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4506631).length < 2 ^ (prefixWord ++ tailWord_4506631).sum := by decide
  have hdescent : baseEnd_4506631 < baseStart_4506631 := by decide
  rcases family_descends (prefixWord ++ tailWord_4506631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4506645 : List Nat := [1, 3, 2, 1, 4, 2, 2, 1, 3, 4]
def baseStart_4506645 : Nat := 118140960795 + 4506645 * 2 ^ 59
def prefixEnd_4506645 : Nat := 4983230072969 + 3 ^ 40 * 4506645 * 2
def baseEnd_4506645 : Nat := 771358341393875154803941

theorem tailTrace_4506645 : CollatzResearch.WordTrace tailWord_4506645 prefixEnd_4506645 771358341393875154803941 := by
  unfold tailWord_4506645
  simp only [CollatzResearch.WordTrace]
  refine ⟨164370846758202313534257389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109580564505468209022838259 164370846758202313534257389)
  ·
    refine ⟨61639067534325867575346521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 164370846758202313534257389 61639067534325867575346521)
    ·
      refine ⟨46229300650744400681509891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61639067534325867575346521 46229300650744400681509891)
      ·
        refine ⟨69343950976116601022264837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46229300650744400681509891 69343950976116601022264837)
        ·
          refine ⟨13001990808021862691674657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69343950976116601022264837 13001990808021862691674657)
          ·
            refine ⟨9751493106016397018755993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13001990808021862691674657 9751493106016397018755993)
            ·
              refine ⟨7313619829512297764066995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9751493106016397018755993 7313619829512297764066995)
              ·
                refine ⟨10970429744268446646100493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7313619829512297764066995 10970429744268446646100493)
                ·
                  refine ⟨4113911154100667492287685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10970429744268446646100493 4113911154100667492287685)
                  ·
                    refine ⟨771358341393875154803941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4113911154100667492287685 771358341393875154803941)
                    ·
                      rfl

theorem cell23_4506645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 2, 1, 3, 4].length) (baseStart_4506645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4506645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4506645 prefixEnd_4506645 := by exact prefixLift 4506645
  have htrace : WordTrace (prefixWord ++ tailWord_4506645) baseStart_4506645 baseEnd_4506645 := by
    simpa [prefixWord, tailWord_4506645, baseEnd_4506645] using wordTrace_append hprefix tailTrace_4506645
  have hstable : (prefixWord ++ tailWord_4506645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4506645).length < 2 ^ (prefixWord ++ tailWord_4506645).sum := by decide
  have hdescent : baseEnd_4506645 < baseStart_4506645 := by decide
  rcases family_descends (prefixWord ++ tailWord_4506645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4506661 : List Nat := [1, 3, 1, 2, 2, 2, 1, 2, 1, 2, 6]
def baseStart_4506661 : Nat := 118140960795 + 4506661 * 2 ^ 59
def prefixEnd_4506661 : Nat := 4983230072969 + 3 ^ 40 * 4506661 * 2
def baseEnd_4506661 : Nat := 2314083239872097401811749

theorem tailTrace_4506661 : CollatzResearch.WordTrace tailWord_4506661 prefixEnd_4506661 2314083239872097401811749 := by
  unfold tailWord_4506661
  simp only [CollatzResearch.WordTrace]
  refine ⟨164371430326144348266839837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109580953550762898844559891 164371430326144348266839837)
  ·
    refine ⟨61639286372304130600064939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 164371430326144348266839837 61639286372304130600064939)
    ·
      refine ⟨92458929558456195900097409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61639286372304130600064939 92458929558456195900097409)
      ·
        refine ⟨69344197168842146925073057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92458929558456195900097409 69344197168842146925073057)
        ·
          refine ⟨52008147876631610193804793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69344197168842146925073057 52008147876631610193804793)
          ·
            refine ⟨39006110907473707645353595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52008147876631610193804793 39006110907473707645353595)
            ·
              refine ⟨58509166361210561468030393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39006110907473707645353595 58509166361210561468030393)
              ·
                refine ⟨43881874770907921101022795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58509166361210561468030393 43881874770907921101022795)
                ·
                  refine ⟨65822812156361881651534193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43881874770907921101022795 65822812156361881651534193)
                  ·
                    refine ⟨49367109117271411238650645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 65822812156361881651534193 49367109117271411238650645)
                    ·
                      refine ⟨2314083239872097401811749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49367109117271411238650645 2314083239872097401811749)
                      ·
                        rfl

theorem cell23_4506661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 2, 1, 2, 6].length) (baseStart_4506661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4506661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4506661 prefixEnd_4506661 := by exact prefixLift 4506661
  have htrace : WordTrace (prefixWord ++ tailWord_4506661) baseStart_4506661 baseEnd_4506661 := by
    simpa [prefixWord, tailWord_4506661, baseEnd_4506661] using wordTrace_append hprefix tailTrace_4506661
  have hstable : (prefixWord ++ tailWord_4506661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4506661).length < 2 ^ (prefixWord ++ tailWord_4506661).sum := by decide
  have hdescent : baseEnd_4506661 < baseStart_4506661 := by decide
  rcases family_descends (prefixWord ++ tailWord_4506661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4506671 : List Nat := [1, 1, 2, 1, 2, 1, 1, 2, 7, 5]
def baseStart_4506671 : Nat := 118140960795 + 4506671 * 2 ^ 59
def prefixEnd_4506671 : Nat := 4983230072969 + 3 ^ 40 * 4506671 * 2
def baseEnd_4506671 : Nat := 771362791559547454228901

theorem tailTrace_4506671 : CollatzResearch.WordTrace tailWord_4506671 prefixEnd_4506671 771362791559547454228901 := by
  unfold tailWord_4506671
  simp only [CollatzResearch.WordTrace]
  refine ⟨164371795056108119974703867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109581196704072079983135911 164371795056108119974703867)
  ·
    refine ⟨246557692584162179962055801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164371795056108119974703867 246557692584162179962055801)
    ·
      refine ⟨184918269438121634971541851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 246557692584162179962055801 184918269438121634971541851)
      ·
        refine ⟨277377404157182452457312777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184918269438121634971541851 277377404157182452457312777)
        ·
          refine ⟨208033053117886839342984583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 277377404157182452457312777 208033053117886839342984583)
          ·
            refine ⟨312049579676830259014476875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 208033053117886839342984583 312049579676830259014476875)
            ·
              refine ⟨468074369515245388521715313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 312049579676830259014476875 468074369515245388521715313)
              ·
                refine ⟨351055777136434041391286485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 468074369515245388521715313 351055777136434041391286485)
                ·
                  refine ⟨8227869776635172845108277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 351055777136434041391286485 8227869776635172845108277)
                  ·
                    refine ⟨771362791559547454228901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8227869776635172845108277 771362791559547454228901)
                    ·
                      rfl

theorem cell23_4506671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 7, 5].length) (baseStart_4506671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4506671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4506671 prefixEnd_4506671 := by exact prefixLift 4506671
  have htrace : WordTrace (prefixWord ++ tailWord_4506671) baseStart_4506671 baseEnd_4506671 := by
    simpa [prefixWord, tailWord_4506671, baseEnd_4506671] using wordTrace_append hprefix tailTrace_4506671
  have hstable : (prefixWord ++ tailWord_4506671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4506671).length < 2 ^ (prefixWord ++ tailWord_4506671).sum := by decide
  have hdescent : baseEnd_4506671 < baseStart_4506671 := by decide
  rcases family_descends (prefixWord ++ tailWord_4506671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4506688 : List Nat := [2, 1, 1, 2, 2, 3, 1, 5, 1, 5]
def baseStart_4506688 : Nat := 118140960795 + 4506688 * 2 ^ 59
def prefixEnd_4506688 : Nat := 4983230072969 + 3 ^ 40 * 4506688 * 2
def baseEnd_4506688 : Nat := 771365701283256265391375

theorem tailTrace_4506688 : CollatzResearch.WordTrace tailWord_4506688 prefixEnd_4506688 771365701283256265391375 := by
  unfold tailWord_4506688
  simp only [CollatzResearch.WordTrace]
  refine ⟨82186207548523265939036359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109581610064697687918715145 82186207548523265939036359)
  ·
    refine ⟨123279311322784898908554539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82186207548523265939036359 123279311322784898908554539)
    ·
      refine ⟨184918966984177348362831809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123279311322784898908554539 184918966984177348362831809)
      ·
        refine ⟨138689225238133011272123857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 184918966984177348362831809 138689225238133011272123857)
        ·
          refine ⟨104016918928599758454092893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 138689225238133011272123857 104016918928599758454092893)
          ·
            refine ⟨39006344598224909420284835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 104016918928599758454092893 39006344598224909420284835)
            ·
              refine ⟨58509516897337364130427253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39006344598224909420284835 58509516897337364130427253)
              ·
                refine ⟨5485267209125377887227555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 58509516897337364130427253 5485267209125377887227555)
                ·
                  refine ⟨8227900813688066830841333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5485267209125377887227555 8227900813688066830841333)
                  ·
                    refine ⟨771365701283256265391375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8227900813688066830841333 771365701283256265391375)
                    ·
                      rfl

theorem cell23_4506688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 5, 1, 5].length) (baseStart_4506688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4506688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4506688 prefixEnd_4506688 := by exact prefixLift 4506688
  have htrace : WordTrace (prefixWord ++ tailWord_4506688) baseStart_4506688 baseEnd_4506688 := by
    simpa [prefixWord, tailWord_4506688, baseEnd_4506688] using wordTrace_append hprefix tailTrace_4506688
  have hstable : (prefixWord ++ tailWord_4506688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4506688).length < 2 ^ (prefixWord ++ tailWord_4506688).sum := by decide
  have hdescent : baseEnd_4506688 < baseStart_4506688 := by decide
  rcases family_descends (prefixWord ++ tailWord_4506688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4506695 : List Nat := [1, 1, 4, 1, 3, 2, 1, 1, 4, 3, 2]
def baseStart_4506695 : Nat := 118140960795 + 4506695 * 2 ^ 59
def prefixEnd_4506695 : Nat := 4983230072969 + 3 ^ 40 * 4506695 * 2
def baseEnd_4506695 : Nat := 2314100698214350268786593

theorem tailTrace_4506695 : CollatzResearch.WordTrace tailWord_4506695 prefixEnd_4506695 2314100698214350268786593 := by
  unfold tailWord_4506695
  simp only [CollatzResearch.WordTrace]
  refine ⟨164372670408021172073577539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109581780272014114715718359 164372670408021172073577539)
  ·
    refine ⟨246559005612031758110366309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164372670408021172073577539 246559005612031758110366309)
    ·
      refine ⟨46229813552255954645693683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 246559005612031758110366309 46229813552255954645693683)
      ·
        refine ⟨69344720328383931968540525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46229813552255954645693683 69344720328383931968540525)
        ·
          refine ⟨26004270123143974488202697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69344720328383931968540525 26004270123143974488202697)
          ·
            refine ⟨19503202592357980866152023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26004270123143974488202697 19503202592357980866152023)
            ·
              refine ⟨29254803888536971299228035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19503202592357980866152023 29254803888536971299228035)
              ·
                refine ⟨43882205832805456948842053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29254803888536971299228035 43882205832805456948842053)
                ·
                  refine ⟨8227913593651023177907885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43882205832805456948842053 8227913593651023177907885)
                  ·
                    refine ⟨3085467597619133691715457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8227913593651023177907885 3085467597619133691715457)
                    ·
                      refine ⟨2314100698214350268786593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3085467597619133691715457 2314100698214350268786593)
                      ·
                        rfl

theorem cell23_4506695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 1, 4, 3, 2].length) (baseStart_4506695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4506695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4506695 prefixEnd_4506695 := by exact prefixLift 4506695
  have htrace : WordTrace (prefixWord ++ tailWord_4506695) baseStart_4506695 baseEnd_4506695 := by
    simpa [prefixWord, tailWord_4506695, baseEnd_4506695] using wordTrace_append hprefix tailTrace_4506695
  have hstable : (prefixWord ++ tailWord_4506695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4506695).length < 2 ^ (prefixWord ++ tailWord_4506695).sum := by decide
  have hdescent : baseEnd_4506695 < baseStart_4506695 := by decide
  rcases family_descends (prefixWord ++ tailWord_4506695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4506722 : List Nat := [3, 3, 2, 2, 1, 1, 3, 2, 1, 5]
def baseStart_4506722 : Nat := 118140960795 + 4506722 * 2 ^ 59
def prefixEnd_4506722 : Nat := 4983230072969 + 3 ^ 40 * 4506722 * 2
def baseEnd_4506722 : Nat := 771371520730673887716323

theorem tailTrace_4506722 : CollatzResearch.WordTrace tailWord_4506722 prefixEnd_4506722 771371520730673887716323 := by
  unfold tailWord_4506722
  simp only [CollatzResearch.WordTrace]
  refine ⟨41093413794730838921202605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109582436785948903789873613 41093413794730838921202605)
  ·
    refine ⟨15410030173024064595450977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41093413794730838921202605 15410030173024064595450977)
    ·
      refine ⟨11557522629768048446588233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15410030173024064595450977 11557522629768048446588233)
      ·
        refine ⟨8668141972326036334941175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11557522629768048446588233 8668141972326036334941175)
        ·
          refine ⟨13002212958489054502411763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8668141972326036334941175 13002212958489054502411763)
          ·
            refine ⟨19503319437733581753617645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13002212958489054502411763 19503319437733581753617645)
            ·
              refine ⟨7313744789150093157606617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19503319437733581753617645 7313744789150093157606617)
              ·
                refine ⟨5485308591862569868204963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7313744789150093157606617 5485308591862569868204963)
                ·
                  refine ⟨8227962887793854802307445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5485308591862569868204963 8227962887793854802307445)
                  ·
                    refine ⟨771371520730673887716323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8227962887793854802307445 771371520730673887716323)
                    ·
                      rfl

theorem cell23_4506722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 3, 2, 1, 5].length) (baseStart_4506722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4506722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4506722 prefixEnd_4506722 := by exact prefixLift 4506722
  have htrace : WordTrace (prefixWord ++ tailWord_4506722) baseStart_4506722 baseEnd_4506722 := by
    simpa [prefixWord, tailWord_4506722, baseEnd_4506722] using wordTrace_append hprefix tailTrace_4506722
  have hstable : (prefixWord ++ tailWord_4506722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4506722).length < 2 ^ (prefixWord ++ tailWord_4506722).sum := by decide
  have hdescent : baseEnd_4506722 < baseStart_4506722 := by decide
  rcases family_descends (prefixWord ++ tailWord_4506722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4506751 : List Nat := [1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 8]
def baseStart_4506751 : Nat := 118140960795 + 4506751 * 2 ^ 59
def prefixEnd_4506751 : Nat := 4983230072969 + 3 ^ 40 * 4506751 * 2
def baseEnd_4506751 : Nat := 2314129453131002049686335

theorem tailTrace_4506751 : CollatzResearch.WordTrace tailWord_4506751 prefixEnd_4506751 2314129453131002049686335 := by
  unfold tailWord_4506751
  simp only [CollatzResearch.WordTrace]
  refine ⟨164374712895818293637616107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109583141930545529091744071 164374712895818293637616107)
  ·
    refine ⟨246562069343727440456424161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164374712895818293637616107 246562069343727440456424161)
    ·
      refine ⟨184921552007795580342318121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 246562069343727440456424161 184921552007795580342318121)
      ·
        refine ⟨138691164005846685256738591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 184921552007795580342318121 138691164005846685256738591)
        ·
          refine ⟨208036746008770027885107887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138691164005846685256738591 208036746008770027885107887)
          ·
            refine ⟨312055119013155041827661831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 208036746008770027885107887 312055119013155041827661831)
            ·
              refine ⟨468082678519732562741492747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 312055119013155041827661831 468082678519732562741492747)
              ·
                refine ⟨702124017779598844112239121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 468082678519732562741492747 702124017779598844112239121)
                ·
                  refine ⟨526593013334699133084179341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 702124017779598844112239121 526593013334699133084179341)
                  ·
                    refine ⟨197472380000512174906567253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 526593013334699133084179341 197472380000512174906567253)
                    ·
                      refine ⟨2314129453131002049686335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 197472380000512174906567253 2314129453131002049686335)
                      ·
                        rfl

theorem cell23_4506751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 8].length) (baseStart_4506751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4506751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4506751 prefixEnd_4506751 := by exact prefixLift 4506751
  have htrace : WordTrace (prefixWord ++ tailWord_4506751) baseStart_4506751 baseEnd_4506751 := by
    simpa [prefixWord, tailWord_4506751, baseEnd_4506751] using wordTrace_append hprefix tailTrace_4506751
  have hstable : (prefixWord ++ tailWord_4506751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4506751).length < 2 ^ (prefixWord ++ tailWord_4506751).sum := by decide
  have hdescent : baseEnd_4506751 < baseStart_4506751 := by decide
  rcases family_descends (prefixWord ++ tailWord_4506751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4506775 : List Nat := [1, 1, 3, 3, 3, 1, 1, 3, 1, 3, 3]
def baseStart_4506775 : Nat := 118140960795 + 4506775 * 2 ^ 59
def prefixEnd_4506775 : Nat := 4983230072969 + 3 ^ 40 * 4506775 * 2
def baseEnd_4506775 : Nat := 2314141776666709955786225

theorem tailTrace_4506775 : CollatzResearch.WordTrace tailWord_4506775 prefixEnd_4506775 2314141776666709955786225 := by
  unfold tailWord_4506775
  simp only [CollatzResearch.WordTrace]
  refine ⟨164375588247731345736489779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109583725498487563824326519 164375588247731345736489779)
  ·
    refine ⟨246563382371597018604734669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164375588247731345736489779 246563382371597018604734669)
    ·
      refine ⟨92461268389348881976775501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 246563382371597018604734669 92461268389348881976775501)
      ·
        refine ⟨34672975646005830741290813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92461268389348881976775501 34672975646005830741290813)
        ·
          refine ⟨13002365867252186527984055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34672975646005830741290813 13002365867252186527984055)
          ·
            refine ⟨19503548800878279791976083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13002365867252186527984055 19503548800878279791976083)
            ·
              refine ⟨29255323201317419687964125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19503548800878279791976083 29255323201317419687964125)
              ·
                refine ⟨10970746200494032382986547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29255323201317419687964125 10970746200494032382986547)
                ·
                  refine ⟨16456119300741048574479821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10970746200494032382986547 16456119300741048574479821)
                  ·
                    refine ⟨6171044737777893215429933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16456119300741048574479821 6171044737777893215429933)
                    ·
                      refine ⟨2314141776666709955786225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6171044737777893215429933 2314141776666709955786225)
                      ·
                        rfl

theorem cell23_4506775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 3, 1, 3, 3].length) (baseStart_4506775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4506775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4506775 prefixEnd_4506775 := by exact prefixLift 4506775
  have htrace : WordTrace (prefixWord ++ tailWord_4506775) baseStart_4506775 baseEnd_4506775 := by
    simpa [prefixWord, tailWord_4506775, baseEnd_4506775] using wordTrace_append hprefix tailTrace_4506775
  have hstable : (prefixWord ++ tailWord_4506775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4506775).length < 2 ^ (prefixWord ++ tailWord_4506775).sum := by decide
  have hdescent : baseEnd_4506775 < baseStart_4506775 := by decide
  rcases family_descends (prefixWord ++ tailWord_4506775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4506782 : List Nat := [4, 3, 1, 1, 2, 2, 3, 7]
def baseStart_4506782 : Nat := 118140960795 + 4506782 * 2 ^ 59
def prefixEnd_4506782 : Nat := 4983230072969 + 3 ^ 40 * 4506782 * 2
def baseEnd_4506782 : Nat := 85709087815973756607359

theorem tailTrace_4506782 : CollatzResearch.WordTrace tailWord_4506782 prefixEnd_4506782 85709087815973756607359 := by
  unfold tailWord_4506782
  simp only [CollatzResearch.WordTrace]
  refine ⟨20546980444838248241499325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109583895705803990621329733 20546980444838248241499325)
  ·
    refine ⟨7705117666814343090562247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20546980444838248241499325 7705117666814343090562247)
    ·
      refine ⟨11557676500221514635843371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7705117666814343090562247 11557676500221514635843371)
      ·
        refine ⟨17336514750332271953765057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11557676500221514635843371 17336514750332271953765057)
        ·
          refine ⟨13002386062749203965323793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17336514750332271953765057 13002386062749203965323793)
          ·
            refine ⟨9751789547061902973992845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13002386062749203965323793 9751789547061902973992845)
            ·
              refine ⟨3656921080148213615247317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9751789547061902973992845 3656921080148213615247317)
              ·
                refine ⟨85709087815973756607359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3656921080148213615247317 85709087815973756607359)
                ·
                  rfl

theorem cell23_4506782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 3, 7].length) (baseStart_4506782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4506782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4506782 prefixEnd_4506782 := by exact prefixLift 4506782
  have htrace : WordTrace (prefixWord ++ tailWord_4506782) baseStart_4506782 baseEnd_4506782 := by
    simpa [prefixWord, tailWord_4506782, baseEnd_4506782] using wordTrace_append hprefix tailTrace_4506782
  have hstable : (prefixWord ++ tailWord_4506782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4506782).length < 2 ^ (prefixWord ++ tailWord_4506782).sum := by decide
  have hdescent : baseEnd_4506782 < baseStart_4506782 := by decide
  rcases family_descends (prefixWord ++ tailWord_4506782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4506809 : List Nat := [1, 2, 1, 4, 1, 5, 1, 2, 2, 1, 3]
def baseStart_4506809 : Nat := 118140960795 + 4506809 * 2 ^ 59
def prefixEnd_4506809 : Nat := 4983230072969 + 3 ^ 40 * 4506809 * 2
def baseEnd_4506809 : Nat := 2314159235008962822761069

theorem tailTrace_4506809 : CollatzResearch.WordTrace tailWord_4506809 prefixEnd_4506809 2314159235008962822761069 := by
  unfold tailWord_4506809
  simp only [CollatzResearch.WordTrace]
  refine ⟨164376828329608169543227481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109584552219738779695484987 164376828329608169543227481)
  ·
    refine ⟨123282621247206127157420611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164376828329608169543227481 123282621247206127157420611)
    ·
      refine ⟨184923931870809190736130917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123282621247206127157420611 184923931870809190736130917)
      ·
        refine ⟨34673237225776723263024547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 184923931870809190736130917 34673237225776723263024547)
        ·
          refine ⟨52009855838665084894536821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34673237225776723263024547 52009855838665084894536821)
          ·
            refine ⟨4875923984874851708862827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 52009855838665084894536821 4875923984874851708862827)
            ·
              refine ⟨7313885977312277563294241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4875923984874851708862827 7313885977312277563294241)
              ·
                refine ⟨5485414482984208172470681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7313885977312277563294241 5485414482984208172470681)
                ·
                  refine ⟨4114060862238156129353011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5485414482984208172470681 4114060862238156129353011)
                  ·
                    refine ⟨6171091293357234194029517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4114060862238156129353011 6171091293357234194029517)
                    ·
                      refine ⟨2314159235008962822761069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6171091293357234194029517 2314159235008962822761069)
                      ·
                        rfl

theorem cell23_4506809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 1, 2, 2, 1, 3].length) (baseStart_4506809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4506809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4506809 prefixEnd_4506809 := by exact prefixLift 4506809
  have htrace : WordTrace (prefixWord ++ tailWord_4506809) baseStart_4506809 baseEnd_4506809 := by
    simpa [prefixWord, tailWord_4506809, baseEnd_4506809] using wordTrace_append hprefix tailTrace_4506809
  have hstable : (prefixWord ++ tailWord_4506809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4506809).length < 2 ^ (prefixWord ++ tailWord_4506809).sum := by decide
  have hdescent : baseEnd_4506809 < baseStart_4506809 := by decide
  rcases family_descends (prefixWord ++ tailWord_4506809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4506815 : List Nat := [1, 1, 2, 2, 2, 2, 2, 2, 3, 4, 2]
def baseStart_4506815 : Nat := 118140960795 + 4506815 * 2 ^ 59
def prefixEnd_4506815 : Nat := 4983230072969 + 3 ^ 40 * 4506815 * 2
def baseEnd_4506815 : Nat := 2314162315892889799286041

theorem tailTrace_4506815 : CollatzResearch.WordTrace tailWord_4506815 prefixEnd_4506815 2314162315892889799286041 := by
  unfold tailWord_4506815
  simp only [CollatzResearch.WordTrace]
  refine ⟨164377047167586432567945899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109584698111724288378630599 164377047167586432567945899)
  ·
    refine ⟨246565570751379648851918849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164377047167586432567945899 246565570751379648851918849)
    ·
      refine ⟨184924178063534736638939137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 246565570751379648851918849 184924178063534736638939137)
      ·
        refine ⟨138693133547651052479204353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 184924178063534736638939137 138693133547651052479204353)
        ·
          refine ⟨104019850160738289359403265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 138693133547651052479204353 104019850160738289359403265)
          ·
            refine ⟨78014887620553717019552449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104019850160738289359403265 78014887620553717019552449)
            ·
              refine ⟨58511165715415287764664337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78014887620553717019552449 58511165715415287764664337)
              ·
                refine ⟨43883374286561465823498253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58511165715415287764664337 43883374286561465823498253)
                ·
                  refine ⟨16456265357460549683811845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43883374286561465823498253 16456265357460549683811845)
                  ·
                    refine ⟨3085549754523853065714721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16456265357460549683811845 3085549754523853065714721)
                    ·
                      refine ⟨2314162315892889799286041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3085549754523853065714721 2314162315892889799286041)
                      ·
                        rfl

theorem cell23_4506815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 4, 2].length) (baseStart_4506815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4506815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4506815 prefixEnd_4506815 := by exact prefixLift 4506815
  have htrace : WordTrace (prefixWord ++ tailWord_4506815) baseStart_4506815 baseEnd_4506815 := by
    simpa [prefixWord, tailWord_4506815, baseEnd_4506815] using wordTrace_append hprefix tailTrace_4506815
  have hstable : (prefixWord ++ tailWord_4506815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4506815).length < 2 ^ (prefixWord ++ tailWord_4506815).sum := by decide
  have hdescent : baseEnd_4506815 < baseStart_4506815 := by decide
  rcases family_descends (prefixWord ++ tailWord_4506815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4506942 : List Nat := [4, 2, 1, 2, 1, 1, 2, 2, 1, 4, 3]
def baseStart_4506942 : Nat := 118140960795 + 4506942 * 2 ^ 59
def prefixEnd_4506942 : Nat := 4983230072969 + 3 ^ 40 * 4506942 * 2
def baseEnd_4506942 : Nat := 2314227527936010802397957

theorem tailTrace_4506942 : CollatzResearch.WordTrace tailWord_4506942 prefixEnd_4506942 2314227527936010802397957 := by
  unfold tailWord_4506942
  simp only [CollatzResearch.WordTrace]
  refine ⟨20547709904765791657227385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109587786158750888838546053 20547709904765791657227385)
  ·
    refine ⟨15410782428574343742920539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20547709904765791657227385 15410782428574343742920539)
    ·
      refine ⟨23116173642861515614380809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15410782428574343742920539 23116173642861515614380809)
      ·
        refine ⟨17337130232146136710785607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23116173642861515614380809 17337130232146136710785607)
        ·
          refine ⟨26005695348219205066178411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17337130232146136710785607 26005695348219205066178411)
          ·
            refine ⟨39008543022328807599267617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26005695348219205066178411 39008543022328807599267617)
            ·
              refine ⟨29256407266746605699450713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39008543022328807599267617 29256407266746605699450713)
              ·
                refine ⟨21942305450059954274588035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29256407266746605699450713 21942305450059954274588035)
                ·
                  refine ⟨32913458175089931411882053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21942305450059954274588035 32913458175089931411882053)
                  ·
                    refine ⟨6171273407829362139727885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32913458175089931411882053 6171273407829362139727885)
                    ·
                      refine ⟨2314227527936010802397957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6171273407829362139727885 2314227527936010802397957)
                      ·
                        rfl

theorem cell23_4506942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 2, 1, 4, 3].length) (baseStart_4506942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4506942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4506942 prefixEnd_4506942 := by exact prefixLift 4506942
  have htrace : WordTrace (prefixWord ++ tailWord_4506942) baseStart_4506942 baseEnd_4506942 := by
    simpa [prefixWord, tailWord_4506942, baseEnd_4506942] using wordTrace_append hprefix tailTrace_4506942
  have hstable : (prefixWord ++ tailWord_4506942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4506942).length < 2 ^ (prefixWord ++ tailWord_4506942).sum := by decide
  have hdescent : baseEnd_4506942 < baseStart_4506942 := by decide
  rcases family_descends (prefixWord ++ tailWord_4506942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4506989 : List Nat := [1, 5, 1, 1, 1, 3, 1, 3, 3, 1, 3]
def baseStart_4506989 : Nat := 118140960795 + 4506989 * 2 ^ 59
def prefixEnd_4506989 : Nat := 4983230072969 + 3 ^ 40 * 4506989 * 2
def baseEnd_4506989 : Nat := 2314251661526772118510241

theorem tailTrace_4506989 : CollatzResearch.WordTrace tailWord_4506989 prefixEnd_4506989 2314251661526772118510241 := by
  unfold tailWord_4506989
  simp only [CollatzResearch.WordTrace]
  refine ⟨164383393468956060284780021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109588928979304040189853347 164383393468956060284780021)
  ·
    refine ⟨15410943137714630651698127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 164383393468956060284780021 15410943137714630651698127)
    ·
      refine ⟨23116414706571945977547191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15410943137714630651698127 23116414706571945977547191)
      ·
        refine ⟨34674622059857918966320787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23116414706571945977547191 34674622059857918966320787)
        ·
          refine ⟨52011933089786878449481181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34674622059857918966320787 52011933089786878449481181)
          ·
            refine ⟨19504474908670079418555443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52011933089786878449481181 19504474908670079418555443)
            ·
              refine ⟨29256712363005119127833165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19504474908670079418555443 29256712363005119127833165)
              ·
                refine ⟨10971267136126919672937437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29256712363005119127833165 10971267136126919672937437)
                ·
                  refine ⟨4114225176047594877351539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10971267136126919672937437 4114225176047594877351539)
                  ·
                    refine ⟨6171337764071392316027309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4114225176047594877351539 6171337764071392316027309)
                    ·
                      refine ⟨2314251661526772118510241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6171337764071392316027309 2314251661526772118510241)
                      ·
                        rfl

theorem cell23_4506989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 3, 3, 1, 3].length) (baseStart_4506989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4506989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4506989 prefixEnd_4506989 := by exact prefixLift 4506989
  have htrace : WordTrace (prefixWord ++ tailWord_4506989) baseStart_4506989 baseEnd_4506989 := by
    simpa [prefixWord, tailWord_4506989, baseEnd_4506989] using wordTrace_append hprefix tailTrace_4506989
  have hstable : (prefixWord ++ tailWord_4506989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4506989).length < 2 ^ (prefixWord ++ tailWord_4506989).sum := by decide
  have hdescent : baseEnd_4506989 < baseStart_4506989 := by decide
  rcases family_descends (prefixWord ++ tailWord_4506989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4507029 : List Nat := [1, 3, 2, 1, 1, 2, 2, 2, 5, 2, 2]
def baseStart_4507029 : Nat := 118140960795 + 4507029 * 2 ^ 59
def prefixEnd_4507029 : Nat := 4983230072969 + 3 ^ 40 * 4507029 * 2
def baseEnd_4507029 : Nat := 2314272200752951962010057

theorem tailTrace_4507029 : CollatzResearch.WordTrace tailWord_4507029 prefixEnd_4507029 2314272200752951962010057 := by
  unfold tailWord_4507029
  simp only [CollatzResearch.WordTrace]
  refine ⟨164384852388811147116236141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109589901592540764744157427 164384852388811147116236141)
  ·
    refine ⟨61644319645804180168588553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 164384852388811147116236141 61644319645804180168588553)
    ·
      refine ⟨46233239734353135126441415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61644319645804180168588553 46233239734353135126441415)
      ·
        refine ⟨69349859601529702689662123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46233239734353135126441415 69349859601529702689662123)
        ·
          refine ⟨104024789402294554034493185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69349859601529702689662123 104024789402294554034493185)
          ·
            refine ⟨78018592051720915525869889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104024789402294554034493185 78018592051720915525869889)
            ·
              refine ⟨58513944038790686644402417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78018592051720915525869889 58513944038790686644402417)
              ·
                refine ⟨43885458029093014983301813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58513944038790686644402417 43885458029093014983301813)
                ·
                  refine ⟨4114261690227470154684545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43885458029093014983301813 4114261690227470154684545)
                  ·
                    refine ⟨3085696267670602616013409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4114261690227470154684545 3085696267670602616013409)
                    ·
                      refine ⟨2314272200752951962010057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3085696267670602616013409 2314272200752951962010057)
                      ·
                        rfl

theorem cell23_4507029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 2, 5, 2, 2].length) (baseStart_4507029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4507029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4507029 prefixEnd_4507029 := by exact prefixLift 4507029
  have htrace : WordTrace (prefixWord ++ tailWord_4507029) baseStart_4507029 baseEnd_4507029 := by
    simpa [prefixWord, tailWord_4507029, baseEnd_4507029] using wordTrace_append hprefix tailTrace_4507029
  have hstable : (prefixWord ++ tailWord_4507029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4507029).length < 2 ^ (prefixWord ++ tailWord_4507029).sum := by decide
  have hdescent : baseEnd_4507029 < baseStart_4507029 := by decide
  rcases family_descends (prefixWord ++ tailWord_4507029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4507042 : List Nat := [3, 3, 1, 2, 1, 2, 1, 2, 1, 1, 6]
def baseStart_4507042 : Nat := 118140960795 + 4507042 * 2 ^ 59
def prefixEnd_4507042 : Nat := 4983230072969 + 3 ^ 40 * 4507042 * 2
def baseEnd_4507042 : Nat := 2314278876001460411147497

theorem tailTrace_4507042 : CollatzResearch.WordTrace tailWord_4507042 prefixEnd_4507042 2314278876001460411147497 := by
  unfold tailWord_4507042
  simp only [CollatzResearch.WordTrace]
  refine ⟨41096331634441012584114845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109590217691842700224306253 41096331634441012584114845)
  ·
    refine ⟨15411124362915379719043067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41096331634441012584114845 15411124362915379719043067)
    ·
      refine ⟨23116686544373069578564601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15411124362915379719043067 23116686544373069578564601)
      ·
        refine ⟨17337514908279802183923451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23116686544373069578564601 17337514908279802183923451)
        ·
          refine ⟨26006272362419703275885177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17337514908279802183923451 26006272362419703275885177)
          ·
            refine ⟨19504704271814777456913883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26006272362419703275885177 19504704271814777456913883)
            ·
              refine ⟨29257056407722166185370825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19504704271814777456913883 29257056407722166185370825)
              ·
                refine ⟨21942792305791624639028119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29257056407722166185370825 21942792305791624639028119)
                ·
                  refine ⟨32914188458687436958542179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21942792305791624639028119 32914188458687436958542179)
                  ·
                    refine ⟨49371282688031155437813269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32914188458687436958542179 49371282688031155437813269)
                    ·
                      refine ⟨2314278876001460411147497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49371282688031155437813269 2314278876001460411147497)
                      ·
                        rfl

theorem cell23_4507042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_4507042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4507042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4507042 prefixEnd_4507042 := by exact prefixLift 4507042
  have htrace : WordTrace (prefixWord ++ tailWord_4507042) baseStart_4507042 baseEnd_4507042 := by
    simpa [prefixWord, tailWord_4507042, baseEnd_4507042] using wordTrace_append hprefix tailTrace_4507042
  have hstable : (prefixWord ++ tailWord_4507042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4507042).length < 2 ^ (prefixWord ++ tailWord_4507042).sum := by decide
  have hdescent : baseEnd_4507042 < baseStart_4507042 := by decide
  rcases family_descends (prefixWord ++ tailWord_4507042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4507075 : List Nat := [1, 1, 1, 3, 1, 1, 4, 1, 1, 4, 5]
def baseStart_4507075 : Nat := 118140960795 + 4507075 * 2 ^ 59
def prefixEnd_4507075 : Nat := 4983230072969 + 3 ^ 40 * 4507075 * 2
def baseEnd_4507075 : Nat := 2314295820863058782034845

theorem tailTrace_4507075 : CollatzResearch.WordTrace tailWord_4507075 prefixEnd_4507075 2314295820863058782034845 := by
  unfold tailWord_4507075
  simp only [CollatzResearch.WordTrace]
  refine ⟨164386530146644496972410679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109591020097762997981607119 164386530146644496972410679)
  ·
    refine ⟨246579795219966745458616019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164386530146644496972410679 246579795219966745458616019)
    ·
      refine ⟨369869692829950118187924029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 246579795219966745458616019 369869692829950118187924029)
      ·
        refine ⟨138701134811231294320471511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 369869692829950118187924029 138701134811231294320471511)
        ·
          refine ⟨208051702216846941480707267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138701134811231294320471511 208051702216846941480707267)
          ·
            refine ⟨312077553325270412221060901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 208051702216846941480707267 312077553325270412221060901)
            ·
              refine ⟨58514541248488202291448919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 312077553325270412221060901 58514541248488202291448919)
              ·
                refine ⟨87771811872732303437173379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58514541248488202291448919 87771811872732303437173379)
                ·
                  refine ⟨131657717809098455155760069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 87771811872732303437173379 131657717809098455155760069)
                  ·
                    refine ⟨24685822089205960341705013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 131657717809098455155760069 24685822089205960341705013)
                    ·
                      refine ⟨2314295820863058782034845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24685822089205960341705013 2314295820863058782034845)
                      ·
                        rfl

theorem cell23_4507075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 4, 5].length) (baseStart_4507075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4507075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4507075 prefixEnd_4507075 := by exact prefixLift 4507075
  have htrace : WordTrace (prefixWord ++ tailWord_4507075) baseStart_4507075 baseEnd_4507075 := by
    simpa [prefixWord, tailWord_4507075, baseEnd_4507075] using wordTrace_append hprefix tailTrace_4507075
  have hstable : (prefixWord ++ tailWord_4507075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4507075).length < 2 ^ (prefixWord ++ tailWord_4507075).sum := by decide
  have hdescent : baseEnd_4507075 < baseStart_4507075 := by decide
  rcases family_descends (prefixWord ++ tailWord_4507075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4507095 : List Nat := [1, 1, 3, 2, 1, 1, 1, 2, 3, 8]
def baseStart_4507095 : Nat := 118140960795 + 4507095 * 2 ^ 59
def prefixEnd_4507095 : Nat := 4983230072969 + 3 ^ 40 * 4507095 * 2
def baseEnd_4507095 : Nat := 771435363492049567928251

theorem tailTrace_4507095 : CollatzResearch.WordTrace tailWord_4507095 prefixEnd_4507095 771435363492049567928251 := by
  unfold tailWord_4507095
  simp only [CollatzResearch.WordTrace]
  refine ⟨164387259606572040388138739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109591506404381360258759159 164387259606572040388138739)
  ·
    refine ⟨246580889409858060582208109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164387259606572040388138739 246580889409858060582208109)
    ·
      refine ⟨92467833528696772718328041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 246580889409858060582208109 92467833528696772718328041)
      ·
        refine ⟨69350875146522579538746031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92467833528696772718328041 69350875146522579538746031)
        ·
          refine ⟨104026312719783869308119047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69350875146522579538746031 104026312719783869308119047)
          ·
            refine ⟨156039469079675803962178571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104026312719783869308119047 156039469079675803962178571)
            ·
              refine ⟨234059203619513705943267857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 156039469079675803962178571 234059203619513705943267857)
              ·
                refine ⟨175544402714635279457450893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 234059203619513705943267857 175544402714635279457450893)
                ·
                  refine ⟨65829151017988229796544085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 175544402714635279457450893 65829151017988229796544085)
                  ·
                    refine ⟨771435363492049567928251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 65829151017988229796544085 771435363492049567928251)
                    ·
                      rfl

theorem cell23_4507095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 3, 8].length) (baseStart_4507095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4507095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4507095 prefixEnd_4507095 := by exact prefixLift 4507095
  have htrace : WordTrace (prefixWord ++ tailWord_4507095) baseStart_4507095 baseEnd_4507095 := by
    simpa [prefixWord, tailWord_4507095, baseEnd_4507095] using wordTrace_append hprefix tailTrace_4507095
  have hstable : (prefixWord ++ tailWord_4507095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4507095).length < 2 ^ (prefixWord ++ tailWord_4507095).sum := by decide
  have hdescent : baseEnd_4507095 < baseStart_4507095 := by decide
  rcases family_descends (prefixWord ++ tailWord_4507095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4507112 : List Nat := [2, 1, 4, 1, 1, 2, 3, 1, 2, 6]
def baseStart_4507112 : Nat := 118140960795 + 4507112 * 2 ^ 59
def prefixEnd_4507112 : Nat := 4983230072969 + 3 ^ 40 * 4507112 * 2
def baseEnd_4507112 : Nat := 771438273215758379090725

theorem tailTrace_4507112 : CollatzResearch.WordTrace tailWord_4507112 prefixEnd_4507112 771438273215758379090725 := by
  unfold tailWord_4507112
  simp only [CollatzResearch.WordTrace]
  refine ⟨82193939823755226145753795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109591919765006968194338393 82193939823755226145753795)
  ·
    refine ⟨123290909735632839218630693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82193939823755226145753795 123290909735632839218630693)
    ·
      refine ⟨23117045575431157353493255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 123290909735632839218630693 23117045575431157353493255)
      ·
        refine ⟨34675568363146736030239883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23117045575431157353493255 34675568363146736030239883)
        ·
          refine ⟨52013352544720104045359825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34675568363146736030239883 52013352544720104045359825)
          ·
            refine ⟨39010014408540078034019869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52013352544720104045359825 39010014408540078034019869)
            ·
              refine ⟨14628755403202529262757451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39010014408540078034019869 14628755403202529262757451)
              ·
                refine ⟨21943133104803793894136177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14628755403202529262757451 21943133104803793894136177)
                ·
                  refine ⟨16457349828602845420602133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21943133104803793894136177 16457349828602845420602133)
                  ·
                    refine ⟨771438273215758379090725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16457349828602845420602133 771438273215758379090725)
                    ·
                      rfl

theorem cell23_4507112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 1, 2, 6].length) (baseStart_4507112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4507112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4507112 prefixEnd_4507112 := by exact prefixLift 4507112
  have htrace : WordTrace (prefixWord ++ tailWord_4507112) baseStart_4507112 baseEnd_4507112 := by
    simpa [prefixWord, tailWord_4507112, baseEnd_4507112] using wordTrace_append hprefix tailTrace_4507112
  have hstable : (prefixWord ++ tailWord_4507112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4507112).length < 2 ^ (prefixWord ++ tailWord_4507112).sum := by decide
  have hdescent : baseEnd_4507112 < baseStart_4507112 := by decide
  rcases family_descends (prefixWord ++ tailWord_4507112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4507119 : List Nat := [1, 1, 2, 1, 4, 1, 3, 3, 1, 4, 2]
def baseStart_4507119 : Nat := 118140960795 + 4507119 * 2 ^ 59
def prefixEnd_4507119 : Nat := 4983230072969 + 3 ^ 40 * 4507119 * 2
def baseEnd_4507119 : Nat := 2314318414011856609884643

theorem tailTrace_4507119 : CollatzResearch.WordTrace tailWord_4507119 prefixEnd_4507119 2314318414011856609884643 := by
  unfold tailWord_4507119
  simp only [CollatzResearch.WordTrace]
  refine ⟨164388134958485092487012411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109592089972323394991341607 164388134958485092487012411)
  ·
    refine ⟨246582202437727638730518617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164388134958485092487012411 246582202437727638730518617)
    ·
      refine ⟨184936651828295729047888963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 246582202437727638730518617 184936651828295729047888963)
      ·
        refine ⟨277404977742443593571833445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184936651828295729047888963 277404977742443593571833445)
        ·
          refine ⟨52013433326708173794718771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 277404977742443593571833445 52013433326708173794718771)
          ·
            refine ⟨78020149990062260692078157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52013433326708173794718771 78020149990062260692078157)
            ·
              refine ⟨29257556246273347759529309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78020149990062260692078157 29257556246273347759529309)
              ·
                refine ⟨10971583592352505409823491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29257556246273347759529309 10971583592352505409823491)
                ·
                  refine ⟨16457375388528758114735237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10971583592352505409823491 16457375388528758114735237)
                  ·
                    refine ⟨3085757885349142146512857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16457375388528758114735237 3085757885349142146512857)
                    ·
                      refine ⟨2314318414011856609884643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3085757885349142146512857 2314318414011856609884643)
                      ·
                        rfl

theorem cell23_4507119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 3, 1, 4, 2].length) (baseStart_4507119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4507119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4507119 prefixEnd_4507119 := by exact prefixLift 4507119
  have htrace : WordTrace (prefixWord ++ tailWord_4507119) baseStart_4507119 baseEnd_4507119 := by
    simpa [prefixWord, tailWord_4507119, baseEnd_4507119] using wordTrace_append hprefix tailTrace_4507119
  have hstable : (prefixWord ++ tailWord_4507119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4507119).length < 2 ^ (prefixWord ++ tailWord_4507119).sum := by decide
  have hdescent : baseEnd_4507119 < baseStart_4507119 := by decide
  rcases family_descends (prefixWord ++ tailWord_4507119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4507169 : List Nat := [1, 2, 3, 2, 2, 2, 2, 1, 2, 3, 3]
def baseStart_4507169 : Nat := 118140960795 + 4507169 * 2 ^ 59
def prefixEnd_4507169 : Nat := 4983230072969 + 3 ^ 40 * 4507169 * 2
def baseEnd_4507169 : Nat := 2314344088044581414259413

theorem tailTrace_4507169 : CollatzResearch.WordTrace tailWord_4507169 prefixEnd_4507169 2314344088044581414259413 := by
  unfold tailWord_4507169
  simp only [CollatzResearch.WordTrace]
  refine ⟨164389958608303951026332561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109593305738869300684221707 164389958608303951026332561)
  ·
    refine ⟨123292468956227963269749421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164389958608303951026332561 123292468956227963269749421)
    ·
      refine ⟨46234675858585486226156033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123292468956227963269749421 46234675858585486226156033)
      ·
        refine ⟨34676006893939114669617025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46234675858585486226156033 34676006893939114669617025)
        ·
          refine ⟨26007005170454336002212769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34676006893939114669617025 26007005170454336002212769)
          ·
            refine ⟨19505253877840752001659577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26007005170454336002212769 19505253877840752001659577)
            ·
              refine ⟨14628940408380564001244683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19505253877840752001659577 14628940408380564001244683)
              ·
                refine ⟨21943410612570846001867025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14628940408380564001244683 21943410612570846001867025)
                ·
                  refine ⟨16457557959428134501400269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21943410612570846001867025 16457557959428134501400269)
                  ·
                    refine ⟨6171584234785550438025101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16457557959428134501400269 6171584234785550438025101)
                    ·
                      refine ⟨2314344088044581414259413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6171584234785550438025101 2314344088044581414259413)
                      ·
                        rfl

theorem cell23_4507169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 1, 2, 3, 3].length) (baseStart_4507169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4507169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4507169 prefixEnd_4507169 := by exact prefixLift 4507169
  have htrace : WordTrace (prefixWord ++ tailWord_4507169) baseStart_4507169 baseEnd_4507169 := by
    simpa [prefixWord, tailWord_4507169, baseEnd_4507169] using wordTrace_append hprefix tailTrace_4507169
  have hstable : (prefixWord ++ tailWord_4507169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4507169).length < 2 ^ (prefixWord ++ tailWord_4507169).sum := by decide
  have hdescent : baseEnd_4507169 < baseStart_4507169 := by decide
  rcases family_descends (prefixWord ++ tailWord_4507169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4507209 : List Nat := [1, 2, 1, 1, 2, 2, 1, 3, 4, 4, 2]
def baseStart_4507209 : Nat := 118140960795 + 4507209 * 2 ^ 59
def prefixEnd_4507209 : Nat := 4983230072969 + 3 ^ 40 * 4507209 * 2
def baseEnd_4507209 : Nat := 2314364627270761257759229

theorem tailTrace_4507209 : CollatzResearch.WordTrace tailWord_4507209 prefixEnd_4507209 2314364627270761257759229 := by
  unfold tailWord_4507209
  simp only [CollatzResearch.WordTrace]
  refine ⟨164391417528159037857788681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109594278352106025238525787 164391417528159037857788681)
  ·
    refine ⟨123293563146119278393341511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164391417528159037857788681 123293563146119278393341511)
    ·
      refine ⟨184940344719178917590012267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123293563146119278393341511 184940344719178917590012267)
      ·
        refine ⟨277410517078768376385018401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184940344719178917590012267 277410517078768376385018401)
        ·
          refine ⟨208057887809076282288763801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 277410517078768376385018401 208057887809076282288763801)
          ·
            refine ⟨156043415856807211716572851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 208057887809076282288763801 156043415856807211716572851)
            ·
              refine ⟨234065123785210817574859277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 156043415856807211716572851 234065123785210817574859277)
              ·
                refine ⟨87774421419454056590572229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 234065123785210817574859277 87774421419454056590572229)
                ·
                  refine ⟨16457704016147635610732293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 87774421419454056590572229 16457704016147635610732293)
                  ·
                    refine ⟨3085819503027681677012305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16457704016147635610732293 3085819503027681677012305)
                    ·
                      refine ⟨2314364627270761257759229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3085819503027681677012305 2314364627270761257759229)
                      ·
                        rfl

theorem cell23_4507209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 4, 4, 2].length) (baseStart_4507209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4507209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4507209 prefixEnd_4507209 := by exact prefixLift 4507209
  have htrace : WordTrace (prefixWord ++ tailWord_4507209) baseStart_4507209 baseEnd_4507209 := by
    simpa [prefixWord, tailWord_4507209, baseEnd_4507209] using wordTrace_append hprefix tailTrace_4507209
  have hstable : (prefixWord ++ tailWord_4507209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4507209).length < 2 ^ (prefixWord ++ tailWord_4507209).sum := by decide
  have hdescent : baseEnd_4507209 < baseStart_4507209 := by decide
  rcases family_descends (prefixWord ++ tailWord_4507209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4507276 : List Nat := [2, 2, 1, 2, 1, 1, 4, 3, 3, 1, 3]
def baseStart_4507276 : Nat := 118140960795 + 4507276 * 2 ^ 59
def prefixEnd_4507276 : Nat := 4983230072969 + 3 ^ 40 * 4507276 * 2
def baseEnd_4507276 : Nat := 2314399030474612495621421

theorem tailTrace_4507276 : CollatzResearch.WordTrace tailWord_4507276 prefixEnd_4507276 2314399030474612495621421 := by
  unfold tailWord_4507276
  simp only [CollatzResearch.WordTrace]
  refine ⟨82196930609458154150238841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109595907479277538866985121 82196930609458154150238841)
  ·
    refine ⟨61647697957093615612679131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82196930609458154150238841 61647697957093615612679131)
    ·
      refine ⟨92471546935640423419018697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61647697957093615612679131 92471546935640423419018697)
      ·
        refine ⟨69353660201730317564264023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92471546935640423419018697 69353660201730317564264023)
        ·
          refine ⟨104030490302595476346396035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69353660201730317564264023 104030490302595476346396035)
          ·
            refine ⟨156045735453893214519594053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104030490302595476346396035 156045735453893214519594053)
            ·
              refine ⟨29258575397604977722423885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 156045735453893214519594053 29258575397604977722423885)
              ·
                refine ⟨10971965774101866645908957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29258575397604977722423885 10971965774101866645908957)
                ·
                  refine ⟨4114487165288199992215859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10971965774101866645908957 4114487165288199992215859)
                  ·
                    refine ⟨6171730747932299988323789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4114487165288199992215859 6171730747932299988323789)
                    ·
                      refine ⟨2314399030474612495621421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6171730747932299988323789 2314399030474612495621421)
                      ·
                        rfl

theorem cell23_4507276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 3, 3, 1, 3].length) (baseStart_4507276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4507276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4507276 prefixEnd_4507276 := by exact prefixLift 4507276
  have htrace : WordTrace (prefixWord ++ tailWord_4507276) baseStart_4507276 baseEnd_4507276 := by
    simpa [prefixWord, tailWord_4507276, baseEnd_4507276] using wordTrace_append hprefix tailTrace_4507276
  have hstable : (prefixWord ++ tailWord_4507276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4507276).length < 2 ^ (prefixWord ++ tailWord_4507276).sum := by decide
  have hdescent : baseEnd_4507276 < baseStart_4507276 := by decide
  rcases family_descends (prefixWord ++ tailWord_4507276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4507299 : List Nat := [1, 1, 1, 4, 1, 1, 3, 3, 3, 1, 4]
def baseStart_4507299 : Nat := 118140960795 + 4507299 * 2 ^ 59
def prefixEnd_4507299 : Nat := 4983230072969 + 3 ^ 40 * 4507299 * 2
def baseEnd_4507299 : Nat := 2314410840529665905633815

theorem tailTrace_4507299 : CollatzResearch.WordTrace tailWord_4507299 prefixEnd_4507299 2314410840529665905633815 := by
  unfold tailWord_4507299
  simp only [CollatzResearch.WordTrace]
  refine ⟨164394700097832983228564951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109596466731888655485709967 164394700097832983228564951)
  ·
    refine ⟨246592050146749474842847427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164394700097832983228564951 246592050146749474842847427)
    ·
      refine ⟨369888075220124212264271141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 246592050146749474842847427 369888075220124212264271141)
      ·
        refine ⟨69354014103773289799550839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 369888075220124212264271141 69354014103773289799550839)
        ·
          refine ⟨104031021155659934699326259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69354014103773289799550839 104031021155659934699326259)
          ·
            refine ⟨156046531733489902048989389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104031021155659934699326259 156046531733489902048989389)
            ·
              refine ⟨58517449400058713268371021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 156046531733489902048989389 58517449400058713268371021)
              ·
                refine ⟨21944043525022017475639133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58517449400058713268371021 21944043525022017475639133)
                ·
                  refine ⟨8229016321883256553364675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21944043525022017475639133 8229016321883256553364675)
                  ·
                    refine ⟨12343524482824884830047013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8229016321883256553364675 12343524482824884830047013)
                    ·
                      refine ⟨2314410840529665905633815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12343524482824884830047013 2314410840529665905633815)
                      ·
                        rfl

theorem cell23_4507299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 3, 3, 1, 4].length) (baseStart_4507299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4507299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4507299 prefixEnd_4507299 := by exact prefixLift 4507299
  have htrace : WordTrace (prefixWord ++ tailWord_4507299) baseStart_4507299 baseEnd_4507299 := by
    simpa [prefixWord, tailWord_4507299, baseEnd_4507299] using wordTrace_append hprefix tailTrace_4507299
  have hstable : (prefixWord ++ tailWord_4507299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4507299).length < 2 ^ (prefixWord ++ tailWord_4507299).sum := by decide
  have hdescent : baseEnd_4507299 < baseStart_4507299 := by decide
  rcases family_descends (prefixWord ++ tailWord_4507299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4507304 : List Nat := [2, 1, 7, 1, 1, 1, 2, 3, 1, 4]
def baseStart_4507304 : Nat := 118140960795 + 4507304 * 2 ^ 59
def prefixEnd_4507304 : Nat := 4983230072969 + 3 ^ 40 * 4507304 * 2
def baseEnd_4507304 : Nat := 771471135977646128690431

theorem tailTrace_4507304 : CollatzResearch.WordTrace tailWord_4507304 prefixEnd_4507304 771471135977646128690431 := by
  unfold tailWord_4507304
  simp only [CollatzResearch.WordTrace]
  refine ⟨82197441231407434541248483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109596588308543246054997977 82197441231407434541248483)
  ·
    refine ⟨123296161847111151811872725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82197441231407434541248483 123296161847111151811872725)
    ·
      refine ⟨2889753793291667620590767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 123296161847111151811872725 2889753793291667620590767)
      ·
        refine ⟨4334630689937501430886151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2889753793291667620590767 4334630689937501430886151)
        ·
          refine ⟨6501946034906252146329227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4334630689937501430886151 6501946034906252146329227)
          ·
            refine ⟨9752919052359378219493841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6501946034906252146329227 9752919052359378219493841)
            ·
              refine ⟨7314689289269533664620381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9752919052359378219493841 7314689289269533664620381)
              ·
                refine ⟨2743008483476075124232643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7314689289269533664620381 2743008483476075124232643)
                ·
                  refine ⟨4114512725214112686348965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2743008483476075124232643 4114512725214112686348965)
                  ·
                    refine ⟨771471135977646128690431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4114512725214112686348965 771471135977646128690431)
                    ·
                      rfl

theorem cell23_4507304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_4507304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4507304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4507304 prefixEnd_4507304 := by exact prefixLift 4507304
  have htrace : WordTrace (prefixWord ++ tailWord_4507304) baseStart_4507304 baseEnd_4507304 := by
    simpa [prefixWord, tailWord_4507304, baseEnd_4507304] using wordTrace_append hprefix tailTrace_4507304
  have hstable : (prefixWord ++ tailWord_4507304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4507304).length < 2 ^ (prefixWord ++ tailWord_4507304).sum := by decide
  have hdescent : baseEnd_4507304 < baseStart_4507304 := by decide
  rcases family_descends (prefixWord ++ tailWord_4507304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4507346 : List Nat := [3, 2, 2, 2, 2, 2, 1, 1, 1, 1, 6]
def baseStart_4507346 : Nat := 118140960795 + 4507346 * 2 ^ 59
def prefixEnd_4507346 : Nat := 4983230072969 + 3 ^ 40 * 4507346 * 2
def baseEnd_4507346 : Nat := 2314434974120427221746099

theorem tailTrace_4507346 : CollatzResearch.WordTrace tailWord_4507346 prefixEnd_4507346 2314434974120427221746099 := by
  unfold tailWord_4507346
  simp only [CollatzResearch.WordTrace]
  refine ⟨41099103582165677563881473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109597609552441806837017261 41099103582165677563881473)
  ·
    refine ⟨30824327686624258172911105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41099103582165677563881473 30824327686624258172911105)
    ·
      refine ⟨23118245764968193629683329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30824327686624258172911105 23118245764968193629683329)
      ·
        refine ⟨17338684323726145222262497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23118245764968193629683329 17338684323726145222262497)
        ·
          refine ⟨13004013242794608916696873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17338684323726145222262497 13004013242794608916696873)
          ·
            refine ⟨9753009932095956687522655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13004013242794608916696873 9753009932095956687522655)
            ·
              refine ⟨14629514898143935031283983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9753009932095956687522655 14629514898143935031283983)
              ·
                refine ⟨21944272347215902546925975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14629514898143935031283983 21944272347215902546925975)
                ·
                  refine ⟨32916408520823853820388963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21944272347215902546925975 32916408520823853820388963)
                  ·
                    refine ⟨49374612781235780730583445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32916408520823853820388963 49374612781235780730583445)
                    ·
                      refine ⟨2314434974120427221746099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49374612781235780730583445 2314434974120427221746099)
                      ·
                        rfl

theorem cell23_4507346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_4507346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4507346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4507346 prefixEnd_4507346 := by exact prefixLift 4507346
  have htrace : WordTrace (prefixWord ++ tailWord_4507346) baseStart_4507346 baseEnd_4507346 := by
    simpa [prefixWord, tailWord_4507346, baseEnd_4507346] using wordTrace_append hprefix tailTrace_4507346
  have hstable : (prefixWord ++ tailWord_4507346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4507346).length < 2 ^ (prefixWord ++ tailWord_4507346).sum := by decide
  have hdescent : baseEnd_4507346 < baseStart_4507346 := by decide
  rcases family_descends (prefixWord ++ tailWord_4507346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4507353 : List Nat := [1, 2, 1, 2, 3, 4, 2, 2, 1, 2, 3]
def baseStart_4507353 : Nat := 118140960795 + 4507353 * 2 ^ 59
def prefixEnd_4507353 : Nat := 4983230072969 + 3 ^ 40 * 4507353 * 2
def baseEnd_4507353 : Nat := 2314438568485008694358567

theorem tailTrace_4507353 : CollatzResearch.WordTrace tailWord_4507353 prefixEnd_4507353 2314438568485008694358567 := by
  unfold tailWord_4507353
  simp only [CollatzResearch.WordTrace]
  refine ⟨164396669639637350451030713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109597779759758233634020475 164396669639637350451030713)
  ·
    refine ⟨123297502229728012838273035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164396669639637350451030713 123297502229728012838273035)
    ·
      refine ⟨184946253344592019257409553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123297502229728012838273035 184946253344592019257409553)
      ·
        refine ⟨138709690008444014443057165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 184946253344592019257409553 138709690008444014443057165)
        ·
          refine ⟨52016133753166505416146437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 138709690008444014443057165 52016133753166505416146437)
          ·
            refine ⟨9753025078718719765527457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52016133753166505416146437 9753025078718719765527457)
            ·
              refine ⟨7314768809039039824145593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9753025078718719765527457 7314768809039039824145593)
              ·
                refine ⟨5486076606779279868109195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7314768809039039824145593 5486076606779279868109195)
                ·
                  refine ⟨8229114910168919802163793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5486076606779279868109195 8229114910168919802163793)
                  ·
                    refine ⟨6171836182626689851622845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8229114910168919802163793 6171836182626689851622845)
                    ·
                      refine ⟨2314438568485008694358567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6171836182626689851622845 2314438568485008694358567)
                      ·
                        rfl

theorem cell23_4507353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 2, 2, 1, 2, 3].length) (baseStart_4507353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4507353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4507353 prefixEnd_4507353 := by exact prefixLift 4507353
  have htrace : WordTrace (prefixWord ++ tailWord_4507353) baseStart_4507353 baseEnd_4507353 := by
    simpa [prefixWord, tailWord_4507353, baseEnd_4507353] using wordTrace_append hprefix tailTrace_4507353
  have hstable : (prefixWord ++ tailWord_4507353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4507353).length < 2 ^ (prefixWord ++ tailWord_4507353).sum := by decide
  have hdescent : baseEnd_4507353 < baseStart_4507353 := by decide
  rcases family_descends (prefixWord ++ tailWord_4507353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4507398 : List Nat := [6, 2, 2, 1, 2, 1, 1, 2, 1, 5]
def baseStart_4507398 : Nat := 118140960795 + 4507398 * 2 ^ 59
def prefixEnd_4507398 : Nat := 4983230072969 + 3 ^ 40 * 4507398 * 2
def baseEnd_4507398 : Nat := 771487225038153672765287

theorem tailTrace_4507398 : CollatzResearch.WordTrace tailWord_4507398 prefixEnd_4507398 771487225038153672765287 := by
  unfold tailWord_4507398
  simp only [CollatzResearch.WordTrace]
  refine ⟨5137447216389822598013089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 109598873949649548757612565 5137447216389822598013089)
  ·
    refine ⟨3853085412292366948509817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5137447216389822598013089 3853085412292366948509817)
    ·
      refine ⟨2889814059219275211382363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3853085412292366948509817 2889814059219275211382363)
      ·
        refine ⟨4334721088828912817073545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2889814059219275211382363 4334721088828912817073545)
        ·
          refine ⟨3251040816621684612805159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4334721088828912817073545 3251040816621684612805159)
          ·
            refine ⟨4876561224932526919207739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3251040816621684612805159 4876561224932526919207739)
            ·
              refine ⟨7314841837398790378811609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4876561224932526919207739 7314841837398790378811609)
              ·
                refine ⟨5486131378049092784108707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7314841837398790378811609 5486131378049092784108707)
                ·
                  refine ⟨8229197067073639176163061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5486131378049092784108707 8229197067073639176163061)
                  ·
                    refine ⟨771487225038153672765287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8229197067073639176163061 771487225038153672765287)
                    ·
                      rfl

theorem cell23_4507398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_4507398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4507398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4507398 prefixEnd_4507398 := by exact prefixLift 4507398
  have htrace : WordTrace (prefixWord ++ tailWord_4507398) baseStart_4507398 baseEnd_4507398 := by
    simpa [prefixWord, tailWord_4507398, baseEnd_4507398] using wordTrace_append hprefix tailTrace_4507398
  have hstable : (prefixWord ++ tailWord_4507398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4507398).length < 2 ^ (prefixWord ++ tailWord_4507398).sum := by decide
  have hdescent : baseEnd_4507398 < baseStart_4507398 := by decide
  rcases family_descends (prefixWord ++ tailWord_4507398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4507419 : List Nat := [1, 1, 1, 1, 1, 1, 4, 4, 1, 4, 4]
def baseStart_4507419 : Nat := 118140960795 + 4507419 * 2 ^ 59
def prefixEnd_4507419 : Nat := 4983230072969 + 3 ^ 40 * 4507419 * 2
def baseEnd_4507419 : Nat := 2314472458208205436133263

theorem tailTrace_4507419 : CollatzResearch.WordTrace tailWord_4507419 prefixEnd_4507419 2314472458208205436133263 := by
  unfold tailWord_4507419
  simp only [CollatzResearch.WordTrace]
  refine ⟨164399076857398243722933311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109599384571598829148622207 164399076857398243722933311)
  ·
    refine ⟨246598615286097365584399967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164399076857398243722933311 246598615286097365584399967)
    ·
      refine ⟨369897922929146048376599951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 246598615286097365584399967 369897922929146048376599951)
      ·
        refine ⟨554846884393719072564899927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 369897922929146048376599951 554846884393719072564899927)
        ·
          refine ⟨832270326590578608847349891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 554846884393719072564899927 832270326590578608847349891)
          ·
            refine ⟨1248405489885867913271024837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 832270326590578608847349891 1248405489885867913271024837)
            ·
              refine ⟨234076029353600233738317157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1248405489885867913271024837 234076029353600233738317157)
              ·
                refine ⟨43889255503800043825934467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 234076029353600233738317157 43889255503800043825934467)
                ·
                  refine ⟨65833883255700065738901701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43889255503800043825934467 65833883255700065738901701)
                  ·
                    refine ⟨12343853110443762326044069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 65833883255700065738901701 12343853110443762326044069)
                    ·
                      refine ⟨2314472458208205436133263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12343853110443762326044069 2314472458208205436133263)
                      ·
                        rfl

theorem cell23_4507419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 1, 4, 4].length) (baseStart_4507419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4507419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4507419 prefixEnd_4507419 := by exact prefixLift 4507419
  have htrace : WordTrace (prefixWord ++ tailWord_4507419) baseStart_4507419 baseEnd_4507419 := by
    simpa [prefixWord, tailWord_4507419, baseEnd_4507419] using wordTrace_append hprefix tailTrace_4507419
  have hstable : (prefixWord ++ tailWord_4507419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4507419).length < 2 ^ (prefixWord ++ tailWord_4507419).sum := by decide
  have hdescent : baseEnd_4507419 < baseStart_4507419 := by decide
  rcases family_descends (prefixWord ++ tailWord_4507419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4507423 : List Nat := [1, 1, 2, 4, 2, 1, 3, 2, 1, 4, 2]
def baseStart_4507423 : Nat := 118140960795 + 4507423 * 2 ^ 59
def prefixEnd_4507423 : Nat := 4983230072969 + 3 ^ 40 * 4507423 * 2
def baseEnd_4507423 : Nat := 2314474512130823420483245

theorem tailTrace_4507423 : CollatzResearch.WordTrace tailWord_4507423 prefixEnd_4507423 2314474512130823420483245 := by
  unfold tailWord_4507423
  simp only [CollatzResearch.WordTrace]
  refine ⟨164399222749383752406078923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109599481832922501604052615 164399222749383752406078923)
  ·
    refine ⟨246598834124075628609118385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164399222749383752406078923 246598834124075628609118385)
    ·
      refine ⟨184949125593056721456838789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 246598834124075628609118385 184949125593056721456838789)
      ·
        refine ⟨34677961048698135273157273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 184949125593056721456838789 34677961048698135273157273)
        ·
          refine ⟨26008470786523601454867955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34677961048698135273157273 26008470786523601454867955)
          ·
            refine ⟨39012706179785402182301933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26008470786523601454867955 39012706179785402182301933)
            ·
              refine ⟨14629764817419525818363225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39012706179785402182301933 14629764817419525818363225)
              ·
                refine ⟨10972323613064644363772419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14629764817419525818363225 10972323613064644363772419)
                ·
                  refine ⟨16458485419596966545658629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10972323613064644363772419 16458485419596966545658629)
                  ·
                    refine ⟨3085966016174431227310993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16458485419596966545658629 3085966016174431227310993)
                    ·
                      refine ⟨2314474512130823420483245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3085966016174431227310993 2314474512130823420483245)
                      ·
                        rfl

theorem cell23_4507423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 2, 1, 4, 2].length) (baseStart_4507423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4507423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4507423 prefixEnd_4507423 := by exact prefixLift 4507423
  have htrace : WordTrace (prefixWord ++ tailWord_4507423) baseStart_4507423 baseEnd_4507423 := by
    simpa [prefixWord, tailWord_4507423, baseEnd_4507423] using wordTrace_append hprefix tailTrace_4507423
  have hstable : (prefixWord ++ tailWord_4507423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4507423).length < 2 ^ (prefixWord ++ tailWord_4507423).sum := by decide
  have hdescent : baseEnd_4507423 < baseStart_4507423 := by decide
  rcases family_descends (prefixWord ++ tailWord_4507423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4507426 : List Nat := [3, 3, 1, 1, 2, 1, 1, 3, 2, 1, 5]
def baseStart_4507426 : Nat := 118140960795 + 4507426 * 2 ^ 59
def prefixEnd_4507426 : Nat := 4983230072969 + 3 ^ 40 * 4507426 * 2
def baseEnd_4507426 : Nat := 2314476052572786908745731

theorem tailTrace_4507426 : CollatzResearch.WordTrace tailWord_4507426 prefixEnd_4507426 2314476052572786908745731 := by
  unfold tailWord_4507426
  simp only [CollatzResearch.WordTrace]
  refine ⟨41099833042093220979609533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109599554778915255945625421 41099833042093220979609533)
  ·
    refine ⟨15412437390784957867353575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41099833042093220979609533 15412437390784957867353575)
    ·
      refine ⟨23118656086177436801030363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15412437390784957867353575 23118656086177436801030363)
      ·
        refine ⟨34677984129266155201545545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23118656086177436801030363 34677984129266155201545545)
        ·
          refine ⟨26008488096949616401159159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34677984129266155201545545 26008488096949616401159159)
          ·
            refine ⟨39012732145424424601738739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26008488096949616401159159 39012732145424424601738739)
            ·
              refine ⟨58519098218136636902608109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39012732145424424601738739 58519098218136636902608109)
              ·
                refine ⟨21944661831801238838478041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58519098218136636902608109 21944661831801238838478041)
                ·
                  refine ⟨16458496373850929128858531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21944661831801238838478041 16458496373850929128858531)
                  ·
                    refine ⟨24687744560776393693287797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16458496373850929128858531 24687744560776393693287797)
                    ·
                      refine ⟨2314476052572786908745731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24687744560776393693287797 2314476052572786908745731)
                      ·
                        rfl

theorem cell23_4507426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 3, 2, 1, 5].length) (baseStart_4507426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4507426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4507426 prefixEnd_4507426 := by exact prefixLift 4507426
  have htrace : WordTrace (prefixWord ++ tailWord_4507426) baseStart_4507426 baseEnd_4507426 := by
    simpa [prefixWord, tailWord_4507426, baseEnd_4507426] using wordTrace_append hprefix tailTrace_4507426
  have hstable : (prefixWord ++ tailWord_4507426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4507426).length < 2 ^ (prefixWord ++ tailWord_4507426).sum := by decide
  have hdescent : baseEnd_4507426 < baseStart_4507426 := by decide
  rcases family_descends (prefixWord ++ tailWord_4507426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4507453 : List Nat := [1, 4, 1, 4, 1, 2, 1, 1, 2, 2, 4]
def baseStart_4507453 : Nat := 118140960795 + 4507453 * 2 ^ 59
def prefixEnd_4507453 : Nat := 4983230072969 + 3 ^ 40 * 4507453 * 2
def baseEnd_4507453 : Nat := 2314489916550458303108107

theorem tailTrace_4507453 : CollatzResearch.WordTrace tailWord_4507453 prefixEnd_4507453 2314489916550458303108107 := by
  unfold tailWord_4507453
  simp only [CollatzResearch.WordTrace]
  refine ⟨164400316939275067529671013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109600211292850045019780675 164400316939275067529671013)
  ·
    refine ⟨30825059426114075161813315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 164400316939275067529671013 30825059426114075161813315)
    ·
      refine ⟨46237589139171112742719973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30825059426114075161813315 46237589139171112742719973)
      ·
        refine ⟨8669547963594583639259995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46237589139171112742719973 8669547963594583639259995)
        ·
          refine ⟨13004321945391875458889993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8669547963594583639259995 13004321945391875458889993)
          ·
            refine ⟨9753241459043906594167495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13004321945391875458889993 9753241459043906594167495)
            ·
              refine ⟨14629862188565859891251243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9753241459043906594167495 14629862188565859891251243)
              ·
                refine ⟨21944793282848789836876865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14629862188565859891251243 21944793282848789836876865)
                ·
                  refine ⟨16458594962136592377657649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21944793282848789836876865 16458594962136592377657649)
                  ·
                    refine ⟨12343946221602444283243237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16458594962136592377657649 12343946221602444283243237)
                    ·
                      refine ⟨2314489916550458303108107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12343946221602444283243237 2314489916550458303108107)
                      ·
                        rfl

theorem cell23_4507453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_4507453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4507453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4507453 prefixEnd_4507453 := by exact prefixLift 4507453
  have htrace : WordTrace (prefixWord ++ tailWord_4507453) baseStart_4507453 baseEnd_4507453 := by
    simpa [prefixWord, tailWord_4507453, baseEnd_4507453] using wordTrace_append hprefix tailTrace_4507453
  have hstable : (prefixWord ++ tailWord_4507453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4507453).length < 2 ^ (prefixWord ++ tailWord_4507453).sum := by decide
  have hdescent : baseEnd_4507453 < baseStart_4507453 := by decide
  rcases family_descends (prefixWord ++ tailWord_4507453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4507513 : List Nat := [1, 2, 1, 3, 2, 2, 1, 3, 2, 4, 2]
def baseStart_4507513 : Nat := 118140960795 + 4507513 * 2 ^ 59
def prefixEnd_4507513 : Nat := 4983230072969 + 3 ^ 40 * 4507513 * 2
def baseEnd_4507513 : Nat := 2314520725389728068357831

theorem tailTrace_4507513 : CollatzResearch.WordTrace tailWord_4507513 prefixEnd_4507513 2314520725389728068357831 := by
  unfold tailWord_4507513
  simp only [CollatzResearch.WordTrace]
  refine ⟨164402505319057697776855193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109601670212705131851236795 164402505319057697776855193)
  ·
    refine ⟨123301878989293273332641395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164402505319057697776855193 123301878989293273332641395)
    ·
      refine ⟨184952818483939909998962093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123301878989293273332641395 184952818483939909998962093)
      ·
        refine ⟨69357306931477466249610785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 184952818483939909998962093 69357306931477466249610785)
        ·
          refine ⟨52017980198608099687208089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69357306931477466249610785 52017980198608099687208089)
          ·
            refine ⟨39013485148956074765406067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52017980198608099687208089 39013485148956074765406067)
            ·
              refine ⟨58520227723434112148109101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39013485148956074765406067 58520227723434112148109101)
              ·
                refine ⟨21945085396287792055540913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58520227723434112148109101 21945085396287792055540913)
                ·
                  refine ⟨16458814047215844041655685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21945085396287792055540913 16458814047215844041655685)
                  ·
                    refine ⟨3086027633852970757810441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16458814047215844041655685 3086027633852970757810441)
                    ·
                      refine ⟨2314520725389728068357831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3086027633852970757810441 2314520725389728068357831)
                      ·
                        rfl

theorem cell23_4507513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 3, 2, 4, 2].length) (baseStart_4507513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4507513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4507513 prefixEnd_4507513 := by exact prefixLift 4507513
  have htrace : WordTrace (prefixWord ++ tailWord_4507513) baseStart_4507513 baseEnd_4507513 := by
    simpa [prefixWord, tailWord_4507513, baseEnd_4507513] using wordTrace_append hprefix tailTrace_4507513
  have hstable : (prefixWord ++ tailWord_4507513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4507513).length < 2 ^ (prefixWord ++ tailWord_4507513).sum := by decide
  have hdescent : baseEnd_4507513 < baseStart_4507513 := by decide
  rcases family_descends (prefixWord ++ tailWord_4507513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4507523 : List Nat := [1, 1, 1, 3, 4, 2, 2, 2, 3, 4]
def baseStart_4507523 : Nat := 118140960795 + 4507523 * 2 ^ 59
def prefixEnd_4507523 : Nat := 4983230072969 + 3 ^ 40 * 4507523 * 2
def baseEnd_4507523 : Nat := 771508620065424343077595

theorem tailTrace_4507523 : CollatzResearch.WordTrace tailWord_4507523 prefixEnd_4507523 771508620065424343077595 := by
  unfold tailWord_4507523
  simp only [CollatzResearch.WordTrace]
  refine ⟨164402870049021469484719223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109601913366014312989812815 164402870049021469484719223)
  ·
    refine ⟨246604305073532204227078835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164402870049021469484719223 246604305073532204227078835)
    ·
      refine ⟨369906457610298306340618253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 246604305073532204227078835 369906457610298306340618253)
      ·
        refine ⟨138714921603861864877731845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 369906457610298306340618253 138714921603861864877731845)
        ·
          refine ⟨26009047800724099664574721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 138714921603861864877731845 26009047800724099664574721)
          ·
            refine ⟨19506785850543074748431041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26009047800724099664574721 19506785850543074748431041)
            ·
              refine ⟨14630089387907306061323281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19506785850543074748431041 14630089387907306061323281)
              ·
                refine ⟨10972567040930479545992461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14630089387907306061323281 10972567040930479545992461)
                ·
                  refine ⟨4114712640348929829747173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10972567040930479545992461 4114712640348929829747173)
                  ·
                    refine ⟨771508620065424343077595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4114712640348929829747173 771508620065424343077595)
                    ·
                      rfl

theorem cell23_4507523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 2, 3, 4].length) (baseStart_4507523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4507523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4507523 prefixEnd_4507523 := by exact prefixLift 4507523
  have htrace : WordTrace (prefixWord ++ tailWord_4507523) baseStart_4507523 baseEnd_4507523 := by
    simpa [prefixWord, tailWord_4507523, baseEnd_4507523] using wordTrace_append hprefix tailTrace_4507523
  have hstable : (prefixWord ++ tailWord_4507523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4507523).length < 2 ^ (prefixWord ++ tailWord_4507523).sum := by decide
  have hdescent : baseEnd_4507523 < baseStart_4507523 := by decide
  rcases family_descends (prefixWord ++ tailWord_4507523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4507616 : List Nat := [2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 6]
def baseStart_4507616 : Nat := 118140960795 + 4507616 * 2 ^ 59
def prefixEnd_4507616 : Nat := 4983230072969 + 3 ^ 40 * 4507616 * 2
def baseEnd_4507616 : Nat := 2314573613897141165369857

theorem tailTrace_4507616 : CollatzResearch.WordTrace tailWord_4507616 prefixEnd_4507616 2314573613897141165369857 := by
  unfold tailWord_4507616
  simp only [CollatzResearch.WordTrace]
  refine ⟨82203131018842273183927351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109604174691789697578569801 82203131018842273183927351)
  ·
    refine ⟨123304696528263409775891027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82203131018842273183927351 123304696528263409775891027)
    ·
      refine ⟨184957044792395114663836541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123304696528263409775891027 184957044792395114663836541)
      ·
        refine ⟨69358891797148167998938703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 184957044792395114663836541 69358891797148167998938703)
        ·
          refine ⟨104038337695722251998408055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69358891797148167998938703 104038337695722251998408055)
          ·
            refine ⟨156057506543583377997612083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104038337695722251998408055 156057506543583377997612083)
            ·
              refine ⟨234086259815375066996418125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 156057506543583377997612083 234086259815375066996418125)
              ·
                refine ⟨87782347430765650123656797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 234086259815375066996418125 87782347430765650123656797)
                ·
                  refine ⟨32918380286537118796371299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 87782347430765650123656797 32918380286537118796371299)
                  ·
                    refine ⟨49377570429805678194556949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32918380286537118796371299 49377570429805678194556949)
                    ·
                      refine ⟨2314573613897141165369857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49377570429805678194556949 2314573613897141165369857)
                      ·
                        rfl

theorem cell23_4507616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 6].length) (baseStart_4507616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4507616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4507616 prefixEnd_4507616 := by exact prefixLift 4507616
  have htrace : WordTrace (prefixWord ++ tailWord_4507616) baseStart_4507616 baseEnd_4507616 := by
    simpa [prefixWord, tailWord_4507616, baseEnd_4507616] using wordTrace_append hprefix tailTrace_4507616
  have hstable : (prefixWord ++ tailWord_4507616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4507616).length < 2 ^ (prefixWord ++ tailWord_4507616).sum := by decide
  have hdescent : baseEnd_4507616 < baseStart_4507616 := by decide
  rcases family_descends (prefixWord ++ tailWord_4507616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4507630 : List Nat := [4, 1, 2, 1, 3, 2, 2, 1, 1, 6]
def baseStart_4507630 : Nat := 118140960795 + 4507630 * 2 ^ 59
def prefixEnd_4507630 : Nat := 4983230072969 + 3 ^ 40 * 4507630 * 2
def baseEnd_4507630 : Nat := 771526934208768036864931

theorem tailTrace_4507630 : CollatzResearch.WordTrace tailWord_4507630 prefixEnd_4507630 771526934208768036864931 := by
  unfold tailWord_4507630
  simp only [CollatzResearch.WordTrace]
  refine ⟨20550846582454228344858043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109604515106422551172576229 20550846582454228344858043)
  ·
    refine ⟨30826269873681342517287065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20550846582454228344858043 30826269873681342517287065)
    ·
      refine ⟨23119702405261006887965299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30826269873681342517287065 23119702405261006887965299)
      ·
        refine ⟨34679553607891510331947949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23119702405261006887965299 34679553607891510331947949)
        ·
          refine ⟨13004832602959316374480481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34679553607891510331947949 13004832602959316374480481)
          ·
            refine ⟨9753624452219487280860361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13004832602959316374480481 9753624452219487280860361)
            ·
              refine ⟨7315218339164615460645271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9753624452219487280860361 7315218339164615460645271)
              ·
                refine ⟨10972827508746923190967907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7315218339164615460645271 10972827508746923190967907)
                ·
                  refine ⟨16459241263120384786451861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10972827508746923190967907 16459241263120384786451861)
                  ·
                    refine ⟨771526934208768036864931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16459241263120384786451861 771526934208768036864931)
                    ·
                      rfl

theorem cell23_4507630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 2, 1, 1, 6].length) (baseStart_4507630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4507630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4507630 prefixEnd_4507630 := by exact prefixLift 4507630
  have htrace : WordTrace (prefixWord ++ tailWord_4507630) baseStart_4507630 baseEnd_4507630 := by
    simpa [prefixWord, tailWord_4507630, baseEnd_4507630] using wordTrace_append hprefix tailTrace_4507630
  have hstable : (prefixWord ++ tailWord_4507630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4507630).length < 2 ^ (prefixWord ++ tailWord_4507630).sum := by decide
  have hdescent : baseEnd_4507630 < baseStart_4507630 := by decide
  rcases family_descends (prefixWord ++ tailWord_4507630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4507684 : List Nat := [2, 3, 1, 4, 3, 1, 1, 1, 1, 2, 4]
def baseStart_4507684 : Nat := 118140960795 + 4507684 * 2 ^ 59
def prefixEnd_4507684 : Nat := 4983230072969 + 3 ^ 40 * 4507684 * 2
def baseEnd_4507684 : Nat := 2314608530581646899319545

theorem tailTrace_4507684 : CollatzResearch.WordTrace tailWord_4507684 prefixEnd_4507684 2314608530581646899319545 := by
  unfold tailWord_4507684
  simp only [CollatzResearch.WordTrace]
  refine ⟨82204371100719096990665053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109605828134292129320886737 82204371100719096990665053)
  ·
    refine ⟨30826639162769661371499395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82204371100719096990665053 30826639162769661371499395)
    ·
      refine ⟨46239958744154492057249093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30826639162769661371499395 46239958744154492057249093)
      ·
        refine ⟨8669992264528967260734205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46239958744154492057249093 8669992264528967260734205)
        ·
          refine ⟨3251247099198362722775327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8669992264528967260734205 3251247099198362722775327)
          ·
            refine ⟨4876870648797544084162991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3251247099198362722775327 4876870648797544084162991)
            ·
              refine ⟨7315305973196316126244487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4876870648797544084162991 7315305973196316126244487)
              ·
                refine ⟨10972958959794474189366731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7315305973196316126244487 10972958959794474189366731)
                ·
                  refine ⟨16459438439691711284050097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10972958959794474189366731 16459438439691711284050097)
                  ·
                    refine ⟨12344578829768783463037573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16459438439691711284050097 12344578829768783463037573)
                    ·
                      refine ⟨2314608530581646899319545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12344578829768783463037573 2314608530581646899319545)
                      ·
                        rfl

theorem cell23_4507684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 1, 1, 1, 2, 4].length) (baseStart_4507684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4507684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4507684 prefixEnd_4507684 := by exact prefixLift 4507684
  have htrace : WordTrace (prefixWord ++ tailWord_4507684) baseStart_4507684 baseEnd_4507684 := by
    simpa [prefixWord, tailWord_4507684, baseEnd_4507684] using wordTrace_append hprefix tailTrace_4507684
  have hstable : (prefixWord ++ tailWord_4507684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4507684).length < 2 ^ (prefixWord ++ tailWord_4507684).sum := by decide
  have hdescent : baseEnd_4507684 < baseStart_4507684 := by decide
  rcases family_descends (prefixWord ++ tailWord_4507684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4507697 : List Nat := [1, 2, 2, 3, 1, 3, 1, 4, 1, 3, 2]
def baseStart_4507697 : Nat := 118140960795 + 4507697 * 2 ^ 59
def prefixEnd_4507697 : Nat := 4983230072969 + 3 ^ 40 * 4507697 * 2
def baseEnd_4507697 : Nat := 2314615205830155348456985

theorem tailTrace_4507697 : CollatzResearch.WordTrace tailWord_4507697 prefixEnd_4507697 2314615205830155348456985 := by
  unfold tailWord_4507697
  simp only [CollatzResearch.WordTrace]
  refine ⟨164409216350391097201553345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109606144233594064801035563 164409216350391097201553345)
  ·
    refine ⟨123306912262793322901165009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164409216350391097201553345 123306912262793322901165009)
    ·
      refine ⟨92480184197094992175873757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123306912262793322901165009 92480184197094992175873757)
      ·
        refine ⟨34680069073910622065952659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92480184197094992175873757 34680069073910622065952659)
        ·
          refine ⟨52020103610865933098928989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34680069073910622065952659 52020103610865933098928989)
          ·
            refine ⟨19507538854074724912098371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52020103610865933098928989 19507538854074724912098371)
            ·
              refine ⟨29261308281112087368147557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19507538854074724912098371 29261308281112087368147557)
              ·
                refine ⟨5486495302708516381527667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29261308281112087368147557 5486495302708516381527667)
                ·
                  refine ⟨8229742954062774572291501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5486495302708516381527667 8229742954062774572291501)
                  ·
                    refine ⟨3086153607773540464609313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8229742954062774572291501 3086153607773540464609313)
                    ·
                      refine ⟨2314615205830155348456985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3086153607773540464609313 2314615205830155348456985)
                      ·
                        rfl

theorem cell23_4507697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 4, 1, 3, 2].length) (baseStart_4507697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4507697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4507697 prefixEnd_4507697 := by exact prefixLift 4507697
  have htrace : WordTrace (prefixWord ++ tailWord_4507697) baseStart_4507697 baseEnd_4507697 := by
    simpa [prefixWord, tailWord_4507697, baseEnd_4507697] using wordTrace_append hprefix tailTrace_4507697
  have hstable : (prefixWord ++ tailWord_4507697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4507697).length < 2 ^ (prefixWord ++ tailWord_4507697).sum := by decide
  have hdescent : baseEnd_4507697 < baseStart_4507697 := by decide
  rcases family_descends (prefixWord ++ tailWord_4507697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4507744 : List Nat := [2, 1, 1, 3, 2, 4, 1, 3, 2, 2, 2]
def baseStart_4507744 : Nat := 118140960795 + 4507744 * 2 ^ 59
def prefixEnd_4507744 : Nat := 4983230072969 + 3 ^ 40 * 4507744 * 2
def baseEnd_4507744 : Nat := 2314639339420916664569269

theorem tailTrace_4507744 : CollatzResearch.WordTrace tailWord_4507744 prefixEnd_4507744 2314639339420916664569269 := by
  unfold tailWord_4507744
  simp only [CollatzResearch.WordTrace]
  refine ⟨82205465290610412114257143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109607287054147216152342857 82205465290610412114257143)
  ·
    refine ⟨123308197935915618171385715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82205465290610412114257143 123308197935915618171385715)
    ·
      refine ⟨184962296903873427257078573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123308197935915618171385715 184962296903873427257078573)
      ·
        refine ⟨69360861338952535221404465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 184962296903873427257078573 69360861338952535221404465)
        ·
          refine ⟨52020646004214401416053349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69360861338952535221404465 52020646004214401416053349)
          ·
            refine ⟨9753871125790200265510003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52020646004214401416053349 9753871125790200265510003)
            ·
              refine ⟨14630806688685300398265005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9753871125790200265510003 14630806688685300398265005)
              ·
                refine ⟨5486552508256987649349377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14630806688685300398265005 5486552508256987649349377)
                ·
                  refine ⟨4114914381192740737012033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5486552508256987649349377 4114914381192740737012033)
                  ·
                    refine ⟨3086185785894555552759025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4114914381192740737012033 3086185785894555552759025)
                    ·
                      refine ⟨2314639339420916664569269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3086185785894555552759025 2314639339420916664569269)
                      ·
                        rfl

theorem cell23_4507744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 3, 2, 2, 2].length) (baseStart_4507744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4507744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4507744 prefixEnd_4507744 := by exact prefixLift 4507744
  have htrace : WordTrace (prefixWord ++ tailWord_4507744) baseStart_4507744 baseEnd_4507744 := by
    simpa [prefixWord, tailWord_4507744, baseEnd_4507744] using wordTrace_append hprefix tailTrace_4507744
  have hstable : (prefixWord ++ tailWord_4507744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4507744).length < 2 ^ (prefixWord ++ tailWord_4507744).sum := by decide
  have hdescent : baseEnd_4507744 < baseStart_4507744 := by decide
  rcases family_descends (prefixWord ++ tailWord_4507744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4507770 : List Nat := [3, 1, 1, 1, 1, 1, 1, 1, 6, 5, 2]
def baseStart_4507770 : Nat := 118140960795 + 4507770 * 2 ^ 59
def prefixEnd_4507770 : Nat := 4983230072969 + 3 ^ 40 * 4507770 * 2
def baseEnd_4507770 : Nat := 2314652689917933562844149

theorem tailTrace_4507770 : CollatzResearch.WordTrace tailWord_4507770 prefixEnd_4507770 2314652689917933562844149 := by
  unfold tailWord_4507770
  simp only [CollatzResearch.WordTrace]
  refine ⟨41102969719781657667240191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109607919252751087112640509 41102969719781657667240191)
  ·
    refine ⟨61654454579672486500860287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41102969719781657667240191 61654454579672486500860287)
    ·
      refine ⟨92481681869508729751290431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61654454579672486500860287 92481681869508729751290431)
      ·
        refine ⟨138722522804263094626935647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92481681869508729751290431 138722522804263094626935647)
        ·
          refine ⟨208083784206394641940403471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138722522804263094626935647 208083784206394641940403471)
          ·
            refine ⟨312125676309591962910605207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 208083784206394641940403471 312125676309591962910605207)
            ·
              refine ⟨468188514464387944365907811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 312125676309591962910605207 468188514464387944365907811)
              ·
                refine ⟨702282771696581916548861717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 468188514464387944365907811 702282771696581916548861717)
                ·
                  refine ⟨32919504923277277338227893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 702282771696581916548861717 32919504923277277338227893)
                  ·
                    refine ⟨3086203586557244750458865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32919504923277277338227893 3086203586557244750458865)
                    ·
                      refine ⟨2314652689917933562844149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3086203586557244750458865 2314652689917933562844149)
                      ·
                        rfl

theorem cell23_4507770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 6, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 6, 5, 2].length) (baseStart_4507770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4507770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4507770 prefixEnd_4507770 := by exact prefixLift 4507770
  have htrace : WordTrace (prefixWord ++ tailWord_4507770) baseStart_4507770 baseEnd_4507770 := by
    simpa [prefixWord, tailWord_4507770, baseEnd_4507770] using wordTrace_append hprefix tailTrace_4507770
  have hstable : (prefixWord ++ tailWord_4507770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4507770).length < 2 ^ (prefixWord ++ tailWord_4507770).sum := by decide
  have hdescent : baseEnd_4507770 < baseStart_4507770 := by decide
  rcases family_descends (prefixWord ++ tailWord_4507770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4507780 : List Nat := [2, 3, 2, 1, 2, 1, 1, 4, 2, 5]
def baseStart_4507780 : Nat := 118140960795 + 4507780 * 2 ^ 59
def prefixEnd_4507780 : Nat := 4983230072969 + 3 ^ 40 * 4507780 * 2
def baseEnd_4507780 : Nat := 771552608241492841239701

theorem tailTrace_4507780 : CollatzResearch.WordTrace tailWord_4507780 prefixEnd_4507780 771552608241492841239701 := by
  unfold tailWord_4507780
  simp only [CollatzResearch.WordTrace]
  refine ⟨82206121804545201188412397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109608162406060268251216529 82206121804545201188412397)
  ·
    refine ⟨30827295676704450445654649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82206121804545201188412397 30827295676704450445654649)
    ·
      refine ⟨23120471757528337834240987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30827295676704450445654649 23120471757528337834240987)
      ·
        refine ⟨34680707636292506751361481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23120471757528337834240987 34680707636292506751361481)
        ·
          refine ⟨26010530727219380063521111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34680707636292506751361481 26010530727219380063521111)
          ·
            refine ⟨39015796090829070095281667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26010530727219380063521111 39015796090829070095281667)
            ·
              refine ⟨58523694136243605142922501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39015796090829070095281667 58523694136243605142922501)
              ·
                refine ⟨10973192650545675964297969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58523694136243605142922501 10973192650545675964297969)
                ·
                  refine ⟨8229894487909256973223477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10973192650545675964297969 8229894487909256973223477)
                  ·
                    refine ⟨771552608241492841239701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8229894487909256973223477 771552608241492841239701)
                    ·
                      rfl

theorem cell23_4507780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 4, 2, 5].length) (baseStart_4507780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4507780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4507780 prefixEnd_4507780 := by exact prefixLift 4507780
  have htrace : WordTrace (prefixWord ++ tailWord_4507780) baseStart_4507780 baseEnd_4507780 := by
    simpa [prefixWord, tailWord_4507780, baseEnd_4507780] using wordTrace_append hprefix tailTrace_4507780
  have hstable : (prefixWord ++ tailWord_4507780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4507780).length < 2 ^ (prefixWord ++ tailWord_4507780).sum := by decide
  have hdescent : baseEnd_4507780 < baseStart_4507780 := by decide
  rcases family_descends (prefixWord ++ tailWord_4507780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4507784 : List Nat := [2, 1, 3, 4, 1, 1, 4, 2, 5]
def baseStart_4507784 : Nat := 118140960795 + 4507784 * 2 ^ 59
def prefixEnd_4507784 : Nat := 4983230072969 + 3 ^ 40 * 4507784 * 2
def baseEnd_4507784 : Nat := 257184430960788500896565

theorem tailTrace_4507784 : CollatzResearch.WordTrace tailWord_4507784 prefixEnd_4507784 257184430960788500896565 := by
  unfold tailWord_4507784
  simp only [CollatzResearch.WordTrace]
  refine ⟨82206194750537955529985203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109608259667383940706646937 82206194750537955529985203)
  ·
    refine ⟨123309292125806933294977805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82206194750537955529985203 123309292125806933294977805)
    ·
      refine ⟨46240984547177599985616677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123309292125806933294977805 46240984547177599985616677)
      ·
        refine ⟨8670184602595799997303127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46240984547177599985616677 8670184602595799997303127)
        ·
          refine ⟨13005276903893699995954691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8670184602595799997303127 13005276903893699995954691)
          ·
            refine ⟨19507915355840549993932037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13005276903893699995954691 19507915355840549993932037)
            ·
              refine ⟨3657734129220103123862257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19507915355840549993932037 3657734129220103123862257)
              ·
                refine ⟨2743300596915077342896693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3657734129220103123862257 2743300596915077342896693)
                ·
                  refine ⟨257184430960788500896565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2743300596915077342896693 257184430960788500896565)
                  ·
                    rfl

theorem cell23_4507784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 4, 2, 5].length) (baseStart_4507784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4507784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4507784 prefixEnd_4507784 := by exact prefixLift 4507784
  have htrace : WordTrace (prefixWord ++ tailWord_4507784) baseStart_4507784 baseEnd_4507784 := by
    simpa [prefixWord, tailWord_4507784, baseEnd_4507784] using wordTrace_append hprefix tailTrace_4507784
  have hstable : (prefixWord ++ tailWord_4507784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4507784).length < 2 ^ (prefixWord ++ tailWord_4507784).sum := by decide
  have hdescent : baseEnd_4507784 < baseStart_4507784 := by decide
  rcases family_descends (prefixWord ++ tailWord_4507784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4507823 : List Nat := [1, 1, 2, 1, 2, 3, 1, 4, 8]
def baseStart_4507823 : Nat := 118140960795 + 4507823 * 2 ^ 59
def prefixEnd_4507823 : Nat := 4983230072969 + 3 ^ 40 * 4507823 * 2
def baseEnd_4507823 : Nat := 257186656043624650609045

theorem tailTrace_4507823 : CollatzResearch.WordTrace tailWord_4507823 prefixEnd_4507823 257186656043624650609045 := by
  unfold tailWord_4507823
  simp only [CollatzResearch.WordTrace]
  refine ⟨164413811947934620720640123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109609207965289747147093415 164413811947934620720640123)
  ·
    refine ⟨246620717921901931080960185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164413811947934620720640123 246620717921901931080960185)
    ·
      refine ⟨184965538441426448310720139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 246620717921901931080960185 184965538441426448310720139)
      ·
        refine ⟨277448307662139672466080209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184965538441426448310720139 277448307662139672466080209)
        ·
          refine ⟨208086230746604754349560157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 277448307662139672466080209 208086230746604754349560157)
          ·
            refine ⟨78032336529976782881085059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 208086230746604754349560157 78032336529976782881085059)
            ·
              refine ⟨117048504794965174321627589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78032336529976782881085059 117048504794965174321627589)
              ·
                refine ⟨21946594649055970185305173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 117048504794965174321627589 21946594649055970185305173)
                ·
                  refine ⟨257186656043624650609045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21946594649055970185305173 257186656043624650609045)
                  ·
                    rfl

theorem cell23_4507823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 4, 8].length) (baseStart_4507823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4507823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4507823 prefixEnd_4507823 := by exact prefixLift 4507823
  have htrace : WordTrace (prefixWord ++ tailWord_4507823) baseStart_4507823 baseEnd_4507823 := by
    simpa [prefixWord, tailWord_4507823, baseEnd_4507823] using wordTrace_append hprefix tailTrace_4507823
  have hstable : (prefixWord ++ tailWord_4507823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4507823).length < 2 ^ (prefixWord ++ tailWord_4507823).sum := by decide
  have hdescent : baseEnd_4507823 < baseStart_4507823 := by decide
  rcases family_descends (prefixWord ++ tailWord_4507823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4507840 : List Nat := [2, 1, 1, 2, 5, 2, 1, 1, 8]
def baseStart_4507840 : Nat := 118140960795 + 4507840 * 2 ^ 59
def prefixEnd_4507840 : Nat := 4983230072969 + 3 ^ 40 * 4507840 * 2
def baseEnd_4507840 : Nat := 257187625951527587663203

theorem tailTrace_4507840 : CollatzResearch.WordTrace tailWord_4507840 prefixEnd_4507840 257187625951527587663203 := by
  unfold tailWord_4507840
  simp only [CollatzResearch.WordTrace]
  refine ⟨82207215994436516312004487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109609621325915355082672649 82207215994436516312004487)
  ·
    refine ⟨123310823991654774468006731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82207215994436516312004487 123310823991654774468006731)
    ·
      refine ⟨184966235987482161702010097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123310823991654774468006731 184966235987482161702010097)
      ·
        refine ⟨138724676990611621276507573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 184966235987482161702010097 138724676990611621276507573)
        ·
          refine ⟨13005438467869839494672585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 138724676990611621276507573 13005438467869839494672585)
          ·
            refine ⟨9754078850902379621004439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13005438467869839494672585 9754078850902379621004439)
            ·
              refine ⟨14631118276353569431506659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9754078850902379621004439 14631118276353569431506659)
              ·
                refine ⟨21946677414530354147259989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14631118276353569431506659 21946677414530354147259989)
                ·
                  refine ⟨257187625951527587663203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21946677414530354147259989 257187625951527587663203)
                  ·
                    rfl

theorem cell23_4507840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 1, 8].length) (baseStart_4507840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4507840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4507840 prefixEnd_4507840 := by exact prefixLift 4507840
  have htrace : WordTrace (prefixWord ++ tailWord_4507840) baseStart_4507840 baseEnd_4507840 := by
    simpa [prefixWord, tailWord_4507840, baseEnd_4507840] using wordTrace_append hprefix tailTrace_4507840
  have hstable : (prefixWord ++ tailWord_4507840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4507840).length < 2 ^ (prefixWord ++ tailWord_4507840).sum := by decide
  have hdescent : baseEnd_4507840 < baseStart_4507840 := by decide
  rcases family_descends (prefixWord ++ tailWord_4507840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4507844 : List Nat := [2, 3, 3, 1, 2, 2, 2, 1, 3, 4]
def baseStart_4507844 : Nat := 118140960795 + 4507844 * 2 ^ 59
def prefixEnd_4507844 : Nat := 4983230072969 + 3 ^ 40 * 4507844 * 2
def baseEnd_4507844 : Nat := 771563562495455424439603

theorem tailTrace_4507844 : CollatzResearch.WordTrace tailWord_4507844 prefixEnd_4507844 771563562495455424439603 := by
  unfold tailWord_4507844
  simp only [CollatzResearch.WordTrace]
  refine ⟨82207288940429270653577293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109609718587239027538103057 82207288940429270653577293)
  ·
    refine ⟨30827733352660976495091485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82207288940429270653577293 30827733352660976495091485)
    ·
      refine ⟨11560400007247866185659307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30827733352660976495091485 11560400007247866185659307)
      ·
        refine ⟨17340600010871799278488961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11560400007247866185659307 17340600010871799278488961)
        ·
          refine ⟨13005450008153849458866721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17340600010871799278488961 13005450008153849458866721)
          ·
            refine ⟨9754087506115387094150041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13005450008153849458866721 9754087506115387094150041)
            ·
              refine ⟨7315565629586540320612531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9754087506115387094150041 7315565629586540320612531)
              ·
                refine ⟨10973348444379810480918797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7315565629586540320612531 10973348444379810480918797)
                ·
                  refine ⟨4115005666642428930344549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10973348444379810480918797 4115005666642428930344549)
                  ·
                    refine ⟨771563562495455424439603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4115005666642428930344549 771563562495455424439603)
                    ·
                      rfl

theorem cell23_4507844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 2, 1, 3, 4].length) (baseStart_4507844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4507844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4507844 prefixEnd_4507844 := by exact prefixLift 4507844
  have htrace : WordTrace (prefixWord ++ tailWord_4507844) baseStart_4507844 baseEnd_4507844 := by
    simpa [prefixWord, tailWord_4507844, baseEnd_4507844] using wordTrace_append hprefix tailTrace_4507844
  have hstable : (prefixWord ++ tailWord_4507844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4507844).length < 2 ^ (prefixWord ++ tailWord_4507844).sum := by decide
  have hdescent : baseEnd_4507844 < baseStart_4507844 := by decide
  rcases family_descends (prefixWord ++ tailWord_4507844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4507887 : List Nat := [1, 1, 2, 1, 6, 1, 2, 3, 1, 5]
def baseStart_4507887 : Nat := 118140960795 + 4507887 * 2 ^ 59
def prefixEnd_4507887 : Nat := 4983230072969 + 3 ^ 40 * 4507887 * 2
def baseEnd_4507887 : Nat := 771570922384836535027037

theorem tailTrace_4507887 : CollatzResearch.WordTrace tailWord_4507887 prefixEnd_4507887 771570922384836535027037 := by
  unfold tailWord_4507887
  simp only [CollatzResearch.WordTrace]
  refine ⟨164416146219702759650969915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109610764146468506433979943 164416146219702759650969915)
  ·
    refine ⟨246624219329554139476454873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164416146219702759650969915 246624219329554139476454873)
    ·
      refine ⟨184968164497165604607341155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 246624219329554139476454873 184968164497165604607341155)
      ·
        refine ⟨277452246745748406911011733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184968164497165604607341155 277452246745748406911011733)
        ·
          refine ⟨13005574066206956573953675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 277452246745748406911011733 13005574066206956573953675)
          ·
            refine ⟨19508361099310434860930513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13005574066206956573953675 19508361099310434860930513)
            ·
              refine ⟨14631270824482826145697885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19508361099310434860930513 14631270824482826145697885)
              ·
                refine ⟨5486726559181059804636707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14631270824482826145697885 5486726559181059804636707)
                ·
                  refine ⟨8230089838771589706955061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5486726559181059804636707 8230089838771589706955061)
                  ·
                    refine ⟨771570922384836535027037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8230089838771589706955061 771570922384836535027037)
                    ·
                      rfl

theorem cell23_4507887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 3, 1, 5].length) (baseStart_4507887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4507887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4507887 prefixEnd_4507887 := by exact prefixLift 4507887
  have htrace : WordTrace (prefixWord ++ tailWord_4507887) baseStart_4507887 baseEnd_4507887 := by
    simpa [prefixWord, tailWord_4507887, baseEnd_4507887] using wordTrace_append hprefix tailTrace_4507887
  have hstable : (prefixWord ++ tailWord_4507887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4507887).length < 2 ^ (prefixWord ++ tailWord_4507887).sum := by decide
  have hdescent : baseEnd_4507887 < baseStart_4507887 := by decide
  rcases family_descends (prefixWord ++ tailWord_4507887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4507894 : List Nat := [5, 1, 1, 1, 1, 1, 3, 1, 4, 3, 2]
def baseStart_4507894 : Nat := 118140960795 + 4507894 * 2 ^ 59
def prefixEnd_4507894 : Nat := 4983230072969 + 3 ^ 40 * 4507894 * 2
def baseEnd_4507894 : Nat := 2314716361519091077693579

theorem tailTrace_4507894 : CollatzResearch.WordTrace tailWord_4507894 prefixEnd_4507894 2314716361519091077693579 := by
  unfold tailWord_4507894
  simp only [CollatzResearch.WordTrace]
  refine ⟨10276025095667337490404671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 109610934353784933230983157 10276025095667337490404671)
  ·
    refine ⟨15414037643501006235607007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10276025095667337490404671 15414037643501006235607007)
    ·
      refine ⟨23121056465251509353410511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15414037643501006235607007 23121056465251509353410511)
      ·
        refine ⟨34681584697877264030115767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23121056465251509353410511 34681584697877264030115767)
        ·
          refine ⟨52022377046815896045173651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34681584697877264030115767 52022377046815896045173651)
          ·
            refine ⟨78033565570223844067760477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52022377046815896045173651 78033565570223844067760477)
            ·
              refine ⟨29262587088833941525410179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78033565570223844067760477 29262587088833941525410179)
              ·
                refine ⟨43893880633250912288115269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29262587088833941525410179 43893880633250912288115269)
                ·
                  refine ⟨8230102618734546054021613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43893880633250912288115269 8230102618734546054021613)
                  ·
                    refine ⟨3086288482025454770258105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8230102618734546054021613 3086288482025454770258105)
                    ·
                      refine ⟨2314716361519091077693579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3086288482025454770258105 2314716361519091077693579)
                      ·
                        rfl

theorem cell23_4507894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 1, 4, 3, 2].length) (baseStart_4507894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4507894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4507894 prefixEnd_4507894 := by exact prefixLift 4507894
  have htrace : WordTrace (prefixWord ++ tailWord_4507894) baseStart_4507894 baseEnd_4507894 := by
    simpa [prefixWord, tailWord_4507894, baseEnd_4507894] using wordTrace_append hprefix tailTrace_4507894
  have hstable : (prefixWord ++ tailWord_4507894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4507894).length < 2 ^ (prefixWord ++ tailWord_4507894).sum := by decide
  have hdescent : baseEnd_4507894 < baseStart_4507894 := by decide
  rcases family_descends (prefixWord ++ tailWord_4507894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4507934 : List Nat := [4, 3, 2, 1, 1, 1, 1, 1, 3, 6]
def baseStart_4507934 : Nat := 118140960795 + 4507934 * 2 ^ 59
def prefixEnd_4507934 : Nat := 4983230072969 + 3 ^ 40 * 4507934 * 2
def baseEnd_4507934 : Nat := 771578966915090307064465

theorem tailTrace_4507934 : CollatzResearch.WordTrace tailWord_4507934 prefixEnd_4507934 771578966915090307064465 := by
  unfold tailWord_4507934
  simp only [CollatzResearch.WordTrace]
  refine ⟨20552232556316560834741357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109611906967021657785287237 20552232556316560834741357)
  ·
    refine ⟨7707087208618710313028009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20552232556316560834741357 7707087208618710313028009)
    ·
      refine ⟨5780315406464032734771007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7707087208618710313028009 5780315406464032734771007)
      ·
        refine ⟨8670473109696049102156511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5780315406464032734771007 8670473109696049102156511)
        ·
          refine ⟨13005709664544073653234767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8670473109696049102156511 13005709664544073653234767)
          ·
            refine ⟨19508564496816110479852151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13005709664544073653234767 19508564496816110479852151)
            ·
              refine ⟨29262846745224165719778227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19508564496816110479852151 29262846745224165719778227)
              ·
                refine ⟨43894270117836248579667341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29262846745224165719778227 43894270117836248579667341)
                ·
                  refine ⟨16460351294188593217375253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43894270117836248579667341 16460351294188593217375253)
                  ·
                    refine ⟨771578966915090307064465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16460351294188593217375253 771578966915090307064465)
                    ·
                      rfl

theorem cell23_4507934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_4507934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4507934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4507934 prefixEnd_4507934 := by exact prefixLift 4507934
  have htrace : WordTrace (prefixWord ++ tailWord_4507934) baseStart_4507934 baseEnd_4507934 := by
    simpa [prefixWord, tailWord_4507934, baseEnd_4507934] using wordTrace_append hprefix tailTrace_4507934
  have hstable : (prefixWord ++ tailWord_4507934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4507934).length < 2 ^ (prefixWord ++ tailWord_4507934).sum := by decide
  have hdescent : baseEnd_4507934 < baseStart_4507934 := by decide
  rcases family_descends (prefixWord ++ tailWord_4507934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4507941 : List Nat := [1, 3, 1, 2, 5, 1, 3, 1, 1, 1, 4]
def baseStart_4507941 : Nat := 118140960795 + 4507941 * 2 ^ 59
def prefixEnd_4507941 : Nat := 4983230072969 + 3 ^ 40 * 4507941 * 2
def baseEnd_4507941 : Nat := 2314740495109852393805863

theorem tailTrace_4507941 : CollatzResearch.WordTrace tailWord_4507941 prefixEnd_4507941 2314740495109852393805863 := by
  unfold tailWord_4507941
  simp only [CollatzResearch.WordTrace]
  refine ⟨164418115761507126873435677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109612077174338084582290451 164418115761507126873435677)
  ·
    refine ⟨61656793410565172577538379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 164418115761507126873435677 61656793410565172577538379)
    ·
      refine ⟨92485190115847758866307569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61656793410565172577538379 92485190115847758866307569)
      ·
        refine ⟨69363892586885819149730677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92485190115847758866307569 69363892586885819149730677)
        ·
          refine ⟨6502864930020545545287251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 69363892586885819149730677 6502864930020545545287251)
          ·
            refine ⟨9754297395030818317930877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6502864930020545545287251 9754297395030818317930877)
            ·
              refine ⟨3657861523136556869224079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9754297395030818317930877 3657861523136556869224079)
              ·
                refine ⟨5486792284704835303836119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3657861523136556869224079 5486792284704835303836119)
                ·
                  refine ⟨8230188427057252955754179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5486792284704835303836119 8230188427057252955754179)
                  ·
                    refine ⟨12345282640585879433631269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8230188427057252955754179 12345282640585879433631269)
                    ·
                      refine ⟨2314740495109852393805863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12345282640585879433631269 2314740495109852393805863)
                      ·
                        rfl

theorem cell23_4507941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 3, 1, 1, 1, 4].length) (baseStart_4507941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4507941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4507941 prefixEnd_4507941 := by exact prefixLift 4507941
  have htrace : WordTrace (prefixWord ++ tailWord_4507941) baseStart_4507941 baseEnd_4507941 := by
    simpa [prefixWord, tailWord_4507941, baseEnd_4507941] using wordTrace_append hprefix tailTrace_4507941
  have hstable : (prefixWord ++ tailWord_4507941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4507941).length < 2 ^ (prefixWord ++ tailWord_4507941).sum := by decide
  have hdescent : baseEnd_4507941 < baseStart_4507941 := by decide
  rcases family_descends (prefixWord ++ tailWord_4507941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4507957 : List Nat := [1, 3, 3, 1, 2, 1, 1, 2, 3, 3, 3]
def baseStart_4507957 : Nat := 118140960795 + 4507957 * 2 ^ 59
def prefixEnd_4507957 : Nat := 4983230072969 + 3 ^ 40 * 4507957 * 2
def baseEnd_4507957 : Nat := 2314748710800324331205789

theorem tailTrace_4507957 : CollatzResearch.WordTrace tailWord_4507957 prefixEnd_4507957 2314748710800324331205789 := by
  unfold tailWord_4507957
  simp only [CollatzResearch.WordTrace]
  refine ⟨164418699329449161606018125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109612466219632774404012083 164418699329449161606018125)
  ·
    refine ⟨61657012248543435602256797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 164418699329449161606018125 61657012248543435602256797)
    ·
      refine ⟨23121379593203788350846299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61657012248543435602256797 23121379593203788350846299)
      ·
        refine ⟨34682069389805682526269449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23121379593203788350846299 34682069389805682526269449)
        ·
          refine ⟨26011552042354261894702087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34682069389805682526269449 26011552042354261894702087)
          ·
            refine ⟨39017328063531392842053131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26011552042354261894702087 39017328063531392842053131)
            ·
              refine ⟨58525992095297089263079697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39017328063531392842053131 58525992095297089263079697)
              ·
                refine ⟨43894494071472816947309773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58525992095297089263079697 43894494071472816947309773)
                ·
                  refine ⟨16460435276802306355241165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43894494071472816947309773 16460435276802306355241165)
                  ·
                    refine ⟨6172663228800864883215437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16460435276802306355241165 6172663228800864883215437)
                    ·
                      refine ⟨2314748710800324331205789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6172663228800864883215437 2314748710800324331205789)
                      ·
                        rfl

theorem cell23_4507957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 2, 3, 3, 3].length) (baseStart_4507957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4507957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4507957 prefixEnd_4507957 := by exact prefixLift 4507957
  have htrace : WordTrace (prefixWord ++ tailWord_4507957) baseStart_4507957 baseEnd_4507957 := by
    simpa [prefixWord, tailWord_4507957, baseEnd_4507957] using wordTrace_append hprefix tailTrace_4507957
  have hstable : (prefixWord ++ tailWord_4507957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4507957).length < 2 ^ (prefixWord ++ tailWord_4507957).sum := by decide
  have hdescent : baseEnd_4507957 < baseStart_4507957 := by decide
  rcases family_descends (prefixWord ++ tailWord_4507957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4507960 : List Nat := [2, 1, 2, 1, 3, 1, 3, 1, 2, 7]
def baseStart_4507960 : Nat := 118140960795 + 4507960 * 2 ^ 59
def prefixEnd_4507960 : Nat := 4983230072969 + 3 ^ 40 * 4507960 * 2
def baseEnd_4507960 : Nat := 771583417080762606489425

theorem tailTrace_4507960 : CollatzResearch.WordTrace tailWord_4507960 prefixEnd_4507960 771583417080762606489425 := by
  unfold tailWord_4507960
  simp only [CollatzResearch.WordTrace]
  refine ⟨82209404374219146559188667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109612539165625528745584889 82209404374219146559188667)
  ·
    refine ⟨123314106561328719838783001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82209404374219146559188667 123314106561328719838783001)
    ·
      refine ⟨92485579920996539879087251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123314106561328719838783001 92485579920996539879087251)
      ·
        refine ⟨138728369881494809818630877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92485579920996539879087251 138728369881494809818630877)
        ·
          refine ⟨52023138705560553681986579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 138728369881494809818630877 52023138705560553681986579)
          ·
            refine ⟨78034708058340830522979869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52023138705560553681986579 78034708058340830522979869)
            ·
              refine ⟨29263015521877811446117451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78034708058340830522979869 29263015521877811446117451)
              ·
                refine ⟨43894523282816717169176177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29263015521877811446117451 43894523282816717169176177)
                ·
                  refine ⟨32920892462112537876882133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43894523282816717169176177 32920892462112537876882133)
                  ·
                    refine ⟨771583417080762606489425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32920892462112537876882133 771583417080762606489425)
                    ·
                      rfl

theorem cell23_4507960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 1, 2, 7].length) (baseStart_4507960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4507960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4507960 prefixEnd_4507960 := by exact prefixLift 4507960
  have htrace : WordTrace (prefixWord ++ tailWord_4507960) baseStart_4507960 baseEnd_4507960 := by
    simpa [prefixWord, tailWord_4507960, baseEnd_4507960] using wordTrace_append hprefix tailTrace_4507960
  have hstable : (prefixWord ++ tailWord_4507960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4507960).length < 2 ^ (prefixWord ++ tailWord_4507960).sum := by decide
  have hdescent : baseEnd_4507960 < baseStart_4507960 := by decide
  rcases family_descends (prefixWord ++ tailWord_4507960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4507984 : List Nat := [2, 1, 1, 1, 1, 6, 2, 1, 3, 3, 2]
def baseStart_4507984 : Nat := 118140960795 + 4507984 * 2 ^ 59
def prefixEnd_4507984 : Nat := 4983230072969 + 3 ^ 40 * 4507984 * 2
def baseEnd_4507984 : Nat := 2314762574777995725568165

theorem tailTrace_4507984 : CollatzResearch.WordTrace tailWord_4507984 prefixEnd_4507984 2314762574777995725568165 := by
  unfold tailWord_4507984
  simp only [CollatzResearch.WordTrace]
  refine ⟨82209842050175672608625503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109613122733567563478167337 82209842050175672608625503)
  ·
    refine ⟨123314763075263508912938255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82209842050175672608625503 123314763075263508912938255)
    ·
      refine ⟨184972144612895263369407383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123314763075263508912938255 184972144612895263369407383)
      ·
        refine ⟨277458216919342895054111075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184972144612895263369407383 277458216919342895054111075)
        ·
          refine ⟨416187325379014342581166613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 277458216919342895054111075 416187325379014342581166613)
          ·
            refine ⟨19508780877141297308492185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 416187325379014342581166613 19508780877141297308492185)
            ·
              refine ⟨14631585657855972981369139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19508780877141297308492185 14631585657855972981369139)
              ·
                refine ⟨21947378486783959472053709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14631585657855972981369139 21947378486783959472053709)
                ·
                  refine ⟨8230266932543984802020141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21947378486783959472053709 8230266932543984802020141)
                  ·
                    refine ⟨3086350099703994300757553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8230266932543984802020141 3086350099703994300757553)
                    ·
                      refine ⟨2314762574777995725568165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3086350099703994300757553 2314762574777995725568165)
                      ·
                        rfl

theorem cell23_4507984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 1, 3, 3, 2].length) (baseStart_4507984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4507984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4507984 prefixEnd_4507984 := by exact prefixLift 4507984
  have htrace : WordTrace (prefixWord ++ tailWord_4507984) baseStart_4507984 baseEnd_4507984 := by
    simpa [prefixWord, tailWord_4507984, baseEnd_4507984] using wordTrace_append hprefix tailTrace_4507984
  have hstable : (prefixWord ++ tailWord_4507984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4507984).length < 2 ^ (prefixWord ++ tailWord_4507984).sum := by decide
  have hdescent : baseEnd_4507984 < baseStart_4507984 := by decide
  rcases family_descends (prefixWord ++ tailWord_4507984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4507998 : List Nat := [4, 4, 2, 1, 1, 1, 10]
def baseStart_4507998 : Nat := 118140960795 + 4507998 * 2 ^ 59
def prefixEnd_4507998 : Nat := 4983230072969 + 3 ^ 40 * 4507998 * 2
def baseEnd_4507998 : Nat := 28577404487742699639421

theorem tailTrace_4507998 : CollatzResearch.WordTrace tailWord_4507998 prefixEnd_4507998 28577404487742699639421 := by
  unfold tailWord_4507998
  simp only [CollatzResearch.WordTrace]
  refine ⟨20552524340287578201032581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109613463148200417072173765 20552524340287578201032581)
  ·
    refine ⟨3853598313803920912693609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20552524340287578201032581 3853598313803920912693609)
    ·
      refine ⟨2890198735352940684520207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3853598313803920912693609 2890198735352940684520207)
      ·
        refine ⟨4335298103029411026780311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2890198735352940684520207 4335298103029411026780311)
        ·
          refine ⟨6502947154544116540170467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4335298103029411026780311 6502947154544116540170467)
          ·
            refine ⟨9754420731816174810255701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6502947154544116540170467 9754420731816174810255701)
            ·
              refine ⟨28577404487742699639421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 9754420731816174810255701 28577404487742699639421)
              ·
                rfl

theorem cell23_4507998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 10].length) (baseStart_4507998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4507998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4507998 prefixEnd_4507998 := by exact prefixLift 4507998
  have htrace : WordTrace (prefixWord ++ tailWord_4507998) baseStart_4507998 baseEnd_4507998 := by
    simpa [prefixWord, tailWord_4507998, baseEnd_4507998] using wordTrace_append hprefix tailTrace_4507998
  have hstable : (prefixWord ++ tailWord_4507998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4507998).length < 2 ^ (prefixWord ++ tailWord_4507998).sum := by decide
  have hdescent : baseEnd_4507998 < baseStart_4507998 := by decide
  rcases family_descends (prefixWord ++ tailWord_4507998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4508007 : List Nat := [1, 1, 5, 1, 3, 1, 1, 2, 2, 6]
def baseStart_4508007 : Nat := 118140960795 + 4508007 * 2 ^ 59
def prefixEnd_4508007 : Nat := 4983230072969 + 3 ^ 40 * 4508007 * 2
def baseEnd_4508007 : Nat := 771591461611016378526853

theorem tailTrace_4508007 : CollatzResearch.WordTrace tailWord_4508007 prefixEnd_4508007 771591461611016378526853 := by
  unfold tailWord_4508007
  simp only [CollatzResearch.WordTrace]
  refine ⟨164420522979268020145338275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109613681986178680096892183 164420522979268020145338275)
  ·
    refine ⟨246630784468902030218007413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164420522979268020145338275 246630784468902030218007413)
    ·
      refine ⟨23121636043959565332938195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 246630784468902030218007413 23121636043959565332938195)
      ·
        refine ⟨34682454065939347999407293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23121636043959565332938195 34682454065939347999407293)
        ·
          refine ⟨13005920274727255499777735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34682454065939347999407293 13005920274727255499777735)
          ·
            refine ⟨19508880412090883249666603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13005920274727255499777735 19508880412090883249666603)
            ·
              refine ⟨29263320618136324874499905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19508880412090883249666603 29263320618136324874499905)
              ·
                refine ⟨21947490463602243655874929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29263320618136324874499905 21947490463602243655874929)
                ·
                  refine ⟨16460617847701682741906197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21947490463602243655874929 16460617847701682741906197)
                  ·
                    refine ⟨771591461611016378526853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16460617847701682741906197 771591461611016378526853)
                    ·
                      rfl

theorem cell23_4508007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 2, 2, 6].length) (baseStart_4508007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4508007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4508007 prefixEnd_4508007 := by exact prefixLift 4508007
  have htrace : WordTrace (prefixWord ++ tailWord_4508007) baseStart_4508007 baseEnd_4508007 := by
    simpa [prefixWord, tailWord_4508007, baseEnd_4508007] using wordTrace_append hprefix tailTrace_4508007
  have hstable : (prefixWord ++ tailWord_4508007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4508007).length < 2 ^ (prefixWord ++ tailWord_4508007).sum := by decide
  have hdescent : baseEnd_4508007 < baseStart_4508007 := by decide
  rcases family_descends (prefixWord ++ tailWord_4508007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4508008 : List Nat := [2, 1, 4, 2, 2, 3, 1, 2, 2, 1, 3]
def baseStart_4508008 : Nat := 118140960795 + 4508008 * 2 ^ 59
def prefixEnd_4508008 : Nat := 4983230072969 + 3 ^ 40 * 4508008 * 2
def baseEnd_4508008 : Nat := 2314774898313703631668055

theorem tailTrace_4508008 : CollatzResearch.WordTrace tailWord_4508008 prefixEnd_4508008 2314774898313703631668055 := by
  unfold tailWord_4508008
  simp only [CollatzResearch.WordTrace]
  refine ⟨82210279726132198658062339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109613706301509598210749785 82210279726132198658062339)
  ·
    refine ⟨123315419589198297987093509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82210279726132198658062339 123315419589198297987093509)
    ·
      refine ⟨23121641172974680872580033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 123315419589198297987093509 23121641172974680872580033)
      ·
        refine ⟨17341230879731010654435025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23121641172974680872580033 17341230879731010654435025)
        ·
          refine ⟨13005923159798257990826269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17341230879731010654435025 13005923159798257990826269)
          ·
            refine ⟨4877221184924346746559851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13005923159798257990826269 4877221184924346746559851)
            ·
              refine ⟨7315831777386520119839777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4877221184924346746559851 7315831777386520119839777)
              ·
                refine ⟨5486873833039890089879833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7315831777386520119839777 5486873833039890089879833)
                ·
                  refine ⟨4115155374779917567409875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5486873833039890089879833 4115155374779917567409875)
                  ·
                    refine ⟨6172733062169876351114813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4115155374779917567409875 6172733062169876351114813)
                    ·
                      refine ⟨2314774898313703631668055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6172733062169876351114813 2314774898313703631668055)
                      ·
                        rfl

theorem cell23_4508008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 1, 2, 2, 1, 3].length) (baseStart_4508008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4508008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4508008 prefixEnd_4508008 := by exact prefixLift 4508008
  have htrace : WordTrace (prefixWord ++ tailWord_4508008) baseStart_4508008 baseEnd_4508008 := by
    simpa [prefixWord, tailWord_4508008, baseEnd_4508008] using wordTrace_append hprefix tailTrace_4508008
  have hstable : (prefixWord ++ tailWord_4508008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4508008).length < 2 ^ (prefixWord ++ tailWord_4508008).sum := by decide
  have hdescent : baseEnd_4508008 < baseStart_4508008 := by decide
  rcases family_descends (prefixWord ++ tailWord_4508008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4508027 : List Nat := [1, 1, 1, 1, 1, 7, 2, 1, 2, 2, 4]
def baseStart_4508027 : Nat := 118140960795 + 4508027 * 2 ^ 59
def prefixEnd_4508027 : Nat := 4983230072969 + 3 ^ 40 * 4508027 * 2
def baseEnd_4508027 : Nat := 2314784654446139057330467

theorem tailTrace_4508027 : CollatzResearch.WordTrace tailWord_4508027 prefixEnd_4508027 2314784654446139057330467 := by
  unfold tailWord_4508027
  simp only [CollatzResearch.WordTrace]
  refine ⟨164421252439195563561066335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109614168292797042374044223 164421252439195563561066335)
  ·
    refine ⟨246631878658793345341599503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164421252439195563561066335 246631878658793345341599503)
    ·
      refine ⟨369947817988190018012399255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 246631878658793345341599503 369947817988190018012399255)
      ·
        refine ⟨554921726982285027018598883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 369947817988190018012399255 554921726982285027018598883)
        ·
          refine ⟨832382590473427540527898325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 554921726982285027018598883 832382590473427540527898325)
          ·
            refine ⟨19508966964220957981122617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 832382590473427540527898325 19508966964220957981122617)
            ·
              refine ⟨14631725223165718485841963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19508966964220957981122617 14631725223165718485841963)
              ·
                refine ⟨21947587834748577728762945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14631725223165718485841963 21947587834748577728762945)
                ·
                  refine ⟨16460690876061433296572209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21947587834748577728762945 16460690876061433296572209)
                  ·
                    refine ⟨12345518157046074972429157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16460690876061433296572209 12345518157046074972429157)
                    ·
                      refine ⟨2314784654446139057330467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12345518157046074972429157 2314784654446139057330467)
                      ·
                        rfl

theorem cell23_4508027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 1, 2, 2, 4].length) (baseStart_4508027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4508027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4508027 prefixEnd_4508027 := by exact prefixLift 4508027
  have htrace : WordTrace (prefixWord ++ tailWord_4508027) baseStart_4508027 baseEnd_4508027 := by
    simpa [prefixWord, tailWord_4508027, baseEnd_4508027] using wordTrace_append hprefix tailTrace_4508027
  have hstable : (prefixWord ++ tailWord_4508027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4508027).length < 2 ^ (prefixWord ++ tailWord_4508027).sum := by decide
  have hdescent : baseEnd_4508027 < baseStart_4508027 := by decide
  rcases family_descends (prefixWord ++ tailWord_4508027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4508067 : List Nat := [1, 1, 1, 4, 1, 4, 1, 1, 4, 5]
def baseStart_4508067 : Nat := 118140960795 + 4508067 * 2 ^ 59
def prefixEnd_4508067 : Nat := 4983230072969 + 3 ^ 40 * 4508067 * 2
def baseEnd_4508067 : Nat := 771601731224106300276761

theorem tailTrace_4508067 : CollatzResearch.WordTrace tailWord_4508067 prefixEnd_4508067 771601731224106300276761 := by
  unfold tailWord_4508067
  simp only [CollatzResearch.WordTrace]
  refine ⟨164422711359050650392522455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109615140906033766928348303 164422711359050650392522455)
  ·
    refine ⟨246634067038575975588783683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164422711359050650392522455 246634067038575975588783683)
    ·
      refine ⟨369951100557863963383175525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 246634067038575975588783683 369951100557863963383175525)
      ·
        refine ⟨69365831354599493134345411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 369951100557863963383175525 69365831354599493134345411)
        ·
          refine ⟨104048747031899239701518117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69365831354599493134345411 104048747031899239701518117)
          ·
            refine ⟨19509140068481107444034647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 104048747031899239701518117 19509140068481107444034647)
            ·
              refine ⟨29263710102721661166051971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19509140068481107444034647 29263710102721661166051971)
              ·
                refine ⟨43895565154082491749077957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29263710102721661166051971 43895565154082491749077957)
                ·
                  refine ⟨8230418466390467202952117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43895565154082491749077957 8230418466390467202952117)
                  ·
                    refine ⟨771601731224106300276761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8230418466390467202952117 771601731224106300276761)
                    ·
                      rfl

theorem cell23_4508067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 1, 4, 5].length) (baseStart_4508067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4508067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4508067 prefixEnd_4508067 := by exact prefixLift 4508067
  have htrace : WordTrace (prefixWord ++ tailWord_4508067) baseStart_4508067 baseEnd_4508067 := by
    simpa [prefixWord, tailWord_4508067, baseEnd_4508067] using wordTrace_append hprefix tailTrace_4508067
  have hstable : (prefixWord ++ tailWord_4508067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4508067).length < 2 ^ (prefixWord ++ tailWord_4508067).sum := by decide
  have hdescent : baseEnd_4508067 < baseStart_4508067 := by decide
  rcases family_descends (prefixWord ++ tailWord_4508067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4508104 : List Nat := [2, 1, 3, 1, 3, 2, 1, 3, 2, 1, 4]
def baseStart_4508104 : Nat := 118140960795 + 4508104 * 2 ^ 59
def prefixEnd_4508104 : Nat := 4983230072969 + 3 ^ 40 * 4508104 * 2
def baseEnd_4508104 : Nat := 2314824192456535256067613

theorem tailTrace_4508104 : CollatzResearch.WordTrace tailWord_4508104 prefixEnd_4508104 2314824192456535256067613 := by
  unfold tailWord_4508104
  simp only [CollatzResearch.WordTrace]
  refine ⟨82212030429958302855809683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109616040573277737141079577 82212030429958302855809683)
  ·
    refine ⟨123318045644937454283714525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82212030429958302855809683 123318045644937454283714525)
    ·
      refine ⟨46244267116851545356392947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123318045644937454283714525 46244267116851545356392947)
      ·
        refine ⟨69366400675277318034589421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46244267116851545356392947 69366400675277318034589421)
        ·
          refine ⟨26012400253228994262971033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69366400675277318034589421 26012400253228994262971033)
          ·
            refine ⟨19509300189921745697228275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26012400253228994262971033 19509300189921745697228275)
            ·
              refine ⟨29263950284882618545842413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19509300189921745697228275 29263950284882618545842413)
              ·
                refine ⟨10973981356830981954690905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29263950284882618545842413 10973981356830981954690905)
                ·
                  refine ⟨8230486017623236466018179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10973981356830981954690905 8230486017623236466018179)
                  ·
                    refine ⟨12345729026434854699027269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8230486017623236466018179 12345729026434854699027269)
                    ·
                      refine ⟨2314824192456535256067613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12345729026434854699027269 2314824192456535256067613)
                      ·
                        rfl

theorem cell23_4508104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 3, 2, 1, 4].length) (baseStart_4508104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4508104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4508104 prefixEnd_4508104 := by exact prefixLift 4508104
  have htrace : WordTrace (prefixWord ++ tailWord_4508104) baseStart_4508104 baseEnd_4508104 := by
    simpa [prefixWord, tailWord_4508104, baseEnd_4508104] using wordTrace_append hprefix tailTrace_4508104
  have hstable : (prefixWord ++ tailWord_4508104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4508104).length < 2 ^ (prefixWord ++ tailWord_4508104).sum := by decide
  have hdescent : baseEnd_4508104 < baseStart_4508104 := by decide
  rcases family_descends (prefixWord ++ tailWord_4508104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4508181 : List Nat := [1, 3, 2, 1, 3, 1, 2, 1, 4, 3, 2]
def baseStart_4508181 : Nat := 118140960795 + 4508181 * 2 ^ 59
def prefixEnd_4508181 : Nat := 4983230072969 + 3 ^ 40 * 4508181 * 2
def baseEnd_4508181 : Nat := 2314863730466931454804759

theorem tailTrace_4508181 : CollatzResearch.WordTrace tailWord_4508181 prefixEnd_4508181 2314863730466931454804759 := by
  unfold tailWord_4508181
  simp only [CollatzResearch.WordTrace]
  refine ⟨164426869280637647862172397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109617912853758431908114931 164426869280637647862172397)
  ·
    refine ⟨61660075980239117948314649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 164426869280637647862172397 61660075980239117948314649)
    ·
      refine ⟨46245056985179338461235987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61660075980239117948314649 46245056985179338461235987)
      ·
        refine ⟨69367585477769007691853981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46245056985179338461235987 69367585477769007691853981)
        ·
          refine ⟨26012844554163377884445243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69367585477769007691853981 26012844554163377884445243)
          ·
            refine ⟨39019266831245066826667865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26012844554163377884445243 39019266831245066826667865)
            ·
              refine ⟨29264450123433800120000899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39019266831245066826667865 29264450123433800120000899)
              ·
                refine ⟨43896675185150700180001349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29264450123433800120000899 43896675185150700180001349)
                ·
                  refine ⟨8230626597215756283750253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43896675185150700180001349 8230626597215756283750253)
                  ·
                    refine ⟨3086484973955908606406345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8230626597215756283750253 3086484973955908606406345)
                    ·
                      refine ⟨2314863730466931454804759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3086484973955908606406345 2314863730466931454804759)
                      ·
                        rfl

theorem cell23_4508181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 1, 4, 3, 2].length) (baseStart_4508181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4508181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4508181 prefixEnd_4508181 := by exact prefixLift 4508181
  have htrace : WordTrace (prefixWord ++ tailWord_4508181) baseStart_4508181 baseEnd_4508181 := by
    simpa [prefixWord, tailWord_4508181, baseEnd_4508181] using wordTrace_append hprefix tailTrace_4508181
  have hstable : (prefixWord ++ tailWord_4508181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4508181).length < 2 ^ (prefixWord ++ tailWord_4508181).sum := by decide
  have hdescent : baseEnd_4508181 < baseStart_4508181 := by decide
  rcases family_descends (prefixWord ++ tailWord_4508181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4508188 : List Nat := [2, 2, 3, 1, 2, 3, 2, 1, 3, 1, 3]
def baseStart_4508188 : Nat := 118140960795 + 4508188 * 2 ^ 59
def prefixEnd_4508188 : Nat := 4983230072969 + 3 ^ 40 * 4508188 * 2
def baseEnd_4508188 : Nat := 2314867324831512927417227

theorem tailTrace_4508188 : CollatzResearch.WordTrace tailWord_4508188 prefixEnd_4508188 2314867324831512927417227 := by
  unfold tailWord_4508188
  simp only [CollatzResearch.WordTrace]
  refine ⟨82213562295806144028838609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109618083061074858705118145 82213562295806144028838609)
  ·
    refine ⟨61660171721854608021628957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82213562295806144028838609 61660171721854608021628957)
    ·
      refine ⟨23122564395695478008110859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61660171721854608021628957 23122564395695478008110859)
      ·
        refine ⟨34683846593543217012166289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23122564395695478008110859 34683846593543217012166289)
        ·
          refine ⟨26012884945157412759124717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34683846593543217012166289 26012884945157412759124717)
          ·
            refine ⟨9754831854434029784671769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26012884945157412759124717 9754831854434029784671769)
            ·
              refine ⟨7316123890825522338503827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9754831854434029784671769 7316123890825522338503827)
              ·
                refine ⟨10974185836238283507755741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7316123890825522338503827 10974185836238283507755741)
                ·
                  refine ⟨4115319688589356315408403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10974185836238283507755741 4115319688589356315408403)
                  ·
                    refine ⟨6172979532884034473112605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4115319688589356315408403 6172979532884034473112605)
                    ·
                      refine ⟨2314867324831512927417227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6172979532884034473112605 2314867324831512927417227)
                      ·
                        rfl

theorem cell23_4508188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 2, 1, 3, 1, 3].length) (baseStart_4508188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4508188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4508188 prefixEnd_4508188 := by exact prefixLift 4508188
  have htrace : WordTrace (prefixWord ++ tailWord_4508188) baseStart_4508188 baseEnd_4508188 := by
    simpa [prefixWord, tailWord_4508188, baseEnd_4508188] using wordTrace_append hprefix tailTrace_4508188
  have hstable : (prefixWord ++ tailWord_4508188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4508188).length < 2 ^ (prefixWord ++ tailWord_4508188).sum := by decide
  have hdescent : baseEnd_4508188 < baseStart_4508188 := by decide
  rcases family_descends (prefixWord ++ tailWord_4508188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4508211 : List Nat := [1, 1, 1, 2, 4, 2, 4, 2, 1, 1, 4]
def baseStart_4508211 : Nat := 118140960795 + 4508211 * 2 ^ 59
def prefixEnd_4508211 : Nat := 4983230072969 + 3 ^ 40 * 4508211 * 2
def baseEnd_4508211 : Nat := 2314879134886566337429621

theorem tailTrace_4508211 : CollatzResearch.WordTrace tailWord_4508211 prefixEnd_4508211 2314879134886566337429621 := by
  unfold tailWord_4508211
  simp only [CollatzResearch.WordTrace]
  refine ⟨164427963470528962985764487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109618642313685975323842991 164427963470528962985764487)
  ·
    refine ⟨246641945205793444478646731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164427963470528962985764487 246641945205793444478646731)
    ·
      refine ⟨369962917808690166717970097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 246641945205793444478646731 369962917808690166717970097)
      ·
        refine ⟨277472188356517625038477573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 369962917808690166717970097 277472188356517625038477573)
        ·
          refine ⟨52026035316847054694714545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 277472188356517625038477573 52026035316847054694714545)
          ·
            refine ⟨39019526487635291021035909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52026035316847054694714545 39019526487635291021035909)
            ·
              refine ⟨7316161216431617066444233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39019526487635291021035909 7316161216431617066444233)
              ·
                refine ⟨5487120912323712799833175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7316161216431617066444233 5487120912323712799833175)
                ·
                  refine ⟨8230681368485569199749763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5487120912323712799833175 8230681368485569199749763)
                  ·
                    refine ⟨12346022052728353799624645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8230681368485569199749763 12346022052728353799624645)
                    ·
                      refine ⟨2314879134886566337429621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12346022052728353799624645 2314879134886566337429621)
                      ·
                        rfl

theorem cell23_4508211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 4, 2, 1, 1, 4].length) (baseStart_4508211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4508211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4508211 prefixEnd_4508211 := by exact prefixLift 4508211
  have htrace : WordTrace (prefixWord ++ tailWord_4508211) baseStart_4508211 baseEnd_4508211 := by
    simpa [prefixWord, tailWord_4508211, baseEnd_4508211] using wordTrace_append hprefix tailTrace_4508211
  have hstable : (prefixWord ++ tailWord_4508211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4508211).length < 2 ^ (prefixWord ++ tailWord_4508211).sum := by decide
  have hdescent : baseEnd_4508211 < baseStart_4508211 := by decide
  rcases family_descends (prefixWord ++ tailWord_4508211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4508221 : List Nat := [1, 4, 1, 3, 2, 1, 1, 2, 4, 4]
def baseStart_4508221 : Nat := 118140960795 + 4508221 * 2 ^ 59
def prefixEnd_4508221 : Nat := 4983230072969 + 3 ^ 40 * 4508221 * 2
def baseEnd_4508221 : Nat := 771628089897703766101525

theorem tailTrace_4508221 : CollatzResearch.WordTrace tailWord_4508221 prefixEnd_4508221 771628089897703766101525 := by
  unfold tailWord_4508221
  simp only [CollatzResearch.WordTrace]
  refine ⟨164428328200492734693628517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109618885466995156462419011 164428328200492734693628517)
  ·
    refine ⟨30830311537592387755055347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 164428328200492734693628517 30830311537592387755055347)
    ·
      refine ⟨46245467306388581632583021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30830311537592387755055347 46245467306388581632583021)
      ·
        refine ⟨17342050239895718112218633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46245467306388581632583021 17342050239895718112218633)
        ·
          refine ⟨13006537679921788584163975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17342050239895718112218633 13006537679921788584163975)
          ·
            refine ⟨19509806519882682876245963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13006537679921788584163975 19509806519882682876245963)
            ·
              refine ⟨29264709779824024314368945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19509806519882682876245963 29264709779824024314368945)
              ·
                refine ⟨21948532334868018235776709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29264709779824024314368945 21948532334868018235776709)
                ·
                  refine ⟨4115349812787753419208133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21948532334868018235776709 4115349812787753419208133)
                  ·
                    refine ⟨771628089897703766101525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4115349812787753419208133 771628089897703766101525)
                    ·
                      rfl

theorem cell23_4508221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 2, 4, 4].length) (baseStart_4508221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4508221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4508221 prefixEnd_4508221 := by exact prefixLift 4508221
  have htrace : WordTrace (prefixWord ++ tailWord_4508221) baseStart_4508221 baseEnd_4508221 := by
    simpa [prefixWord, tailWord_4508221, baseEnd_4508221] using wordTrace_append hprefix tailTrace_4508221
  have hstable : (prefixWord ++ tailWord_4508221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4508221).length < 2 ^ (prefixWord ++ tailWord_4508221).sum := by decide
  have hdescent : baseEnd_4508221 < baseStart_4508221 := by decide
  rcases family_descends (prefixWord ++ tailWord_4508221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4508224 : List Nat := [2, 1, 1, 2, 2, 2, 2, 4, 1, 2, 4]
def baseStart_4508224 : Nat := 118140960795 + 4508224 * 2 ^ 59
def prefixEnd_4508224 : Nat := 4983230072969 + 3 ^ 40 * 4508224 * 2
def baseEnd_4508224 : Nat := 2314885810135074786567061

theorem tailTrace_4508224 : CollatzResearch.WordTrace tailWord_4508224 prefixEnd_4508224 2314885810135074786567061 := by
  unfold tailWord_4508224
  simp only [CollatzResearch.WordTrace]
  refine ⟨82214218809740933102993863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109618958412987910803991817 82214218809740933102993863)
  ·
    refine ⟨123321328214611399654490795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82214218809740933102993863 123321328214611399654490795)
    ·
      refine ⟨184981992321917099481736193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123321328214611399654490795 184981992321917099481736193)
      ·
        refine ⟨138736494241437824611302145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 184981992321917099481736193 138736494241437824611302145)
        ·
          refine ⟨104052370681078368458476609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 138736494241437824611302145 104052370681078368458476609)
          ·
            refine ⟨78039278010808776343857457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104052370681078368458476609 78039278010808776343857457)
            ·
              refine ⟨58529458508106582257893093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78039278010808776343857457 58529458508106582257893093)
              ·
                refine ⟨10974273470269984173354955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58529458508106582257893093 10974273470269984173354955)
                ·
                  refine ⟨16461410205404976260032433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10974273470269984173354955 16461410205404976260032433)
                  ·
                    refine ⟨12346057654053732195024325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16461410205404976260032433 12346057654053732195024325)
                    ·
                      refine ⟨2314885810135074786567061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12346057654053732195024325 2314885810135074786567061)
                      ·
                        rfl

theorem cell23_4508224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 4, 1, 2, 4].length) (baseStart_4508224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4508224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4508224 prefixEnd_4508224 := by exact prefixLift 4508224
  have htrace : WordTrace (prefixWord ++ tailWord_4508224) baseStart_4508224 baseEnd_4508224 := by
    simpa [prefixWord, tailWord_4508224, baseEnd_4508224] using wordTrace_append hprefix tailTrace_4508224
  have hstable : (prefixWord ++ tailWord_4508224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4508224).length < 2 ^ (prefixWord ++ tailWord_4508224).sum := by decide
  have hdescent : baseEnd_4508224 < baseStart_4508224 := by decide
  rcases family_descends (prefixWord ++ tailWord_4508224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4508231 : List Nat := [1, 1, 4, 1, 4, 2, 2, 1, 1, 1, 5]
def baseStart_4508231 : Nat := 118140960795 + 4508231 * 2 ^ 59
def prefixEnd_4508231 : Nat := 4983230072969 + 3 ^ 40 * 4508231 * 2
def baseEnd_4508231 : Nat := 2314889404499656259179529

theorem tailTrace_4508231 : CollatzResearch.WordTrace tailWord_4508231 prefixEnd_4508231 2314889404499656259179529 := by
  unfold tailWord_4508231
  simp only [CollatzResearch.WordTrace]
  refine ⟨164428692930456506401492547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109619128620304337600995031 164428692930456506401492547)
  ·
    refine ⟨246643039395684759602238821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164428692930456506401492547 246643039395684759602238821)
    ·
      refine ⟨46245569886690892425419779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 246643039395684759602238821 46245569886690892425419779)
      ·
        refine ⟨69368354830036338638129669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46245569886690892425419779 69368354830036338638129669)
        ·
          refine ⟨13006566530631813494649313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69368354830036338638129669 13006566530631813494649313)
          ·
            refine ⟨9754924897973860120986985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13006566530631813494649313 9754924897973860120986985)
            ·
              refine ⟨7316193673480395090740239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9754924897973860120986985 7316193673480395090740239)
              ·
                refine ⟨10974290510220592636110359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7316193673480395090740239 10974290510220592636110359)
                ·
                  refine ⟨16461435765330888954165539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10974290510220592636110359 16461435765330888954165539)
                  ·
                    refine ⟨24692153647996333431248309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16461435765330888954165539 24692153647996333431248309)
                    ·
                      refine ⟨2314889404499656259179529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24692153647996333431248309 2314889404499656259179529)
                      ·
                        rfl

theorem cell23_4508231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 2, 1, 1, 1, 5].length) (baseStart_4508231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4508231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4508231 prefixEnd_4508231 := by exact prefixLift 4508231
  have htrace : WordTrace (prefixWord ++ tailWord_4508231) baseStart_4508231 baseEnd_4508231 := by
    simpa [prefixWord, tailWord_4508231, baseEnd_4508231] using wordTrace_append hprefix tailTrace_4508231
  have hstable : (prefixWord ++ tailWord_4508231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4508231).length < 2 ^ (prefixWord ++ tailWord_4508231).sum := by decide
  have hdescent : baseEnd_4508231 < baseStart_4508231 := by decide
  rcases family_descends (prefixWord ++ tailWord_4508231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4508234 : List Nat := [3, 1, 2, 1, 1, 6, 9]
def baseStart_4508234 : Nat := 118140960795 + 4508234 * 2 ^ 59
def prefixEnd_4508234 : Nat := 4983230072969 + 3 ^ 40 * 4508234 * 2
def baseEnd_4508234 : Nat := 28578900554834811696815

theorem tailTrace_4508234 : CollatzResearch.WordTrace tailWord_4508234 prefixEnd_4508234 28578900554834811696815 := by
  unfold tailWord_4508234
  simp only [CollatzResearch.WordTrace]
  refine ⟨41107200587361409478462939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109619201566297091942567837 41107200587361409478462939)
  ·
    refine ⟨61660800881042114217694409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41107200587361409478462939 61660800881042114217694409)
    ·
      refine ⟨46245600660781585663270807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61660800881042114217694409 46245600660781585663270807)
      ·
        refine ⟨69368400991172378494906211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46245600660781585663270807 69368400991172378494906211)
        ·
          refine ⟨104052601486758567742359317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69368400991172378494906211 104052601486758567742359317)
          ·
            refine ⟨4877465694691807862923093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 104052601486758567742359317 4877465694691807862923093)
            ·
              refine ⟨28578900554834811696815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4877465694691807862923093 28578900554834811696815)
              ·
                rfl

theorem cell23_4508234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 9].length) (baseStart_4508234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4508234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4508234 prefixEnd_4508234 := by exact prefixLift 4508234
  have htrace : WordTrace (prefixWord ++ tailWord_4508234) baseStart_4508234 baseEnd_4508234 := by
    simpa [prefixWord, tailWord_4508234, baseEnd_4508234] using wordTrace_append hprefix tailTrace_4508234
  have hstable : (prefixWord ++ tailWord_4508234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4508234).length < 2 ^ (prefixWord ++ tailWord_4508234).sum := by decide
  have hdescent : baseEnd_4508234 < baseStart_4508234 := by decide
  rcases family_descends (prefixWord ++ tailWord_4508234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4508245 : List Nat := [1, 3, 2, 2, 1, 1, 2, 6, 1, 2, 2]
def baseStart_4508245 : Nat := 118140960795 + 4508245 * 2 ^ 59
def prefixEnd_4508245 : Nat := 4983230072969 + 3 ^ 40 * 4508245 * 2
def baseEnd_4508245 : Nat := 2314896593228819204404465

theorem tailTrace_4508245 : CollatzResearch.WordTrace tailWord_4508245 prefixEnd_4508245 2314896593228819204404465 := by
  unfold tailWord_4508245
  simp only [CollatzResearch.WordTrace]
  refine ⟨164429203552405786792502189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109619469034937191195001459 164429203552405786792502189)
  ·
    refine ⟨61660951332152170047188321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 164429203552405786792502189 61660951332152170047188321)
    ·
      refine ⟨46245713499114127535391241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61660951332152170047188321 46245713499114127535391241)
      ·
        refine ⟨34684285124335595651543431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46245713499114127535391241 34684285124335595651543431)
        ·
          refine ⟨52026427686503393477315147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34684285124335595651543431 52026427686503393477315147)
          ·
            refine ⟨78039641529755090215972721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52026427686503393477315147 78039641529755090215972721)
            ·
              refine ⟨58529731147316317661979541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78039641529755090215972721 58529731147316317661979541)
              ·
                refine ⟨2743581147530452390405291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 58529731147316317661979541 2743581147530452390405291)
                ·
                  refine ⟨4115371721295678585607937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2743581147530452390405291 4115371721295678585607937)
                  ·
                    refine ⟨3086528790971758939205953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4115371721295678585607937 3086528790971758939205953)
                    ·
                      refine ⟨2314896593228819204404465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3086528790971758939205953 2314896593228819204404465)
                      ·
                        rfl

theorem cell23_4508245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 6, 1, 2, 2].length) (baseStart_4508245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4508245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4508245 prefixEnd_4508245 := by exact prefixLift 4508245
  have htrace : WordTrace (prefixWord ++ tailWord_4508245) baseStart_4508245 baseEnd_4508245 := by
    simpa [prefixWord, tailWord_4508245, baseEnd_4508245] using wordTrace_append hprefix tailTrace_4508245
  have hstable : (prefixWord ++ tailWord_4508245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4508245).length < 2 ^ (prefixWord ++ tailWord_4508245).sum := by decide
  have hdescent : baseEnd_4508245 < baseStart_4508245 := by decide
  rcases family_descends (prefixWord ++ tailWord_4508245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4508290 : List Nat := [3, 4, 3, 1, 2, 1, 2, 2, 1, 1, 3]
def baseStart_4508290 : Nat := 118140960795 + 4508290 * 2 ^ 59
def prefixEnd_4508290 : Nat := 4983230072969 + 3 ^ 40 * 4508290 * 2
def baseEnd_4508290 : Nat := 2314919699858271528341759

theorem tailTrace_4508290 : CollatzResearch.WordTrace tailWord_4508290 prefixEnd_4508290 2314919699858271528341759 := by
  unfold tailWord_4508290
  simp only [CollatzResearch.WordTrace]
  refine ⟨41107711209310689869472581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109620563224828506318593549 41107711209310689869472581)
  ·
    refine ⟨7707695851745754350526109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41107711209310689869472581 7707695851745754350526109)
    ·
      refine ⟨2890385944404657881447291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7707695851745754350526109 2890385944404657881447291)
      ·
        refine ⟨4335578916606986822170937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2890385944404657881447291 4335578916606986822170937)
        ·
          refine ⟨3251684187455240116628203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4335578916606986822170937 3251684187455240116628203)
          ·
            refine ⟨4877526281182860174942305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3251684187455240116628203 4877526281182860174942305)
            ·
              refine ⟨3658144710887145131206729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4877526281182860174942305 3658144710887145131206729)
              ·
                refine ⟨2743608533165358848405047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3658144710887145131206729 2743608533165358848405047)
                ·
                  refine ⟨4115412799748038272607571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2743608533165358848405047 4115412799748038272607571)
                  ·
                    refine ⟨6173119199622057408911357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4115412799748038272607571 6173119199622057408911357)
                    ·
                      refine ⟨2314919699858271528341759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6173119199622057408911357 2314919699858271528341759)
                      ·
                        rfl

theorem cell23_4508290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_4508290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4508290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4508290 prefixEnd_4508290 := by exact prefixLift 4508290
  have htrace : WordTrace (prefixWord ++ tailWord_4508290) baseStart_4508290 baseEnd_4508290 := by
    simpa [prefixWord, tailWord_4508290, baseEnd_4508290] using wordTrace_append hprefix tailTrace_4508290
  have hstable : (prefixWord ++ tailWord_4508290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4508290).length < 2 ^ (prefixWord ++ tailWord_4508290).sum := by decide
  have hdescent : baseEnd_4508290 < baseStart_4508290 := by decide
  rcases family_descends (prefixWord ++ tailWord_4508290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4508351 : List Nat := [1, 1, 2, 2, 2, 4, 1, 2, 2, 3, 3]
def baseStart_4508351 : Nat := 118140960795 + 4508351 * 2 ^ 59
def prefixEnd_4508351 : Nat := 4983230072969 + 3 ^ 40 * 4508351 * 2
def baseEnd_4508351 : Nat := 2314951022178195789678977

theorem tailTrace_4508351 : CollatzResearch.WordTrace tailWord_4508351 prefixEnd_4508351 2314951022178195789678977 := by
  unfold tailWord_4508351
  simp only [CollatzResearch.WordTrace]
  refine ⟨164433069690021766895860907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109622046460014511263907271 164433069690021766895860907)
  ·
    refine ⟨246649604535032650343791361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164433069690021766895860907 246649604535032650343791361)
    ·
      refine ⟨184987203401274487757843521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 246649604535032650343791361 184987203401274487757843521)
      ·
        refine ⟨138740402550955865818382641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 184987203401274487757843521 138740402550955865818382641)
        ·
          refine ⟨104055301913216899363786981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 138740402550955865818382641 104055301913216899363786981)
          ·
            refine ⟨19510369108728168630710059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 104055301913216899363786981 19510369108728168630710059)
            ·
              refine ⟨29265553663092252946065089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19510369108728168630710059 29265553663092252946065089)
              ·
                refine ⟨21949165247319189709548817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29265553663092252946065089 21949165247319189709548817)
                ·
                  refine ⟨16461873935489392282161613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21949165247319189709548817 16461873935489392282161613)
                  ·
                    refine ⟨6173202725808522105810605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16461873935489392282161613 6173202725808522105810605)
                    ·
                      refine ⟨2314951022178195789678977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6173202725808522105810605 2314951022178195789678977)
                      ·
                        rfl

theorem cell23_4508351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 2, 2, 3, 3].length) (baseStart_4508351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4508351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4508351 prefixEnd_4508351 := by exact prefixLift 4508351
  have htrace : WordTrace (prefixWord ++ tailWord_4508351) baseStart_4508351 baseEnd_4508351 := by
    simpa [prefixWord, tailWord_4508351, baseEnd_4508351] using wordTrace_append hprefix tailTrace_4508351
  have hstable : (prefixWord ++ tailWord_4508351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4508351).length < 2 ^ (prefixWord ++ tailWord_4508351).sum := by decide
  have hdescent : baseEnd_4508351 < baseStart_4508351 := by decide
  rcases family_descends (prefixWord ++ tailWord_4508351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4508352 : List Nat := [2, 1, 1, 2, 4, 4, 1, 2, 2, 2, 2]
def baseStart_4508352 : Nat := 118140960795 + 4508352 * 2 ^ 59
def prefixEnd_4508352 : Nat := 4983230072969 + 3 ^ 40 * 4508352 * 2
def baseEnd_4508352 : Nat := 2314951535658850285766473

theorem tailTrace_4508352 : CollatzResearch.WordTrace tailWord_4508352 prefixEnd_4508352 2314951535658850285766473 := by
  unfold tailWord_4508352
  simp only [CollatzResearch.WordTrace]
  refine ⟨82216553081509072033323655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109622070775345429377764873 82216553081509072033323655)
  ·
    refine ⟨123324829622263608049985483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82216553081509072033323655 123324829622263608049985483)
    ·
      refine ⟨184987244433395412074978225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123324829622263608049985483 184987244433395412074978225)
      ·
        refine ⟨138740433325046559056233669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 184987244433395412074978225 138740433325046559056233669)
        ·
          refine ⟨26013831248446229823043813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 138740433325046559056233669 26013831248446229823043813)
          ·
            refine ⟨4877593359083668091820715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26013831248446229823043813 4877593359083668091820715)
            ·
              refine ⟨7316390038625502137731073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4877593359083668091820715 7316390038625502137731073)
              ·
                refine ⟨5487292528969126603298305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7316390038625502137731073 5487292528969126603298305)
                ·
                  refine ⟨4115469396726844952473729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5487292528969126603298305 4115469396726844952473729)
                  ·
                    refine ⟨3086602047545133714355297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4115469396726844952473729 3086602047545133714355297)
                    ·
                      refine ⟨2314951535658850285766473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3086602047545133714355297 2314951535658850285766473)
                      ·
                        rfl

theorem cell23_4508352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 1, 2, 2, 2, 2].length) (baseStart_4508352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4508352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4508352 prefixEnd_4508352 := by exact prefixLift 4508352
  have htrace : WordTrace (prefixWord ++ tailWord_4508352) baseStart_4508352 baseEnd_4508352 := by
    simpa [prefixWord, tailWord_4508352, baseEnd_4508352] using wordTrace_append hprefix tailTrace_4508352
  have hstable : (prefixWord ++ tailWord_4508352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4508352).length < 2 ^ (prefixWord ++ tailWord_4508352).sum := by decide
  have hdescent : baseEnd_4508352 < baseStart_4508352 := by decide
  rcases family_descends (prefixWord ++ tailWord_4508352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4508384 : List Nat := [2, 1, 1, 3, 1, 2, 1, 1, 1, 10]
def baseStart_4508384 : Nat := 118140960795 + 4508384 * 2 ^ 59
def prefixEnd_4508384 : Nat := 4983230072969 + 3 ^ 40 * 4508384 * 2
def baseEnd_4508384 : Nat := 771655989013264720188775

theorem tailTrace_4508384 : CollatzResearch.WordTrace tailWord_4508384 prefixEnd_4508384 771655989013264720188775 := by
  unfold tailWord_4508384
  simp only [CollatzResearch.WordTrace]
  refine ⟨82217136649451106765906103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109622848865934809021208137 82217136649451106765906103)
  ·
    refine ⟨123325704974176660148859155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82217136649451106765906103 123325704974176660148859155)
    ·
      refine ⟨184988557461264990223288733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123325704974176660148859155 184988557461264990223288733)
      ·
        refine ⟨69370709047974371333733275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 184988557461264990223288733 69370709047974371333733275)
        ·
          refine ⟨104056063571961557000599913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69370709047974371333733275 104056063571961557000599913)
          ·
            refine ⟨78042047678971167750449935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104056063571961557000599913 78042047678971167750449935)
            ·
              refine ⟨117063071518456751625674903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78042047678971167750449935 117063071518456751625674903)
              ·
                refine ⟨175594607277685127438512355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 117063071518456751625674903 175594607277685127438512355)
                ·
                  refine ⟨263391910916527691157768533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 175594607277685127438512355 263391910916527691157768533)
                  ·
                    refine ⟨771655989013264720188775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 263391910916527691157768533 771655989013264720188775)
                    ·
                      rfl

theorem cell23_4508384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 1, 10].length) (baseStart_4508384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4508384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4508384 prefixEnd_4508384 := by exact prefixLift 4508384
  have htrace : WordTrace (prefixWord ++ tailWord_4508384) baseStart_4508384 baseEnd_4508384 := by
    simpa [prefixWord, tailWord_4508384, baseEnd_4508384] using wordTrace_append hprefix tailTrace_4508384
  have hstable : (prefixWord ++ tailWord_4508384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4508384).length < 2 ^ (prefixWord ++ tailWord_4508384).sum := by decide
  have hdescent : baseEnd_4508384 < baseStart_4508384 := by decide
  rcases family_descends (prefixWord ++ tailWord_4508384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4508392 : List Nat := [2, 1, 4, 1, 5, 1, 1, 3, 5]
def baseStart_4508392 : Nat := 118140960795 + 4508392 * 2 ^ 59
def prefixEnd_4508392 : Nat := 4983230072969 + 3 ^ 40 * 4508392 * 2
def baseEnd_4508392 : Nat := 257219119431670014362921

theorem tailTrace_4508392 : CollatzResearch.WordTrace tailWord_4508392 prefixEnd_4508392 257219119431670014362921 := by
  unfold tailWord_4508392
  simp only [CollatzResearch.WordTrace]
  refine ⟨82217282541436615449051715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109623043388582153932068953 82217282541436615449051715)
  ·
    refine ⟨123325923812154923173577573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82217282541436615449051715 123325923812154923173577573)
    ·
      refine ⟨23123610714779048095045795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 123325923812154923173577573 23123610714779048095045795)
      ·
        refine ⟨34685416072168572142568693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23123610714779048095045795 34685416072168572142568693)
        ·
          refine ⟨3251757756765803638365815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 34685416072168572142568693 3251757756765803638365815)
          ·
            refine ⟨4877636635148705457548723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3251757756765803638365815 4877636635148705457548723)
            ·
              refine ⟨7316454952723058186323085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4877636635148705457548723 7316454952723058186323085)
              ·
                refine ⟨2743670607271146819871157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7316454952723058186323085 2743670607271146819871157)
                ·
                  refine ⟨257219119431670014362921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2743670607271146819871157 257219119431670014362921)
                  ·
                    rfl

theorem cell23_4508392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 1, 3, 5].length) (baseStart_4508392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4508392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4508392 prefixEnd_4508392 := by exact prefixLift 4508392
  have htrace : WordTrace (prefixWord ++ tailWord_4508392) baseStart_4508392 baseEnd_4508392 := by
    simpa [prefixWord, tailWord_4508392, baseEnd_4508392] using wordTrace_append hprefix tailTrace_4508392
  have hstable : (prefixWord ++ tailWord_4508392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4508392).length < 2 ^ (prefixWord ++ tailWord_4508392).sum := by decide
  have hdescent : baseEnd_4508392 < baseStart_4508392 := by decide
  rcases family_descends (prefixWord ++ tailWord_4508392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4508431 : List Nat := [1, 1, 2, 1, 1, 1, 7, 3, 6]
def baseStart_4508431 : Nat := 118140960795 + 4508431 * 2 ^ 59
def prefixEnd_4508431 : Nat := 4983230072969 + 3 ^ 40 * 4508431 * 2
def baseEnd_4508431 : Nat := 257221344514506164075401

theorem tailTrace_4508431 : CollatzResearch.WordTrace tailWord_4508431 prefixEnd_4508431 257221344514506164075401 := by
  unfold tailWord_4508431
  simp only [CollatzResearch.WordTrace]
  refine ⟨164435987529731940558773147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109623991686487960372515431 164435987529731940558773147)
  ·
    refine ⟨246653981294597910838159721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164435987529731940558773147 246653981294597910838159721)
    ·
      refine ⟨184990485970948433128619791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 246653981294597910838159721 184990485970948433128619791)
      ·
        refine ⟨277485728956422649692929687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184990485970948433128619791 277485728956422649692929687)
        ·
          refine ⟨416228593434633974539394531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 277485728956422649692929687 416228593434633974539394531)
          ·
            refine ⟨624342890151950961809091797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 416228593434633974539394531 624342890151950961809091797)
            ·
              refine ⟨14633036487936350667400589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 624342890151950961809091797 14633036487936350667400589)
              ·
                refine ⟨5487388682976131500275221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14633036487936350667400589 5487388682976131500275221)
                ·
                  refine ⟨257221344514506164075401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5487388682976131500275221 257221344514506164075401)
                  ·
                    rfl

theorem cell23_4508431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 3, 6].length) (baseStart_4508431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4508431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4508431 prefixEnd_4508431 := by exact prefixLift 4508431
  have htrace : WordTrace (prefixWord ++ tailWord_4508431) baseStart_4508431 baseEnd_4508431 := by
    simpa [prefixWord, tailWord_4508431, baseEnd_4508431] using wordTrace_append hprefix tailTrace_4508431
  have hstable : (prefixWord ++ tailWord_4508431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4508431).length < 2 ^ (prefixWord ++ tailWord_4508431).sum := by decide
  have hdescent : baseEnd_4508431 < baseStart_4508431 := by decide
  rcases family_descends (prefixWord ++ tailWord_4508431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4508469 : List Nat := [1, 3, 3, 1, 3, 3, 2, 2, 1, 4]
def baseStart_4508469 : Nat := 118140960795 + 4508469 * 2 ^ 59
def prefixEnd_4508469 : Nat := 4983230072969 + 3 ^ 40 * 4508469 * 2
def baseEnd_4508469 : Nat := 771670537631808776001145

theorem tailTrace_4508469 : CollatzResearch.WordTrace tailWord_4508469 prefixEnd_4508469 771670537631808776001145 := by
  unfold tailWord_4508469
  simp only [CollatzResearch.WordTrace]
  refine ⟨164437373503594273048656461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109624915669062848699104307 164437373503594273048656461)
  ·
    refine ⟨61664015063847852393246173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 164437373503594273048656461 61664015063847852393246173)
    ·
      refine ⟨23124005648942944647467315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61664015063847852393246173 23124005648942944647467315)
      ·
        refine ⟨34686008473414416971200973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23124005648942944647467315 34686008473414416971200973)
        ·
          refine ⟨13007253177530406364200365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34686008473414416971200973 13007253177530406364200365)
          ·
            refine ⟨4877719941573902386575137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13007253177530406364200365 4877719941573902386575137)
            ·
              refine ⟨3658289956180426789931353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4877719941573902386575137 3658289956180426789931353)
              ·
                refine ⟨2743717467135320092448515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3658289956180426789931353 2743717467135320092448515)
                ·
                  refine ⟨4115576200702980138672773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2743717467135320092448515 4115576200702980138672773)
                  ·
                    refine ⟨771670537631808776001145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4115576200702980138672773 771670537631808776001145)
                    ·
                      rfl

theorem cell23_4508469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 2, 2, 1, 4].length) (baseStart_4508469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4508469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4508469 prefixEnd_4508469 := by exact prefixLift 4508469
  have htrace : WordTrace (prefixWord ++ tailWord_4508469) baseStart_4508469 baseEnd_4508469 := by
    simpa [prefixWord, tailWord_4508469, baseEnd_4508469] using wordTrace_append hprefix tailTrace_4508469
  have hstable : (prefixWord ++ tailWord_4508469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4508469).length < 2 ^ (prefixWord ++ tailWord_4508469).sum := by decide
  have hdescent : baseEnd_4508469 < baseStart_4508469 := by decide
  rcases family_descends (prefixWord ++ tailWord_4508469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4508498 : List Nat := [3, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4]
def baseStart_4508498 : Nat := 118140960795 + 4508498 * 2 ^ 59
def prefixEnd_4508498 : Nat := 4983230072969 + 3 ^ 40 * 4508498 * 2
def baseEnd_4508498 : Nat := 2315026503834406714540801

theorem tailTrace_4508498 : CollatzResearch.WordTrace tailWord_4508498 prefixEnd_4508498 2315026503834406714540801 := by
  unfold tailWord_4508498
  simp only [CollatzResearch.WordTrace]
  refine ⟨41109607805122302750365537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109625620813659474000974765 41109607805122302750365537)
  ·
    refine ⟨30832205853841727062774153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41109607805122302750365537 30832205853841727062774153)
    ·
      refine ⟨23124154390381295297080615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30832205853841727062774153 23124154390381295297080615)
      ·
        refine ⟨34686231585571942945620923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23124154390381295297080615 34686231585571942945620923)
        ·
          refine ⟨52029347378357914418431385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34686231585571942945620923 52029347378357914418431385)
          ·
            refine ⟨39022010533768435813823539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52029347378357914418431385 39022010533768435813823539)
            ·
              refine ⟨58533015800652653720735309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39022010533768435813823539 58533015800652653720735309)
              ·
                refine ⟨21949880925244745145275741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58533015800652653720735309 21949880925244745145275741)
                ·
                  refine ⟨8231205346966779429478403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21949880925244745145275741 8231205346966779429478403)
                  ·
                    refine ⟨12346808020450169144217605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8231205346966779429478403 12346808020450169144217605)
                    ·
                      refine ⟨2315026503834406714540801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12346808020450169144217605 2315026503834406714540801)
                      ·
                        rfl

theorem cell23_4508498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4].length) (baseStart_4508498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4508498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4508498 prefixEnd_4508498 := by exact prefixLift 4508498
  have htrace : WordTrace (prefixWord ++ tailWord_4508498) baseStart_4508498 baseEnd_4508498 := by
    simpa [prefixWord, tailWord_4508498, baseEnd_4508498] using wordTrace_append hprefix tailTrace_4508498
  have hstable : (prefixWord ++ tailWord_4508498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4508498).length < 2 ^ (prefixWord ++ tailWord_4508498).sum := by decide
  have hdescent : baseEnd_4508498 < baseStart_4508498 := by decide
  rcases family_descends (prefixWord ++ tailWord_4508498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4508515 : List Nat := [1, 1, 1, 5, 3, 2, 1, 3, 1, 1, 4]
def baseStart_4508515 : Nat := 118140960795 + 4508515 * 2 ^ 59
def prefixEnd_4508515 : Nat := 4983230072969 + 3 ^ 40 * 4508515 * 2
def baseEnd_4508515 : Nat := 2315035233005533148028223

theorem tailTrace_4508515 : CollatzResearch.WordTrace tailWord_4508515 prefixEnd_4508515 2315035233005533148028223 := by
  unfold tailWord_4508515
  simp only [CollatzResearch.WordTrace]
  refine ⟨164439051261427622904830999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109626034174285081936553999 164439051261427622904830999)
  ·
    refine ⟨246658576892141434357246499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164439051261427622904830999 246658576892141434357246499)
    ·
      refine ⟨369987865338212151535869749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 246658576892141434357246499 369987865338212151535869749)
      ·
        refine ⟨34686362375457389206487789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 369987865338212151535869749 34686362375457389206487789)
        ·
          refine ⟨13007385890796520952432921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34686362375457389206487789 13007385890796520952432921)
          ·
            refine ⟨9755539418097390714324691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13007385890796520952432921 9755539418097390714324691)
            ·
              refine ⟨14633309127146086071487037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9755539418097390714324691 14633309127146086071487037)
              ·
                refine ⟨5487490922679782276807639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14633309127146086071487037 5487490922679782276807639)
                ·
                  refine ⟨8231236384019673415211459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5487490922679782276807639 8231236384019673415211459)
                  ·
                    refine ⟨12346854576029510122817189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8231236384019673415211459 12346854576029510122817189)
                    ·
                      refine ⟨2315035233005533148028223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12346854576029510122817189 2315035233005533148028223)
                      ·
                        rfl

theorem cell23_4508515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 3, 1, 1, 4].length) (baseStart_4508515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4508515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4508515 prefixEnd_4508515 := by exact prefixLift 4508515
  have htrace : WordTrace (prefixWord ++ tailWord_4508515) baseStart_4508515 baseEnd_4508515 := by
    simpa [prefixWord, tailWord_4508515, baseEnd_4508515] using wordTrace_append hprefix tailTrace_4508515
  have hstable : (prefixWord ++ tailWord_4508515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4508515).length < 2 ^ (prefixWord ++ tailWord_4508515).sum := by decide
  have hdescent : baseEnd_4508515 < baseStart_4508515 := by decide
  rcases family_descends (prefixWord ++ tailWord_4508515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4508552 : List Nat := [2, 1, 3, 3, 2, 2, 2, 2, 1, 2, 3]
def baseStart_4508552 : Nat := 118140960795 + 4508552 * 2 ^ 59
def prefixEnd_4508552 : Nat := 4983230072969 + 3 ^ 40 * 4508552 * 2
def baseEnd_4508552 : Nat := 2315054231789749503265553

theorem tailTrace_4508552 : CollatzResearch.WordTrace tailWord_4508552 prefixEnd_4508552 2315054231789749503265553 := by
  unfold tailWord_4508552
  simp only [CollatzResearch.WordTrace]
  refine ⟨82220200381146789111963955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109626933841529052149285273 82220200381146789111963955)
  ·
    refine ⟨123330300571720183667945933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82220200381146789111963955 123330300571720183667945933)
    ·
      refine ⟨46248862714395068875479725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123330300571720183667945933 46248862714395068875479725)
      ·
        refine ⟨17343323517898150828304897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46248862714395068875479725 17343323517898150828304897)
        ·
          refine ⟨13007492638423613121228673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17343323517898150828304897 13007492638423613121228673)
          ·
            refine ⟨9755619478817709840921505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13007492638423613121228673 9755619478817709840921505)
            ·
              refine ⟨7316714609113282380691129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9755619478817709840921505 7316714609113282380691129)
              ·
                refine ⟨5487535956834961785518347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7316714609113282380691129 5487535956834961785518347)
                ·
                  refine ⟨8231303935252442678277521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5487535956834961785518347 8231303935252442678277521)
                  ·
                    refine ⟨6173477951439332008708141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8231303935252442678277521 6173477951439332008708141)
                    ·
                      refine ⟨2315054231789749503265553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6173477951439332008708141 2315054231789749503265553)
                      ·
                        rfl

theorem cell23_4508552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 2, 2, 1, 2, 3].length) (baseStart_4508552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4508552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4508552 prefixEnd_4508552 := by exact prefixLift 4508552
  have htrace : WordTrace (prefixWord ++ tailWord_4508552) baseStart_4508552 baseEnd_4508552 := by
    simpa [prefixWord, tailWord_4508552, baseEnd_4508552] using wordTrace_append hprefix tailTrace_4508552
  have hstable : (prefixWord ++ tailWord_4508552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4508552).length < 2 ^ (prefixWord ++ tailWord_4508552).sum := by decide
  have hdescent : baseEnd_4508552 < baseStart_4508552 := by decide
  rcases family_descends (prefixWord ++ tailWord_4508552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4508565 : List Nat := [1, 3, 2, 1, 1, 4, 1, 2, 4, 1, 3]
def baseStart_4508565 : Nat := 118140960795 + 4508565 * 2 ^ 59
def prefixEnd_4508565 : Nat := 4983230072969 + 3 ^ 40 * 4508565 * 2
def baseEnd_4508565 : Nat := 2315060907038257952402993

theorem tailTrace_4508565 : CollatzResearch.WordTrace tailWord_4508565 prefixEnd_4508565 2315060907038257952402993 := by
  unfold tailWord_4508565
  simp only [CollatzResearch.WordTrace]
  refine ⟨164440874911246481444151149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109627249940830987629434099 164440874911246481444151149)
  ·
    refine ⟨61665328091717430541556681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 164440874911246481444151149 61665328091717430541556681)
    ·
      refine ⟨46248996068788072906167511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61665328091717430541556681 46248996068788072906167511)
      ·
        refine ⟨69373494103182109359251267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46248996068788072906167511 69373494103182109359251267)
        ·
          refine ⟨104060241154773164038876901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69373494103182109359251267 104060241154773164038876901)
          ·
            refine ⟨19511295216519968257289419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 104060241154773164038876901 19511295216519968257289419)
            ·
              refine ⟨29266942824779952385934129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19511295216519968257289419 29266942824779952385934129)
              ·
                refine ⟨21950207118584964289450597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29266942824779952385934129 21950207118584964289450597)
                ·
                  refine ⟨4115663834734680804271987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21950207118584964289450597 4115663834734680804271987)
                  ·
                    refine ⟨6173495752102021206407981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4115663834734680804271987 6173495752102021206407981)
                    ·
                      refine ⟨2315060907038257952402993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6173495752102021206407981 2315060907038257952402993)
                      ·
                        rfl

theorem cell23_4508565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 2, 4, 1, 3].length) (baseStart_4508565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4508565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4508565 prefixEnd_4508565 := by exact prefixLift 4508565
  have htrace : WordTrace (prefixWord ++ tailWord_4508565) baseStart_4508565 baseEnd_4508565 := by
    simpa [prefixWord, tailWord_4508565, baseEnd_4508565] using wordTrace_append hprefix tailTrace_4508565
  have hstable : (prefixWord ++ tailWord_4508565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4508565).length < 2 ^ (prefixWord ++ tailWord_4508565).sum := by decide
  have hdescent : baseEnd_4508565 < baseStart_4508565 := by decide
  rcases family_descends (prefixWord ++ tailWord_4508565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4508583 : List Nat := [1, 1, 6, 1, 3, 1, 3, 2, 1, 2, 2]
def baseStart_4508583 : Nat := 118140960795 + 4508583 * 2 ^ 59
def prefixEnd_4508583 : Nat := 4983230072969 + 3 ^ 40 * 4508583 * 2
def baseEnd_4508583 : Nat := 2315070149690038881977911

theorem tailTrace_4508583 : CollatzResearch.WordTrace tailWord_4508583 prefixEnd_4508583 2315070149690038881977911 := by
  unfold tailWord_4508583
  simp only [CollatzResearch.WordTrace]
  refine ⟨164441531425181270518306403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109627687616787513678870935 164441531425181270518306403)
  ·
    refine ⟨246662297137771905777459605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164441531425181270518306403 246662297137771905777459605)
    ·
      refine ⟨11562295178333058083318419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 246662297137771905777459605 11562295178333058083318419)
      ·
        refine ⟨17343442767499587124977629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11562295178333058083318419 17343442767499587124977629)
        ·
          refine ⟨6503791037812345171866611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17343442767499587124977629 6503791037812345171866611)
          ·
            refine ⟨9755686556718517757799917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6503791037812345171866611 9755686556718517757799917)
            ·
              refine ⟨3658382458769444159174969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9755686556718517757799917 3658382458769444159174969)
              ·
                refine ⟨2743786844077083119381227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3658382458769444159174969 2743786844077083119381227)
                ·
                  refine ⟨4115680266115624679071841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2743786844077083119381227 4115680266115624679071841)
                  ·
                    refine ⟨3086760199586718509303881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4115680266115624679071841 3086760199586718509303881)
                    ·
                      refine ⟨2315070149690038881977911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3086760199586718509303881 2315070149690038881977911)
                      ·
                        rfl

theorem cell23_4508583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 3, 2, 1, 2, 2].length) (baseStart_4508583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4508583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4508583 prefixEnd_4508583 := by exact prefixLift 4508583
  have htrace : WordTrace (prefixWord ++ tailWord_4508583) baseStart_4508583 baseEnd_4508583 := by
    simpa [prefixWord, tailWord_4508583, baseEnd_4508583] using wordTrace_append hprefix tailTrace_4508583
  have hstable : (prefixWord ++ tailWord_4508583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4508583).length < 2 ^ (prefixWord ++ tailWord_4508583).sum := by decide
  have hdescent : baseEnd_4508583 < baseStart_4508583 := by decide
  rcases family_descends (prefixWord ++ tailWord_4508583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4508608 : List Nat := [2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 5]
def baseStart_4508608 : Nat := 118140960795 + 4508608 * 2 ^ 59
def prefixEnd_4508608 : Nat := 4983230072969 + 3 ^ 40 * 4508608 * 2
def baseEnd_4508608 : Nat := 2315082986706401284165295

theorem tailTrace_4508608 : CollatzResearch.WordTrace tailWord_4508608 prefixEnd_4508608 2315082986706401284165295 := by
  unfold tailWord_4508608
  simp only [CollatzResearch.WordTrace]
  refine ⟨82221221625045349893983239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109628295500060466525310985 82221221625045349893983239)
  ·
    refine ⟨123331832437568024840974859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82221221625045349893983239 123331832437568024840974859)
    ·
      refine ⟨184997748656352037261462289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123331832437568024840974859 184997748656352037261462289)
      ·
        refine ⟨138748311492264027946096717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 184997748656352037261462289 138748311492264027946096717)
        ·
          refine ⟨52030616809599010479786269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 138748311492264027946096717 52030616809599010479786269)
          ·
            refine ⟨19511481303599628929919851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52030616809599010479786269 19511481303599628929919851)
            ·
              refine ⟨29267221955399443394879777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19511481303599628929919851 29267221955399443394879777)
              ·
                refine ⟨21950416466549582546159833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29267221955399443394879777 21950416466549582546159833)
                ·
                  refine ⟨16462812349912186909619875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21950416466549582546159833 16462812349912186909619875)
                  ·
                    refine ⟨24694218524868280364429813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16462812349912186909619875 24694218524868280364429813)
                    ·
                      refine ⟨2315082986706401284165295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24694218524868280364429813 2315082986706401284165295)
                      ·
                        rfl

theorem cell23_4508608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 5].length) (baseStart_4508608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4508608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4508608 prefixEnd_4508608 := by exact prefixLift 4508608
  have htrace : WordTrace (prefixWord ++ tailWord_4508608) baseStart_4508608 baseEnd_4508608 := by
    simpa [prefixWord, tailWord_4508608, baseEnd_4508608] using wordTrace_append hprefix tailTrace_4508608
  have hstable : (prefixWord ++ tailWord_4508608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4508608).length < 2 ^ (prefixWord ++ tailWord_4508608).sum := by decide
  have hdescent : baseEnd_4508608 < baseStart_4508608 := by decide
  rcases family_descends (prefixWord ++ tailWord_4508608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4508618 : List Nat := [3, 1, 2, 1, 2, 1, 1, 2, 4, 2, 4]
def baseStart_4508618 : Nat := 118140960795 + 4508618 * 2 ^ 59
def prefixEnd_4508618 : Nat := 4983230072969 + 3 ^ 40 * 4508618 * 2
def baseEnd_4508618 : Nat := 2315088121512946245040249

theorem tailTrace_4508618 : CollatzResearch.WordTrace tailWord_4508618 prefixEnd_4508618 2315088121512946245040249 := by
  unfold tailWord_4508618
  simp only [CollatzResearch.WordTrace]
  refine ⟨41110701995013617873957627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109628538653369647663887005 41110701995013617873957627)
  ·
    refine ⟨61666052992520426810936441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41110701995013617873957627 61666052992520426810936441)
    ·
      refine ⟨46249539744390320108202331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61666052992520426810936441 46249539744390320108202331)
      ·
        refine ⟨69374309616585480162303497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46249539744390320108202331 69374309616585480162303497)
        ·
          refine ⟨52030732212439110121727623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69374309616585480162303497 52030732212439110121727623)
          ·
            refine ⟨78046098318658665182591435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52030732212439110121727623 78046098318658665182591435)
            ·
              refine ⟨117069147477987997773887153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78046098318658665182591435 117069147477987997773887153)
              ·
                refine ⟨87801860608490998330415365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 117069147477987997773887153 87801860608490998330415365)
                ·
                  refine ⟨16462848864092062186952881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 87801860608490998330415365 16462848864092062186952881)
                  ·
                    refine ⟨12347136648069046640214661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16462848864092062186952881 12347136648069046640214661)
                    ·
                      refine ⟨2315088121512946245040249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12347136648069046640214661 2315088121512946245040249)
                      ·
                        rfl

theorem cell23_4508618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 4, 2, 4].length) (baseStart_4508618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4508618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4508618 prefixEnd_4508618 := by exact prefixLift 4508618
  have htrace : WordTrace (prefixWord ++ tailWord_4508618) baseStart_4508618 baseEnd_4508618 := by
    simpa [prefixWord, tailWord_4508618, baseEnd_4508618] using wordTrace_append hprefix tailTrace_4508618
  have hstable : (prefixWord ++ tailWord_4508618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4508618).length < 2 ^ (prefixWord ++ tailWord_4508618).sum := by decide
  have hdescent : baseEnd_4508618 < baseStart_4508618 := by decide
  rcases family_descends (prefixWord ++ tailWord_4508618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4508622 : List Nat := [4, 1, 1, 1, 2, 4, 1, 2, 1, 4, 2]
def baseStart_4508622 : Nat := 118140960795 + 4508622 * 2 ^ 59
def prefixEnd_4508622 : Nat := 4983230072969 + 3 ^ 40 * 4508622 * 2
def baseEnd_4508622 : Nat := 2315090175435564229390231

theorem tailTrace_4508622 : CollatzResearch.WordTrace tailWord_4508622 prefixEnd_4508622 2315090175435564229390231 := by
  unfold tailWord_4508622
  simp only [CollatzResearch.WordTrace]
  refine ⟨20555369234004997522372015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109628635914693320119317413 20555369234004997522372015)
  ·
    refine ⟨30833053851007496283558023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20555369234004997522372015 30833053851007496283558023)
    ·
      refine ⟨46249580776511244425337035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30833053851007496283558023 46249580776511244425337035)
      ·
        refine ⟨69374371164766866638005553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46249580776511244425337035 69374371164766866638005553)
        ·
          refine ⟨52030778373575149978504165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69374371164766866638005553 52030778373575149978504165)
          ·
            refine ⟨9755770945045340620969531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52030778373575149978504165 9755770945045340620969531)
            ·
              refine ⟨14633656417568010931454297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9755770945045340620969531 14633656417568010931454297)
              ·
                refine ⟨10975242313176008198590723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14633656417568010931454297 10975242313176008198590723)
                ·
                  refine ⟨16462863469764012297886085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10975242313176008198590723 16462863469764012297886085)
                  ·
                    refine ⟨3086786900580752305853641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16462863469764012297886085 3086786900580752305853641)
                    ·
                      refine ⟨2315090175435564229390231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3086786900580752305853641 2315090175435564229390231)
                      ·
                        rfl

theorem cell23_4508622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 2, 1, 4, 2].length) (baseStart_4508622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4508622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4508622 prefixEnd_4508622 := by exact prefixLift 4508622
  have htrace : WordTrace (prefixWord ++ tailWord_4508622) baseStart_4508622 baseEnd_4508622 := by
    simpa [prefixWord, tailWord_4508622, baseEnd_4508622] using wordTrace_append hprefix tailTrace_4508622
  have hstable : (prefixWord ++ tailWord_4508622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4508622).length < 2 ^ (prefixWord ++ tailWord_4508622).sum := by decide
  have hdescent : baseEnd_4508622 < baseStart_4508622 := by decide
  rcases family_descends (prefixWord ++ tailWord_4508622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4508626 : List Nat := [3, 2, 2, 3, 1, 2, 3, 1, 1, 3, 2]
def baseStart_4508626 : Nat := 118140960795 + 4508626 * 2 ^ 59
def prefixEnd_4508626 : Nat := 4983230072969 + 3 ^ 40 * 4508626 * 2
def baseEnd_4508626 : Nat := 2315092229358182213740213

theorem tailTrace_4508626 : CollatzResearch.WordTrace tailWord_4508626 prefixEnd_4508626 2315092229358182213740213 := by
  unfold tailWord_4508626
  simp only [CollatzResearch.WordTrace]
  refine ⟨41110774941006372215530433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109628733176016992574747821 41110774941006372215530433)
  ·
    refine ⟨30833081205754779161647825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41110774941006372215530433 30833081205754779161647825)
    ·
      refine ⟨23124810904316084371235869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30833081205754779161647825 23124810904316084371235869)
      ·
        refine ⟨8671804089118531639213451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23124810904316084371235869 8671804089118531639213451)
        ·
          refine ⟨13007706133677797458820177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8671804089118531639213451 13007706133677797458820177)
          ·
            refine ⟨9755779600258348094115133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13007706133677797458820177 9755779600258348094115133)
            ·
              refine ⟨3658417350096880535293175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9755779600258348094115133 3658417350096880535293175)
              ·
                refine ⟨5487626025145320802939763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3658417350096880535293175 5487626025145320802939763)
                ·
                  refine ⟨8231439037717981204409645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5487626025145320802939763 8231439037717981204409645)
                  ·
                    refine ⟨3086789639144242951653617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8231439037717981204409645 3086789639144242951653617)
                    ·
                      refine ⟨2315092229358182213740213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3086789639144242951653617 2315092229358182213740213)
                      ·
                        rfl

theorem cell23_4508626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 3, 1, 1, 3, 2].length) (baseStart_4508626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4508626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4508626 prefixEnd_4508626 := by exact prefixLift 4508626
  have htrace : WordTrace (prefixWord ++ tailWord_4508626) baseStart_4508626 baseEnd_4508626 := by
    simpa [prefixWord, tailWord_4508626, baseEnd_4508626] using wordTrace_append hprefix tailTrace_4508626
  have hstable : (prefixWord ++ tailWord_4508626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4508626).length < 2 ^ (prefixWord ++ tailWord_4508626).sum := by decide
  have hdescent : baseEnd_4508626 < baseStart_4508626 := by decide
  rcases family_descends (prefixWord ++ tailWord_4508626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4508642 : List Nat := [3, 3, 3, 1, 1, 1, 1, 1, 2, 4, 3]
def baseStart_4508642 : Nat := 118140960795 + 4508642 * 2 ^ 59
def prefixEnd_4508642 : Nat := 4983230072969 + 3 ^ 40 * 4508642 * 2
def baseEnd_4508642 : Nat := 2315100445048654151140139

theorem tailTrace_4508642 : CollatzResearch.WordTrace tailWord_4508642 prefixEnd_4508642 2315100445048654151140139 := by
  unfold tailWord_4508642
  simp only [CollatzResearch.WordTrace]
  refine ⟨41110920832991880898676045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109629122221311682396469453 41110920832991880898676045)
  ·
    refine ⟨15416595312371955337003517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41110920832991880898676045 15416595312371955337003517)
    ·
      refine ⟨5781223242139483251376319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15416595312371955337003517 5781223242139483251376319)
      ·
        refine ⟨8671834863209224877064479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5781223242139483251376319 8671834863209224877064479)
        ·
          refine ⟨13007752294813837315596719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8671834863209224877064479 13007752294813837315596719)
          ·
            refine ⟨19511628442220755973395079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13007752294813837315596719 19511628442220755973395079)
            ·
              refine ⟨29267442663331133960092619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19511628442220755973395079 29267442663331133960092619)
              ·
                refine ⟨43901163994996700940138929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29267442663331133960092619 43901163994996700940138929)
                ·
                  refine ⟨32925872996247525705104197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43901163994996700940138929 32925872996247525705104197)
                  ·
                    refine ⟨6173601186796411069707037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32925872996247525705104197 6173601186796411069707037)
                    ·
                      refine ⟨2315100445048654151140139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6173601186796411069707037 2315100445048654151140139)
                      ·
                        rfl

theorem cell23_4508642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_4508642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4508642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4508642 prefixEnd_4508642 := by exact prefixLift 4508642
  have htrace : WordTrace (prefixWord ++ tailWord_4508642) baseStart_4508642 baseEnd_4508642 := by
    simpa [prefixWord, tailWord_4508642, baseEnd_4508642] using wordTrace_append hprefix tailTrace_4508642
  have hstable : (prefixWord ++ tailWord_4508642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4508642).length < 2 ^ (prefixWord ++ tailWord_4508642).sum := by decide
  have hdescent : baseEnd_4508642 < baseStart_4508642 := by decide
  rcases family_descends (prefixWord ++ tailWord_4508642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4508655 : List Nat := [1, 1, 2, 1, 4, 4, 1, 1, 2, 3, 3]
def baseStart_4508655 : Nat := 118140960795 + 4508655 * 2 ^ 59
def prefixEnd_4508655 : Nat := 4983230072969 + 3 ^ 40 * 4508655 * 2
def baseEnd_4508655 : Nat := 2315107120297162600277579

theorem tailTrace_4508655 : CollatzResearch.WordTrace tailWord_4508655 prefixEnd_4508655 2315107120297162600277579 := by
  unfold tailWord_4508655
  simp only [CollatzResearch.WordTrace]
  refine ⟨164444157480920426814927419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109629438320613617876618279 164444157480920426814927419)
  ·
    refine ⟨246666236221380640222391129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164444157480920426814927419 246666236221380640222391129)
    ·
      refine ⟨184999677166035480166793347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 246666236221380640222391129 184999677166035480166793347)
      ·
        refine ⟨277499515749053220250190021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184999677166035480166793347 277499515749053220250190021)
        ·
          refine ⟨52031159202947478796910629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 277499515749053220250190021 52031159202947478796910629)
          ·
            refine ⟨9755842350552652274420743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52031159202947478796910629 9755842350552652274420743)
            ·
              refine ⟨14633763525828978411631115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9755842350552652274420743 14633763525828978411631115)
              ·
                refine ⟨21950645288743467617446673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14633763525828978411631115 21950645288743467617446673)
                ·
                  refine ⟨16462983966557600713085005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21950645288743467617446673 16462983966557600713085005)
                  ·
                    refine ⟨6173618987459100267406877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16462983966557600713085005 6173618987459100267406877)
                    ·
                      refine ⟨2315107120297162600277579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6173618987459100267406877 2315107120297162600277579)
                      ·
                        rfl

theorem cell23_4508655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 1, 2, 3, 3].length) (baseStart_4508655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4508655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4508655 prefixEnd_4508655 := by exact prefixLift 4508655
  have htrace : WordTrace (prefixWord ++ tailWord_4508655) baseStart_4508655 baseEnd_4508655 := by
    simpa [prefixWord, tailWord_4508655, baseEnd_4508655] using wordTrace_append hprefix tailTrace_4508655
  have hstable : (prefixWord ++ tailWord_4508655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4508655).length < 2 ^ (prefixWord ++ tailWord_4508655).sum := by decide
  have hdescent : baseEnd_4508655 < baseStart_4508655 := by decide
  rcases family_descends (prefixWord ++ tailWord_4508655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4508665 : List Nat := [1, 2, 1, 3, 1, 3, 1, 2, 2, 5, 2]
def baseStart_4508665 : Nat := 118140960795 + 4508665 * 2 ^ 59
def prefixEnd_4508665 : Nat := 4983230072969 + 3 ^ 40 * 4508665 * 2
def baseEnd_4508665 : Nat := 2315112255103707561152533

theorem tailTrace_4508665 : CollatzResearch.WordTrace tailWord_4508665 prefixEnd_4508665 2315112255103707561152533 := by
  unfold tailWord_4508665
  simp only [CollatzResearch.WordTrace]
  refine ⟨164444522210884198522791449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109629681473922799015194299 164444522210884198522791449)
  ·
    refine ⟨123333391658163148892093587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164444522210884198522791449 123333391658163148892093587)
    ·
      refine ⟨185000087487244723338140381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123333391658163148892093587 185000087487244723338140381)
      ·
        refine ⟨69375032807716771251802643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 185000087487244723338140381 69375032807716771251802643)
        ·
          refine ⟨104062549211575156877703965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69375032807716771251802643 104062549211575156877703965)
          ·
            refine ⟨39023455954340683829138987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 104062549211575156877703965 39023455954340683829138987)
            ·
              refine ⟨58535183931511025743708481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39023455954340683829138987 58535183931511025743708481)
              ·
                refine ⟨43901387948633269307781361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58535183931511025743708481 43901387948633269307781361)
                ·
                  refine ⟨32926040961474951980836021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43901387948633269307781361 32926040961474951980836021)
                  ·
                    refine ⟨3086816340138276748203377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32926040961474951980836021 3086816340138276748203377)
                    ·
                      refine ⟨2315112255103707561152533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3086816340138276748203377 2315112255103707561152533)
                      ·
                        rfl

theorem cell23_4508665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 2, 2, 5, 2].length) (baseStart_4508665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4508665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4508665 prefixEnd_4508665 := by exact prefixLift 4508665
  have htrace : WordTrace (prefixWord ++ tailWord_4508665) baseStart_4508665 baseEnd_4508665 := by
    simpa [prefixWord, tailWord_4508665, baseEnd_4508665] using wordTrace_append hprefix tailTrace_4508665
  have hstable : (prefixWord ++ tailWord_4508665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4508665).length < 2 ^ (prefixWord ++ tailWord_4508665).sum := by decide
  have hdescent : baseEnd_4508665 < baseStart_4508665 := by decide
  rcases family_descends (prefixWord ++ tailWord_4508665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4508749 : List Nat := [1, 6, 1, 1, 1, 3, 1, 2, 2, 2, 3]
def baseStart_4508749 : Nat := 118140960795 + 4508749 * 2 ^ 59
def prefixEnd_4508749 : Nat := 4983230072969 + 3 ^ 40 * 4508749 * 2
def baseEnd_4508749 : Nat := 2315155387478685232502147

theorem tailTrace_4508749 : CollatzResearch.WordTrace tailWord_4508749 prefixEnd_4508749 2315155387478685232502147 := by
  unfold tailWord_4508749
  simp only [CollatzResearch.WordTrace]
  refine ⟨164447585942579880868849301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109631723961719920579232867 164447585942579880868849301)
  ·
    refine ⟨7708480591058431915727311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 164447585942579880868849301 7708480591058431915727311)
    ·
      refine ⟨11562720886587647873590967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7708480591058431915727311 11562720886587647873590967)
      ·
        refine ⟨17344081329881471810386451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11562720886587647873590967 17344081329881471810386451)
        ·
          refine ⟨26016121994822207715579677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17344081329881471810386451 26016121994822207715579677)
          ·
            refine ⟨9756045748058327893342379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26016121994822207715579677 9756045748058327893342379)
            ·
              refine ⟨14634068622087491840013569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9756045748058327893342379 14634068622087491840013569)
              ·
                refine ⟨10975551466565618880010177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14634068622087491840013569 10975551466565618880010177)
                ·
                  refine ⟨8231663599924214160007633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10975551466565618880010177 8231663599924214160007633)
                  ·
                    refine ⟨6173747699943160620005725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8231663599924214160007633 6173747699943160620005725)
                    ·
                      refine ⟨2315155387478685232502147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6173747699943160620005725 2315155387478685232502147)
                      ·
                        rfl

theorem cell23_4508749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 2, 2, 2, 3].length) (baseStart_4508749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4508749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4508749 prefixEnd_4508749 := by exact prefixLift 4508749
  have htrace : WordTrace (prefixWord ++ tailWord_4508749) baseStart_4508749 baseEnd_4508749 := by
    simpa [prefixWord, tailWord_4508749, baseEnd_4508749] using wordTrace_append hprefix tailTrace_4508749
  have hstable : (prefixWord ++ tailWord_4508749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4508749).length < 2 ^ (prefixWord ++ tailWord_4508749).sum := by decide
  have hdescent : baseEnd_4508749 < baseStart_4508749 := by decide
  rcases family_descends (prefixWord ++ tailWord_4508749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4508762 : List Nat := [3, 1, 1, 2, 1, 1, 2, 5, 3, 1, 3]
def baseStart_4508762 : Nat := 118140960795 + 4508762 * 2 ^ 59
def prefixEnd_4508762 : Nat := 4983230072969 + 3 ^ 40 * 4508762 * 2
def baseEnd_4508762 : Nat := 2315162062727193681639587

theorem tailTrace_4508762 : CollatzResearch.WordTrace tailWord_4508762 prefixEnd_4508762 2315162062727193681639587 := by
  unfold tailWord_4508762
  simp only [CollatzResearch.WordTrace]
  refine ⟨41112015022883196022268135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109632040061021856059381693 41112015022883196022268135)
  ·
    refine ⟨61668022534324794033402203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41112015022883196022268135 61668022534324794033402203)
    ·
      refine ⟨92502033801487191050103305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61668022534324794033402203 92502033801487191050103305)
      ·
        refine ⟨69376525351115393287577479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92502033801487191050103305 69376525351115393287577479)
        ·
          refine ⟨104064788026673089931366219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69376525351115393287577479 104064788026673089931366219)
          ·
            refine ⟨156097182040009634897049329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104064788026673089931366219 156097182040009634897049329)
            ·
              refine ⟨117072886530007226172786997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 156097182040009634897049329 117072886530007226172786997)
              ·
                refine ⟨10975583112188177453698781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 117072886530007226172786997 10975583112188177453698781)
                ·
                  refine ⟨4115843667070566545137043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10975583112188177453698781 4115843667070566545137043)
                  ·
                    refine ⟨6173765500605849817705565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4115843667070566545137043 6173765500605849817705565)
                    ·
                      refine ⟨2315162062727193681639587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6173765500605849817705565 2315162062727193681639587)
                      ·
                        rfl

theorem cell23_4508762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 5, 3, 1, 3].length) (baseStart_4508762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4508762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4508762 prefixEnd_4508762 := by exact prefixLift 4508762
  have htrace : WordTrace (prefixWord ++ tailWord_4508762) baseStart_4508762 baseEnd_4508762 := by
    simpa [prefixWord, tailWord_4508762, baseEnd_4508762] using wordTrace_append hprefix tailTrace_4508762
  have hstable : (prefixWord ++ tailWord_4508762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4508762).length < 2 ^ (prefixWord ++ tailWord_4508762).sum := by decide
  have hdescent : baseEnd_4508762 < baseStart_4508762 := by decide
  rcases family_descends (prefixWord ++ tailWord_4508762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4508772 : List Nat := [2, 3, 1, 1, 2, 1, 1, 1, 6, 3, 2]
def baseStart_4508772 : Nat := 118140960795 + 4508772 * 2 ^ 59
def prefixEnd_4508772 : Nat := 4983230072969 + 3 ^ 40 * 4508772 * 2
def baseEnd_4508772 : Nat := 2315167197533738642514541

theorem tailTrace_4508772 : CollatzResearch.WordTrace tailWord_4508772 prefixEnd_4508772 2315167197533738642514541 := by
  unfold tailWord_4508772
  simp only [CollatzResearch.WordTrace]
  refine ⟨82224212410748277898468285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109632283214331037197957713 82224212410748277898468285)
  ·
    refine ⟨30834079654030604211925607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82224212410748277898468285 30834079654030604211925607)
    ·
      refine ⟨46251119481045906317888411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30834079654030604211925607 46251119481045906317888411)
      ·
        refine ⟨69376679221568859476832617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46251119481045906317888411 69376679221568859476832617)
        ·
          refine ⟨52032509416176644607624463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69376679221568859476832617 52032509416176644607624463)
          ·
            refine ⟨78048764124264966911436695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52032509416176644607624463 78048764124264966911436695)
            ·
              refine ⟨117073146186397450367155043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78048764124264966911436695 117073146186397450367155043)
              ·
                refine ⟨175609719279596175550732565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 117073146186397450367155043 175609719279596175550732565)
                ·
                  refine ⟨8231705591231070728940589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 175609719279596175550732565 8231705591231070728940589)
                  ·
                    refine ⟨3086889596711651523352721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8231705591231070728940589 3086889596711651523352721)
                    ·
                      refine ⟨2315167197533738642514541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3086889596711651523352721 2315167197533738642514541)
                      ·
                        rfl

theorem cell23_4508772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 6, 3, 2].length) (baseStart_4508772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4508772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4508772 prefixEnd_4508772 := by exact prefixLift 4508772
  have htrace : WordTrace (prefixWord ++ tailWord_4508772) baseStart_4508772 baseEnd_4508772 := by
    simpa [prefixWord, tailWord_4508772, baseEnd_4508772] using wordTrace_append hprefix tailTrace_4508772
  have hstable : (prefixWord ++ tailWord_4508772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4508772).length < 2 ^ (prefixWord ++ tailWord_4508772).sum := by decide
  have hdescent : baseEnd_4508772 < baseStart_4508772 := by decide
  rcases family_descends (prefixWord ++ tailWord_4508772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4508782 : List Nat := [4, 1, 2, 2, 1, 3, 1, 1, 3, 5]
def baseStart_4508782 : Nat := 118140960795 + 4508782 * 2 ^ 59
def prefixEnd_4508782 : Nat := 4983230072969 + 3 ^ 40 * 4508782 * 2
def baseEnd_4508782 : Nat := 771724110780094534463165

theorem tailTrace_4508782 : CollatzResearch.WordTrace tailWord_4508782 prefixEnd_4508782 771724110780094534463165 := by
  unfold tailWord_4508782
  simp only [CollatzResearch.WordTrace]
  refine ⟨20556098693932540938100075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109632526367640218336533733 20556098693932540938100075)
  ·
    refine ⟨30834148040898811407150113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20556098693932540938100075 30834148040898811407150113)
    ·
      refine ⟨23125611030674108555362585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30834148040898811407150113 23125611030674108555362585)
      ·
        refine ⟨17344208273005581416521939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23125611030674108555362585 17344208273005581416521939)
        ·
          refine ⟨26016312409508372124782909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17344208273005581416521939 26016312409508372124782909)
          ·
            refine ⟨9756117153565639546793591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26016312409508372124782909 9756117153565639546793591)
            ·
              refine ⟨14634175730348459320190387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9756117153565639546793591 14634175730348459320190387)
              ·
                refine ⟨21951263595522688980285581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14634175730348459320190387 21951263595522688980285581)
                ·
                  refine ⟨8231723848321008367607093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21951263595522688980285581 8231723848321008367607093)
                  ·
                    refine ⟨771724110780094534463165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8231723848321008367607093 771724110780094534463165)
                    ·
                      rfl

theorem cell23_4508782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 1, 3, 5].length) (baseStart_4508782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4508782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4508782 prefixEnd_4508782 := by exact prefixLift 4508782
  have htrace : WordTrace (prefixWord ++ tailWord_4508782) baseStart_4508782 baseEnd_4508782 := by
    simpa [prefixWord, tailWord_4508782, baseEnd_4508782] using wordTrace_append hprefix tailTrace_4508782
  have hstable : (prefixWord ++ tailWord_4508782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4508782).length < 2 ^ (prefixWord ++ tailWord_4508782).sum := by decide
  have hdescent : baseEnd_4508782 < baseStart_4508782 := by decide
  rcases family_descends (prefixWord ++ tailWord_4508782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4508795 : List Nat := [1, 1, 1, 1, 1, 4, 1, 3, 6, 4]
def baseStart_4508795 : Nat := 118140960795 + 4508795 * 2 ^ 59
def prefixEnd_4508795 : Nat := 4983230072969 + 3 ^ 40 * 4508795 * 2
def baseEnd_4508795 : Nat := 771726335862930684175645

theorem tailTrace_4508795 : CollatzResearch.WordTrace tailWord_4508795 prefixEnd_4508795 771726335862930684175645 := by
  unfold tailWord_4508795
  simp only [CollatzResearch.WordTrace]
  refine ⟨164449263700413230725023839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109632842466942153816682559 164449263700413230725023839)
  ·
    refine ⟨246673895550619846087535759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164449263700413230725023839 246673895550619846087535759)
    ·
      refine ⟨370010843325929769131303639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 246673895550619846087535759 370010843325929769131303639)
      ·
        refine ⟨555016264988894653696955459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 370010843325929769131303639 555016264988894653696955459)
        ·
          refine ⟨832524397483341980545433189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 555016264988894653696955459 832524397483341980545433189)
          ·
            refine ⟨156098324528126621352268723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 832524397483341980545433189 156098324528126621352268723)
            ·
              refine ⟨234147486792189932028403085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 156098324528126621352268723 234147486792189932028403085)
              ·
                refine ⟨87805307547071224510651157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 234147486792189932028403085 87805307547071224510651157)
                ·
                  refine ⟨4115873791268963648936773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 87805307547071224510651157 4115873791268963648936773)
                  ·
                    refine ⟨771726335862930684175645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4115873791268963648936773 771726335862930684175645)
                    ·
                      rfl

theorem cell23_4508795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 6, 4].length) (baseStart_4508795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4508795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4508795 prefixEnd_4508795 := by exact prefixLift 4508795
  have htrace : WordTrace (prefixWord ++ tailWord_4508795) baseStart_4508795 baseEnd_4508795 := by
    simpa [prefixWord, tailWord_4508795, baseEnd_4508795] using wordTrace_append hprefix tailTrace_4508795
  have hstable : (prefixWord ++ tailWord_4508795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4508795).length < 2 ^ (prefixWord ++ tailWord_4508795).sum := by decide
  have hdescent : baseEnd_4508795 < baseStart_4508795 := by decide
  rcases family_descends (prefixWord ++ tailWord_4508795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4508832 : List Nat := [2, 1, 1, 4, 2, 1, 4, 1, 1, 2, 4]
def baseStart_4508832 : Nat := 118140960795 + 4508832 * 2 ^ 59
def prefixEnd_4508832 : Nat := 4983230072969 + 3 ^ 40 * 4508832 * 2
def baseEnd_4508832 : Nat := 2315198006373008407764265

theorem tailTrace_4508832 : CollatzResearch.WordTrace tailWord_4508832 prefixEnd_4508832 2315198006373008407764265 := by
  unfold tailWord_4508832
  simp only [CollatzResearch.WordTrace]
  refine ⟨82225306600639593022060375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109633742134186124029413833 82225306600639593022060375)
  ·
    refine ⟨123337959900959389533090563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82225306600639593022060375 123337959900959389533090563)
    ·
      refine ⟨185006939851439084299635845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123337959900959389533090563 185006939851439084299635845)
      ·
        refine ⟨34688801222144828306181721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 185006939851439084299635845 34688801222144828306181721)
        ·
          refine ⟨26016600916608621229636291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34688801222144828306181721 26016600916608621229636291)
          ·
            refine ⟨39024901374912931844454437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26016600916608621229636291 39024901374912931844454437)
            ·
              refine ⟨7317169007796174720835207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39024901374912931844454437 7317169007796174720835207)
              ·
                refine ⟨10975753511694262081252811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7317169007796174720835207 10975753511694262081252811)
                ·
                  refine ⟨16463630267541393121879217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10975753511694262081252811 16463630267541393121879217)
                  ·
                    refine ⟨12347722700656044841409413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16463630267541393121879217 12347722700656044841409413)
                    ·
                      refine ⟨2315198006373008407764265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12347722700656044841409413 2315198006373008407764265)
                      ·
                        rfl

theorem cell23_4508832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 4, 1, 1, 2, 4].length) (baseStart_4508832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4508832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4508832 prefixEnd_4508832 := by exact prefixLift 4508832
  have htrace : WordTrace (prefixWord ++ tailWord_4508832) baseStart_4508832 baseEnd_4508832 := by
    simpa [prefixWord, tailWord_4508832, baseEnd_4508832] using wordTrace_append hprefix tailTrace_4508832
  have hstable : (prefixWord ++ tailWord_4508832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4508832).length < 2 ^ (prefixWord ++ tailWord_4508832).sum := by decide
  have hdescent : baseEnd_4508832 < baseStart_4508832 := by decide
  rcases family_descends (prefixWord ++ tailWord_4508832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4508836 : List Nat := [2, 3, 1, 2, 3, 2, 1, 2, 3, 2, 2]
def baseStart_4508836 : Nat := 118140960795 + 4508836 * 2 ^ 59
def prefixEnd_4508836 : Nat := 4983230072969 + 3 ^ 40 * 4508836 * 2
def baseEnd_4508836 : Nat := 2315200060295626392114247

theorem tailTrace_4508836 : CollatzResearch.WordTrace tailWord_4508836 prefixEnd_4508836 2315200060295626392114247 := by
  unfold tailWord_4508836
  simp only [CollatzResearch.WordTrace]
  refine ⟨82225379546632347363633181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109633839395509796484844241 82225379546632347363633181)
  ·
    refine ⟨30834517329987130261362443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82225379546632347363633181 30834517329987130261362443)
    ·
      refine ⟨46251775994980695392043665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30834517329987130261362443 46251775994980695392043665)
      ·
        refine ⟨34688831996235521544032749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46251775994980695392043665 34688831996235521544032749)
        ·
          refine ⟨13008311998588320579012281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34688831996235521544032749 13008311998588320579012281)
          ·
            refine ⟨9756233998941240434259211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13008311998588320579012281 9756233998941240434259211)
            ·
              refine ⟨14634350998411860651388817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9756233998941240434259211 14634350998411860651388817)
              ·
                refine ⟨10975763248808895488541613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14634350998411860651388817 10975763248808895488541613)
                ·
                  refine ⟨4115911218303335808203105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10975763248808895488541613 4115911218303335808203105)
                  ·
                    refine ⟨3086933413727501856152329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4115911218303335808203105 3086933413727501856152329)
                    ·
                      refine ⟨2315200060295626392114247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3086933413727501856152329 2315200060295626392114247)
                      ·
                        rfl

theorem cell23_4508836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 2, 3, 2, 2].length) (baseStart_4508836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4508836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4508836 prefixEnd_4508836 := by exact prefixLift 4508836
  have htrace : WordTrace (prefixWord ++ tailWord_4508836) baseStart_4508836 baseEnd_4508836 := by
    simpa [prefixWord, tailWord_4508836, baseEnd_4508836] using wordTrace_append hprefix tailTrace_4508836
  have hstable : (prefixWord ++ tailWord_4508836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4508836).length < 2 ^ (prefixWord ++ tailWord_4508836).sum := by decide
  have hdescent : baseEnd_4508836 < baseStart_4508836 := by decide
  rcases family_descends (prefixWord ++ tailWord_4508836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4508839 : List Nat := [1, 1, 6, 2, 1, 1, 2, 1, 3, 2, 3]
def baseStart_4508839 : Nat := 118140960795 + 4508839 * 2 ^ 59
def prefixEnd_4508839 : Nat := 4983230072969 + 3 ^ 40 * 4508839 * 2
def baseEnd_4508839 : Nat := 2315201600737589880376733

theorem tailTrace_4508839 : CollatzResearch.WordTrace tailWord_4508839 prefixEnd_4508839 2315201600737589880376733 := by
  unfold tailWord_4508839
  simp only [CollatzResearch.WordTrace]
  refine ⟨164450868512253826239625571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109633912341502550826417047 164450868512253826239625571)
  ·
    refine ⟨246676302768380739359438357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164450868512253826239625571 246676302768380739359438357)
    ·
      refine ⟨11562951692267847157473673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 246676302768380739359438357 11562951692267847157473673)
      ·
        refine ⟨8672213769200885368105255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11562951692267847157473673 8672213769200885368105255)
        ·
          refine ⟨13008320653801328052157883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8672213769200885368105255 13008320653801328052157883)
          ·
            refine ⟨19512480980701992078236825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13008320653801328052157883 19512480980701992078236825)
            ·
              refine ⟨14634360735526494058677619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19512480980701992078236825 14634360735526494058677619)
              ·
                refine ⟨21951541103289741088016429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14634360735526494058677619 21951541103289741088016429)
                ·
                  refine ⟨8231827913733652908006161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21951541103289741088016429 8231827913733652908006161)
                  ·
                    refine ⟨6173870935300239681004621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8231827913733652908006161 6173870935300239681004621)
                    ·
                      refine ⟨2315201600737589880376733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6173870935300239681004621 2315201600737589880376733)
                      ·
                        rfl

theorem cell23_4508839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_4508839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4508839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4508839 prefixEnd_4508839 := by exact prefixLift 4508839
  have htrace : WordTrace (prefixWord ++ tailWord_4508839) baseStart_4508839 baseEnd_4508839 := by
    simpa [prefixWord, tailWord_4508839, baseEnd_4508839] using wordTrace_append hprefix tailTrace_4508839
  have hstable : (prefixWord ++ tailWord_4508839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4508839).length < 2 ^ (prefixWord ++ tailWord_4508839).sum := by decide
  have hdescent : baseEnd_4508839 < baseStart_4508839 := by decide
  rcases family_descends (prefixWord ++ tailWord_4508839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4508875 : List Nat := [1, 1, 1, 1, 3, 2, 2, 3, 2, 3, 4]
def baseStart_4508875 : Nat := 118140960795 + 4508875 * 2 ^ 59
def prefixEnd_4508875 : Nat := 4983230072969 + 3 ^ 40 * 4508875 * 2
def baseEnd_4508875 : Nat := 2315220086041151739526567

theorem tailTrace_4508875 : CollatzResearch.WordTrace tailWord_4508875 prefixEnd_4508875 2315220086041151739526567 := by
  unfold tailWord_4508875
  simp only [CollatzResearch.WordTrace]
  refine ⟨164452181540123404387936079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109634787693415602925290719 164452181540123404387936079)
  ·
    refine ⟨246678272310185106581904119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164452181540123404387936079 246678272310185106581904119)
    ·
      refine ⟨370017408465277659872856179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 246678272310185106581904119 370017408465277659872856179)
      ·
        refine ⟨555026112697916489809284269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 370017408465277659872856179 555026112697916489809284269)
        ·
          refine ⟨208134792261718683678481601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 555026112697916489809284269 208134792261718683678481601)
          ·
            refine ⟨156101094196289012758861201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 208134792261718683678481601 156101094196289012758861201)
            ·
              refine ⟨117075820647216759569145901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 156101094196289012758861201 117075820647216759569145901)
              ·
                refine ⟨43903432742706284838429713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 117075820647216759569145901 43903432742706284838429713)
                ·
                  refine ⟨32927574557029713628822285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43903432742706284838429713 32927574557029713628822285)
                  ·
                    refine ⟨12347840458886142610808357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32927574557029713628822285 12347840458886142610808357)
                    ·
                      refine ⟨2315220086041151739526567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12347840458886142610808357 2315220086041151739526567)
                      ·
                        rfl

theorem cell23_4508875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 3, 2, 3, 4].length) (baseStart_4508875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4508875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4508875 prefixEnd_4508875 := by exact prefixLift 4508875
  have htrace : WordTrace (prefixWord ++ tailWord_4508875) baseStart_4508875 baseEnd_4508875 := by
    simpa [prefixWord, tailWord_4508875, baseEnd_4508875] using wordTrace_append hprefix tailTrace_4508875
  have hstable : (prefixWord ++ tailWord_4508875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4508875).length < 2 ^ (prefixWord ++ tailWord_4508875).sum := by decide
  have hdescent : baseEnd_4508875 < baseStart_4508875 := by decide
  rcases family_descends (prefixWord ++ tailWord_4508875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4508896 : List Nat := [2, 1, 1, 3, 1, 5, 2, 2, 1, 3, 2]
def baseStart_4508896 : Nat := 118140960795 + 4508896 * 2 ^ 59
def prefixEnd_4508896 : Nat := 4983230072969 + 3 ^ 40 * 4508896 * 2
def baseEnd_4508896 : Nat := 2315230869134896157363971

theorem tailTrace_4508896 : CollatzResearch.WordTrace tailWord_4508896 prefixEnd_4508896 2315230869134896157363971 := by
  unfold tailWord_4508896
  simp only [CollatzResearch.WordTrace]
  refine ⟨82226473736523662487225271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109635298315364883316300361 82226473736523662487225271)
  ·
    refine ⟨123339710604785493730837907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82226473736523662487225271 123339710604785493730837907)
    ·
      refine ⟨185009565907178240596256861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123339710604785493730837907 185009565907178240596256861)
      ·
        refine ⟨69378587215191840223596323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 185009565907178240596256861 69378587215191840223596323)
        ·
          refine ⟨104067880822787760335394485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69378587215191840223596323 104067880822787760335394485)
          ·
            refine ⟨9756363827136352531443233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 104067880822787760335394485 9756363827136352531443233)
            ·
              refine ⟨7317272870352264398582425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9756363827136352531443233 7317272870352264398582425)
              ·
                refine ⟨5487954652764198298936819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7317272870352264398582425 5487954652764198298936819)
                ·
                  refine ⟨8231931979146297448405229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5487954652764198298936819 8231931979146297448405229)
                  ·
                    refine ⟨3086974492179861543151961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8231931979146297448405229 3086974492179861543151961)
                    ·
                      refine ⟨2315230869134896157363971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3086974492179861543151961 2315230869134896157363971)
                      ·
                        rfl

theorem cell23_4508896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 2, 2, 1, 3, 2].length) (baseStart_4508896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4508896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4508896 prefixEnd_4508896 := by exact prefixLift 4508896
  have htrace : WordTrace (prefixWord ++ tailWord_4508896) baseStart_4508896 baseEnd_4508896 := by
    simpa [prefixWord, tailWord_4508896, baseEnd_4508896] using wordTrace_append hprefix tailTrace_4508896
  have hstable : (prefixWord ++ tailWord_4508896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4508896).length < 2 ^ (prefixWord ++ tailWord_4508896).sum := by decide
  have hdescent : baseEnd_4508896 < baseStart_4508896 := by decide
  rcases family_descends (prefixWord ++ tailWord_4508896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4508955 : List Nat := [1, 1, 1, 1, 1, 1, 5, 1, 3, 1, 7]
def baseStart_4508955 : Nat := 118140960795 + 4508955 * 2 ^ 59
def prefixEnd_4508955 : Nat := 4983230072969 + 3 ^ 40 * 4508955 * 2
def baseEnd_4508955 : Nat := 2315261164493511426526199

theorem tailTrace_4508955 : CollatzResearch.WordTrace tailWord_4508955 prefixEnd_4508955 2315261164493511426526199 := by
  unfold tailWord_4508955
  simp only [CollatzResearch.WordTrace]
  refine ⟨164455099379833578050848319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109636732919889052033898879 164455099379833578050848319)
  ·
    refine ⟨246682649069750367076272479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164455099379833578050848319 246682649069750367076272479)
    ·
      refine ⟨370023973604625550614408719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 246682649069750367076272479 370023973604625550614408719)
      ·
        refine ⟨555035960406938325921613079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 370023973604625550614408719 555035960406938325921613079)
        ·
          refine ⟨832553940610407488882419619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 555035960406938325921613079 832553940610407488882419619)
          ·
            refine ⟨1248830910915611233323629429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 832553940610407488882419619 1248830910915611233323629429)
            ·
              refine ⟨117077897898338553124090259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1248830910915611233323629429 117077897898338553124090259)
              ·
                refine ⟨175616846847507829686135389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 117077897898338553124090259 175616846847507829686135389)
                ·
                  refine ⟨65856317567815436132300771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 175616846847507829686135389 65856317567815436132300771)
                  ·
                    refine ⟨98784476351723154198451157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 65856317567815436132300771 98784476351723154198451157)
                    ·
                      refine ⟨2315261164493511426526199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 98784476351723154198451157 2315261164493511426526199)
                      ·
                        rfl

theorem cell23_4508955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 3, 1, 7].length) (baseStart_4508955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4508955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4508955 prefixEnd_4508955 := by exact prefixLift 4508955
  have htrace : WordTrace (prefixWord ++ tailWord_4508955) baseStart_4508955 baseEnd_4508955 := by
    simpa [prefixWord, tailWord_4508955, baseEnd_4508955] using wordTrace_append hprefix tailTrace_4508955
  have hstable : (prefixWord ++ tailWord_4508955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4508955).length < 2 ^ (prefixWord ++ tailWord_4508955).sum := by decide
  have hdescent : baseEnd_4508955 < baseStart_4508955 := by decide
  rcases family_descends (prefixWord ++ tailWord_4508955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4508999 : List Nat := [1, 1, 4, 1, 2, 3, 1, 1, 1, 6, 2]
def baseStart_4508999 : Nat := 118140960795 + 4508999 * 2 ^ 59
def prefixEnd_4508999 : Nat := 4983230072969 + 3 ^ 40 * 4508999 * 2
def baseEnd_4508999 : Nat := 2315283757642309254375997

theorem tailTrace_4508999 : CollatzResearch.WordTrace tailWord_4508999 prefixEnd_4508999 2315283757642309254375997 := by
  unfold tailWord_4508999
  simp only [CollatzResearch.WordTrace]
  refine ⟨164456704191674173565450051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109637802794449449043633367 164456704191674173565450051)
  ·
    refine ⟨246685056287511260348175077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164456704191674173565450051 246685056287511260348175077)
    ·
      refine ⟨46253448053908361315282827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 246685056287511260348175077 46253448053908361315282827)
      ·
        refine ⟨69380172080862541972924241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46253448053908361315282827 69380172080862541972924241)
        ·
          refine ⟨52035129060646906479693181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69380172080862541972924241 52035129060646906479693181)
          ·
            refine ⟨19513173397742589929884943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52035129060646906479693181 19513173397742589929884943)
            ·
              refine ⟨29269760096613884894827415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19513173397742589929884943 29269760096613884894827415)
              ·
                refine ⟨43904640144920827342241123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29269760096613884894827415 43904640144920827342241123)
                ·
                  refine ⟨65856960217381241013361685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43904640144920827342241123 65856960217381241013361685)
                  ·
                    refine ⟨3087045010189745672501329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 65856960217381241013361685 3087045010189745672501329)
                    ·
                      refine ⟨2315283757642309254375997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3087045010189745672501329 2315283757642309254375997)
                      ·
                        rfl

theorem cell23_4508999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 1, 1, 6, 2].length) (baseStart_4508999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4508999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4508999 prefixEnd_4508999 := by exact prefixLift 4508999
  have htrace : WordTrace (prefixWord ++ tailWord_4508999) baseStart_4508999 baseEnd_4508999 := by
    simpa [prefixWord, tailWord_4508999, baseEnd_4508999] using wordTrace_append hprefix tailTrace_4508999
  have hstable : (prefixWord ++ tailWord_4508999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4508999).length < 2 ^ (prefixWord ++ tailWord_4508999).sum := by decide
  have hdescent : baseEnd_4508999 < baseStart_4508999 := by decide
  rcases family_descends (prefixWord ++ tailWord_4508999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4509009 : List Nat := [1, 2, 2, 1, 4, 1, 3, 2, 3, 4]
def baseStart_4509009 : Nat := 118140960795 + 4509009 * 2 ^ 59
def prefixEnd_4509009 : Nat := 4983230072969 + 3 ^ 40 * 4509009 * 2
def baseEnd_4509009 : Nat := 771762964149618071750317

theorem tailTrace_4509009 : CollatzResearch.WordTrace tailWord_4509009 prefixEnd_4509009 771762964149618071750317 := by
  unfold tailWord_4509009
  simp only [CollatzResearch.WordTrace]
  refine ⟨164457068921637945273314081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109638045947758630182209387 164457068921637945273314081)
  ·
    refine ⟨123342801691228458954985561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164457068921637945273314081 123342801691228458954985561)
    ·
      refine ⟨92507101268421344216239171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123342801691228458954985561 92507101268421344216239171)
      ·
        refine ⟨138760651902632016324358757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92507101268421344216239171 138760651902632016324358757)
        ·
          refine ⟨26017622231743503060817267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 138760651902632016324358757 26017622231743503060817267)
          ·
            refine ⟨39026433347615254591225901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26017622231743503060817267 39026433347615254591225901)
            ·
              refine ⟨14634912505355720471709713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39026433347615254591225901 14634912505355720471709713)
              ·
                refine ⟨10976184379016790353782285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14634912505355720471709713 10976184379016790353782285)
                ·
                  refine ⟨4116069142131296382668357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10976184379016790353782285 4116069142131296382668357)
                  ·
                    refine ⟨771762964149618071750317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4116069142131296382668357 771762964149618071750317)
                    ·
                      rfl

theorem cell23_4509009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 2, 3, 4].length) (baseStart_4509009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4509009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4509009 prefixEnd_4509009 := by exact prefixLift 4509009
  have htrace : WordTrace (prefixWord ++ tailWord_4509009) baseStart_4509009 baseEnd_4509009 := by
    simpa [prefixWord, tailWord_4509009, baseEnd_4509009] using wordTrace_append hprefix tailTrace_4509009
  have hstable : (prefixWord ++ tailWord_4509009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4509009).length < 2 ^ (prefixWord ++ tailWord_4509009).sum := by decide
  have hdescent : baseEnd_4509009 < baseStart_4509009 := by decide
  rcases family_descends (prefixWord ++ tailWord_4509009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4509042 : List Nat := [3, 2, 1, 2, 1, 2, 1, 1, 1, 1, 8]
def baseStart_4509042 : Nat := 118140960795 + 4509042 * 2 ^ 59
def prefixEnd_4509042 : Nat := 4983230072969 + 3 ^ 40 * 4509042 * 2
def baseEnd_4509042 : Nat := 2315305837310452586138299

theorem tailTrace_4509042 : CollatzResearch.WordTrace tailWord_4509042 prefixEnd_4509042 2315305837310452586138299 := by
  unfold tailWord_4509042
  simp only [CollatzResearch.WordTrace]
  refine ⟨41114568132629597977316345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109638848353678927939510253 41114568132629597977316345)
  ·
    refine ⟨30835926099472198482987259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41114568132629597977316345 30835926099472198482987259)
    ·
      refine ⟨46253889149208297724480889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30835926099472198482987259 46253889149208297724480889)
      ·
        refine ⟨34690416861906223293360667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46253889149208297724480889 34690416861906223293360667)
        ·
          refine ⟨52035625292859334940041001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34690416861906223293360667 52035625292859334940041001)
          ·
            refine ⟨39026718969644501205030751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52035625292859334940041001 39026718969644501205030751)
            ·
              refine ⟨58540078454466751807546127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39026718969644501205030751 58540078454466751807546127)
              ·
                refine ⟨87810117681700127711319191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58540078454466751807546127 87810117681700127711319191)
                ·
                  refine ⟨131715176522550191566978787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 87810117681700127711319191 131715176522550191566978787)
                  ·
                    refine ⟨197572764783825287350468181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 131715176522550191566978787 197572764783825287350468181)
                    ·
                      refine ⟨2315305837310452586138299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 197572764783825287350468181 2315305837310452586138299)
                      ·
                        rfl

theorem cell23_4509042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 1, 1, 8].length) (baseStart_4509042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4509042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4509042 prefixEnd_4509042 := by exact prefixLift 4509042
  have htrace : WordTrace (prefixWord ++ tailWord_4509042) baseStart_4509042 baseEnd_4509042 := by
    simpa [prefixWord, tailWord_4509042, baseEnd_4509042] using wordTrace_append hprefix tailTrace_4509042
  have hstable : (prefixWord ++ tailWord_4509042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4509042).length < 2 ^ (prefixWord ++ tailWord_4509042).sum := by decide
  have hdescent : baseEnd_4509042 < baseStart_4509042 := by decide
  rcases family_descends (prefixWord ++ tailWord_4509042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4509112 : List Nat := [2, 1, 2, 1, 2, 2, 3, 10]
def baseStart_4509112 : Nat := 118140960795 + 4509112 * 2 ^ 59
def prefixEnd_4509112 : Nat := 4983230072969 + 3 ^ 40 * 4509112 * 2
def baseEnd_4509112 : Nat := 85753399294676567120851

theorem tailTrace_4509112 : CollatzResearch.WordTrace tailWord_4509112 prefixEnd_4509112 85753399294676567120851 := by
  unfold tailWord_4509112
  simp only [CollatzResearch.WordTrace]
  refine ⟨82230412820132396932156795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109640550426843195909542393 82230412820132396932156795)
  ·
    refine ⟨123345619230198595398235193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82230412820132396932156795 123345619230198595398235193)
    ·
      refine ⟨92509214422648946548676395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123345619230198595398235193 92509214422648946548676395)
      ·
        refine ⟨138763821633973419823014593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92509214422648946548676395 138763821633973419823014593)
        ·
          refine ⟨104072866225480064867260945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 138763821633973419823014593 104072866225480064867260945)
          ·
            refine ⟨78054649669110048650445709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104072866225480064867260945 78054649669110048650445709)
            ·
              refine ⟨29270493625916268243917141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78054649669110048650445709 29270493625916268243917141)
              ·
                refine ⟨85753399294676567120851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 29270493625916268243917141 85753399294676567120851)
                ·
                  rfl

theorem cell23_4509112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 10].length) (baseStart_4509112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4509112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4509112 prefixEnd_4509112 := by exact prefixLift 4509112
  have htrace : WordTrace (prefixWord ++ tailWord_4509112) baseStart_4509112 baseEnd_4509112 := by
    simpa [prefixWord, tailWord_4509112, baseEnd_4509112] using wordTrace_append hprefix tailTrace_4509112
  have hstable : (prefixWord ++ tailWord_4509112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4509112).length < 2 ^ (prefixWord ++ tailWord_4509112).sum := by decide
  have hdescent : baseEnd_4509112 < baseStart_4509112 := by decide
  rcases family_descends (prefixWord ++ tailWord_4509112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4509140 : List Nat := [2, 4, 1, 2, 3, 1, 3, 1, 1, 1, 4]
def baseStart_4509140 : Nat := 118140960795 + 4509140 * 2 ^ 59
def prefixEnd_4509140 : Nat := 4983230072969 + 3 ^ 40 * 4509140 * 2
def baseEnd_4509140 : Nat := 2315356158414593202712849

theorem tailTrace_4509140 : CollatzResearch.WordTrace tailWord_4509140 prefixEnd_4509140 2315356158414593202712849 := by
  unfold tailWord_4509140
  simp only [CollatzResearch.WordTrace]
  refine ⟨82230923442081677323166437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109641231256108903097555249 82230923442081677323166437)
  ·
    refine ⟨15418298145390314498093707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82230923442081677323166437 15418298145390314498093707)
    ·
      refine ⟨23127447218085471747140561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15418298145390314498093707 23127447218085471747140561)
      ·
        refine ⟨17345585413564103810355421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23127447218085471747140561 17345585413564103810355421)
        ·
          refine ⟨6504594530086538928883283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17345585413564103810355421 6504594530086538928883283)
          ·
            refine ⟨9756891795129808393324925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6504594530086538928883283 9756891795129808393324925)
            ·
              refine ⟨3658834423173678147496847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9756891795129808393324925 3658834423173678147496847)
              ·
                refine ⟨5488251634760517221245271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3658834423173678147496847 5488251634760517221245271)
                ·
                  refine ⟨8232377452140775831867907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5488251634760517221245271 8232377452140775831867907)
                  ·
                    refine ⟨12348566178211163747801861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8232377452140775831867907 12348566178211163747801861)
                    ·
                      refine ⟨2315356158414593202712849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12348566178211163747801861 2315356158414593202712849)
                      ·
                        rfl

theorem cell23_4509140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 3, 1, 1, 1, 4].length) (baseStart_4509140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4509140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4509140 prefixEnd_4509140 := by exact prefixLift 4509140
  have htrace : WordTrace (prefixWord ++ tailWord_4509140) baseStart_4509140 baseEnd_4509140 := by
    simpa [prefixWord, tailWord_4509140, baseEnd_4509140] using wordTrace_append hprefix tailTrace_4509140
  have hstable : (prefixWord ++ tailWord_4509140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4509140).length < 2 ^ (prefixWord ++ tailWord_4509140).sum := by decide
  have hdescent : baseEnd_4509140 < baseStart_4509140 := by decide
  rcases family_descends (prefixWord ++ tailWord_4509140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4509156 : List Nat := [2, 3, 1, 1, 1, 1, 1, 5, 4, 1, 3]
def baseStart_4509156 : Nat := 118140960795 + 4509156 * 2 ^ 59
def prefixEnd_4509156 : Nat := 4983230072969 + 3 ^ 40 * 4509156 * 2
def baseEnd_4509156 : Nat := 2315364374105065140112775

theorem tailTrace_4509156 : CollatzResearch.WordTrace tailWord_4509156 prefixEnd_4509156 2315364374105065140112775 := by
  unfold tailWord_4509156
  simp only [CollatzResearch.WordTrace]
  refine ⟨82231215226052694689457661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109641620301403592919276881 82231215226052694689457661)
  ·
    refine ⟨30836705709769760508546623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82231215226052694689457661 30836705709769760508546623)
    ·
      refine ⟨46255058564654640762819935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30836705709769760508546623 46255058564654640762819935)
      ·
        refine ⟨69382587846981961144229903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46255058564654640762819935 69382587846981961144229903)
        ·
          refine ⟨104073881770472941716344855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69382587846981961144229903 104073881770472941716344855)
          ·
            refine ⟨156110822655709412574517283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104073881770472941716344855 156110822655709412574517283)
            ·
              refine ⟨234166233983564118861775925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 156110822655709412574517283 234166233983564118861775925)
              ·
                refine ⟨21953084435959136143291493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 234166233983564118861775925 21953084435959136143291493)
                ·
                  refine ⟨4116203331742338026867155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21953084435959136143291493 4116203331742338026867155)
                  ·
                    refine ⟨6174304997613507040300733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4116203331742338026867155 6174304997613507040300733)
                    ·
                      refine ⟨2315364374105065140112775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6174304997613507040300733 2315364374105065140112775)
                      ·
                        rfl

theorem cell23_4509156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 5, 4, 1, 3].length) (baseStart_4509156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4509156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4509156 prefixEnd_4509156 := by exact prefixLift 4509156
  have htrace : WordTrace (prefixWord ++ tailWord_4509156) baseStart_4509156 baseEnd_4509156 := by
    simpa [prefixWord, tailWord_4509156, baseEnd_4509156] using wordTrace_append hprefix tailTrace_4509156
  have hstable : (prefixWord ++ tailWord_4509156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4509156).length < 2 ^ (prefixWord ++ tailWord_4509156).sum := by decide
  have hdescent : baseEnd_4509156 < baseStart_4509156 := by decide
  rcases family_descends (prefixWord ++ tailWord_4509156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4509157 : List Nat := [1, 3, 1, 5, 1, 2, 1, 4, 1, 2, 2]
def baseStart_4509157 : Nat := 118140960795 + 4509157 * 2 ^ 59
def prefixEnd_4509157 : Nat := 4983230072969 + 3 ^ 40 * 4509157 * 2
def baseEnd_4509157 : Nat := 2315364887585719636200271

theorem tailTrace_4509157 : CollatzResearch.WordTrace tailWord_4509157 prefixEnd_4509157 2315364887585719636200271 := by
  unfold tailWord_4509157
  simp only [CollatzResearch.WordTrace]
  refine ⟨164462466925101766549701725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109641644616734511033134483 164462466925101766549701725)
  ·
    refine ⟨61673425096913162456138147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 164462466925101766549701725 61673425096913162456138147)
    ·
      refine ⟨92510137645369743684207221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61673425096913162456138147 92510137645369743684207221)
      ·
        refine ⟨8672825404253413470394427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 92510137645369743684207221 8672825404253413470394427)
        ·
          refine ⟨13009238106380120205591641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8672825404253413470394427 13009238106380120205591641)
          ·
            refine ⟨9756928579785090154193731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13009238106380120205591641 9756928579785090154193731)
            ·
              refine ⟨14635392869677635231290597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9756928579785090154193731 14635392869677635231290597)
              ·
                refine ⟨2744136163064556605866987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14635392869677635231290597 2744136163064556605866987)
                ·
                  refine ⟨4116204244596834908800481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2744136163064556605866987 4116204244596834908800481)
                  ·
                    refine ⟨3087153183447626181600361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4116204244596834908800481 3087153183447626181600361)
                    ·
                      refine ⟨2315364887585719636200271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3087153183447626181600361 2315364887585719636200271)
                      ·
                        rfl

theorem cell23_4509157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 4, 1, 2, 2].length) (baseStart_4509157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4509157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4509157 prefixEnd_4509157 := by exact prefixLift 4509157
  have htrace : WordTrace (prefixWord ++ tailWord_4509157) baseStart_4509157 baseEnd_4509157 := by
    simpa [prefixWord, tailWord_4509157, baseEnd_4509157] using wordTrace_append hprefix tailTrace_4509157
  have hstable : (prefixWord ++ tailWord_4509157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4509157).length < 2 ^ (prefixWord ++ tailWord_4509157).sum := by decide
  have hdescent : baseEnd_4509157 < baseStart_4509157 := by decide
  rcases family_descends (prefixWord ++ tailWord_4509157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4509159 : List Nat := [1, 1, 5, 2, 1, 2, 1, 1, 2, 7]
def baseStart_4509159 : Nat := 118140960795 + 4509159 * 2 ^ 59
def prefixEnd_4509159 : Nat := 4983230072969 + 3 ^ 40 * 4509159 * 2
def baseEnd_4509159 : Nat := 771788638182342876125087

theorem tailTrace_4509159 : CollatzResearch.WordTrace tailWord_4509159 prefixEnd_4509159 771788638182342876125087 := by
  unfold tailWord_4509159
  simp only [CollatzResearch.WordTrace]
  refine ⟨164462539871094520891274531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109641693247396347260849687 164462539871094520891274531)
  ·
    refine ⟨246693809806641781336911797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164462539871094520891274531 246693809806641781336911797)
    ·
      refine ⟨23127544669372667000335481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 246693809806641781336911797 23127544669372667000335481)
      ·
        refine ⟨17345658502029500250251611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23127544669372667000335481 17345658502029500250251611)
        ·
          refine ⟨26018487753044250375377417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17345658502029500250251611 26018487753044250375377417)
          ·
            refine ⟨19513865814783187781533063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26018487753044250375377417 19513865814783187781533063)
            ·
              refine ⟨29270798722174781672299595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19513865814783187781533063 29270798722174781672299595)
              ·
                refine ⟨43906198083262172508449393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29270798722174781672299595 43906198083262172508449393)
                ·
                  refine ⟨32929648562446629381337045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43906198083262172508449393 32929648562446629381337045)
                  ·
                    refine ⟨771788638182342876125087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32929648562446629381337045 771788638182342876125087)
                    ·
                      rfl

theorem cell23_4509159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 1, 2, 7].length) (baseStart_4509159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4509159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4509159 prefixEnd_4509159 := by exact prefixLift 4509159
  have htrace : WordTrace (prefixWord ++ tailWord_4509159) baseStart_4509159 baseEnd_4509159 := by
    simpa [prefixWord, tailWord_4509159, baseEnd_4509159] using wordTrace_append hprefix tailTrace_4509159
  have hstable : (prefixWord ++ tailWord_4509159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4509159).length < 2 ^ (prefixWord ++ tailWord_4509159).sum := by decide
  have hdescent : baseEnd_4509159 < baseStart_4509159 := by decide
  rcases family_descends (prefixWord ++ tailWord_4509159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4509173 : List Nat := [1, 3, 5, 1, 1, 1, 1, 3, 1, 3, 3]
def baseStart_4509173 : Nat := 118140960795 + 4509173 * 2 ^ 59
def prefixEnd_4509173 : Nat := 4983230072969 + 3 ^ 40 * 4509173 * 2
def baseEnd_4509173 : Nat := 2315373103276191573600197

theorem tailTrace_4509173 : CollatzResearch.WordTrace tailWord_4509173 prefixEnd_4509173 2315373103276191573600197 := by
  unfold tailWord_4509173
  simp only [CollatzResearch.WordTrace]
  refine ⟨164463050493043801282284173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109642033662029200854856115 164463050493043801282284173)
  ·
    refine ⟨61673643934891425480856565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 164463050493043801282284173 61673643934891425480856565)
    ·
      refine ⟨5781904118896071138830303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 61673643934891425480856565 5781904118896071138830303)
      ·
        refine ⟨8672856178344106708245455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5781904118896071138830303 8672856178344106708245455)
        ·
          refine ⟨13009284267516160062368183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8672856178344106708245455 13009284267516160062368183)
          ·
            refine ⟨19513926401274240093552275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13009284267516160062368183 19513926401274240093552275)
            ·
              refine ⟨29270889601911360140328413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19513926401274240093552275 29270889601911360140328413)
              ·
                refine ⟨10976583600716760052623155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29270889601911360140328413 10976583600716760052623155)
                ·
                  refine ⟨16464875401075140078934733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10976583600716760052623155 16464875401075140078934733)
                  ·
                    refine ⟨6174328275403177529600525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16464875401075140078934733 6174328275403177529600525)
                    ·
                      refine ⟨2315373103276191573600197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6174328275403177529600525 2315373103276191573600197)
                      ·
                        rfl

theorem cell23_4509173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_4509173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4509173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4509173 prefixEnd_4509173 := by exact prefixLift 4509173
  have htrace : WordTrace (prefixWord ++ tailWord_4509173) baseStart_4509173 baseEnd_4509173 := by
    simpa [prefixWord, tailWord_4509173, baseEnd_4509173] using wordTrace_append hprefix tailTrace_4509173
  have hstable : (prefixWord ++ tailWord_4509173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4509173).length < 2 ^ (prefixWord ++ tailWord_4509173).sum := by decide
  have hdescent : baseEnd_4509173 < baseStart_4509173 := by decide
  rcases family_descends (prefixWord ++ tailWord_4509173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4509226 : List Nat := [3, 1, 4, 1, 1, 1, 1, 3, 2, 2, 4]
def baseStart_4509226 : Nat := 118140960795 + 4509226 * 2 ^ 59
def prefixEnd_4509226 : Nat := 4983230072969 + 3 ^ 40 * 4509226 * 2
def baseEnd_4509226 : Nat := 2315400317750879866237453

theorem tailTrace_4509226 : CollatzResearch.WordTrace tailWord_4509226 prefixEnd_4509226 2315400317750879866237453 := by
  unfold tailWord_4509226
  simp only [CollatzResearch.WordTrace]
  refine ⟨41116245890462947833490883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109643322374567860889309021 41116245890462947833490883)
  ·
    refine ⟨61674368835694421750236325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41116245890462947833490883 61674368835694421750236325)
    ·
      refine ⟨11563944156692704078169311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61674368835694421750236325 11563944156692704078169311)
      ·
        refine ⟨17345916235039056117253967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11563944156692704078169311 17345916235039056117253967)
        ·
          refine ⟨26018874352558584175880951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17345916235039056117253967 26018874352558584175880951)
          ·
            refine ⟨39028311528837876263821427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26018874352558584175880951 39028311528837876263821427)
            ·
              refine ⟨58542467293256814395732141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39028311528837876263821427 58542467293256814395732141)
              ·
                refine ⟨21953425234971305398399553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58542467293256814395732141 21953425234971305398399553)
                ·
                  refine ⟨16465068926228479048799665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21953425234971305398399553 16465068926228479048799665)
                  ·
                    refine ⟨12348801694671359286599749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16465068926228479048799665 12348801694671359286599749)
                    ·
                      refine ⟨2315400317750879866237453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12348801694671359286599749 2315400317750879866237453)
                      ·
                        rfl

theorem cell23_4509226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_4509226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4509226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4509226 prefixEnd_4509226 := by exact prefixLift 4509226
  have htrace : WordTrace (prefixWord ++ tailWord_4509226) baseStart_4509226 baseEnd_4509226 := by
    simpa [prefixWord, tailWord_4509226, baseEnd_4509226] using wordTrace_append hprefix tailTrace_4509226
  have hstable : (prefixWord ++ tailWord_4509226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4509226).length < 2 ^ (prefixWord ++ tailWord_4509226).sum := by decide
  have hdescent : baseEnd_4509226 < baseStart_4509226 := by decide
  rcases family_descends (prefixWord ++ tailWord_4509226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4509230 : List Nat := [4, 1, 3, 1, 2, 1, 3, 1, 1, 4, 2]
def baseStart_4509230 : Nat := 118140960795 + 4509230 * 2 ^ 59
def prefixEnd_4509230 : Nat := 4983230072969 + 3 ^ 40 * 4509230 * 2
def baseEnd_4509230 : Nat := 2315402371673497850587435

theorem tailTrace_4509230 : CollatzResearch.WordTrace tailWord_4509230 prefixEnd_4509230 2315402371673497850587435 := by
  unfold tailWord_4509230
  simp only [CollatzResearch.WordTrace]
  refine ⟨20558141181729662502138643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109643419635891533344739429 20558141181729662502138643)
  ·
    refine ⟨30837211772594493753207965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20558141181729662502138643 30837211772594493753207965)
    ·
      refine ⟨11563954414722935157452987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30837211772594493753207965 11563954414722935157452987)
      ·
        refine ⟨17345931622084402736179481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11563954414722935157452987 17345931622084402736179481)
        ·
          refine ⟨13009448716563302052134611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17345931622084402736179481 13009448716563302052134611)
          ·
            refine ⟨19514173074844953078201917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13009448716563302052134611 19514173074844953078201917)
            ·
              refine ⟨7317814903066857404325719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19514173074844953078201917 7317814903066857404325719)
              ·
                refine ⟨10976722354600286106488579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7317814903066857404325719 10976722354600286106488579)
                ·
                  refine ⟨16465083531900429159732869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10976722354600286106488579 16465083531900429159732869)
                  ·
                    refine ⟨3087203162231330467449913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16465083531900429159732869 3087203162231330467449913)
                    ·
                      refine ⟨2315402371673497850587435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3087203162231330467449913 2315402371673497850587435)
                      ·
                        rfl

theorem cell23_4509230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 3, 1, 1, 4, 2].length) (baseStart_4509230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4509230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4509230 prefixEnd_4509230 := by exact prefixLift 4509230
  have htrace : WordTrace (prefixWord ++ tailWord_4509230) baseStart_4509230 baseEnd_4509230 := by
    simpa [prefixWord, tailWord_4509230, baseEnd_4509230] using wordTrace_append hprefix tailTrace_4509230
  have hstable : (prefixWord ++ tailWord_4509230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4509230).length < 2 ^ (prefixWord ++ tailWord_4509230).sum := by decide
  have hdescent : baseEnd_4509230 < baseStart_4509230 := by decide
  rcases family_descends (prefixWord ++ tailWord_4509230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4509256 : List Nat := [2, 1, 3, 1, 1, 1, 1, 1, 3, 7, 2]
def baseStart_4509256 : Nat := 118140960795 + 4509256 * 2 ^ 59
def prefixEnd_4509256 : Nat := 4983230072969 + 3 ^ 40 * 4509256 * 2
def baseEnd_4509256 : Nat := 2315415722170514748862315

theorem tailTrace_4509256 : CollatzResearch.WordTrace tailWord_4509256 prefixEnd_4509256 2315415722170514748862315 := by
  unfold tailWord_4509256
  simp only [CollatzResearch.WordTrace]
  refine ⟨82233038875871553228777811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109644051834495404305037081 82233038875871553228777811)
  ·
    refine ⟨123349558313807329843166717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82233038875871553228777811 123349558313807329843166717)
    ·
      refine ⟨46256084367677748691187519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123349558313807329843166717 46256084367677748691187519)
      ·
        refine ⟨69384126551516623036781279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46256084367677748691187519 69384126551516623036781279)
        ·
          refine ⟨104076189827274934555171919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69384126551516623036781279 104076189827274934555171919)
          ·
            refine ⟨156114284740912401832757879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104076189827274934555171919 156114284740912401832757879)
            ·
              refine ⟨234171427111368602749136819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 156114284740912401832757879 234171427111368602749136819)
              ·
                refine ⟨351257140667052904123705229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 234171427111368602749136819 351257140667052904123705229)
                ·
                  refine ⟨131721427750144839046389461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 351257140667052904123705229 131721427750144839046389461)
                  ·
                    refine ⟨3087220962894019665149753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 131721427750144839046389461 3087220962894019665149753)
                    ·
                      refine ⟨2315415722170514748862315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3087220962894019665149753 2315415722170514748862315)
                      ·
                        rfl

theorem cell23_4509256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 3, 7, 2].length) (baseStart_4509256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4509256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4509256 prefixEnd_4509256 := by exact prefixLift 4509256
  have htrace : WordTrace (prefixWord ++ tailWord_4509256) baseStart_4509256 baseEnd_4509256 := by
    simpa [prefixWord, tailWord_4509256, baseEnd_4509256] using wordTrace_append hprefix tailTrace_4509256
  have hstable : (prefixWord ++ tailWord_4509256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4509256).length < 2 ^ (prefixWord ++ tailWord_4509256).sum := by decide
  have hdescent : baseEnd_4509256 < baseStart_4509256 := by decide
  rcases family_descends (prefixWord ++ tailWord_4509256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4509259 : List Nat := [1, 1, 1, 1, 3, 1, 3, 4, 1, 2, 5]
def baseStart_4509259 : Nat := 118140960795 + 4509259 * 2 ^ 59
def prefixEnd_4509259 : Nat := 4983230072969 + 3 ^ 40 * 4509259 * 2
def baseEnd_4509259 : Nat := 2315417262612478237124801

theorem tailTrace_4509259 : CollatzResearch.WordTrace tailWord_4509259 prefixEnd_4509259 2315417262612478237124801 := by
  unfold tailWord_4509259
  simp only [CollatzResearch.WordTrace]
  refine ⟨164466187170732237969914831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109644124780488158646609887 164466187170732237969914831)
  ·
    refine ⟨246699280756098356954872247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164466187170732237969914831 246699280756098356954872247)
    ·
      refine ⟨370048921134147535432308371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 246699280756098356954872247 370048921134147535432308371)
      ·
        refine ⟨555073381701221303148462557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 370048921134147535432308371 555073381701221303148462557)
        ·
          refine ⟨208152518137957988680673459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 555073381701221303148462557 208152518137957988680673459)
          ·
            refine ⟨312228777206936983021010189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 208152518137957988680673459 312228777206936983021010189)
            ·
              refine ⟨117085791452601368632878821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 312228777206936983021010189 117085791452601368632878821)
              ·
                refine ⟨21953585897362756618664779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 117085791452601368632878821 21953585897362756618664779)
                ·
                  refine ⟨32930378846044134927997169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21953585897362756618664779 32930378846044134927997169)
                  ·
                    refine ⟨24697784134533101195997877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32930378846044134927997169 24697784134533101195997877)
                    ·
                      refine ⟨2315417262612478237124801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24697784134533101195997877 2315417262612478237124801)
                      ·
                        rfl

theorem cell23_4509259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 4, 1, 2, 5].length) (baseStart_4509259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4509259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4509259 prefixEnd_4509259 := by exact prefixLift 4509259
  have htrace : WordTrace (prefixWord ++ tailWord_4509259) baseStart_4509259 baseEnd_4509259 := by
    simpa [prefixWord, tailWord_4509259, baseEnd_4509259] using wordTrace_append hprefix tailTrace_4509259
  have hstable : (prefixWord ++ tailWord_4509259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4509259).length < 2 ^ (prefixWord ++ tailWord_4509259).sum := by decide
  have hdescent : baseEnd_4509259 < baseStart_4509259 := by decide
  rcases family_descends (prefixWord ++ tailWord_4509259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4509266 : List Nat := [3, 2, 2, 1, 2, 2, 1, 1, 4, 5]
def baseStart_4509266 : Nat := 118140960795 + 4509266 * 2 ^ 59
def prefixEnd_4509266 : Nat := 4983230072969 + 3 ^ 40 * 4509266 * 2
def baseEnd_4509266 : Nat := 771806952325686569912423

theorem tailTrace_4509266 : CollatzResearch.WordTrace tailWord_4509266 prefixEnd_4509266 771806952325686569912423 := by
  unfold tailWord_4509266
  simp only [CollatzResearch.WordTrace]
  refine ⟨41116610620426719541354913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109644294987804585443613101 41116610620426719541354913)
  ·
    refine ⟨30837457965320039656016185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41116610620426719541354913 30837457965320039656016185)
    ·
      refine ⟨23128093473990029742012139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30837457965320039656016185 23128093473990029742012139)
      ·
        refine ⟨34692140210985044613018209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23128093473990029742012139 34692140210985044613018209)
        ·
          refine ⟨26019105158238783459763657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34692140210985044613018209 26019105158238783459763657)
          ·
            refine ⟨19514328868679087594822743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26019105158238783459763657 19514328868679087594822743)
            ·
              refine ⟨29271493303018631392234115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19514328868679087594822743 29271493303018631392234115)
              ·
                refine ⟨43907239954527947088351173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29271493303018631392234115 43907239954527947088351173)
                ·
                  refine ⟨8232607491473990079065845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43907239954527947088351173 8232607491473990079065845)
                  ·
                    refine ⟨771806952325686569912423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8232607491473990079065845 771806952325686569912423)
                    ·
                      rfl

theorem cell23_4509266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 1, 4, 5].length) (baseStart_4509266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4509266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4509266 prefixEnd_4509266 := by exact prefixLift 4509266
  have htrace : WordTrace (prefixWord ++ tailWord_4509266) baseStart_4509266 baseEnd_4509266 := by
    simpa [prefixWord, tailWord_4509266, baseEnd_4509266] using wordTrace_append hprefix tailTrace_4509266
  have hstable : (prefixWord ++ tailWord_4509266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4509266).length < 2 ^ (prefixWord ++ tailWord_4509266).sum := by decide
  have hdescent : baseEnd_4509266 < baseStart_4509266 := by decide
  rcases family_descends (prefixWord ++ tailWord_4509266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4509276 : List Nat := [2, 2, 4, 1, 2, 1, 1, 1, 1, 1, 7]
def baseStart_4509276 : Nat := 118140960795 + 4509276 * 2 ^ 59
def prefixEnd_4509276 : Nat := 4983230072969 + 3 ^ 40 * 4509276 * 2
def baseEnd_4509276 : Nat := 2315425991783604670612223

theorem tailTrace_4509276 : CollatzResearch.WordTrace tailWord_4509276 prefixEnd_4509276 2315425991783604670612223 := by
  unfold tailWord_4509276
  simp only [CollatzResearch.WordTrace]
  refine ⟨82233403605835324936641841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109644538141113766582189121 82233403605835324936641841)
  ·
    refine ⟨61675052704376493702481381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82233403605835324936641841 61675052704376493702481381)
    ·
      refine ⟨11564072382070592569215259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61675052704376493702481381 11564072382070592569215259)
      ·
        refine ⟨17346108573105888853822889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11564072382070592569215259 17346108573105888853822889)
        ·
          refine ⟨13009581429829416640367167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17346108573105888853822889 13009581429829416640367167)
          ·
            refine ⟨19514372144744124960550751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13009581429829416640367167 19514372144744124960550751)
            ·
              refine ⟨29271558217116187440826127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19514372144744124960550751 29271558217116187440826127)
              ·
                refine ⟨43907337325674281161239191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29271558217116187440826127 43907337325674281161239191)
                ·
                  refine ⟨65861005988511421741858787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43907337325674281161239191 65861005988511421741858787)
                  ·
                    refine ⟨98791508982767132612788181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 65861005988511421741858787 98791508982767132612788181)
                    ·
                      refine ⟨2315425991783604670612223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 98791508982767132612788181 2315425991783604670612223)
                      ·
                        rfl

theorem cell23_4509276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_4509276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4509276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4509276 prefixEnd_4509276 := by exact prefixLift 4509276
  have htrace : WordTrace (prefixWord ++ tailWord_4509276) baseStart_4509276 baseEnd_4509276 := by
    simpa [prefixWord, tailWord_4509276, baseEnd_4509276] using wordTrace_append hprefix tailTrace_4509276
  have hstable : (prefixWord ++ tailWord_4509276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4509276).length < 2 ^ (prefixWord ++ tailWord_4509276).sum := by decide
  have hdescent : baseEnd_4509276 < baseStart_4509276 := by decide
  rcases family_descends (prefixWord ++ tailWord_4509276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4509363 : List Nat := [1, 1, 1, 2, 3, 3, 3, 1, 1, 5, 2]
def baseStart_4509363 : Nat := 118140960795 + 4509363 * 2 ^ 59
def prefixEnd_4509363 : Nat := 4983230072969 + 3 ^ 40 * 4509363 * 2
def baseEnd_4509363 : Nat := 2315470664600545830224323

theorem tailTrace_4509363 : CollatzResearch.WordTrace tailWord_4509363 prefixEnd_4509363 2315470664600545830224323 := by
  unfold tailWord_4509363
  simp only [CollatzResearch.WordTrace]
  refine ⟨164469980362355463731700743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109646653574903642487800495 164469980362355463731700743)
  ·
    refine ⟨246704970543533195597551115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164469980362355463731700743 246704970543533195597551115)
    ·
      refine ⟨370057455815299793396326673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 246704970543533195597551115 370057455815299793396326673)
      ·
        refine ⟨277543091861474845047245005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 370057455815299793396326673 277543091861474845047245005)
        ·
          refine ⟨104078659448053066892716877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 277543091861474845047245005 104078659448053066892716877)
          ·
            refine ⟨39029497293019900084768829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 104078659448053066892716877 39029497293019900084768829)
            ·
              refine ⟨14636061484882462531788311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39029497293019900084768829 14636061484882462531788311)
              ·
                refine ⟨21954092227323693797682467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14636061484882462531788311 21954092227323693797682467)
                ·
                  refine ⟨32931138340985540696523701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21954092227323693797682467 32931138340985540696523701)
                  ·
                    refine ⟨3087294219467394440299097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32931138340985540696523701 3087294219467394440299097)
                    ·
                      refine ⟨2315470664600545830224323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3087294219467394440299097 2315470664600545830224323)
                      ·
                        rfl

theorem cell23_4509363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 1, 1, 5, 2].length) (baseStart_4509363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4509363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4509363 prefixEnd_4509363 := by exact prefixLift 4509363
  have htrace : WordTrace (prefixWord ++ tailWord_4509363) baseStart_4509363 baseEnd_4509363 := by
    simpa [prefixWord, tailWord_4509363, baseEnd_4509363] using wordTrace_append hprefix tailTrace_4509363
  have hstable : (prefixWord ++ tailWord_4509363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4509363).length < 2 ^ (prefixWord ++ tailWord_4509363).sum := by decide
  have hdescent : baseEnd_4509363 < baseStart_4509363 := by decide
  rcases family_descends (prefixWord ++ tailWord_4509363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4509373 : List Nat := [1, 4, 1, 2, 1, 2, 3, 3, 1, 5]
def baseStart_4509373 : Nat := 118140960795 + 4509373 * 2 ^ 59
def prefixEnd_4509373 : Nat := 4983230072969 + 3 ^ 40 * 4509373 * 2
def baseEnd_4509373 : Nat := 771825266469030263699759

theorem tailTrace_4509373 : CollatzResearch.WordTrace tailWord_4509373 prefixEnd_4509373 771825266469030263699759 := by
  unfold tailWord_4509373
  simp only [CollatzResearch.WordTrace]
  refine ⟨164470345092319235439564773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109646896728212823626376515 164470345092319235439564773)
  ·
    refine ⟨30838189704809856644918395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 164470345092319235439564773 30838189704809856644918395)
    ·
      refine ⟨46257284557214784967377593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30838189704809856644918395 46257284557214784967377593)
      ·
        refine ⟨34692963417911088725533195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46257284557214784967377593 34692963417911088725533195)
        ·
          refine ⟨52039445126866633088299793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34692963417911088725533195 52039445126866633088299793)
          ·
            refine ⟨39029583845149974816224845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52039445126866633088299793 39029583845149974816224845)
            ·
              refine ⟨14636093941931240556084317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39029583845149974816224845 14636093941931240556084317)
              ·
                refine ⟨5488535228224215208531619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14636093941931240556084317 5488535228224215208531619)
                ·
                  refine ⟨8232802842336322812797429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5488535228224215208531619 8232802842336322812797429)
                  ·
                    refine ⟨771825266469030263699759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8232802842336322812797429 771825266469030263699759)
                    ·
                      rfl

theorem cell23_4509373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 3, 1, 5].length) (baseStart_4509373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4509373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4509373 prefixEnd_4509373 := by exact prefixLift 4509373
  have htrace : WordTrace (prefixWord ++ tailWord_4509373) baseStart_4509373 baseEnd_4509373 := by
    simpa [prefixWord, tailWord_4509373, baseEnd_4509373] using wordTrace_append hprefix tailTrace_4509373
  have hstable : (prefixWord ++ tailWord_4509373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4509373).length < 2 ^ (prefixWord ++ tailWord_4509373).sum := by decide
  have hdescent : baseEnd_4509373 < baseStart_4509373 := by decide
  rcases family_descends (prefixWord ++ tailWord_4509373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4509380 : List Nat := [2, 3, 3, 1, 1, 1, 2, 1, 4, 3, 2]
def baseStart_4509380 : Nat := 118140960795 + 4509380 * 2 ^ 59
def prefixEnd_4509380 : Nat := 4983230072969 + 3 ^ 40 * 4509380 * 2
def baseEnd_4509380 : Nat := 2315479393771672263711745

theorem tailTrace_4509380 : CollatzResearch.WordTrace tailWord_4509380 prefixEnd_4509380 2315479393771672263711745 := by
  unfold tailWord_4509380
  simp only [CollatzResearch.WordTrace]
  refine ⟨82235300201646937817534797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109647066935529250423379729 82235300201646937817534797)
  ·
    refine ⟨30838237575617601681575549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82235300201646937817534797 30838237575617601681575549)
    ·
      refine ⟨11564339090856600630590831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30838237575617601681575549 11564339090856600630590831)
      ·
        refine ⟨17346508636284900945886247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11564339090856600630590831 17346508636284900945886247)
        ·
          refine ⟨26019762954427351418829371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17346508636284900945886247 26019762954427351418829371)
          ·
            refine ⟨39029644431641027128244057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26019762954427351418829371 39029644431641027128244057)
            ·
              refine ⟨29272233323730770346183043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39029644431641027128244057 29272233323730770346183043)
              ·
                refine ⟨43908349985596155519274565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29272233323730770346183043 43908349985596155519274565)
                ·
                  refine ⟨8232815622299279159863981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43908349985596155519274565 8232815622299279159863981)
                  ·
                    refine ⟨3087305858362229684948993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8232815622299279159863981 3087305858362229684948993)
                    ·
                      refine ⟨2315479393771672263711745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3087305858362229684948993 2315479393771672263711745)
                      ·
                        rfl

theorem cell23_4509380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 1, 4, 3, 2].length) (baseStart_4509380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4509380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4509380 prefixEnd_4509380 := by exact prefixLift 4509380
  have htrace : WordTrace (prefixWord ++ tailWord_4509380) baseStart_4509380 baseEnd_4509380 := by
    simpa [prefixWord, tailWord_4509380, baseEnd_4509380] using wordTrace_append hprefix tailTrace_4509380
  have hstable : (prefixWord ++ tailWord_4509380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4509380).length < 2 ^ (prefixWord ++ tailWord_4509380).sum := by decide
  have hdescent : baseEnd_4509380 < baseStart_4509380 := by decide
  rcases family_descends (prefixWord ++ tailWord_4509380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4509430 : List Nat := [5, 1, 1, 1, 1, 4, 2, 1, 1, 1, 5]
def baseStart_4509430 : Nat := 118140960795 + 4509430 * 2 ^ 59
def prefixEnd_4509430 : Nat := 4983230072969 + 3 ^ 40 * 4509430 * 2
def baseEnd_4509430 : Nat := 2315505067804397068086515

theorem tailTrace_4509430 : CollatzResearch.WordTrace tailWord_4509430 prefixEnd_4509430 2315505067804397068086515 := by
  unfold tailWord_4509430
  simp only [CollatzResearch.WordTrace]
  refine ⟨10279526503319545885899359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 109648282702075156116259829 10279526503319545885899359)
  ·
    refine ⟨15419289754979318828849039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10279526503319545885899359 15419289754979318828849039)
    ·
      refine ⟨23128934632468978243273559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15419289754979318828849039 23128934632468978243273559)
      ·
        refine ⟨34693401948703467364910339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23128934632468978243273559 34693401948703467364910339)
        ·
          refine ⟨52040102923055201047365509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34693401948703467364910339 52040102923055201047365509)
          ·
            refine ⟨9757519298072850196381033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52040102923055201047365509 9757519298072850196381033)
            ·
              refine ⟨7318139473554637647285775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9757519298072850196381033 7318139473554637647285775)
              ·
                refine ⟨10977209210331956470928663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7318139473554637647285775 10977209210331956470928663)
                ·
                  refine ⟨16465813815497934706392995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10977209210331956470928663 16465813815497934706392995)
                  ·
                    refine ⟨24698720723246902059589493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16465813815497934706392995 24698720723246902059589493)
                    ·
                      refine ⟨2315505067804397068086515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24698720723246902059589493 2315505067804397068086515)
                      ·
                        rfl

theorem cell23_4509430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 2, 1, 1, 1, 5].length) (baseStart_4509430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4509430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4509430 prefixEnd_4509430 := by exact prefixLift 4509430
  have htrace : WordTrace (prefixWord ++ tailWord_4509430) baseStart_4509430 baseEnd_4509430 := by
    simpa [prefixWord, tailWord_4509430, baseEnd_4509430] using wordTrace_append hprefix tailTrace_4509430
  have hstable : (prefixWord ++ tailWord_4509430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4509430).length < 2 ^ (prefixWord ++ tailWord_4509430).sum := by decide
  have hdescent : baseEnd_4509430 < baseStart_4509430 := by decide
  rcases family_descends (prefixWord ++ tailWord_4509430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4509444 : List Nat := [2, 3, 2, 2, 1, 4, 1, 1, 3, 2, 2]
def baseStart_4509444 : Nat := 118140960795 + 4509444 * 2 ^ 59
def prefixEnd_4509444 : Nat := 4983230072969 + 3 ^ 40 * 4509444 * 2
def baseEnd_4509444 : Nat := 2315512256533560013311451

theorem tailTrace_4509444 : CollatzResearch.WordTrace tailWord_4509444 prefixEnd_4509444 2315512256533560013311451 := by
  unfold tailWord_4509444
  simp only [CollatzResearch.WordTrace]
  refine ⟨82236467337531007282699693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109648623116708009710266257 82236467337531007282699693)
  ·
    refine ⟨30838675251574127731012385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82236467337531007282699693 30838675251574127731012385)
    ·
      refine ⟨23129006438680595798259289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30838675251574127731012385 23129006438680595798259289)
      ·
        refine ⟨17346754829010446848694467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23129006438680595798259289 17346754829010446848694467)
        ·
          refine ⟨26020132243515670273041701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17346754829010446848694467 26020132243515670273041701)
          ·
            refine ⟨4878774795659188176195319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26020132243515670273041701 4878774795659188176195319)
            ·
              refine ⟨7318162193488782264292979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4878774795659188176195319 7318162193488782264292979)
              ·
                refine ⟨10977243290233173396439469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7318162193488782264292979 10977243290233173396439469)
                ·
                  refine ⟨4116466233837440023664801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10977243290233173396439469 4116466233837440023664801)
                  ·
                    refine ⟨3087349675378080017748601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4116466233837440023664801 3087349675378080017748601)
                    ·
                      refine ⟨2315512256533560013311451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3087349675378080017748601 2315512256533560013311451)
                      ·
                        rfl

theorem cell23_4509444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 1, 1, 3, 2, 2].length) (baseStart_4509444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4509444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4509444 prefixEnd_4509444 := by exact prefixLift 4509444
  have htrace : WordTrace (prefixWord ++ tailWord_4509444) baseStart_4509444 baseEnd_4509444 := by
    simpa [prefixWord, tailWord_4509444, baseEnd_4509444] using wordTrace_append hprefix tailTrace_4509444
  have hstable : (prefixWord ++ tailWord_4509444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4509444).length < 2 ^ (prefixWord ++ tailWord_4509444).sum := by decide
  have hdescent : baseEnd_4509444 < baseStart_4509444 := by decide
  rcases family_descends (prefixWord ++ tailWord_4509444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4509483 : List Nat := [1, 1, 1, 1, 2, 1, 2, 2, 2, 8, 2]
def baseStart_4509483 : Nat := 118140960795 + 4509483 * 2 ^ 59
def prefixEnd_4509483 : Nat := 4983230072969 + 3 ^ 40 * 4509483 * 2
def baseEnd_4509483 : Nat := 2315532282279085360723771

theorem tailTrace_4509483 : CollatzResearch.WordTrace tailWord_4509483 prefixEnd_4509483 2315532282279085360723771 := by
  unfold tailWord_4509483
  simp only [CollatzResearch.WordTrace]
  refine ⟨164474357121920724226069103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109649571414613816150712735 164474357121920724226069103)
  ·
    refine ⟨246711535682881086339103655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164474357121920724226069103 246711535682881086339103655)
    ·
      refine ⟨370067303524321629508655483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 246711535682881086339103655 370067303524321629508655483)
      ·
        refine ⟨555100955286482444262983225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 370067303524321629508655483 555100955286482444262983225)
        ·
          refine ⟨416325716464861833197237419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 555100955286482444262983225 416325716464861833197237419)
          ·
            refine ⟨624488574697292749795856129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 416325716464861833197237419 624488574697292749795856129)
            ·
              refine ⟨468366431022969562346892097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 624488574697292749795856129 468366431022969562346892097)
              ·
                refine ⟨351274823267227171760169073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 468366431022969562346892097 351274823267227171760169073)
                ·
                  refine ⟨263456117450420378820126805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 351274823267227171760169073 263456117450420378820126805)
                  ·
                    refine ⟨3087376376372113814298361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 263456117450420378820126805 3087376376372113814298361)
                    ·
                      refine ⟨2315532282279085360723771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3087376376372113814298361 2315532282279085360723771)
                      ·
                        rfl

theorem cell23_4509483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 8, 2].length) (baseStart_4509483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4509483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4509483 prefixEnd_4509483 := by exact prefixLift 4509483
  have htrace : WordTrace (prefixWord ++ tailWord_4509483) baseStart_4509483 baseEnd_4509483 := by
    simpa [prefixWord, tailWord_4509483, baseEnd_4509483] using wordTrace_append hprefix tailTrace_4509483
  have hstable : (prefixWord ++ tailWord_4509483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4509483).length < 2 ^ (prefixWord ++ tailWord_4509483).sum := by decide
  have hdescent : baseEnd_4509483 < baseStart_4509483 := by decide
  rcases family_descends (prefixWord ++ tailWord_4509483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4509494 : List Nat := [5, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3]
def baseStart_4509494 : Nat := 118140960795 + 4509494 * 2 ^ 59
def prefixEnd_4509494 : Nat := 4983230072969 + 3 ^ 40 * 4509494 * 2
def baseEnd_4509494 : Nat := 2315537930566284817686221

theorem tailTrace_4509494 : CollatzResearch.WordTrace tailWord_4509494 prefixEnd_4509494 2315537930566284817686221 := by
  unfold tailWord_4509494
  simp only [CollatzResearch.WordTrace]
  refine ⟨10279672395305054569044971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 109649838883253915403146357 10279672395305054569044971)
  ·
    refine ⟨15419508592957581853567457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10279672395305054569044971 15419508592957581853567457)
    ·
      refine ⟨11564631444718186390175593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15419508592957581853567457 11564631444718186390175593)
      ·
        refine ⟨8673473583538639792631695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11564631444718186390175593 8673473583538639792631695)
        ·
          refine ⟨13010210375307959688947543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8673473583538639792631695 13010210375307959688947543)
          ·
            refine ⟨19515315562961939533421315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13010210375307959688947543 19515315562961939533421315)
            ·
              refine ⟨29272973344442909300131973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19515315562961939533421315 29272973344442909300131973)
              ·
                refine ⟨5488682502083045493774745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29272973344442909300131973 5488682502083045493774745)
                ·
                  refine ⟨4116511876562284120331059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5488682502083045493774745 4116511876562284120331059)
                  ·
                    refine ⟨6174767814843426180496589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4116511876562284120331059 6174767814843426180496589)
                    ·
                      refine ⟨2315537930566284817686221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6174767814843426180496589 2315537930566284817686221)
                      ·
                        rfl

theorem cell23_4509494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_4509494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4509494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4509494 prefixEnd_4509494 := by exact prefixLift 4509494
  have htrace : WordTrace (prefixWord ++ tailWord_4509494) baseStart_4509494 baseEnd_4509494 := by
    simpa [prefixWord, tailWord_4509494, baseEnd_4509494] using wordTrace_append hprefix tailTrace_4509494
  have hstable : (prefixWord ++ tailWord_4509494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4509494).length < 2 ^ (prefixWord ++ tailWord_4509494).sum := by decide
  have hdescent : baseEnd_4509494 < baseStart_4509494 := by decide
  rcases family_descends (prefixWord ++ tailWord_4509494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4509513 : List Nat := [1, 2, 1, 1, 2, 4, 3, 1, 2, 2, 4]
def baseStart_4509513 : Nat := 118140960795 + 4509513 * 2 ^ 59
def prefixEnd_4509513 : Nat := 4983230072969 + 3 ^ 40 * 4509513 * 2
def baseEnd_4509513 : Nat := 2315547686698720243348633

theorem tailTrace_4509513 : CollatzResearch.WordTrace tailWord_4509513 prefixEnd_4509513 2315547686698720243348633 := by
  unfold tailWord_4509513
  simp only [CollatzResearch.WordTrace]
  refine ⟨164475451311812039349661193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109650300874541359566440795 164475451311812039349661193)
  ·
    refine ⟨123356588483859029512245895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164475451311812039349661193 123356588483859029512245895)
    ·
      refine ⟨185034882725788544268368843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123356588483859029512245895 185034882725788544268368843)
      ·
        refine ⟨277552324088682816402553265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185034882725788544268368843 277552324088682816402553265)
        ·
          refine ⟨208164243066512112301914949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 277552324088682816402553265 208164243066512112301914949)
          ·
            refine ⟨39030795574971021056609053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 208164243066512112301914949 39030795574971021056609053)
            ·
              refine ⟨14636548340614132896228395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39030795574971021056609053 14636548340614132896228395)
              ·
                refine ⟨21954822510921199344342593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14636548340614132896228395 21954822510921199344342593)
                ·
                  refine ⟨16466116883190899508256945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21954822510921199344342593 16466116883190899508256945)
                  ·
                    refine ⟨12349587662393174631192709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16466116883190899508256945 12349587662393174631192709)
                    ·
                      refine ⟨2315547686698720243348633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12349587662393174631192709 2315547686698720243348633)
                      ·
                        rfl

theorem cell23_4509513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 1, 2, 2, 4].length) (baseStart_4509513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4509513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4509513 prefixEnd_4509513 := by exact prefixLift 4509513
  have htrace : WordTrace (prefixWord ++ tailWord_4509513) baseStart_4509513 baseEnd_4509513 := by
    simpa [prefixWord, tailWord_4509513, baseEnd_4509513] using wordTrace_append hprefix tailTrace_4509513
  have hstable : (prefixWord ++ tailWord_4509513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4509513).length < 2 ^ (prefixWord ++ tailWord_4509513).sum := by decide
  have hdescent : baseEnd_4509513 < baseStart_4509513 := by decide
  rcases family_descends (prefixWord ++ tailWord_4509513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4509553 : List Nat := [1, 2, 2, 2, 1, 3, 2, 1, 4, 5]
def baseStart_4509553 : Nat := 118140960795 + 4509553 * 2 ^ 59
def prefixEnd_4509553 : Nat := 4983230072969 + 3 ^ 40 * 4509553 * 2
def baseEnd_4509553 : Nat := 771856075308300028949483

theorem tailTrace_4509553 : CollatzResearch.WordTrace tailWord_4509553 prefixEnd_4509553 771856075308300028949483 := by
  unfold tailWord_4509553
  simp only [CollatzResearch.WordTrace]
  refine ⟨164476910231667126181117313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109651273487778084120744875 164476910231667126181117313)
  ·
    refine ⟨123357682673750344635837985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164476910231667126181117313 123357682673750344635837985)
    ·
      refine ⟨92518262005312758476878489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123357682673750344635837985 92518262005312758476878489)
      ·
        refine ⟨69388696503984568857658867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92518262005312758476878489 69388696503984568857658867)
        ·
          refine ⟨104083044755976853286488301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69388696503984568857658867 104083044755976853286488301)
          ·
            refine ⟨39031141783491319982433113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 104083044755976853286488301 39031141783491319982433113)
            ·
              refine ⟨29273356337618489986824835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39031141783491319982433113 29273356337618489986824835)
              ·
                refine ⟨43910034506427734980237253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29273356337618489986824835 43910034506427734980237253)
                ·
                  refine ⟨8233131469955200308794485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43910034506427734980237253 8233131469955200308794485)
                  ·
                    refine ⟨771856075308300028949483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8233131469955200308794485 771856075308300028949483)
                    ·
                      rfl

theorem cell23_4509553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 1, 4, 5].length) (baseStart_4509553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4509553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4509553 prefixEnd_4509553 := by exact prefixLift 4509553
  have htrace : WordTrace (prefixWord ++ tailWord_4509553) baseStart_4509553 baseEnd_4509553 := by
    simpa [prefixWord, tailWord_4509553, baseEnd_4509553] using wordTrace_append hprefix tailTrace_4509553
  have hstable : (prefixWord ++ tailWord_4509553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4509553).length < 2 ^ (prefixWord ++ tailWord_4509553).sum := by decide
  have hdescent : baseEnd_4509553 < baseStart_4509553 := by decide
  rcases family_descends (prefixWord ++ tailWord_4509553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4509573 : List Nat := [1, 3, 1, 1, 3, 2, 1, 1, 3, 3, 4]
def baseStart_4509573 : Nat := 118140960795 + 4509573 * 2 ^ 59
def prefixEnd_4509573 : Nat := 4983230072969 + 3 ^ 40 * 4509573 * 2
def baseEnd_4509573 : Nat := 2315578495537990008598357

theorem tailTrace_4509573 : CollatzResearch.WordTrace tailWord_4509573 prefixEnd_4509573 2315578495537990008598357 := by
  unfold tailWord_4509573
  simp only [CollatzResearch.WordTrace]
  refine ⟨164477639691594669596845373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109651759794396446397896915 164477639691594669596845373)
  ·
    refine ⟨61679114884348001098817015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 164477639691594669596845373 61679114884348001098817015)
    ·
      refine ⟨92518672326522001648225523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61679114884348001098817015 92518672326522001648225523)
      ·
        refine ⟨138778008489783002472338285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92518672326522001648225523 138778008489783002472338285)
        ·
          refine ⟨52041753183668625927126857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 138778008489783002472338285 52041753183668625927126857)
          ·
            refine ⟨39031314887751469445345143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52041753183668625927126857 39031314887751469445345143)
            ·
              refine ⟨58546972331627204168017715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39031314887751469445345143 58546972331627204168017715)
              ·
                refine ⟨87820458497440806252026573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58546972331627204168017715 87820458497440806252026573)
                ·
                  refine ⟨32932671936540302344509965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 87820458497440806252026573 32932671936540302344509965)
                  ·
                    refine ⟨12349751976202613379191237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32932671936540302344509965 12349751976202613379191237)
                    ·
                      refine ⟨2315578495537990008598357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12349751976202613379191237 2315578495537990008598357)
                      ·
                        rfl

theorem cell23_4509573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 3, 3, 4].length) (baseStart_4509573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4509573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4509573 prefixEnd_4509573 := by exact prefixLift 4509573
  have htrace : WordTrace (prefixWord ++ tailWord_4509573) baseStart_4509573 baseEnd_4509573 := by
    simpa [prefixWord, tailWord_4509573, baseEnd_4509573] using wordTrace_append hprefix tailTrace_4509573
  have hstable : (prefixWord ++ tailWord_4509573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4509573).length < 2 ^ (prefixWord ++ tailWord_4509573).sum := by decide
  have hdescent : baseEnd_4509573 < baseStart_4509573 := by decide
  rcases family_descends (prefixWord ++ tailWord_4509573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4509607 : List Nat := [1, 1, 6, 1, 2, 2, 1, 2, 2, 1, 4]
def baseStart_4509607 : Nat := 118140960795 + 4509607 * 2 ^ 59
def prefixEnd_4509607 : Nat := 4983230072969 + 3 ^ 40 * 4509607 * 2
def baseEnd_4509607 : Nat := 2315595953880242875573201

theorem tailTrace_4509607 : CollatzResearch.WordTrace tailWord_4509607 prefixEnd_4509607 2315595953880242875573201 := by
  unfold tailWord_4509607
  simp only [CollatzResearch.WordTrace]
  refine ⟨164478879773471493403583075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109652586515647662269055383 164478879773471493403583075)
  ·
    refine ⟨246718319660207240105374613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164478879773471493403583075 246718319660207240105374613)
    ·
      refine ⟨11564921234072214379939435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 246718319660207240105374613 11564921234072214379939435)
      ·
        refine ⟨17347381851108321569909153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11564921234072214379939435 17347381851108321569909153)
        ·
          refine ⟨13010536388331241177431865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17347381851108321569909153 13010536388331241177431865)
          ·
            refine ⟨9757902291248430883073899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13010536388331241177431865 9757902291248430883073899)
            ·
              refine ⟨14636853436872646324610849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9757902291248430883073899 14636853436872646324610849)
              ·
                refine ⟨10977640077654484743458137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14636853436872646324610849 10977640077654484743458137)
                ·
                  refine ⟨8233230058240863557593603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10977640077654484743458137 8233230058240863557593603)
                  ·
                    refine ⟨12349845087361295336390405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8233230058240863557593603 12349845087361295336390405)
                    ·
                      refine ⟨2315595953880242875573201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12349845087361295336390405 2315595953880242875573201)
                      ·
                        rfl

theorem cell23_4509607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_4509607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4509607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4509607 prefixEnd_4509607 := by exact prefixLift 4509607
  have htrace : WordTrace (prefixWord ++ tailWord_4509607) baseStart_4509607 baseEnd_4509607 := by
    simpa [prefixWord, tailWord_4509607, baseEnd_4509607] using wordTrace_append hprefix tailTrace_4509607
  have hstable : (prefixWord ++ tailWord_4509607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4509607).length < 2 ^ (prefixWord ++ tailWord_4509607).sum := by decide
  have hdescent : baseEnd_4509607 < baseStart_4509607 := by decide
  rcases family_descends (prefixWord ++ tailWord_4509607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4509617 : List Nat := [1, 2, 2, 4, 2, 1, 3, 1, 3, 4]
def baseStart_4509617 : Nat := 118140960795 + 4509617 * 2 ^ 59
def prefixEnd_4509617 : Nat := 4983230072969 + 3 ^ 40 * 4509617 * 2
def baseEnd_4509617 : Nat := 771867029562262612149385

theorem tailTrace_4509617 : CollatzResearch.WordTrace tailWord_4509617 prefixEnd_4509617 771867029562262612149385 := by
  unfold tailWord_4509617
  simp only [CollatzResearch.WordTrace]
  refine ⟨164479244503435265111447105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109652829668956843407631403 164479244503435265111447105)
  ·
    refine ⟨123359433377576448833585329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164479244503435265111447105 123359433377576448833585329)
    ·
      refine ⟨92519575033182336625188997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123359433377576448833585329 92519575033182336625188997)
      ·
        refine ⟨17347420318721688117222937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 92519575033182336625188997 17347420318721688117222937)
        ·
          refine ⟨13010565239041266087917203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17347420318721688117222937 13010565239041266087917203)
          ·
            refine ⟨19515847858561899131875805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13010565239041266087917203 19515847858561899131875805)
            ·
              refine ⟨7318442946960712174453427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19515847858561899131875805 7318442946960712174453427)
              ·
                refine ⟨10977664420441068261680141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7318442946960712174453427 10977664420441068261680141)
                ·
                  refine ⟨4116624157665400598130053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10977664420441068261680141 4116624157665400598130053)
                  ·
                    refine ⟨771867029562262612149385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4116624157665400598130053 771867029562262612149385)
                    ·
                      rfl

theorem cell23_4509617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 3, 1, 3, 4].length) (baseStart_4509617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4509617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4509617 prefixEnd_4509617 := by exact prefixLift 4509617
  have htrace : WordTrace (prefixWord ++ tailWord_4509617) baseStart_4509617 baseEnd_4509617 := by
    simpa [prefixWord, tailWord_4509617, baseEnd_4509617] using wordTrace_append hprefix tailTrace_4509617
  have hstable : (prefixWord ++ tailWord_4509617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4509617).length < 2 ^ (prefixWord ++ tailWord_4509617).sum := by decide
  have hdescent : baseEnd_4509617 < baseStart_4509617 := by decide
  rcases family_descends (prefixWord ++ tailWord_4509617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4509680 : List Nat := [2, 1, 1, 1, 3, 2, 3, 2, 3, 1, 4]
def baseStart_4509680 : Nat := 118140960795 + 4509680 * 2 ^ 59
def prefixEnd_4509680 : Nat := 4983230072969 + 3 ^ 40 * 4509680 * 2
def baseEnd_4509680 : Nat := 2315633437968021089960365

theorem tailTrace_4509680 : CollatzResearch.WordTrace tailWord_4509680 prefixEnd_4509680 2315633437968021089960365 := by
  unfold tailWord_4509680
  simp only [CollatzResearch.WordTrace]
  refine ⟨82240771151103513435495247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109654361534804684580660329 82240771151103513435495247)
  ·
    refine ⟨123361156726655270153242871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82240771151103513435495247 123361156726655270153242871)
    ·
      refine ⟨185041735089982905229864307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123361156726655270153242871 185041735089982905229864307)
      ·
        refine ⟨277562602634974357844796461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185041735089982905229864307 277562602634974357844796461)
        ·
          refine ⟨104085975988115384191798673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 277562602634974357844796461 104085975988115384191798673)
          ·
            refine ⟨78064481991086538143849005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104085975988115384191798673 78064481991086538143849005)
            ·
              refine ⟨29274180746657451803943377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78064481991086538143849005 29274180746657451803943377)
              ·
                refine ⟨21955635559993088852957533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29274180746657451803943377 21955635559993088852957533)
                ·
                  refine ⟨8233363334997408319859075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21955635559993088852957533 8233363334997408319859075)
                  ·
                    refine ⟨12350045002496112479788613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8233363334997408319859075 12350045002496112479788613)
                    ·
                      refine ⟨2315633437968021089960365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12350045002496112479788613 2315633437968021089960365)
                      ·
                        rfl

theorem cell23_4509680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 2, 3, 1, 4].length) (baseStart_4509680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4509680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4509680 prefixEnd_4509680 := by exact prefixLift 4509680
  have htrace : WordTrace (prefixWord ++ tailWord_4509680) baseStart_4509680 baseEnd_4509680 := by
    simpa [prefixWord, tailWord_4509680, baseEnd_4509680] using wordTrace_append hprefix tailTrace_4509680
  have hstable : (prefixWord ++ tailWord_4509680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4509680).length < 2 ^ (prefixWord ++ tailWord_4509680).sum := by decide
  have hdescent : baseEnd_4509680 < baseStart_4509680 := by decide
  rcases family_descends (prefixWord ++ tailWord_4509680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4509690 : List Nat := [3, 1, 1, 1, 1, 2, 1, 1, 8, 4]
def baseStart_4509690 : Nat := 118140960795 + 4509690 * 2 ^ 59
def prefixEnd_4509690 : Nat := 4983230072969 + 3 ^ 40 * 4509690 * 2
def baseEnd_4509690 : Nat := 771879524258188683611773

theorem tailTrace_4509690 : CollatzResearch.WordTrace tailWord_4509690 prefixEnd_4509690 771879524258188683611773 := by
  unfold tailWord_4509690
  simp only [CollatzResearch.WordTrace]
  refine ⟨41120476758042699644713631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109654604688113865719236349 41120476758042699644713631)
  ·
    refine ⟨61680715137064049467070447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41120476758042699644713631 61680715137064049467070447)
    ·
      refine ⟨92521072705596074200605671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61680715137064049467070447 92521072705596074200605671)
      ·
        refine ⟨138781609058394111300908507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92521072705596074200605671 138781609058394111300908507)
        ·
          refine ⟨208172413587591166951362761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138781609058394111300908507 208172413587591166951362761)
          ·
            refine ⟨156129310190693375213522071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 208172413587591166951362761 156129310190693375213522071)
            ·
              refine ⟨234193965286040062820283107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 156129310190693375213522071 234193965286040062820283107)
              ·
                refine ⟨351290947929060094230424661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 234193965286040062820283107 351290947929060094230424661)
                ·
                  refine ⟨4116690796043672979262789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 351290947929060094230424661 4116690796043672979262789)
                  ·
                    refine ⟨771879524258188683611773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4116690796043672979262789 771879524258188683611773)
                    ·
                      rfl

theorem cell23_4509690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 8, 4].length) (baseStart_4509690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4509690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4509690 prefixEnd_4509690 := by exact prefixLift 4509690
  have htrace : WordTrace (prefixWord ++ tailWord_4509690) baseStart_4509690 baseEnd_4509690 := by
    simpa [prefixWord, tailWord_4509690, baseEnd_4509690] using wordTrace_append hprefix tailTrace_4509690
  have hstable : (prefixWord ++ tailWord_4509690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4509690).length < 2 ^ (prefixWord ++ tailWord_4509690).sum := by decide
  have hdescent : baseEnd_4509690 < baseStart_4509690 := by decide
  rcases family_descends (prefixWord ++ tailWord_4509690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4509697 : List Nat := [1, 2, 4, 1, 2, 1, 2, 4, 1, 1, 4]
def baseStart_4509697 : Nat := 118140960795 + 4509697 * 2 ^ 59
def prefixEnd_4509697 : Nat := 4983230072969 + 3 ^ 40 * 4509697 * 2
def baseEnd_4509697 : Nat := 2315642167139147523447787

theorem tailTrace_4509697 : CollatzResearch.WordTrace tailWord_4509697 prefixEnd_4509697 2315642167139147523447787 := by
  unfold tailWord_4509697
  simp only [CollatzResearch.WordTrace]
  refine ⟨164482162343145438774359345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109654774895430292516239563 164482162343145438774359345)
  ·
    refine ⟨123361621757359079080769509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164482162343145438774359345 123361621757359079080769509)
    ·
      refine ⟨23130304079504827327644283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 123361621757359079080769509 23130304079504827327644283)
      ·
        refine ⟨34695456119257240991466425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23130304079504827327644283 34695456119257240991466425)
        ·
          refine ⟨26021592089442930743599819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34695456119257240991466425 26021592089442930743599819)
          ·
            refine ⟨39032388134164396115399729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26021592089442930743599819 39032388134164396115399729)
            ·
              refine ⟨29274291100623297086549797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39032388134164396115399729 29274291100623297086549797)
              ·
                refine ⟨5488929581366868203728087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29274291100623297086549797 5488929581366868203728087)
                ·
                  refine ⟨8233394372050302305592131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5488929581366868203728087 8233394372050302305592131)
                  ·
                    refine ⟨12350091558075453458388197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8233394372050302305592131 12350091558075453458388197)
                    ·
                      refine ⟨2315642167139147523447787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12350091558075453458388197 2315642167139147523447787)
                      ·
                        rfl

theorem cell23_4509697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 4, 1, 1, 4].length) (baseStart_4509697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4509697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4509697 prefixEnd_4509697 := by exact prefixLift 4509697
  have htrace : WordTrace (prefixWord ++ tailWord_4509697) baseStart_4509697 baseEnd_4509697 := by
    simpa [prefixWord, tailWord_4509697, baseEnd_4509697] using wordTrace_append hprefix tailTrace_4509697
  have hstable : (prefixWord ++ tailWord_4509697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4509697).length < 2 ^ (prefixWord ++ tailWord_4509697).sum := by decide
  have hdescent : baseEnd_4509697 < baseStart_4509697 := by decide
  rcases family_descends (prefixWord ++ tailWord_4509697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4509702 : List Nat := [6, 2, 1, 2, 1, 1, 2, 3, 1, 4]
def baseStart_4509702 : Nat := 118140960795 + 4509702 * 2 ^ 59
def prefixEnd_4509702 : Nat := 4983230072969 + 3 ^ 40 * 4509702 * 2
def baseEnd_4509702 : Nat := 771881578180806667961755

theorem tailTrace_4509702 : CollatzResearch.WordTrace tailWord_4509702 prefixEnd_4509702 771881578180806667961755 := by
  unfold tailWord_4509702
  simp only [CollatzResearch.WordTrace]
  refine ⟨5140073272128978894634105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 109654896472084883085527573 5140073272128978894634105)
  ·
    refine ⟨3855054954096734170975579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5140073272128978894634105 3855054954096734170975579)
    ·
      refine ⟨5782582431145101256463369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3855054954096734170975579 5782582431145101256463369)
      ·
        refine ⟨4336936823358825942347527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5782582431145101256463369 4336936823358825942347527)
        ·
          refine ⟨6505405235038238913521291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4336936823358825942347527 6505405235038238913521291)
          ·
            refine ⟨9758107852557358370281937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6505405235038238913521291 9758107852557358370281937)
            ·
              refine ⟨7318580889418018777711453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9758107852557358370281937 7318580889418018777711453)
              ·
                refine ⟨2744467833531757041641795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7318580889418018777711453 2744467833531757041641795)
                ·
                  refine ⟨4116701750297635562462693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2744467833531757041641795 4116701750297635562462693)
                  ·
                    refine ⟨771881578180806667961755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4116701750297635562462693 771881578180806667961755)
                    ·
                      rfl

theorem cell23_4509702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_4509702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4509702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4509702 prefixEnd_4509702 := by exact prefixLift 4509702
  have htrace : WordTrace (prefixWord ++ tailWord_4509702) baseStart_4509702 baseEnd_4509702 := by
    simpa [prefixWord, tailWord_4509702, baseEnd_4509702] using wordTrace_append hprefix tailTrace_4509702
  have hstable : (prefixWord ++ tailWord_4509702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4509702).length < 2 ^ (prefixWord ++ tailWord_4509702).sum := by decide
  have hdescent : baseEnd_4509702 < baseStart_4509702 := by decide
  rcases family_descends (prefixWord ++ tailWord_4509702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4509724 : List Nat := [2, 2, 3, 1, 3, 1, 3, 2, 2, 4]
def baseStart_4509724 : Nat := 118140960795 + 4509724 * 2 ^ 59
def prefixEnd_4509724 : Nat := 4983230072969 + 3 ^ 40 * 4509724 * 2
def baseEnd_4509724 : Nat := 771885343705606305936721

theorem tailTrace_4509724 : CollatzResearch.WordTrace tailWord_4509724 prefixEnd_4509724 771885343705606305936721 := by
  unfold tailWord_4509724
  simp only [CollatzResearch.WordTrace]
  refine ⟨82241573557023811192796113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109655431409365081590394817 82241573557023811192796113)
  ·
    refine ⟨61681180167767858394597085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82241573557023811192796113 61681180167767858394597085)
    ·
      refine ⟨23130442562912946897973907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61681180167767858394597085 23130442562912946897973907)
      ·
        refine ⟨34695663844369420346960861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23130442562912946897973907 34695663844369420346960861)
        ·
          refine ⟨13010873941638532630110323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34695663844369420346960861 13010873941638532630110323)
          ·
            refine ⟨19516310912457798945165485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13010873941638532630110323 19516310912457798945165485)
            ·
              refine ⟨7318616592171674604437057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19516310912457798945165485 7318616592171674604437057)
              ·
                refine ⟨5488962444128755953327793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7318616592171674604437057 5488962444128755953327793)
                ·
                  refine ⟨4116721833096566964995845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5488962444128755953327793 4116721833096566964995845)
                  ·
                    refine ⟨771885343705606305936721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4116721833096566964995845 771885343705606305936721)
                    ·
                      rfl

theorem cell23_4509724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 3, 2, 2, 4].length) (baseStart_4509724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4509724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4509724 prefixEnd_4509724 := by exact prefixLift 4509724
  have htrace : WordTrace (prefixWord ++ tailWord_4509724) baseStart_4509724 baseEnd_4509724 := by
    simpa [prefixWord, tailWord_4509724, baseEnd_4509724] using wordTrace_append hprefix tailTrace_4509724
  have hstable : (prefixWord ++ tailWord_4509724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4509724).length < 2 ^ (prefixWord ++ tailWord_4509724).sum := by decide
  have hdescent : baseEnd_4509724 < baseStart_4509724 := by decide
  rcases family_descends (prefixWord ++ tailWord_4509724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4509731 : List Nat := [1, 1, 1, 4, 3, 1, 1, 6, 1, 2, 2]
def baseStart_4509731 : Nat := 118140960795 + 4509731 * 2 ^ 59
def prefixEnd_4509731 : Nat := 4983230072969 + 3 ^ 40 * 4509731 * 2
def baseEnd_4509731 : Nat := 2315659625481400390422631

theorem tailTrace_4509731 : CollatzResearch.WordTrace tailWord_4509731 prefixEnd_4509731 2315659625481400390422631 := by
  unfold tailWord_4509731
  simp only [CollatzResearch.WordTrace]
  refine ⟨164483402425022262581097047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109655601616681508387398031 164483402425022262581097047)
  ·
    refine ⟨246725103637533393871645571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164483402425022262581097047 246725103637533393871645571)
    ·
      refine ⟨370087655456300090807468357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 246725103637533393871645571 370087655456300090807468357)
      ·
        refine ⟨69391435398056267026400317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 370087655456300090807468357 69391435398056267026400317)
        ·
          refine ⟨26021788274271100134900119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69391435398056267026400317 26021788274271100134900119)
          ·
            refine ⟨39032682411406650202350179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26021788274271100134900119 39032682411406650202350179)
            ·
              refine ⟨58549023617109975303525269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39032682411406650202350179 58549023617109975303525269)
              ·
                refine ⟨2744485482052030092352747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 58549023617109975303525269 2744485482052030092352747)
                ·
                  refine ⟨4116728223078045138529121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2744485482052030092352747 4116728223078045138529121)
                  ·
                    refine ⟨3087546167308533853896841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4116728223078045138529121 3087546167308533853896841)
                    ·
                      refine ⟨2315659625481400390422631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3087546167308533853896841 2315659625481400390422631)
                      ·
                        rfl

theorem cell23_4509731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 6, 1, 2, 2].length) (baseStart_4509731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4509731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4509731 prefixEnd_4509731 := by exact prefixLift 4509731
  have htrace : WordTrace (prefixWord ++ tailWord_4509731) baseStart_4509731 baseEnd_4509731 := by
    simpa [prefixWord, tailWord_4509731, baseEnd_4509731] using wordTrace_append hprefix tailTrace_4509731
  have hstable : (prefixWord ++ tailWord_4509731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4509731).length < 2 ^ (prefixWord ++ tailWord_4509731).sum := by decide
  have hdescent : baseEnd_4509731 < baseStart_4509731 := by decide
  rcases family_descends (prefixWord ++ tailWord_4509731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4509747 : List Nat := [1, 1, 1, 2, 4, 1, 5, 1, 1, 3, 3]
def baseStart_4509747 : Nat := 118140960795 + 4509747 * 2 ^ 59
def prefixEnd_4509747 : Nat := 4983230072969 + 3 ^ 40 * 4509747 * 2
def baseEnd_4509747 : Nat := 2315667841171872327822557

theorem tailTrace_4509747 : CollatzResearch.WordTrace tailWord_4509747 prefixEnd_4509747 2315667841171872327822557 := by
  unfold tailWord_4509747
  simp only [CollatzResearch.WordTrace]
  refine ⟨164483985992964297313679495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109655990661976198209119663 164483985992964297313679495)
  ·
    refine ⟨246725978989446445970519243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164483985992964297313679495 246725978989446445970519243)
    ·
      refine ⟨370088968484169668955778865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 246725978989446445970519243 370088968484169668955778865)
      ·
        refine ⟨277566726363127251716834149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 370088968484169668955778865 277566726363127251716834149)
        ·
          refine ⟨52043761193086359696906403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 277566726363127251716834149 52043761193086359696906403)
          ·
            refine ⟨78065641789629539545359605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52043761193086359696906403 78065641789629539545359605)
            ·
              refine ⟨7318653917777769332377463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 78065641789629539545359605 7318653917777769332377463)
              ·
                refine ⟨10977980876666653998566195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7318653917777769332377463 10977980876666653998566195)
                ·
                  refine ⟨16466971314999980997849293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10977980876666653998566195 16466971314999980997849293)
                  ·
                    refine ⟨6175114243124992874193485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16466971314999980997849293 6175114243124992874193485)
                    ·
                      refine ⟨2315667841171872327822557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6175114243124992874193485 2315667841171872327822557)
                      ·
                        rfl

theorem cell23_4509747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 5, 1, 1, 3, 3].length) (baseStart_4509747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4509747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4509747 prefixEnd_4509747 := by exact prefixLift 4509747
  have htrace : WordTrace (prefixWord ++ tailWord_4509747) baseStart_4509747 baseEnd_4509747 := by
    simpa [prefixWord, tailWord_4509747, baseEnd_4509747] using wordTrace_append hprefix tailTrace_4509747
  have hstable : (prefixWord ++ tailWord_4509747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4509747).length < 2 ^ (prefixWord ++ tailWord_4509747).sum := by decide
  have hdescent : baseEnd_4509747 < baseStart_4509747 := by decide
  rcases family_descends (prefixWord ++ tailWord_4509747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4509760 : List Nat := [2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 5]
def baseStart_4509760 : Nat := 118140960795 + 4509760 * 2 ^ 59
def prefixEnd_4509760 : Nat := 4983230072969 + 3 ^ 40 * 4509760 * 2
def baseEnd_4509760 : Nat := 2315674516420380776959997

theorem tailTrace_4509760 : CollatzResearch.WordTrace tailWord_4509760 prefixEnd_4509760 2315674516420380776959997 := by
  unfold tailWord_4509760
  simp only [CollatzResearch.WordTrace]
  refine ⟨82242230070958600266951367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109656306761278133689268489 82242230070958600266951367)
  ·
    refine ⟨123363345106437900400427051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82242230070958600266951367 123363345106437900400427051)
    ·
      refine ⟨185045017659656850600640577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123363345106437900400427051 185045017659656850600640577)
      ·
        refine ⟨138783763244742637950480433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 185045017659656850600640577 138783763244742637950480433)
        ·
          refine ⟨104087822433556978462860325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 138783763244742637950480433 104087822433556978462860325)
          ·
            refine ⟨19516466706291933461786311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 104087822433556978462860325 19516466706291933461786311)
            ·
              refine ⟨29274700059437900192679467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19516466706291933461786311 29274700059437900192679467)
              ·
                refine ⟨43912050089156850289019201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29274700059437900192679467 43912050089156850289019201)
                ·
                  refine ⟨32934037566867637716764401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43912050089156850289019201 32934037566867637716764401)
                  ·
                    refine ⟨24700528175150728287573301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32934037566867637716764401 24700528175150728287573301)
                    ·
                      refine ⟨2315674516420380776959997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24700528175150728287573301 2315674516420380776959997)
                      ·
                        rfl

theorem cell23_4509760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 5].length) (baseStart_4509760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4509760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4509760 prefixEnd_4509760 := by exact prefixLift 4509760
  have htrace : WordTrace (prefixWord ++ tailWord_4509760) baseStart_4509760 baseEnd_4509760 := by
    simpa [prefixWord, tailWord_4509760, baseEnd_4509760] using wordTrace_append hprefix tailTrace_4509760
  have hstable : (prefixWord ++ tailWord_4509760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4509760).length < 2 ^ (prefixWord ++ tailWord_4509760).sum := by decide
  have hdescent : baseEnd_4509760 < baseStart_4509760 := by decide
  rcases family_descends (prefixWord ++ tailWord_4509760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4509770 : List Nat := [3, 1, 2, 1, 1, 2, 1, 2, 1, 5, 4]
def baseStart_4509770 : Nat := 118140960795 + 4509770 * 2 ^ 59
def prefixEnd_4509770 : Nat := 4983230072969 + 3 ^ 40 * 4509770 * 2
def baseEnd_4509770 : Nat := 2315679651226925737834951

theorem tailTrace_4509770 : CollatzResearch.WordTrace tailWord_4509770 prefixEnd_4509770 2315679651226925737834951 := by
  unfold tailWord_4509770
  simp only [CollatzResearch.WordTrace]
  refine ⟨41121206217970243060441691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109656549914587314827844509 41121206217970243060441691)
  ·
    refine ⟨61681809326955364590662537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41121206217970243060441691 61681809326955364590662537)
    ·
      refine ⟨46261356995216523442996903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61681809326955364590662537 46261356995216523442996903)
      ·
        refine ⟨69392035492824785164495355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46261356995216523442996903 69392035492824785164495355)
        ·
          refine ⟨104088053239237177746743033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69392035492824785164495355 104088053239237177746743033)
          ·
            refine ⟨78066039929427883310057275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104088053239237177746743033 78066039929427883310057275)
            ·
              refine ⟨117099059894141824965085913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78066039929427883310057275 117099059894141824965085913)
              ·
                refine ⟨87824294920606368723814435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 117099059894141824965085913 87824294920606368723814435)
                ·
                  refine ⟨131736442380909553085721653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 87824294920606368723814435 131736442380909553085721653)
                  ·
                    refine ⟨12350291473210270601786405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 131736442380909553085721653 12350291473210270601786405)
                    ·
                      refine ⟨2315679651226925737834951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12350291473210270601786405 2315679651226925737834951)
                      ·
                        rfl

theorem cell23_4509770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 1, 5, 4].length) (baseStart_4509770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4509770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4509770 prefixEnd_4509770 := by exact prefixLift 4509770
  have htrace : WordTrace (prefixWord ++ tailWord_4509770) baseStart_4509770 baseEnd_4509770 := by
    simpa [prefixWord, tailWord_4509770, baseEnd_4509770] using wordTrace_append hprefix tailTrace_4509770
  have hstable : (prefixWord ++ tailWord_4509770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4509770).length < 2 ^ (prefixWord ++ tailWord_4509770).sum := by decide
  have hdescent : baseEnd_4509770 < baseStart_4509770 := by decide
  rcases family_descends (prefixWord ++ tailWord_4509770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4509876 : List Nat := [2, 5, 3, 1, 2, 1, 2, 1, 1, 3, 2]
def baseStart_4509876 : Nat := 118140960795 + 4509876 * 2 ^ 59
def prefixEnd_4509876 : Nat := 4983230072969 + 3 ^ 40 * 4509876 * 2
def baseEnd_4509876 : Nat := 2315734080176302323109465

theorem tailTrace_4509876 : CollatzResearch.WordTrace tailWord_4509876 prefixEnd_4509876 2315734080176302323109465 := by
  unfold tailWord_4509876
  simp only [CollatzResearch.WordTrace]
  refine ⟨82244345504748476172562741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109659127339664634896750321 82244345504748476172562741)
  ·
    refine ⟨7710407391070169641177757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 82244345504748476172562741 7710407391070169641177757)
    ·
      refine ⟨2891402771651313615441659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7710407391070169641177757 2891402771651313615441659)
      ·
        refine ⟨4337104157476970423162489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2891402771651313615441659 4337104157476970423162489)
        ·
          refine ⟨3252828118107727817371867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4337104157476970423162489 3252828118107727817371867)
          ·
            refine ⟨4879242177161591726057801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3252828118107727817371867 4879242177161591726057801)
            ·
              refine ⟨3659431632871193794543351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4879242177161591726057801 3659431632871193794543351)
              ·
                refine ⟨5489147449306790691815027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3659431632871193794543351 5489147449306790691815027)
                ·
                  refine ⟨8233721173960186037722541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5489147449306790691815027 8233721173960186037722541)
                  ·
                    refine ⟨3087645440235069764145953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8233721173960186037722541 3087645440235069764145953)
                    ·
                      refine ⟨2315734080176302323109465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3087645440235069764145953 2315734080176302323109465)
                      ·
                        rfl

theorem cell23_4509876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_4509876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4509876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4509876 prefixEnd_4509876 := by exact prefixLift 4509876
  have htrace : WordTrace (prefixWord ++ tailWord_4509876) baseStart_4509876 baseEnd_4509876 := by
    simpa [prefixWord, tailWord_4509876, baseEnd_4509876] using wordTrace_append hprefix tailTrace_4509876
  have hstable : (prefixWord ++ tailWord_4509876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4509876).length < 2 ^ (prefixWord ++ tailWord_4509876).sum := by decide
  have hdescent : baseEnd_4509876 < baseStart_4509876 := by decide
  rcases family_descends (prefixWord ++ tailWord_4509876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4509887 : List Nat := [1, 1, 2, 2, 2, 2, 1, 1, 7, 4]
def baseStart_4509887 : Nat := 118140960795 + 4509887 * 2 ^ 59
def prefixEnd_4509887 : Nat := 4983230072969 + 3 ^ 40 * 4509887 * 2
def baseEnd_4509887 : Nat := 771913242821167260023971

theorem tailTrace_4509887 : CollatzResearch.WordTrace tailWord_4509887 prefixEnd_4509887 771913242821167260023971 := by
  unfold tailWord_4509887
  simp only [CollatzResearch.WordTrace]
  refine ⟨164489092212457101223775915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109659394808304734149183943 164489092212457101223775915)
  ·
    refine ⟨246733638318685651835663873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164489092212457101223775915 246733638318685651835663873)
    ·
      refine ⟨185050228739014238876747905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 246733638318685651835663873 185050228739014238876747905)
      ·
        refine ⟨138787671554260679157560929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 185050228739014238876747905 138787671554260679157560929)
        ·
          refine ⟨104090753665695509368170697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 138787671554260679157560929 104090753665695509368170697)
          ·
            refine ⟨78068065249271632026128023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104090753665695509368170697 78068065249271632026128023)
            ·
              refine ⟨117102097873907448039192035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78068065249271632026128023 117102097873907448039192035)
              ·
                refine ⟨175653146810861172058788053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 117102097873907448039192035 175653146810861172058788053)
                ·
                  refine ⟨4116870628379558720127845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 175653146810861172058788053 4116870628379558720127845)
                  ·
                    refine ⟨771913242821167260023971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4116870628379558720127845 771913242821167260023971)
                    ·
                      rfl

theorem cell23_4509887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 7, 4].length) (baseStart_4509887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4509887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4509887 prefixEnd_4509887 := by exact prefixLift 4509887
  have htrace : WordTrace (prefixWord ++ tailWord_4509887) baseStart_4509887 baseEnd_4509887 := by
    simpa [prefixWord, tailWord_4509887, baseEnd_4509887] using wordTrace_append hprefix tailTrace_4509887
  have hstable : (prefixWord ++ tailWord_4509887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4509887).length < 2 ^ (prefixWord ++ tailWord_4509887).sum := by decide
  have hdescent : baseEnd_4509887 < baseStart_4509887 := by decide
  rcases family_descends (prefixWord ++ tailWord_4509887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4509938 : List Nat := [3, 2, 1, 3, 2, 1, 3, 3, 1, 4]
def baseStart_4509938 : Nat := 118140960795 + 4509938 * 2 ^ 59
def prefixEnd_4509938 : Nat := 4983230072969 + 3 ^ 40 * 4509938 * 2
def baseEnd_4509938 : Nat := 771921971992293693511393

theorem tailTrace_4509938 : CollatzResearch.WordTrace tailWord_4509938 prefixEnd_4509938 771921971992293693511393 := by
  unfold tailWord_4509938
  simp only [CollatzResearch.WordTrace]
  refine ⟨41122738083818084233470617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109660634890181557955921645 41122738083818084233470617)
  ·
    refine ⟨30842053562863563175102963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41122738083818084233470617 30842053562863563175102963)
    ·
      refine ⟨46263080344295344762654445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30842053562863563175102963 46263080344295344762654445)
      ·
        refine ⟨17348655129110754285995417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46263080344295344762654445 17348655129110754285995417)
        ·
          refine ⟨13011491346833065714496563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17348655129110754285995417 13011491346833065714496563)
          ·
            refine ⟨19517237020249598571744845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13011491346833065714496563 19517237020249598571744845)
            ·
              refine ⟨7318963882593599464404317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19517237020249598571744845 7318963882593599464404317)
              ·
                refine ⟨2744611455972599799151619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7318963882593599464404317 2744611455972599799151619)
                ·
                  refine ⟨4116917183958899698727429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2744611455972599799151619 4116917183958899698727429)
                  ·
                    refine ⟨771921971992293693511393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4116917183958899698727429 771921971992293693511393)
                    ·
                      rfl

theorem cell23_4509938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 3, 3, 1, 4].length) (baseStart_4509938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4509938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4509938 prefixEnd_4509938 := by exact prefixLift 4509938
  have htrace : WordTrace (prefixWord ++ tailWord_4509938) baseStart_4509938 baseEnd_4509938 := by
    simpa [prefixWord, tailWord_4509938, baseEnd_4509938] using wordTrace_append hprefix tailTrace_4509938
  have hstable : (prefixWord ++ tailWord_4509938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4509938).length < 2 ^ (prefixWord ++ tailWord_4509938).sum := by decide
  have hdescent : baseEnd_4509938 < baseStart_4509938 := by decide
  rcases family_descends (prefixWord ++ tailWord_4509938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4509944 : List Nat := [2, 1, 2, 1, 1, 2, 1, 4, 5, 1, 3]
def baseStart_4509944 : Nat := 118140960795 + 4509944 * 2 ^ 59
def prefixEnd_4509944 : Nat := 4983230072969 + 3 ^ 40 * 4509944 * 2
def baseEnd_4509944 : Nat := 2315768996860808057059151

theorem tailTrace_4509944 : CollatzResearch.WordTrace tailWord_4509944 prefixEnd_4509944 2315768996860808057059151 := by
  unfold tailWord_4509944
  simp only [CollatzResearch.WordTrace]
  refine ⟨82245585586625299979300443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109660780782167066639067257 82245585586625299979300443)
  ·
    refine ⟨123368378379937949968950665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82245585586625299979300443 123368378379937949968950665)
    ·
      refine ⟨92526283784953462476712999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123368378379937949968950665 92526283784953462476712999)
      ·
        refine ⟨138789425677430193715069499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92526283784953462476712999 138789425677430193715069499)
        ·
          refine ⟨208184138516145290572604249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138789425677430193715069499 208184138516145290572604249)
          ·
            refine ⟨156138103887108967929453187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 208184138516145290572604249 156138103887108967929453187)
            ·
              refine ⟨234207155830663451894179781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 156138103887108967929453187 234207155830663451894179781)
              ·
                refine ⟨43913841718249397230158709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 234207155830663451894179781 43913841718249397230158709)
                ·
                  refine ⟨4116922661085880990327379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43913841718249397230158709 4116922661085880990327379)
                  ·
                    refine ⟨6175383991628821485491069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4116922661085880990327379 6175383991628821485491069)
                    ·
                      refine ⟨2315768996860808057059151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6175383991628821485491069 2315768996860808057059151)
                      ·
                        rfl

theorem cell23_4509944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 4, 5, 1, 3].length) (baseStart_4509944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4509944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4509944 prefixEnd_4509944 := by exact prefixLift 4509944
  have htrace : WordTrace (prefixWord ++ tailWord_4509944) baseStart_4509944 baseEnd_4509944 := by
    simpa [prefixWord, tailWord_4509944, baseEnd_4509944] using wordTrace_append hprefix tailTrace_4509944
  have hstable : (prefixWord ++ tailWord_4509944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4509944).length < 2 ^ (prefixWord ++ tailWord_4509944).sum := by decide
  have hdescent : baseEnd_4509944 < baseStart_4509944 := by decide
  rcases family_descends (prefixWord ++ tailWord_4509944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4509961 : List Nat := [1, 2, 1, 1, 3, 4, 3, 1, 3, 1, 3]
def baseStart_4509961 : Nat := 118140960795 + 4509961 * 2 ^ 59
def prefixEnd_4509961 : Nat := 4983230072969 + 3 ^ 40 * 4509961 * 2
def baseEnd_4509961 : Nat := 2315777726031934490546573

theorem tailTrace_4509961 : CollatzResearch.WordTrace tailWord_4509961 prefixEnd_4509961 2315777726031934490546573 := by
  unfold tailWord_4509961
  simp only [CollatzResearch.WordTrace]
  refine ⟨164491791214189011861969737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109661194142792674574646491 164491791214189011861969737)
  ·
    refine ⟨123368843410641758896477303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164491791214189011861969737 123368843410641758896477303)
    ·
      refine ⟨185053265115962638344715955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123368843410641758896477303 185053265115962638344715955)
      ·
        refine ⟨277579897673943957517073933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185053265115962638344715955 277579897673943957517073933)
        ·
          refine ⟨104092461627728984068902725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 277579897673943957517073933 104092461627728984068902725)
          ·
            refine ⟨19517336555199184512919261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 104092461627728984068902725 19517336555199184512919261)
            ·
              refine ⟨7319001208199694192344723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19517336555199184512919261 7319001208199694192344723)
              ·
                refine ⟨10978501812299541288517085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7319001208199694192344723 10978501812299541288517085)
                ·
                  refine ⟨4116938179612327983193907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10978501812299541288517085 4116938179612327983193907)
                  ·
                    refine ⟨6175407269418491974790861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4116938179612327983193907 6175407269418491974790861)
                    ·
                      refine ⟨2315777726031934490546573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6175407269418491974790861 2315777726031934490546573)
                      ·
                        rfl

theorem cell23_4509961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 3, 1, 3, 1, 3].length) (baseStart_4509961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4509961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4509961 prefixEnd_4509961 := by exact prefixLift 4509961
  have htrace : WordTrace (prefixWord ++ tailWord_4509961) baseStart_4509961 baseEnd_4509961 := by
    simpa [prefixWord, tailWord_4509961, baseEnd_4509961] using wordTrace_append hprefix tailTrace_4509961
  have hstable : (prefixWord ++ tailWord_4509961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4509961).length < 2 ^ (prefixWord ++ tailWord_4509961).sum := by decide
  have hdescent : baseEnd_4509961 < baseStart_4509961 := by decide
  rcases family_descends (prefixWord ++ tailWord_4509961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4509981 : List Nat := [1, 4, 2, 3, 2, 1, 1, 1, 3, 5]
def baseStart_4509981 : Nat := 118140960795 + 4509981 * 2 ^ 59
def prefixEnd_4509981 : Nat := 4983230072969 + 3 ^ 40 * 4509981 * 2
def baseEnd_4509981 : Nat := 771929331881674804098827

theorem tailTrace_4509981 : CollatzResearch.WordTrace tailWord_4509981 prefixEnd_4509981 771929331881674804098827 := by
  unfold tailWord_4509981
  simp only [CollatzResearch.WordTrace]
  refine ⟨164492520674116555277697797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109661680449411036851798531 164492520674116555277697797)
  ·
    refine ⟨30842347626396854114568337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 164492520674116555277697797 30842347626396854114568337)
    ·
      refine ⟨23131760719797640585926253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30842347626396854114568337 23131760719797640585926253)
      ·
        refine ⟨8674410269924115219722345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23131760719797640585926253 8674410269924115219722345)
        ·
          refine ⟨6505807702443086414791759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8674410269924115219722345 6505807702443086414791759)
          ·
            refine ⟨9758711553664629622187639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6505807702443086414791759 9758711553664629622187639)
            ·
              refine ⟨14638067330496944433281459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9758711553664629622187639 14638067330496944433281459)
              ·
                refine ⟨21957100995745416649922189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14638067330496944433281459 21957100995745416649922189)
                ·
                  refine ⟨8233912873404531243720821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21957100995745416649922189 8233912873404531243720821)
                  ·
                    refine ⟨771929331881674804098827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8233912873404531243720821 771929331881674804098827)
                    ·
                      rfl

theorem cell23_4509981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 1, 3, 5].length) (baseStart_4509981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4509981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4509981 prefixEnd_4509981 := by exact prefixLift 4509981
  have htrace : WordTrace (prefixWord ++ tailWord_4509981) baseStart_4509981 baseEnd_4509981 := by
    simpa [prefixWord, tailWord_4509981, baseEnd_4509981] using wordTrace_append hprefix tailTrace_4509981
  have hstable : (prefixWord ++ tailWord_4509981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4509981).length < 2 ^ (prefixWord ++ tailWord_4509981).sum := by decide
  have hdescent : baseEnd_4509981 < baseStart_4509981 := by decide
  rcases family_descends (prefixWord ++ tailWord_4509981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4509988 : List Nat := [2, 3, 1, 3, 1, 3, 2, 1, 2, 3, 2]
def baseStart_4509988 : Nat := 118140960795 + 4509988 * 2 ^ 59
def prefixEnd_4509988 : Nat := 4983230072969 + 3 ^ 40 * 4509988 * 2
def baseEnd_4509988 : Nat := 2315791590009605884908949

theorem tailTrace_4509988 : CollatzResearch.WordTrace tailWord_4509988 prefixEnd_4509988 2315791590009605884908949 := by
  unfold tailWord_4509988
  simp only [CollatzResearch.WordTrace]
  refine ⟨82246387992545597736601309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109661850656727463648801745 82246387992545597736601309)
  ·
    refine ⟨30842395497204599151225491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82246387992545597736601309 30842395497204599151225491)
    ·
      refine ⟨46263593245806898726838237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30842395497204599151225491 46263593245806898726838237)
      ·
        refine ⟨17348847467177587022564339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46263593245806898726838237 17348847467177587022564339)
        ·
          refine ⟨26023271200766380533846509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17348847467177587022564339 26023271200766380533846509)
          ·
            refine ⟨9758726700287392700192441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26023271200766380533846509 9758726700287392700192441)
            ·
              refine ⟨7319045025215544525144331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9758726700287392700192441 7319045025215544525144331)
              ·
                refine ⟨10978567537823316787716497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7319045025215544525144331 10978567537823316787716497)
                ·
                  refine ⟨8233925653367487590787373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10978567537823316787716497 8233925653367487590787373)
                  ·
                    refine ⟨3087722120012807846545265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8233925653367487590787373 3087722120012807846545265)
                    ·
                      refine ⟨2315791590009605884908949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3087722120012807846545265 2315791590009605884908949)
                      ·
                        rfl

theorem cell23_4509988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 2, 1, 2, 3, 2].length) (baseStart_4509988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4509988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4509988 prefixEnd_4509988 := by exact prefixLift 4509988
  have htrace : WordTrace (prefixWord ++ tailWord_4509988) baseStart_4509988 baseEnd_4509988 := by
    simpa [prefixWord, tailWord_4509988, baseEnd_4509988] using wordTrace_append hprefix tailTrace_4509988
  have hstable : (prefixWord ++ tailWord_4509988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4509988).length < 2 ^ (prefixWord ++ tailWord_4509988).sum := by decide
  have hdescent : baseEnd_4509988 < baseStart_4509988 := by decide
  rcases family_descends (prefixWord ++ tailWord_4509988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4510051 : List Nat := [1, 1, 1, 5, 2, 1, 2, 2, 4, 1, 3]
def baseStart_4510051 : Nat := 118140960795 + 4510051 * 2 ^ 59
def prefixEnd_4510051 : Nat := 4983230072969 + 3 ^ 40 * 4510051 * 2
def baseEnd_4510051 : Nat := 2315823939290839138421159

theorem tailTrace_4510051 : CollatzResearch.WordTrace tailWord_4510051 prefixEnd_4510051 2315823939290839138421159 := by
  unfold tailWord_4510051
  simp only [CollatzResearch.WordTrace]
  refine ⟨164495073783862957232746007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109663382522575304821830671 164495073783862957232746007)
  ·
    refine ⟨246742610675794435849119011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164495073783862957232746007 246742610675794435849119011)
    ·
      refine ⟨370113916013691653773678517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 246742610675794435849119011 370113916013691653773678517)
      ·
        refine ⟨34698179626283592541282361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 370113916013691653773678517 34698179626283592541282361)
        ·
          refine ⟨26023634719712694405961771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34698179626283592541282361 26023634719712694405961771)
          ·
            refine ⟨39035452079569041608942657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26023634719712694405961771 39035452079569041608942657)
            ·
              refine ⟨29276589059676781206706993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39035452079569041608942657 29276589059676781206706993)
              ·
                refine ⟨21957441794757585905030245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29276589059676781206706993 21957441794757585905030245)
                ·
                  refine ⟨4117020336517047357193171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21957441794757585905030245 4117020336517047357193171)
                  ·
                    refine ⟨6175530504775571035789757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4117020336517047357193171 6175530504775571035789757)
                    ·
                      refine ⟨2315823939290839138421159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6175530504775571035789757 2315823939290839138421159)
                      ·
                        rfl

theorem cell23_4510051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 2, 4, 1, 3].length) (baseStart_4510051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4510051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4510051 prefixEnd_4510051 := by exact prefixLift 4510051
  have htrace : WordTrace (prefixWord ++ tailWord_4510051) baseStart_4510051 baseEnd_4510051 := by
    simpa [prefixWord, tailWord_4510051, baseEnd_4510051] using wordTrace_append hprefix tailTrace_4510051
  have hstable : (prefixWord ++ tailWord_4510051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4510051).length < 2 ^ (prefixWord ++ tailWord_4510051).sum := by decide
  have hdescent : baseEnd_4510051 < baseStart_4510051 := by decide
  rcases family_descends (prefixWord ++ tailWord_4510051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4510055 : List Nat := [1, 1, 5, 1, 3, 3, 2, 1, 1, 2, 3]
def baseStart_4510055 : Nat := 118140960795 + 4510055 * 2 ^ 59
def prefixEnd_4510055 : Nat := 4983230072969 + 3 ^ 40 * 4510055 * 2
def baseEnd_4510055 : Nat := 2315825993213457122771141

theorem tailTrace_4510055 : CollatzResearch.WordTrace tailWord_4510055 prefixEnd_4510055 2315825993213457122771141 := by
  unfold tailWord_4510055
  simp only [CollatzResearch.WordTrace]
  refine ⟨164495219675848465915891619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109663479783898977277261079 164495219675848465915891619)
  ·
    refine ⟨246742829513772698873837429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164495219675848465915891619 246742829513772698873837429)
    ·
      refine ⟨23132140266916190519422259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 246742829513772698873837429 23132140266916190519422259)
      ·
        refine ⟨34698210400374285779133389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23132140266916190519422259 34698210400374285779133389)
        ·
          refine ⟨13011828900140357167175021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34698210400374285779133389 13011828900140357167175021)
          ·
            refine ⟨4879435837552633937690633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13011828900140357167175021 4879435837552633937690633)
            ·
              refine ⟨3659576878164475453267975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4879435837552633937690633 3659576878164475453267975)
              ·
                refine ⟨5489365317246713179901963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3659576878164475453267975 5489365317246713179901963)
                ·
                  refine ⟨8234047975870069769852945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5489365317246713179901963 8234047975870069769852945)
                  ·
                    refine ⟨6175535981902552327389709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8234047975870069769852945 6175535981902552327389709)
                    ·
                      refine ⟨2315825993213457122771141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6175535981902552327389709 2315825993213457122771141)
                      ·
                        rfl

theorem cell23_4510055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 2, 1, 1, 2, 3].length) (baseStart_4510055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4510055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4510055 prefixEnd_4510055 := by exact prefixLift 4510055
  have htrace : WordTrace (prefixWord ++ tailWord_4510055) baseStart_4510055 baseEnd_4510055 := by
    simpa [prefixWord, tailWord_4510055, baseEnd_4510055] using wordTrace_append hprefix tailTrace_4510055
  have hstable : (prefixWord ++ tailWord_4510055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4510055).length < 2 ^ (prefixWord ++ tailWord_4510055).sum := by decide
  have hdescent : baseEnd_4510055 < baseStart_4510055 := by decide
  rcases family_descends (prefixWord ++ tailWord_4510055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4510067 : List Nat := [1, 1, 1, 2, 2, 1, 2, 2, 3, 8]
def baseStart_4510067 : Nat := 118140960795 + 4510067 * 2 ^ 59
def prefixEnd_4510067 : Nat := 4983230072969 + 3 ^ 40 * 4510067 * 2
def baseEnd_4510067 : Nat := 771944051660437025273695

theorem tailTrace_4510067 : CollatzResearch.WordTrace tailWord_4510067 prefixEnd_4510067 771944051660437025273695 := by
  unfold tailWord_4510067
  simp only [CollatzResearch.WordTrace]
  refine ⟨164495657351804991965328455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109663771567869994643552303 164495657351804991965328455)
  ·
    refine ⟨246743486027707487947992683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164495657351804991965328455 246743486027707487947992683)
    ·
      refine ⟨370115229041561231921989025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 246743486027707487947992683 370115229041561231921989025)
      ·
        refine ⟨277586421781170923941491769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 370115229041561231921989025 277586421781170923941491769)
        ·
          refine ⟨208189816335878192956118827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 277586421781170923941491769 208189816335878192956118827)
          ·
            refine ⟨312284724503817289434178241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 208189816335878192956118827 312284724503817289434178241)
            ·
              refine ⟨234213543377862967075633681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 312284724503817289434178241 234213543377862967075633681)
              ·
                refine ⟨175660157533397225306725261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 234213543377862967075633681 175660157533397225306725261)
                ·
                  refine ⟨65872559075023959490021973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 175660157533397225306725261 65872559075023959490021973)
                  ·
                    refine ⟨771944051660437025273695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 65872559075023959490021973 771944051660437025273695)
                    ·
                      rfl

theorem cell23_4510067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 3, 8].length) (baseStart_4510067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4510067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4510067 prefixEnd_4510067 := by exact prefixLift 4510067
  have htrace : WordTrace (prefixWord ++ tailWord_4510067) baseStart_4510067 baseEnd_4510067 := by
    simpa [prefixWord, tailWord_4510067, baseEnd_4510067] using wordTrace_append hprefix tailTrace_4510067
  have hstable : (prefixWord ++ tailWord_4510067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4510067).length < 2 ^ (prefixWord ++ tailWord_4510067).sum := by decide
  have hdescent : baseEnd_4510067 < baseStart_4510067 := by decide
  rcases family_descends (prefixWord ++ tailWord_4510067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4510082 : List Nat := [3, 4, 2, 1, 3, 1, 1, 1, 1, 2, 4]
def baseStart_4510082 : Nat := 118140960795 + 4510082 * 2 ^ 59
def prefixEnd_4510082 : Nat := 4983230072969 + 3 ^ 40 * 4510082 * 2
def baseEnd_4510082 : Nat := 2315839857191128517133517

theorem tailTrace_4510082 : CollatzResearch.WordTrace tailWord_4510082 prefixEnd_4510082 2315839857191128517133517 := by
  unfold tailWord_4510082
  simp only [CollatzResearch.WordTrace]
  refine ⟨41124051111687662381781125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109664136297833766351416333 41124051111687662381781125)
  ·
    refine ⟨7710759583441436696583961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41124051111687662381781125 7710759583441436696583961)
    ·
      refine ⟨5783069687581077522437971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7710759583441436696583961 5783069687581077522437971)
      ·
        refine ⟨8674604531371616283656957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5783069687581077522437971 8674604531371616283656957)
        ·
          refine ⟨3252976699264356106371359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8674604531371616283656957 3252976699264356106371359)
          ·
            refine ⟨4879465048896534159557039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3252976699264356106371359 4879465048896534159557039)
            ·
              refine ⟨7319197573344801239335559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4879465048896534159557039 7319197573344801239335559)
              ·
                refine ⟨10978796360017201859003339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7319197573344801239335559 10978796360017201859003339)
                ·
                  refine ⟨16468194540025802788505009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10978796360017201859003339 16468194540025802788505009)
                  ·
                    refine ⟨12351145905019352091378757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16468194540025802788505009 12351145905019352091378757)
                    ·
                      refine ⟨2315839857191128517133517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12351145905019352091378757 2315839857191128517133517)
                      ·
                        rfl

theorem cell23_4510082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 1, 1, 1, 2, 4].length) (baseStart_4510082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4510082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4510082 prefixEnd_4510082 := by exact prefixLift 4510082
  have htrace : WordTrace (prefixWord ++ tailWord_4510082) baseStart_4510082 baseEnd_4510082 := by
    simpa [prefixWord, tailWord_4510082, baseEnd_4510082] using wordTrace_append hprefix tailTrace_4510082
  have hstable : (prefixWord ++ tailWord_4510082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4510082).length < 2 ^ (prefixWord ++ tailWord_4510082).sum := by decide
  have hdescent : baseEnd_4510082 < baseStart_4510082 := by decide
  rcases family_descends (prefixWord ++ tailWord_4510082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4510084 : List Nat := [2, 3, 2, 1, 1, 2, 1, 3, 2, 6]
def baseStart_4510084 : Nat := 118140960795 + 4510084 * 2 ^ 59
def prefixEnd_4510084 : Nat := 4983230072969 + 3 ^ 40 * 4510084 * 2
def baseEnd_4510084 : Nat := 771946961384145836436169

theorem tailTrace_4510084 : CollatzResearch.WordTrace tailWord_4510084 prefixEnd_4510084 771946961384145836436169 := by
  unfold tailWord_4510084
  simp only [CollatzResearch.WordTrace]
  refine ⟨82248138696371701934348653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109664184928495602579131537 82248138696371701934348653)
  ·
    refine ⟨30843052011139388225380745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82248138696371701934348653 30843052011139388225380745)
    ·
      refine ⟨23132289008354541169035559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30843052011139388225380745 23132289008354541169035559)
      ·
        refine ⟨34698433512531811753553339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23132289008354541169035559 34698433512531811753553339)
        ·
          refine ⟨52047650268797717630330009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34698433512531811753553339 52047650268797717630330009)
          ·
            refine ⟨39035737701598288222747507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52047650268797717630330009 39035737701598288222747507)
            ·
              refine ⟨58553606552397432334121261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39035737701598288222747507 58553606552397432334121261)
              ·
                refine ⟨21957602457149037125295473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58553606552397432334121261 21957602457149037125295473)
                ·
                  refine ⟨16468201842861777843971605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21957602457149037125295473 16468201842861777843971605)
                  ·
                    refine ⟨771946961384145836436169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16468201842861777843971605 771946961384145836436169)
                    ·
                      rfl

theorem cell23_4510084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 3, 2, 6].length) (baseStart_4510084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4510084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4510084 prefixEnd_4510084 := by exact prefixLift 4510084
  have htrace : WordTrace (prefixWord ++ tailWord_4510084) baseStart_4510084 baseEnd_4510084 := by
    simpa [prefixWord, tailWord_4510084, baseEnd_4510084] using wordTrace_append hprefix tailTrace_4510084
  have hstable : (prefixWord ++ tailWord_4510084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4510084).length < 2 ^ (prefixWord ++ tailWord_4510084).sum := by decide
  have hdescent : baseEnd_4510084 < baseStart_4510084 := by decide
  rcases family_descends (prefixWord ++ tailWord_4510084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4510142 : List Nat := [4, 2, 1, 1, 1, 1, 6, 1, 2, 2, 2]
def baseStart_4510142 : Nat := 118140960795 + 4510142 * 2 ^ 59
def prefixEnd_4510142 : Nat := 4983230072969 + 3 ^ 40 * 4510142 * 2
def baseEnd_4510142 : Nat := 2315870666030398282383241

theorem tailTrace_4510142 : CollatzResearch.WordTrace tailWord_4510142 prefixEnd_4510142 2315870666030398282383241 := by
  unfold tailWord_4510142
  simp only [CollatzResearch.WordTrace]
  refine ⟨20562299103316659971788585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109665595217688853182872453 20562299103316659971788585)
  ·
    refine ⟨15421724327487494978841439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20562299103316659971788585 15421724327487494978841439)
    ·
      refine ⟨23132586491231242468262159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15421724327487494978841439 23132586491231242468262159)
      ·
        refine ⟨34698879736846863702393239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23132586491231242468262159 34698879736846863702393239)
        ·
          refine ⟨52048319605270295553589859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34698879736846863702393239 52048319605270295553589859)
          ·
            refine ⟨78072479407905443330384789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52048319605270295553589859 78072479407905443330384789)
            ·
              refine ⟨3659647472245567656111787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 78072479407905443330384789 3659647472245567656111787)
              ·
                refine ⟨5489471208368351484167681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3659647472245567656111787 5489471208368351484167681)
                ·
                  refine ⟨4117103406276263613125761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5489471208368351484167681 4117103406276263613125761)
                  ·
                    refine ⟨3087827554707197709844321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4117103406276263613125761 3087827554707197709844321)
                    ·
                      refine ⟨2315870666030398282383241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3087827554707197709844321 2315870666030398282383241)
                      ·
                        rfl

theorem cell23_4510142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 6, 1, 2, 2, 2].length) (baseStart_4510142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4510142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4510142 prefixEnd_4510142 := by exact prefixLift 4510142
  have htrace : WordTrace (prefixWord ++ tailWord_4510142) baseStart_4510142 baseEnd_4510142 := by
    simpa [prefixWord, tailWord_4510142, baseEnd_4510142] using wordTrace_append hprefix tailTrace_4510142
  have hstable : (prefixWord ++ tailWord_4510142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4510142).length < 2 ^ (prefixWord ++ tailWord_4510142).sum := by decide
  have hdescent : baseEnd_4510142 < baseStart_4510142 := by decide
  rcases family_descends (prefixWord ++ tailWord_4510142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4510144 : List Nat := [2, 1, 1, 2, 3, 1, 1, 1, 6, 5]
def baseStart_4510144 : Nat := 118140960795 + 4510144 * 2 ^ 59
def prefixEnd_4510144 : Nat := 4983230072969 + 3 ^ 40 * 4510144 * 2
def baseEnd_4510144 : Nat := 771957230997235758186077

theorem tailTrace_4510144 : CollatzResearch.WordTrace tailWord_4510144 prefixEnd_4510144 771957230997235758186077 := by
  unfold tailWord_4510144
  simp only [CollatzResearch.WordTrace]
  refine ⟨82249232886263017057940743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109665643848350689410587657 82249232886263017057940743)
  ·
    refine ⟨123373849329394525586911115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82249232886263017057940743 123373849329394525586911115)
    ·
      refine ⟨185060773994091788380366673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123373849329394525586911115 185060773994091788380366673)
      ·
        refine ⟨138795580495568841285275005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 185060773994091788380366673 138795580495568841285275005)
        ·
          refine ⟨52048342685838315481978127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 138795580495568841285275005 52048342685838315481978127)
          ·
            refine ⟨78072514028757473222967191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52048342685838315481978127 78072514028757473222967191)
            ·
              refine ⟨117108771043136209834450787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78072514028757473222967191 117108771043136209834450787)
              ·
                refine ⟨175663156564704314751676181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 117108771043136209834450787 175663156564704314751676181)
                ·
                  refine ⟨8234210463970514753984821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 175663156564704314751676181 8234210463970514753984821)
                  ·
                    refine ⟨771957230997235758186077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8234210463970514753984821 771957230997235758186077)
                    ·
                      rfl

theorem cell23_4510144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 6, 5].length) (baseStart_4510144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4510144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4510144 prefixEnd_4510144 := by exact prefixLift 4510144
  have htrace : WordTrace (prefixWord ++ tailWord_4510144) baseStart_4510144 baseEnd_4510144 := by
    simpa [prefixWord, tailWord_4510144, baseEnd_4510144] using wordTrace_append hprefix tailTrace_4510144
  have hstable : (prefixWord ++ tailWord_4510144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4510144).length < 2 ^ (prefixWord ++ tailWord_4510144).sum := by decide
  have hdescent : baseEnd_4510144 < baseStart_4510144 := by decide
  rcases family_descends (prefixWord ++ tailWord_4510144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4510154 : List Nat := [3, 1, 2, 1, 2, 2, 1, 2, 1, 1, 7]
def baseStart_4510154 : Nat := 118140960795 + 4510154 * 2 ^ 59
def prefixEnd_4510154 : Nat := 4983230072969 + 3 ^ 40 * 4510154 * 2
def baseEnd_4510154 : Nat := 2315876827798252235433185

theorem tailTrace_4510154 : CollatzResearch.WordTrace tailWord_4510154 prefixEnd_4510154 2315876827798252235433185 := by
  unfold tailWord_4510154
  simp only [CollatzResearch.WordTrace]
  refine ⟨41124707625622451455936379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109665887001659870549163677 41124707625622451455936379)
  ·
    refine ⟨61687061438433677183904569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41124707625622451455936379 61687061438433677183904569)
    ·
      refine ⟨46265296078825257887928427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61687061438433677183904569 46265296078825257887928427)
      ·
        refine ⟨69397944118237886831892641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46265296078825257887928427 69397944118237886831892641)
        ·
          refine ⟨52048458088678415123919481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69397944118237886831892641 52048458088678415123919481)
          ·
            refine ⟨39036343566508811342939611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52048458088678415123919481 39036343566508811342939611)
            ·
              refine ⟨58554515349763217014409417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39036343566508811342939611 58554515349763217014409417)
              ·
                refine ⟨43915886512322412760807063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58554515349763217014409417 43915886512322412760807063)
                ·
                  refine ⟨65873829768483619141210595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43915886512322412760807063 65873829768483619141210595)
                  ·
                    refine ⟨98810744652725428711815893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 65873829768483619141210595 98810744652725428711815893)
                    ·
                      refine ⟨2315876827798252235433185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 98810744652725428711815893 2315876827798252235433185)
                      ·
                        rfl

theorem cell23_4510154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 2, 1, 1, 7].length) (baseStart_4510154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4510154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4510154 prefixEnd_4510154 := by exact prefixLift 4510154
  have htrace : WordTrace (prefixWord ++ tailWord_4510154) baseStart_4510154 baseEnd_4510154 := by
    simpa [prefixWord, tailWord_4510154, baseEnd_4510154] using wordTrace_append hprefix tailTrace_4510154
  have hstable : (prefixWord ++ tailWord_4510154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4510154).length < 2 ^ (prefixWord ++ tailWord_4510154).sum := by decide
  have hdescent : baseEnd_4510154 < baseStart_4510154 := by decide
  rcases family_descends (prefixWord ++ tailWord_4510154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4510191 : List Nat := [1, 1, 2, 1, 4, 1, 1, 5, 3, 4]
def baseStart_4510191 : Nat := 118140960795 + 4510191 * 2 ^ 59
def prefixEnd_4510191 : Nat := 4983230072969 + 3 ^ 40 * 4510191 * 2
def baseEnd_4510191 : Nat := 771965275527489530223505

theorem tailTrace_4510191 : CollatzResearch.WordTrace tailWord_4510191 prefixEnd_4510191 771965275527489530223505 := by
  unfold tailWord_4510191
  simp only [CollatzResearch.WordTrace]
  refine ⟨164500180003355761142842427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109666786668903840761894951 164500180003355761142842427)
  ·
    refine ⟨246750270005033641714263641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164500180003355761142842427 246750270005033641714263641)
    ·
      refine ⟨185062702503775231285697731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 246750270005033641714263641 185062702503775231285697731)
      ·
        refine ⟨277594053755662846928546597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185062702503775231285697731 277594053755662846928546597)
        ·
          refine ⟨52048885079186783799102487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 277594053755662846928546597 52048885079186783799102487)
          ·
            refine ⟨78073327618780175698653731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52048885079186783799102487 78073327618780175698653731)
            ·
              refine ⟨117109991428170263547980597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78073327618780175698653731 117109991428170263547980597)
              ·
                refine ⟨10979061696390962207623181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 117109991428170263547980597 10979061696390962207623181)
                ·
                  refine ⟨4117148136146610827858693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10979061696390962207623181 4117148136146610827858693)
                  ·
                    refine ⟨771965275527489530223505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4117148136146610827858693 771965275527489530223505)
                    ·
                      rfl

theorem cell23_4510191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 5, 3, 4].length) (baseStart_4510191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4510191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4510191 prefixEnd_4510191 := by exact prefixLift 4510191
  have htrace : WordTrace (prefixWord ++ tailWord_4510191) baseStart_4510191 baseEnd_4510191 := by
    simpa [prefixWord, tailWord_4510191, baseEnd_4510191] using wordTrace_append hprefix tailTrace_4510191
  have hstable : (prefixWord ++ tailWord_4510191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4510191).length < 2 ^ (prefixWord ++ tailWord_4510191).sum := by decide
  have hdescent : baseEnd_4510191 < baseStart_4510191 := by decide
  rcases family_descends (prefixWord ++ tailWord_4510191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4510201 : List Nat := [1, 2, 1, 3, 1, 2, 2, 2, 4, 2, 3]
def baseStart_4510201 : Nat := 118140960795 + 4510201 * 2 ^ 59
def prefixEnd_4510201 : Nat := 4983230072969 + 3 ^ 40 * 4510201 * 2
def baseEnd_4510201 : Nat := 2315900961389013551545469

theorem tailTrace_4510201 : CollatzResearch.WordTrace tailWord_4510201 prefixEnd_4510201 2315900961389013551545469 := by
  unfold tailWord_4510201
  simp only [CollatzResearch.WordTrace]
  refine ⟨164500544733319532850706457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109667029822213021900470971 164500544733319532850706457)
  ·
    refine ⟨123375408549989649638029843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164500544733319532850706457 123375408549989649638029843)
    ·
      refine ⟨185063112824984474457044765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123375408549989649638029843 185063112824984474457044765)
      ·
        refine ⟨69398667309369177921391787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 185063112824984474457044765 69398667309369177921391787)
        ·
          refine ⟨104098000964053766882087681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69398667309369177921391787 104098000964053766882087681)
          ·
            refine ⟨78073500723040325161565761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104098000964053766882087681 78073500723040325161565761)
            ·
              refine ⟨58555125542280243871174321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78073500723040325161565761 58555125542280243871174321)
              ·
                refine ⟨43916344156710182903380741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58555125542280243871174321 43916344156710182903380741)
                ·
                  refine ⟨8234314529383159294383889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43916344156710182903380741 8234314529383159294383889)
                  ·
                    refine ⟨6175735897037369470787917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8234314529383159294383889 6175735897037369470787917)
                    ·
                      refine ⟨2315900961389013551545469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6175735897037369470787917 2315900961389013551545469)
                      ·
                        rfl

theorem cell23_4510201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 2, 4, 2, 3].length) (baseStart_4510201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4510201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4510201 prefixEnd_4510201 := by exact prefixLift 4510201
  have htrace : WordTrace (prefixWord ++ tailWord_4510201) baseStart_4510201 baseEnd_4510201 := by
    simpa [prefixWord, tailWord_4510201, baseEnd_4510201] using wordTrace_append hprefix tailTrace_4510201
  have hstable : (prefixWord ++ tailWord_4510201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4510201).length < 2 ^ (prefixWord ++ tailWord_4510201).sum := by decide
  have hdescent : baseEnd_4510201 < baseStart_4510201 := by decide
  rcases family_descends (prefixWord ++ tailWord_4510201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4510204 : List Nat := [2, 2, 2, 1, 2, 1, 1, 2, 10]
def baseStart_4510204 : Nat := 118140960795 + 4510204 * 2 ^ 59
def prefixEnd_4510204 : Nat := 4983230072969 + 3 ^ 40 * 4510204 * 2
def baseEnd_4510204 : Nat := 257322500203441893311995

theorem tailTrace_4510204 : CollatzResearch.WordTrace tailWord_4510204 prefixEnd_4510204 257322500203441893311995 := by
  unfold tailWord_4510204
  simp only [CollatzResearch.WordTrace]
  refine ⟨82250327076154332181532833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109667102768205776242043777 82250327076154332181532833)
  ·
    refine ⟨61687745307115749136149625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82250327076154332181532833 61687745307115749136149625)
    ·
      refine ⟨46265808980336811852112219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61687745307115749136149625 46265808980336811852112219)
      ·
        refine ⟨69398713470505217778168329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46265808980336811852112219 69398713470505217778168329)
        ·
          refine ⟨52049035102878913333626247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69398713470505217778168329 52049035102878913333626247)
          ·
            refine ⟨78073552654318370000439371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52049035102878913333626247 78073552654318370000439371)
            ·
              refine ⟨117110328981477555000659057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78073552654318370000439371 117110328981477555000659057)
              ·
                refine ⟨87832746736108166250494293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 117110328981477555000659057 87832746736108166250494293)
                ·
                  refine ⟨257322500203441893311995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 87832746736108166250494293 257322500203441893311995)
                  ·
                    rfl

theorem cell23_4510204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 10].length) (baseStart_4510204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4510204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4510204 prefixEnd_4510204 := by exact prefixLift 4510204
  have htrace : WordTrace (prefixWord ++ tailWord_4510204) baseStart_4510204 baseEnd_4510204 := by
    simpa [prefixWord, tailWord_4510204, baseEnd_4510204] using wordTrace_append hprefix tailTrace_4510204
  have hstable : (prefixWord ++ tailWord_4510204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4510204).length < 2 ^ (prefixWord ++ tailWord_4510204).sum := by decide
  have hdescent : baseEnd_4510204 < baseStart_4510204 := by decide
  rcases family_descends (prefixWord ++ tailWord_4510204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4510215 : List Nat := [1, 1, 4, 3, 3, 2, 1, 1, 2, 1, 4]
def baseStart_4510215 : Nat := 118140960795 + 4510215 * 2 ^ 59
def prefixEnd_4510215 : Nat := 4983230072969 + 3 ^ 40 * 4510215 * 2
def baseEnd_4510215 : Nat := 2315908150118176496770405

theorem tailTrace_4510215 : CollatzResearch.WordTrace tailWord_4510215 prefixEnd_4510215 2315908150118176496770405 := by
  unfold tailWord_4510215
  simp only [CollatzResearch.WordTrace]
  refine ⟨164501055355268813241716099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109667370236845875494477399 164501055355268813241716099)
  ·
    refine ⟨246751583032903219862574149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164501055355268813241716099 246751583032903219862574149)
    ·
      refine ⟨46265921818669353724232653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 246751583032903219862574149 46265921818669353724232653)
      ·
        refine ⟨17349720682001007646587245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46265921818669353724232653 17349720682001007646587245)
        ·
          refine ⟨6506145255750377867470217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17349720682001007646587245 6506145255750377867470217)
          ·
            refine ⟨4879608941812783400602663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6506145255750377867470217 4879608941812783400602663)
            ·
              refine ⟨7319413412719175100903995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4879608941812783400602663 7319413412719175100903995)
              ·
                refine ⟨10979120119078762651355993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7319413412719175100903995 10979120119078762651355993)
                ·
                  refine ⟨8234340089309071988516995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10979120119078762651355993 8234340089309071988516995)
                  ·
                    refine ⟨12351510133963607982775493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8234340089309071988516995 12351510133963607982775493)
                    ·
                      refine ⟨2315908150118176496770405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12351510133963607982775493 2315908150118176496770405)
                      ·
                        rfl

theorem cell23_4510215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 1, 1, 2, 1, 4].length) (baseStart_4510215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4510215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4510215 prefixEnd_4510215 := by exact prefixLift 4510215
  have htrace : WordTrace (prefixWord ++ tailWord_4510215) baseStart_4510215 baseEnd_4510215 := by
    simpa [prefixWord, tailWord_4510215, baseEnd_4510215] using wordTrace_append hprefix tailTrace_4510215
  have hstable : (prefixWord ++ tailWord_4510215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4510215).length < 2 ^ (prefixWord ++ tailWord_4510215).sum := by decide
  have hdescent : baseEnd_4510215 < baseStart_4510215 := by decide
  rcases family_descends (prefixWord ++ tailWord_4510215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4510228 : List Nat := [2, 4, 3, 1, 1, 1, 1, 1, 2, 1, 6]
def baseStart_4510228 : Nat := 118140960795 + 4510228 * 2 ^ 59
def prefixEnd_4510228 : Nat := 4983230072969 + 3 ^ 40 * 4510228 * 2
def baseEnd_4510228 : Nat := 2315914825366684945907845

theorem tailTrace_4510228 : CollatzResearch.WordTrace tailWord_4510228 prefixEnd_4510228 2315914825366684945907845 := by
  unfold tailWord_4510228
  simp only [CollatzResearch.WordTrace]
  refine ⟨82250764752110858230969669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109667686336147810974626225 82250764752110858230969669)
  ·
    refine ⟨15422018391020785918306813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82250764752110858230969669 15422018391020785918306813)
    ·
      refine ⟨5783256896632794719365055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15422018391020785918306813 5783256896632794719365055)
      ·
        refine ⟨8674885344949192079047583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5783256896632794719365055 8674885344949192079047583)
        ·
          refine ⟨13012328017423788118571375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8674885344949192079047583 13012328017423788118571375)
          ·
            refine ⟨19518492026135682177857063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13012328017423788118571375 19518492026135682177857063)
            ·
              refine ⟨29277738039203523266785595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19518492026135682177857063 29277738039203523266785595)
              ·
                refine ⟨43916607058805284900178393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29277738039203523266785595 43916607058805284900178393)
                ·
                  refine ⟨32937455294103963675133795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43916607058805284900178393 32937455294103963675133795)
                  ·
                    refine ⟨49406182941155945512700693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32937455294103963675133795 49406182941155945512700693)
                    ·
                      refine ⟨2315914825366684945907845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49406182941155945512700693 2315914825366684945907845)
                      ·
                        rfl

theorem cell23_4510228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_4510228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4510228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4510228 prefixEnd_4510228 := by exact prefixLift 4510228
  have htrace : WordTrace (prefixWord ++ tailWord_4510228) baseStart_4510228 baseEnd_4510228 := by
    simpa [prefixWord, tailWord_4510228, baseEnd_4510228] using wordTrace_append hprefix tailTrace_4510228
  have hstable : (prefixWord ++ tailWord_4510228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4510228).length < 2 ^ (prefixWord ++ tailWord_4510228).sum := by decide
  have hdescent : baseEnd_4510228 < baseStart_4510228 := by decide
  rcases family_descends (prefixWord ++ tailWord_4510228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4510258 : List Nat := [3, 2, 1, 1, 2, 1, 3, 2, 1, 5, 2]
def baseStart_4510258 : Nat := 118140960795 + 4510258 * 2 ^ 59
def prefixEnd_4510258 : Nat := 4983230072969 + 3 ^ 40 * 4510258 * 2
def baseEnd_4510258 : Nat := 2315930229786319828532707

theorem tailTrace_4510258 : CollatzResearch.WordTrace tailWord_4510258 prefixEnd_4510258 2315930229786319828532707 := by
  unfold tailWord_4510258
  simp only [CollatzResearch.WordTrace]
  refine ⟨41125655923528257896382857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109668415796075354390354285 41125655923528257896382857)
  ·
    refine ⟨30844241942646193422287143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41125655923528257896382857 30844241942646193422287143)
    ·
      refine ⟨46266362913969290133430715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30844241942646193422287143 46266362913969290133430715)
      ·
        refine ⟨69399544370953935200146073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46266362913969290133430715 69399544370953935200146073)
        ·
          refine ⟨52049658278215451400109555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69399544370953935200146073 52049658278215451400109555)
          ·
            refine ⟨78074487417323177100164333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52049658278215451400109555 78074487417323177100164333)
            ·
              refine ⟨29277932781496191412561625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78074487417323177100164333 29277932781496191412561625)
              ·
                refine ⟨21958449586122143559421219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29277932781496191412561625 21958449586122143559421219)
                ·
                  refine ⟨32937674379183215339131829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21958449586122143559421219 32937674379183215339131829)
                  ·
                    refine ⟨3087906973048426438043609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32937674379183215339131829 3087906973048426438043609)
                    ·
                      refine ⟨2315930229786319828532707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3087906973048426438043609 2315930229786319828532707)
                      ·
                        rfl

theorem cell23_4510258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 2, 1, 5, 2].length) (baseStart_4510258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4510258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4510258 prefixEnd_4510258 := by exact prefixLift 4510258
  have htrace : WordTrace (prefixWord ++ tailWord_4510258) baseStart_4510258 baseEnd_4510258 := by
    simpa [prefixWord, tailWord_4510258, baseEnd_4510258] using wordTrace_append hprefix tailTrace_4510258
  have hstable : (prefixWord ++ tailWord_4510258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4510258).length < 2 ^ (prefixWord ++ tailWord_4510258).sum := by decide
  have hdescent : baseEnd_4510258 < baseStart_4510258 := by decide
  rcases family_descends (prefixWord ++ tailWord_4510258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4510268 : List Nat := [2, 2, 2, 2, 3, 1, 1, 4, 1, 5]
def baseStart_4510268 : Nat := 118140960795 + 4510268 * 2 ^ 59
def prefixEnd_4510268 : Nat := 4983230072969 + 3 ^ 40 * 4510268 * 2
def baseEnd_4510268 : Nat := 771978454864288263135887

theorem tailTrace_4510268 : CollatzResearch.WordTrace tailWord_4510268 prefixEnd_4510268 771978454864288263135887 := by
  unfold tailWord_4510268
  simp only [CollatzResearch.WordTrace]
  refine ⟨82251494212038401646697729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109668658949384535528930305 82251494212038401646697729)
  ·
    refine ⟨61688620659028801235023297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82251494212038401646697729 61688620659028801235023297)
    ·
      refine ⟨46266465494271600926267473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61688620659028801235023297 46266465494271600926267473)
      ·
        refine ⟨34699849120703700694700605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46266465494271600926267473 34699849120703700694700605)
        ·
          refine ⟨13012443420263887760512727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34699849120703700694700605 13012443420263887760512727)
          ·
            refine ⟨19518665130395831640769091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13012443420263887760512727 19518665130395831640769091)
            ·
              refine ⟨29277997695593747461153637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19518665130395831640769091 29277997695593747461153637)
              ·
                refine ⟨5489624567923827648966307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29277997695593747461153637 5489624567923827648966307)
                ·
                  refine ⟨8234436851885741473449461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5489624567923827648966307 8234436851885741473449461)
                  ·
                    refine ⟨771978454864288263135887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8234436851885741473449461 771978454864288263135887)
                    ·
                      rfl

theorem cell23_4510268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 4, 1, 5].length) (baseStart_4510268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4510268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4510268 prefixEnd_4510268 := by exact prefixLift 4510268
  have htrace : WordTrace (prefixWord ++ tailWord_4510268) baseStart_4510268 baseEnd_4510268 := by
    simpa [prefixWord, tailWord_4510268, baseEnd_4510268] using wordTrace_append hprefix tailTrace_4510268
  have hstable : (prefixWord ++ tailWord_4510268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4510268).length < 2 ^ (prefixWord ++ tailWord_4510268).sum := by decide
  have hdescent : baseEnd_4510268 < baseStart_4510268 := by decide
  rcases family_descends (prefixWord ++ tailWord_4510268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4510282 : List Nat := [3, 1, 2, 1, 1, 4, 3, 3, 1, 1, 3]
def baseStart_4510282 : Nat := 118140960795 + 4510282 * 2 ^ 59
def prefixEnd_4510282 : Nat := 4983230072969 + 3 ^ 40 * 4510282 * 2
def baseEnd_4510282 : Nat := 2315942553322027734632597

theorem tailTrace_4510282 : CollatzResearch.WordTrace tailWord_4510282 prefixEnd_4510282 2315942553322027734632597 := by
  unfold tailWord_4510282
  simp only [CollatzResearch.WordTrace]
  refine ⟨41125874761506520921101275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109668999364017389122936733 41125874761506520921101275)
  ·
    refine ⟨61688812142259781381651913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41125874761506520921101275 61688812142259781381651913)
    ·
      refine ⟨46266609106694836036238935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61688812142259781381651913 46266609106694836036238935)
      ·
        refine ⟨69399913660042254054358403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46266609106694836036238935 69399913660042254054358403)
        ·
          refine ⟨104099870490063381081537605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69399913660042254054358403 104099870490063381081537605)
          ·
            refine ⟨19518725716886883952788301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 104099870490063381081537605 19518725716886883952788301)
            ·
              refine ⟨7319522143832581482295613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19518725716886883952788301 7319522143832581482295613)
              ·
                refine ⟨2744820803937218055860855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7319522143832581482295613 2744820803937218055860855)
                ·
                  refine ⟨4117231205905827083791283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2744820803937218055860855 4117231205905827083791283)
                  ·
                    refine ⟨6175846808858740625686925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4117231205905827083791283 6175846808858740625686925)
                    ·
                      refine ⟨2315942553322027734632597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6175846808858740625686925 2315942553322027734632597)
                      ·
                        rfl

theorem cell23_4510282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 3, 3, 1, 1, 3].length) (baseStart_4510282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4510282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4510282 prefixEnd_4510282 := by exact prefixLift 4510282
  have htrace : WordTrace (prefixWord ++ tailWord_4510282) baseStart_4510282 baseEnd_4510282 := by
    simpa [prefixWord, tailWord_4510282, baseEnd_4510282] using wordTrace_append hprefix tailTrace_4510282
  have hstable : (prefixWord ++ tailWord_4510282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4510282).length < 2 ^ (prefixWord ++ tailWord_4510282).sum := by decide
  have hdescent : baseEnd_4510282 < baseStart_4510282 := by decide
  rcases family_descends (prefixWord ++ tailWord_4510282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4510285 : List Nat := [1, 6, 1, 1, 2, 1, 2, 3, 1, 5]
def baseStart_4510285 : Nat := 118140960795 + 4510285 * 2 ^ 59
def prefixEnd_4510285 : Nat := 4983230072969 + 3 ^ 40 * 4510285 * 2
def baseEnd_4510285 : Nat := 771981364587997074298361

theorem tailTrace_4510285 : CollatzResearch.WordTrace tailWord_4510285 prefixEnd_4510285 771981364587997074298361 := by
  unfold tailWord_4510285
  simp only [CollatzResearch.WordTrace]
  refine ⟨164503608465015215196764309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109669072310010143464509539 164503608465015215196764309)
  ·
    refine ⟨7711106646797588212348327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 164503608465015215196764309 7711106646797588212348327)
    ·
      refine ⟨11566659970196382318522491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7711106646797588212348327 11566659970196382318522491)
      ·
        refine ⟨17349989955294573477783737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11566659970196382318522491 17349989955294573477783737)
        ·
          refine ⟨13012492466470930108337803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17349989955294573477783737 13012492466470930108337803)
          ·
            refine ⟨19518738699706395162506705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13012492466470930108337803 19518738699706395162506705)
            ·
              refine ⟨14639054024779796371880029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19518738699706395162506705 14639054024779796371880029)
              ·
                refine ⟨5489645259292423639455011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14639054024779796371880029 5489645259292423639455011)
                ·
                  refine ⟨8234467888938635459182517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5489645259292423639455011 8234467888938635459182517)
                  ·
                    refine ⟨771981364587997074298361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8234467888938635459182517 771981364587997074298361)
                    ·
                      rfl

theorem cell23_4510285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 3, 1, 5].length) (baseStart_4510285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4510285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4510285 prefixEnd_4510285 := by exact prefixLift 4510285
  have htrace : WordTrace (prefixWord ++ tailWord_4510285) baseStart_4510285 baseEnd_4510285 := by
    simpa [prefixWord, tailWord_4510285, baseEnd_4510285] using wordTrace_append hprefix tailTrace_4510285
  have hstable : (prefixWord ++ tailWord_4510285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4510285).length < 2 ^ (prefixWord ++ tailWord_4510285).sum := by decide
  have hdescent : baseEnd_4510285 < baseStart_4510285 := by decide
  rcases family_descends (prefixWord ++ tailWord_4510285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4510308 : List Nat := [2, 3, 1, 1, 2, 2, 2, 2, 3, 2, 3]
def baseStart_4510308 : Nat := 118140960795 + 4510308 * 2 ^ 59
def prefixEnd_4510308 : Nat := 4983230072969 + 3 ^ 40 * 4510308 * 2
def baseEnd_4510308 : Nat := 2315955903819044632907477

theorem tailTrace_4510308 : CollatzResearch.WordTrace tailWord_4510308 prefixEnd_4510308 2315955903819044632907477 := by
  unfold tailWord_4510308
  simp only [CollatzResearch.WordTrace]
  refine ⟨82252223671965945062425789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109669631562621260083234385 82252223671965945062425789)
  ·
    refine ⟨30844583876987229398409671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82252223671965945062425789 30844583876987229398409671)
    ·
      refine ⟨46266875815480844097614507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30844583876987229398409671 46266875815480844097614507)
      ·
        refine ⟨69400313723221266146421761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46266875815480844097614507 69400313723221266146421761)
        ·
          refine ⟨52050235292415949609816321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69400313723221266146421761 52050235292415949609816321)
          ·
            refine ⟨39037676469311962207362241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52050235292415949609816321 39037676469311962207362241)
            ·
              refine ⟨29278257351983971655521681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39037676469311962207362241 29278257351983971655521681)
              ·
                refine ⟨21958693013987978741641261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29278257351983971655521681 21958693013987978741641261)
                ·
                  refine ⟨8234509880245492028115473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21958693013987978741641261 8234509880245492028115473)
                  ·
                    refine ⟨6175882410184119021086605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8234509880245492028115473 6175882410184119021086605)
                    ·
                      refine ⟨2315955903819044632907477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6175882410184119021086605 2315955903819044632907477)
                      ·
                        rfl

theorem cell23_4510308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 2, 3, 2, 3].length) (baseStart_4510308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4510308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4510308 prefixEnd_4510308 := by exact prefixLift 4510308
  have htrace : WordTrace (prefixWord ++ tailWord_4510308) baseStart_4510308 baseEnd_4510308 := by
    simpa [prefixWord, tailWord_4510308, baseEnd_4510308] using wordTrace_append hprefix tailTrace_4510308
  have hstable : (prefixWord ++ tailWord_4510308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4510308).length < 2 ^ (prefixWord ++ tailWord_4510308).sum := by decide
  have hdescent : baseEnd_4510308 < baseStart_4510308 := by decide
  rcases family_descends (prefixWord ++ tailWord_4510308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4510318 : List Nat := [4, 1, 2, 2, 2, 1, 2, 1, 1, 1, 6]
def baseStart_4510318 : Nat := 118140960795 + 4510318 * 2 ^ 59
def prefixEnd_4510318 : Nat := 4983230072969 + 3 ^ 40 * 4510318 * 2
def baseEnd_4510318 : Nat := 2315961038625589593782431

theorem tailTrace_4510318 : CollatzResearch.WordTrace tailWord_4510318 prefixEnd_4510318 2315961038625589593782431 := by
  unfold tailWord_4510318
  simp only [CollatzResearch.WordTrace]
  refine ⟨20563101509236957729089451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109669874715930441221810405 20563101509236957729089451)
  ·
    refine ⟨30844652263855436593634177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20563101509236957729089451 30844652263855436593634177)
    ·
      refine ⟨23133489197891577445225633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30844652263855436593634177 23133489197891577445225633)
      ·
        refine ⟨17350116898418683083919225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23133489197891577445225633 17350116898418683083919225)
        ·
          refine ⟨13012587673814012312939419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17350116898418683083919225 13012587673814012312939419)
          ·
            refine ⟨19518881510721018469409129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13012587673814012312939419 19518881510721018469409129)
            ·
              refine ⟨14639161133040763852056847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19518881510721018469409129 14639161133040763852056847)
              ·
                refine ⟨21958741699561145778085271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14639161133040763852056847 21958741699561145778085271)
                ·
                  refine ⟨32938112549341718667127907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21958741699561145778085271 32938112549341718667127907)
                  ·
                    refine ⟨49407168824012578000691861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32938112549341718667127907 49407168824012578000691861)
                    ·
                      refine ⟨2315961038625589593782431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49407168824012578000691861 2315961038625589593782431)
                      ·
                        rfl

theorem cell23_4510318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_4510318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4510318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4510318 prefixEnd_4510318 := by exact prefixLift 4510318
  have htrace : WordTrace (prefixWord ++ tailWord_4510318) baseStart_4510318 baseEnd_4510318 := by
    simpa [prefixWord, tailWord_4510318, baseEnd_4510318] using wordTrace_append hprefix tailTrace_4510318
  have hstable : (prefixWord ++ tailWord_4510318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4510318).length < 2 ^ (prefixWord ++ tailWord_4510318).sum := by decide
  have hdescent : baseEnd_4510318 < baseStart_4510318 := by decide
  rcases family_descends (prefixWord ++ tailWord_4510318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4510322 : List Nat := [3, 2, 1, 2, 4, 2, 1, 2, 1, 1, 4]
def baseStart_4510322 : Nat := 118140960795 + 4510322 * 2 ^ 59
def prefixEnd_4510322 : Nat := 4983230072969 + 3 ^ 40 * 4510322 * 2
def baseEnd_4510322 : Nat := 2315963092548207578132413

theorem tailTrace_4510322 : CollatzResearch.WordTrace tailWord_4510322 prefixEnd_4510322 2315963092548207578132413 := by
  unfold tailWord_4510322
  simp only [CollatzResearch.WordTrace]
  refine ⟨41126239491470292628965305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109669971977254113677240813 41126239491470292628965305)
  ·
    refine ⟨30844679618602719471723979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41126239491470292628965305 30844679618602719471723979)
    ·
      refine ⟨46267019427904079207585969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30844679618602719471723979 46267019427904079207585969)
      ·
        refine ⟨34700264570928059405689477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46267019427904079207585969 34700264570928059405689477)
        ·
          refine ⟨6506299607049011138566777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34700264570928059405689477 6506299607049011138566777)
          ·
            refine ⟨4879724705286758353925083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6506299607049011138566777 4879724705286758353925083)
            ·
              refine ⟨7319587057930137530887625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4879724705286758353925083 7319587057930137530887625)
              ·
                refine ⟨5489690293447603148165719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7319587057930137530887625 5489690293447603148165719)
                ·
                  refine ⟨8234535440171404722248579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5489690293447603148165719 8234535440171404722248579)
                  ·
                    refine ⟨12351803160257107083372869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8234535440171404722248579 12351803160257107083372869)
                    ·
                      refine ⟨2315963092548207578132413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12351803160257107083372869 2315963092548207578132413)
                      ·
                        rfl

theorem cell23_4510322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 1, 2, 1, 1, 4].length) (baseStart_4510322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4510322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4510322 prefixEnd_4510322 := by exact prefixLift 4510322
  have htrace : WordTrace (prefixWord ++ tailWord_4510322) baseStart_4510322 baseEnd_4510322 := by
    simpa [prefixWord, tailWord_4510322, baseEnd_4510322] using wordTrace_append hprefix tailTrace_4510322
  have hstable : (prefixWord ++ tailWord_4510322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4510322).length < 2 ^ (prefixWord ++ tailWord_4510322).sum := by decide
  have hdescent : baseEnd_4510322 < baseStart_4510322 := by decide
  rcases family_descends (prefixWord ++ tailWord_4510322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4510356 : List Nat := [2, 4, 2, 2, 1, 2, 1, 4, 1, 2, 2]
def baseStart_4510356 : Nat := 118140960795 + 4510356 * 2 ^ 59
def prefixEnd_4510356 : Nat := 4983230072969 + 3 ^ 40 * 4510356 * 2
def baseEnd_4510356 : Nat := 2315980550890460445107257

theorem tailTrace_4510356 : CollatzResearch.WordTrace tailWord_4510356 prefixEnd_4510356 2315980550890460445107257 := by
  unfold tailWord_4510356
  simp only [CollatzResearch.WordTrace]
  refine ⟨82253099023878997161299461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109670798698505329548399281 82253099023878997161299461)
  ·
    refine ⟨15422456066977311967743649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82253099023878997161299461 15422456066977311967743649)
    ·
      refine ⟨11566842050232983975807737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15422456066977311967743649 11566842050232983975807737)
      ·
        refine ⟨8675131537674737981855803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11566842050232983975807737 8675131537674737981855803)
        ·
          refine ⟨13012697306512106972783705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8675131537674737981855803 13012697306512106972783705)
          ·
            refine ⟨9759522979884080229587779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13012697306512106972783705 9759522979884080229587779)
            ·
              refine ⟨14639284469826120344381669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9759522979884080229587779 14639284469826120344381669)
              ·
                refine ⟨2744865838092397564571563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14639284469826120344381669 2744865838092397564571563)
                ·
                  refine ⟨4117298757138596346857345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2744865838092397564571563 4117298757138596346857345)
                  ·
                    refine ⟨3087974067853947260143009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4117298757138596346857345 3087974067853947260143009)
                    ·
                      refine ⟨2315980550890460445107257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3087974067853947260143009 2315980550890460445107257)
                      ·
                        rfl

theorem cell23_4510356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 4, 1, 2, 2].length) (baseStart_4510356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4510356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4510356 prefixEnd_4510356 := by exact prefixLift 4510356
  have htrace : WordTrace (prefixWord ++ tailWord_4510356) baseStart_4510356 baseEnd_4510356 := by
    simpa [prefixWord, tailWord_4510356, baseEnd_4510356] using wordTrace_append hprefix tailTrace_4510356
  have hstable : (prefixWord ++ tailWord_4510356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4510356).length < 2 ^ (prefixWord ++ tailWord_4510356).sum := by decide
  have hdescent : baseEnd_4510356 < baseStart_4510356 := by decide
  rcases family_descends (prefixWord ++ tailWord_4510356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4510361 : List Nat := [1, 2, 1, 2, 1, 2, 3, 1, 1, 5, 4]
def baseStart_4510361 : Nat := 118140960795 + 4510361 * 2 ^ 59
def prefixEnd_4510361 : Nat := 4983230072969 + 3 ^ 40 * 4510361 * 2
def baseEnd_4510361 : Nat := 2315983118293732925544733

theorem tailTrace_4510361 : CollatzResearch.WordTrace tailWord_4510361 prefixEnd_4510361 2315983118293732925544733 := by
  unfold tailWord_4510361
  simp only [CollatzResearch.WordTrace]
  refine ⟨164506380412739880176530937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109670920275159920117687291 164506380412739880176530937)
  ·
    refine ⟨123379785309554910132398203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164506380412739880176530937 123379785309554910132398203)
    ·
      refine ⟨185069677964332365198597305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123379785309554910132398203 185069677964332365198597305)
      ·
        refine ⟨138802258473249273898947979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 185069677964332365198597305 138802258473249273898947979)
        ·
          refine ⟨208203387709873910848421969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138802258473249273898947979 208203387709873910848421969)
          ·
            refine ⟨156152540782405433136316477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 208203387709873910848421969 156152540782405433136316477)
            ·
              refine ⟨58557202793402037426118679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 156152540782405433136316477 58557202793402037426118679)
              ·
                refine ⟨87835804190103056139178019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58557202793402037426118679 87835804190103056139178019)
                ·
                  refine ⟨131753706285154584208767029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 87835804190103056139178019 131753706285154584208767029)
                  ·
                    refine ⟨12351909964233242269571909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 131753706285154584208767029 12351909964233242269571909)
                    ·
                      refine ⟨2315983118293732925544733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12351909964233242269571909 2315983118293732925544733)
                      ·
                        rfl

theorem cell23_4510361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 5, 4].length) (baseStart_4510361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4510361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4510361 prefixEnd_4510361 := by exact prefixLift 4510361
  have htrace : WordTrace (prefixWord ++ tailWord_4510361) baseStart_4510361 baseEnd_4510361 := by
    simpa [prefixWord, tailWord_4510361, baseEnd_4510361] using wordTrace_append hprefix tailTrace_4510361
  have hstable : (prefixWord ++ tailWord_4510361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4510361).length < 2 ^ (prefixWord ++ tailWord_4510361).sum := by decide
  have hdescent : baseEnd_4510361 < baseStart_4510361 := by decide
  rcases family_descends (prefixWord ++ tailWord_4510361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4510362 : List Nat := [3, 1, 1, 6, 2, 1, 1, 8]
def baseStart_4510362 : Nat := 118140960795 + 4510362 * 2 ^ 59
def prefixEnd_4510362 : Nat := 4983230072969 + 3 ^ 40 * 4510362 * 2
def baseEnd_4510362 : Nat := 85777171547199534134527

theorem tailTrace_4510362 : CollatzResearch.WordTrace tailWord_4510362 prefixEnd_4510362 85777171547199534134527 := by
  unfold tailWord_4510362
  simp only [CollatzResearch.WordTrace]
  refine ⟨41126604221434064336829335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109670944590490838231544893 41126604221434064336829335)
  ·
    refine ⟨61689906332151096505244003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41126604221434064336829335 61689906332151096505244003)
    ·
      refine ⟨92534859498226644757866005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61689906332151096505244003 92534859498226644757866005)
      ·
        refine ⟨4337571538979373973024969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 92534859498226644757866005 4337571538979373973024969)
        ·
          refine ⟨3253178654234530479768727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4337571538979373973024969 3253178654234530479768727)
          ·
            refine ⟨4879767981351795719653091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3253178654234530479768727 4879767981351795719653091)
            ·
              refine ⟨7319651972027693579479637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4879767981351795719653091 7319651972027693579479637)
              ·
                refine ⟨85777171547199534134527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7319651972027693579479637 85777171547199534134527)
                ·
                  rfl

theorem cell23_4510362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 1, 8].length) (baseStart_4510362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4510362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4510362 prefixEnd_4510362 := by exact prefixLift 4510362
  have htrace : WordTrace (prefixWord ++ tailWord_4510362) baseStart_4510362 baseEnd_4510362 := by
    simpa [prefixWord, tailWord_4510362, baseEnd_4510362] using wordTrace_append hprefix tailTrace_4510362
  have hstable : (prefixWord ++ tailWord_4510362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4510362).length < 2 ^ (prefixWord ++ tailWord_4510362).sum := by decide
  have hdescent : baseEnd_4510362 < baseStart_4510362 := by decide
  rcases family_descends (prefixWord ++ tailWord_4510362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4510365 : List Nat := [1, 4, 2, 1, 1, 1, 3, 2, 3, 3, 2]
def baseStart_4510365 : Nat := 118140960795 + 4510365 * 2 ^ 59
def prefixEnd_4510365 : Nat := 4983230072969 + 3 ^ 40 * 4510365 * 2
def baseEnd_4510365 : Nat := 2315985172216350909894715

theorem tailTrace_4510365 : CollatzResearch.WordTrace tailWord_4510365 prefixEnd_4510365 2315985172216350909894715 := by
  unfold tailWord_4510365
  simp only [CollatzResearch.WordTrace]
  refine ⟨164506526304725388859676549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109671017536483592573117699 164506526304725388859676549)
  ·
    refine ⟨30844973682136010411189353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 164506526304725388859676549 30844973682136010411189353)
    ·
      refine ⟨23133730261602007808392015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30844973682136010411189353 23133730261602007808392015)
      ·
        refine ⟨34700595392403011712588023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23133730261602007808392015 34700595392403011712588023)
        ·
          refine ⟨52050893088604517568882035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34700595392403011712588023 52050893088604517568882035)
          ·
            refine ⟨78076339632906776353323053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52050893088604517568882035 78076339632906776353323053)
            ·
              refine ⟨29278627362340041132496145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78076339632906776353323053 29278627362340041132496145)
              ·
                refine ⟨21958970521755030849372109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29278627362340041132496145 21958970521755030849372109)
                ·
                  refine ⟨8234613945658136568514541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21958970521755030849372109 8234613945658136568514541)
                  ·
                    refine ⟨3087980229621801213192953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8234613945658136568514541 3087980229621801213192953)
                    ·
                      refine ⟨2315985172216350909894715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3087980229621801213192953 2315985172216350909894715)
                      ·
                        rfl

theorem cell23_4510365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 2, 3, 3, 2].length) (baseStart_4510365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4510365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4510365 prefixEnd_4510365 := by exact prefixLift 4510365
  have htrace : WordTrace (prefixWord ++ tailWord_4510365) baseStart_4510365 baseEnd_4510365 := by
    simpa [prefixWord, tailWord_4510365, baseEnd_4510365] using wordTrace_append hprefix tailTrace_4510365
  have hstable : (prefixWord ++ tailWord_4510365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4510365).length < 2 ^ (prefixWord ++ tailWord_4510365).sum := by decide
  have hdescent : baseEnd_4510365 < baseStart_4510365 := by decide
  rcases family_descends (prefixWord ++ tailWord_4510365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4510398 : List Nat := [4, 2, 1, 1, 2, 1, 2, 1, 1, 3, 5]
def baseStart_4510398 : Nat := 118140960795 + 4510398 * 2 ^ 59
def prefixEnd_4510398 : Nat := 4983230072969 + 3 ^ 40 * 4510398 * 2
def baseEnd_4510398 : Nat := 2316002117077949280782063

theorem tailTrace_4510398 : CollatzResearch.WordTrace tailWord_4510398 prefixEnd_4510398 2316002117077949280782063 := by
  unfold tailWord_4510398
  simp only [CollatzResearch.WordTrace]
  refine ⟨20563466239200729436953481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109671819942403890330418565 20563466239200729436953481)
  ·
    refine ⟨15422599679400547077715111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20563466239200729436953481 15422599679400547077715111)
    ·
      refine ⟨23133899519100820616572667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15422599679400547077715111 23133899519100820616572667)
      ·
        refine ⟨34700849278651230924859001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23133899519100820616572667 34700849278651230924859001)
        ·
          refine ⟨26025636958988423193644251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34700849278651230924859001 26025636958988423193644251)
          ·
            refine ⟨39038455438482634790466377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26025636958988423193644251 39038455438482634790466377)
            ·
              refine ⟨29278841578861976092849783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39038455438482634790466377 29278841578861976092849783)
              ·
                refine ⟨43918262368292964139274675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29278841578861976092849783 43918262368292964139274675)
                ·
                  refine ⟨65877393552439446208912013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43918262368292964139274675 65877393552439446208912013)
                  ·
                    refine ⟨24704022582164792328342005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 65877393552439446208912013 24704022582164792328342005)
                    ·
                      refine ⟨2316002117077949280782063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24704022582164792328342005 2316002117077949280782063)
                      ·
                        rfl

theorem cell23_4510398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 1, 1, 3, 5].length) (baseStart_4510398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4510398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4510398 prefixEnd_4510398 := by exact prefixLift 4510398
  have htrace : WordTrace (prefixWord ++ tailWord_4510398) baseStart_4510398 baseEnd_4510398 := by
    simpa [prefixWord, tailWord_4510398, baseEnd_4510398] using wordTrace_append hprefix tailTrace_4510398
  have hstable : (prefixWord ++ tailWord_4510398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4510398).length < 2 ^ (prefixWord ++ tailWord_4510398).sum := by decide
  have hdescent : baseEnd_4510398 < baseStart_4510398 := by decide
  rcases family_descends (prefixWord ++ tailWord_4510398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4510399 : List Nat := [1, 1, 2, 2, 2, 6, 2, 1, 1, 3, 2]
def baseStart_4510399 : Nat := 118140960795 + 4510399 * 2 ^ 59
def prefixEnd_4510399 : Nat := 4983230072969 + 3 ^ 40 * 4510399 * 2
def baseEnd_4510399 : Nat := 2316002630558603776869559

theorem tailTrace_4510399 : CollatzResearch.WordTrace tailWord_4510399 prefixEnd_4510399 2316002630558603776869559 := by
  unfold tailWord_4510399
  simp only [CollatzResearch.WordTrace]
  refine ⟨164507766386602212666414251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109671844257734808444276167 164507766386602212666414251)
  ·
    refine ⟨246761649579903318999621377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164507766386602212666414251 246761649579903318999621377)
    ·
      refine ⟨185071237184927489249716033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 246761649579903318999621377 185071237184927489249716033)
      ·
        refine ⟨138803427888695616937287025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 185071237184927489249716033 138803427888695616937287025)
        ·
          refine ⟨104102570916521712702965269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 138803427888695616937287025 104102570916521712702965269)
          ·
            refine ⟨4879808011711955282951497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 104102570916521712702965269 4879808011711955282951497)
            ·
              refine ⟨3659856008783966462213623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4879808011711955282951497 3659856008783966462213623)
              ·
                refine ⟨5489784013175949693320435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3659856008783966462213623 5489784013175949693320435)
                ·
                  refine ⟨8234676019763924539980653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5489784013175949693320435 8234676019763924539980653)
                  ·
                    refine ⟨3088003507411471702492745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8234676019763924539980653 3088003507411471702492745)
                    ·
                      refine ⟨2316002630558603776869559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3088003507411471702492745 2316002630558603776869559)
                      ·
                        rfl

theorem cell23_4510399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 2, 1, 1, 3, 2].length) (baseStart_4510399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4510399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4510399 prefixEnd_4510399 := by exact prefixLift 4510399
  have htrace : WordTrace (prefixWord ++ tailWord_4510399) baseStart_4510399 baseEnd_4510399 := by
    simpa [prefixWord, tailWord_4510399, baseEnd_4510399] using wordTrace_append hprefix tailTrace_4510399
  have hstable : (prefixWord ++ tailWord_4510399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4510399).length < 2 ^ (prefixWord ++ tailWord_4510399).sum := by decide
  have hdescent : baseEnd_4510399 < baseStart_4510399 := by decide
  rcases family_descends (prefixWord ++ tailWord_4510399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4510406 : List Nat := [6, 1, 2, 1, 2, 1, 1, 1, 4, 1, 3]
def baseStart_4510406 : Nat := 118140960795 + 4510406 * 2 ^ 59
def prefixEnd_4510406 : Nat := 4983230072969 + 3 ^ 40 * 4510406 * 2
def baseEnd_4510406 : Nat := 2316006224923185249482027

theorem tailTrace_4510406 : CollatzResearch.WordTrace tailWord_4510406 prefixEnd_4510406 2316006224923185249482027 := by
  unfold tailWord_4510406
  simp only [CollatzResearch.WordTrace]
  refine ⟨5140875678049276651934971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 109672014465051235241279381 5140875678049276651934971)
  ·
    refine ⟨7711313517073914977902457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5140875678049276651934971 7711313517073914977902457)
    ·
      refine ⟨5783485137805436233426843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7711313517073914977902457 5783485137805436233426843)
      ·
        refine ⟨8675227706708154350140265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5783485137805436233426843 8675227706708154350140265)
        ·
          refine ⟨6506420780031115762605199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8675227706708154350140265 6506420780031115762605199)
          ·
            refine ⟨9759631170046673643907799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6506420780031115762605199 9759631170046673643907799)
            ·
              refine ⟨14639446755070010465861699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9759631170046673643907799 14639446755070010465861699)
              ·
                refine ⟨21959170132605015698792549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14639446755070010465861699 21959170132605015698792549)
                ·
                  refine ⟨4117344399863440443523603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21959170132605015698792549 4117344399863440443523603)
                  ·
                    refine ⟨6176016599795160665285405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4117344399863440443523603 6176016599795160665285405)
                    ·
                      refine ⟨2316006224923185249482027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6176016599795160665285405 2316006224923185249482027)
                      ·
                        rfl

theorem cell23_4510406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_4510406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4510406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4510406 prefixEnd_4510406 := by exact prefixLift 4510406
  have htrace : WordTrace (prefixWord ++ tailWord_4510406) baseStart_4510406 baseEnd_4510406 := by
    simpa [prefixWord, tailWord_4510406, baseEnd_4510406] using wordTrace_append hprefix tailTrace_4510406
  have hstable : (prefixWord ++ tailWord_4510406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4510406).length < 2 ^ (prefixWord ++ tailWord_4510406).sum := by decide
  have hdescent : baseEnd_4510406 < baseStart_4510406 := by decide
  rcases family_descends (prefixWord ++ tailWord_4510406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4510408 : List Nat := [2, 1, 3, 1, 2, 3, 1, 2, 2, 2, 4]
def baseStart_4510408 : Nat := 118140960795 + 4510408 * 2 ^ 59
def prefixEnd_4510408 : Nat := 4983230072969 + 3 ^ 40 * 4510408 * 2
def baseEnd_4510408 : Nat := 2316007251884494241657017

theorem tailTrace_4510408 : CollatzResearch.WordTrace tailWord_4510408 prefixEnd_4510408 2316007251884494241657017 := by
  unfold tailWord_4510408
  simp only [CollatzResearch.WordTrace]
  refine ⟨82254047321784803601745939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109672063095713071468994585 82254047321784803601745939)
  ·
    refine ⟨123381070982677205402618909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82254047321784803601745939 123381070982677205402618909)
    ·
      refine ⟨46267901618503952025982091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123381070982677205402618909 46267901618503952025982091)
      ·
        refine ⟨69401852427755928038973137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46267901618503952025982091 69401852427755928038973137)
        ·
          refine ⟨52051389320816946029229853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69401852427755928038973137 52051389320816946029229853)
          ·
            refine ⟨19519270995306354760961195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52051389320816946029229853 19519270995306354760961195)
            ·
              refine ⟨29278906492959532141441793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19519270995306354760961195 29278906492959532141441793)
              ·
                refine ⟨21959179869719649106081345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29278906492959532141441793 21959179869719649106081345)
                ·
                  refine ⟨16469384902289736829561009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21959179869719649106081345 16469384902289736829561009)
                  ·
                    refine ⟨12352038676717302622170757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16469384902289736829561009 12352038676717302622170757)
                    ·
                      refine ⟨2316007251884494241657017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12352038676717302622170757 2316007251884494241657017)
                      ·
                        rfl

theorem cell23_4510408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 2, 2, 2, 4].length) (baseStart_4510408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4510408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4510408 prefixEnd_4510408 := by exact prefixLift 4510408
  have htrace : WordTrace (prefixWord ++ tailWord_4510408) baseStart_4510408 baseEnd_4510408 := by
    simpa [prefixWord, tailWord_4510408, baseEnd_4510408] using wordTrace_append hprefix tailTrace_4510408
  have hstable : (prefixWord ++ tailWord_4510408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4510408).length < 2 ^ (prefixWord ++ tailWord_4510408).sum := by decide
  have hdescent : baseEnd_4510408 < baseStart_4510408 := by decide
  rcases family_descends (prefixWord ++ tailWord_4510408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4510448 : List Nat := [2, 1, 1, 1, 3, 1, 4, 3, 2, 5]
def baseStart_4510448 : Nat := 118140960795 + 4510448 * 2 ^ 59
def prefixEnd_4510448 : Nat := 4983230072969 + 3 ^ 40 * 4510448 * 2
def baseEnd_4510448 : Nat := 772009263703558028385611

theorem tailTrace_4510448 : CollatzResearch.WordTrace tailWord_4510448 prefixEnd_4510448 772009263703558028385611 := by
  unfold tailWord_4510448
  simp only [CollatzResearch.WordTrace]
  refine ⟨82254776781712347017473999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109673035708949796023298665 82254776781712347017473999)
  ·
    refine ⟨123382165172568520526210999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82254776781712347017473999 123382165172568520526210999)
    ·
      refine ⟨185073247758852780789316499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123382165172568520526210999 185073247758852780789316499)
      ·
        refine ⟨277609871638279171183974749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185073247758852780789316499 277609871638279171183974749)
        ·
          refine ⟨104103701864354689193990531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 277609871638279171183974749 104103701864354689193990531)
          ·
            refine ⟨156155552796532033790985797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104103701864354689193990531 156155552796532033790985797)
            ·
              refine ⟨29279166149349756335809837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 156155552796532033790985797 29279166149349756335809837)
              ·
                refine ⟨10979687306006158625928689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29279166149349756335809837 10979687306006158625928689)
                ·
                  refine ⟨8234765479504618969446517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10979687306006158625928689 8234765479504618969446517)
                  ·
                    refine ⟨772009263703558028385611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8234765479504618969446517 772009263703558028385611)
                    ·
                      rfl

theorem cell23_4510448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 3, 2, 5].length) (baseStart_4510448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4510448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4510448 prefixEnd_4510448 := by exact prefixLift 4510448
  have htrace : WordTrace (prefixWord ++ tailWord_4510448) baseStart_4510448 baseEnd_4510448 := by
    simpa [prefixWord, tailWord_4510448, baseEnd_4510448] using wordTrace_append hprefix tailTrace_4510448
  have hstable : (prefixWord ++ tailWord_4510448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4510448).length < 2 ^ (prefixWord ++ tailWord_4510448).sum := by decide
  have hdescent : baseEnd_4510448 < baseStart_4510448 := by decide
  rcases family_descends (prefixWord ++ tailWord_4510448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4510485 : List Nat := [1, 3, 2, 1, 2, 2, 2, 1, 1, 6, 2]
def baseStart_4510485 : Nat := 118140960795 + 4510485 * 2 ^ 59
def prefixEnd_4510485 : Nat := 4983230072969 + 3 ^ 40 * 4510485 * 2
def baseEnd_4510485 : Nat := 2316046789894890440394163

theorem tailTrace_4510485 : CollatzResearch.WordTrace tailWord_4510485 prefixEnd_4510485 2316046789894890440394163 := by
  unfold tailWord_4510485
  simp only [CollatzResearch.WordTrace]
  refine ⟨164510903064290649354044909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109673935376193766236029939 164510903064290649354044909)
  ·
    refine ⟨61691588649108993507766841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 164510903064290649354044909 61691588649108993507766841)
    ·
      refine ⟨46268691486831745130825131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61691588649108993507766841 46268691486831745130825131)
      ·
        refine ⟨69403037230247617696237697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46268691486831745130825131 69403037230247617696237697)
        ·
          refine ⟨52052277922685713272178273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69403037230247617696237697 52052277922685713272178273)
          ·
            refine ⟨39039208442014284954133705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52052277922685713272178273 39039208442014284954133705)
            ·
              refine ⟨29279406331510713715600279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39039208442014284954133705 29279406331510713715600279)
              ·
                refine ⟨43919109497266070573400419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29279406331510713715600279 43919109497266070573400419)
                ·
                  refine ⟨65878664245899105860100629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43919109497266070573400419 65878664245899105860100629)
                  ·
                    refine ⟨3088062386526520587192217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 65878664245899105860100629 3088062386526520587192217)
                    ·
                      refine ⟨2316046789894890440394163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3088062386526520587192217 2316046789894890440394163)
                      ·
                        rfl

theorem cell23_4510485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 1, 1, 6, 2].length) (baseStart_4510485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4510485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4510485 prefixEnd_4510485 := by exact prefixLift 4510485
  have htrace : WordTrace (prefixWord ++ tailWord_4510485) baseStart_4510485 baseEnd_4510485 := by
    simpa [prefixWord, tailWord_4510485, baseEnd_4510485] using wordTrace_append hprefix tailTrace_4510485
  have hstable : (prefixWord ++ tailWord_4510485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4510485).length < 2 ^ (prefixWord ++ tailWord_4510485).sum := by decide
  have hdescent : baseEnd_4510485 < baseStart_4510485 := by decide
  rcases family_descends (prefixWord ++ tailWord_4510485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4510575 : List Nat := [1, 1, 2, 1, 3, 1, 1, 2, 1, 8, 2]
def baseStart_4510575 : Nat := 118140960795 + 4510575 * 2 ^ 59
def prefixEnd_4510575 : Nat := 4983230072969 + 3 ^ 40 * 4510575 * 2
def baseEnd_4510575 : Nat := 2316093003153795088268749

theorem tailTrace_4510575 : CollatzResearch.WordTrace tailWord_4510575 prefixEnd_4510575 2316093003153795088268749 := by
  unfold tailWord_4510575
  simp only [CollatzResearch.WordTrace]
  refine ⟨164514185633964594724821179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109676123755976396483214119 164514185633964594724821179)
  ·
    refine ⟨246771278450946892087231769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164514185633964594724821179 246771278450946892087231769)
    ·
      refine ⟨185078458838210169065423827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 246771278450946892087231769 185078458838210169065423827)
      ·
        refine ⟨277617688257315253598135741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185078458838210169065423827 277617688257315253598135741)
        ·
          refine ⟨104106633096493220099300903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 277617688257315253598135741 104106633096493220099300903)
          ·
            refine ⟨156159949644739830148951355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104106633096493220099300903 156159949644739830148951355)
            ·
              refine ⟨234239924467109745223427033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 156159949644739830148951355 234239924467109745223427033)
              ·
                refine ⟨175679943350332308917570275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 234239924467109745223427033 175679943350332308917570275)
                ·
                  refine ⟨263519915025498463376355413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 175679943350332308917570275 263519915025498463376355413)
                  ·
                    refine ⟨3088124004205060117691665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 263519915025498463376355413 3088124004205060117691665)
                    ·
                      refine ⟨2316093003153795088268749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3088124004205060117691665 2316093003153795088268749)
                      ·
                        rfl

theorem cell23_4510575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 8, 2].length) (baseStart_4510575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4510575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4510575 prefixEnd_4510575 := by exact prefixLift 4510575
  have htrace : WordTrace (prefixWord ++ tailWord_4510575) baseStart_4510575 baseEnd_4510575 := by
    simpa [prefixWord, tailWord_4510575, baseEnd_4510575] using wordTrace_append hprefix tailTrace_4510575
  have hstable : (prefixWord ++ tailWord_4510575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4510575).length < 2 ^ (prefixWord ++ tailWord_4510575).sum := by decide
  have hdescent : baseEnd_4510575 < baseStart_4510575 := by decide
  rcases family_descends (prefixWord ++ tailWord_4510575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4510595 : List Nat := [1, 1, 1, 3, 4, 1, 3, 2, 1, 1, 5]
def baseStart_4510595 : Nat := 118140960795 + 4510595 * 2 ^ 59
def prefixEnd_4510595 : Nat := 4983230072969 + 3 ^ 40 * 4510595 * 2
def baseEnd_4510595 : Nat := 2316103272766885010018657

theorem tailTrace_4510595 : CollatzResearch.WordTrace tailWord_4510595 prefixEnd_4510595 2316103272766885010018657 := by
  unfold tailWord_4510595
  simp only [CollatzResearch.WordTrace]
  refine ⟨164514915093892138140549239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109676610062594758760366159 164514915093892138140549239)
  ·
    refine ⟨246772372640838207210823859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164514915093892138140549239 246772372640838207210823859)
    ·
      refine ⟨370158558961257310816235789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 246772372640838207210823859 370158558961257310816235789)
      ·
        refine ⟨138809459610471491556088421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 370158558961257310816235789 138809459610471491556088421)
        ·
          refine ⟨26026773676963404666766579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 138809459610471491556088421 26026773676963404666766579)
          ·
            refine ⟨39040160515445107000149869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26026773676963404666766579 39040160515445107000149869)
            ·
              refine ⟨14640060193291915125056201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39040160515445107000149869 14640060193291915125056201)
              ·
                refine ⟨10980045144968936343792151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14640060193291915125056201 10980045144968936343792151)
                ·
                  refine ⟨16470067717453404515688227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10980045144968936343792151 16470067717453404515688227)
                  ·
                    refine ⟨24705101576180106773532341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16470067717453404515688227 24705101576180106773532341)
                    ·
                      refine ⟨2316103272766885010018657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24705101576180106773532341 2316103272766885010018657)
                      ·
                        rfl

theorem cell23_4510595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 2, 1, 1, 5].length) (baseStart_4510595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4510595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4510595 prefixEnd_4510595 := by exact prefixLift 4510595
  have htrace : WordTrace (prefixWord ++ tailWord_4510595) baseStart_4510595 baseEnd_4510595 := by
    simpa [prefixWord, tailWord_4510595, baseEnd_4510595] using wordTrace_append hprefix tailTrace_4510595
  have hstable : (prefixWord ++ tailWord_4510595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4510595).length < 2 ^ (prefixWord ++ tailWord_4510595).sum := by decide
  have hdescent : baseEnd_4510595 < baseStart_4510595 := by decide
  rcases family_descends (prefixWord ++ tailWord_4510595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4510602 : List Nat := [3, 1, 2, 4, 1, 1, 3, 1, 1, 6]
def baseStart_4510602 : Nat := 118140960795 + 4510602 * 2 ^ 59
def prefixEnd_4510602 : Nat := 4983230072969 + 3 ^ 40 * 4510602 * 2
def baseEnd_4510602 : Nat := 772035622377155494210375

theorem tailTrace_4510602 : CollatzResearch.WordTrace tailWord_4510602 prefixEnd_4510602 772035622377155494210375 := by
  unfold tailWord_4510602
  simp only [CollatzResearch.WordTrace]
  refine ⟨41128792601216694584013515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109676780269911185557369373 41128792601216694584013515)
  ·
    refine ⟨61693188901825041876020273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41128792601216694584013515 61693188901825041876020273)
    ·
      refine ⟨46269891676368781407015205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61693188901825041876020273 46269891676368781407015205)
      ·
        refine ⟨8675604689319146513815351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46269891676368781407015205 8675604689319146513815351)
        ·
          refine ⟨13013407033978719770723027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8675604689319146513815351 13013407033978719770723027)
          ·
            refine ⟨19520110550968079656084541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13013407033978719770723027 19520110550968079656084541)
            ·
              refine ⟨7320041456613029871031703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19520110550968079656084541 7320041456613029871031703)
              ·
                refine ⟨10980062184919544806547555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7320041456613029871031703 10980062184919544806547555)
                ·
                  refine ⟨16470093277379317209821333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10980062184919544806547555 16470093277379317209821333)
                  ·
                    refine ⟨772035622377155494210375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16470093277379317209821333 772035622377155494210375)
                    ·
                      rfl

theorem cell23_4510602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 3, 1, 1, 6].length) (baseStart_4510602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4510602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4510602 prefixEnd_4510602 := by exact prefixLift 4510602
  have htrace : WordTrace (prefixWord ++ tailWord_4510602) baseStart_4510602 baseEnd_4510602 := by
    simpa [prefixWord, tailWord_4510602, baseEnd_4510602] using wordTrace_append hprefix tailTrace_4510602
  have hstable : (prefixWord ++ tailWord_4510602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4510602).length < 2 ^ (prefixWord ++ tailWord_4510602).sum := by decide
  have hdescent : baseEnd_4510602 < baseStart_4510602 := by decide
  rcases family_descends (prefixWord ++ tailWord_4510602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4510620 : List Nat := [2, 2, 3, 3, 3, 1, 1, 3, 1, 1, 3]
def baseStart_4510620 : Nat := 118140960795 + 4510620 * 2 ^ 59
def prefixEnd_4510620 : Nat := 4983230072969 + 3 ^ 40 * 4510620 * 2
def baseEnd_4510620 : Nat := 2316116109783247412206043

theorem tailTrace_4510620 : CollatzResearch.WordTrace tailWord_4510620 prefixEnd_4510620 2316116109783247412206043 := by
  unfold tailWord_4510620
  simp only [CollatzResearch.WordTrace]
  refine ⟨82257913459400783705104657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109677217945867711606806209 82257913459400783705104657)
  ·
    refine ⟨61693435094550587778828493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82257913459400783705104657 61693435094550587778828493)
    ·
      refine ⟨23135038160456470417060685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61693435094550587778828493 23135038160456470417060685)
      ·
        refine ⟨8675639310171176406397757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23135038160456470417060685 8675639310171176406397757)
        ·
          refine ⟨3253364741314191152399159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8675639310171176406397757 3253364741314191152399159)
          ·
            refine ⟨4880047111971286728598739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3253364741314191152399159 4880047111971286728598739)
            ·
              refine ⟨7320070667956930092898109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4880047111971286728598739 7320070667956930092898109)
              ·
                refine ⟨2745026500483848784836791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7320070667956930092898109 2745026500483848784836791)
                ·
                  refine ⟨4117539750725773177255187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2745026500483848784836791 4117539750725773177255187)
                  ·
                    refine ⟨6176309626088659765882781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4117539750725773177255187 6176309626088659765882781)
                    ·
                      refine ⟨2316116109783247412206043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6176309626088659765882781 2316116109783247412206043)
                      ·
                        rfl

theorem cell23_4510620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 1, 3, 1, 1, 3].length) (baseStart_4510620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4510620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4510620 prefixEnd_4510620 := by exact prefixLift 4510620
  have htrace : WordTrace (prefixWord ++ tailWord_4510620) baseStart_4510620 baseEnd_4510620 := by
    simpa [prefixWord, tailWord_4510620, baseEnd_4510620] using wordTrace_append hprefix tailTrace_4510620
  have hstable : (prefixWord ++ tailWord_4510620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4510620).length < 2 ^ (prefixWord ++ tailWord_4510620).sum := by decide
  have hdescent : baseEnd_4510620 < baseStart_4510620 := by decide
  rcases family_descends (prefixWord ++ tailWord_4510620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4510645 : List Nat := [1, 3, 3, 2, 1, 1, 2, 1, 2, 7]
def baseStart_4510645 : Nat := 118140960795 + 4510645 * 2 ^ 59
def prefixEnd_4510645 : Nat := 4983230072969 + 3 ^ 40 * 4510645 * 2
def baseEnd_4510645 : Nat := 772042982266536604797809

theorem tailTrace_4510645 : CollatzResearch.WordTrace tailWord_4510645 prefixEnd_4510645 772042982266536604797809 := by
  unfold tailWord_4510645
  simp only [CollatzResearch.WordTrace]
  refine ⟨164516738743710996679869389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109677825829140664453246259 164516738743710996679869389)
  ·
    refine ⟨61693777028891623754951021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 164516738743710996679869389 61693777028891623754951021)
    ·
      refine ⟨23135166385834358908106633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61693777028891623754951021 23135166385834358908106633)
      ·
        refine ⟨17351374789375769181079975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23135166385834358908106633 17351374789375769181079975)
        ·
          refine ⟨26027062184063653771619963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17351374789375769181079975 26027062184063653771619963)
          ·
            refine ⟨39040593276095480657429945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26027062184063653771619963 39040593276095480657429945)
            ·
              refine ⟨29280444957071610493072459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39040593276095480657429945 29280444957071610493072459)
              ·
                refine ⟨43920667435607415739608689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29280444957071610493072459 43920667435607415739608689)
                ·
                  refine ⟨32940500576705561804706517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43920667435607415739608689 32940500576705561804706517)
                  ·
                    refine ⟨772042982266536604797809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32940500576705561804706517 772042982266536604797809)
                    ·
                      rfl

theorem cell23_4510645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 1, 2, 7].length) (baseStart_4510645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4510645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4510645 prefixEnd_4510645 := by exact prefixLift 4510645
  have htrace : WordTrace (prefixWord ++ tailWord_4510645) baseStart_4510645 baseEnd_4510645 := by
    simpa [prefixWord, tailWord_4510645, baseEnd_4510645] using wordTrace_append hprefix tailTrace_4510645
  have hstable : (prefixWord ++ tailWord_4510645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4510645).length < 2 ^ (prefixWord ++ tailWord_4510645).sum := by decide
  have hdescent : baseEnd_4510645 < baseStart_4510645 := by decide
  rcases family_descends (prefixWord ++ tailWord_4510645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4510653 : List Nat := [1, 4, 1, 2, 5, 1, 2, 1, 2, 4]
def baseStart_4510653 : Nat := 118140960795 + 4510653 * 2 ^ 59
def prefixEnd_4510653 : Nat := 4983230072969 + 3 ^ 40 * 4510653 * 2
def baseEnd_4510653 : Nat := 772044351548281927697797

theorem tailTrace_4510653 : CollatzResearch.WordTrace tailWord_4510653 prefixEnd_4510653 772044351548281927697797 := by
  unfold tailWord_4510653
  simp only [CollatzResearch.WordTrace]
  refine ⟨164517030527682014046160613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109678020351788009364107075 164517030527682014046160613)
  ·
    refine ⟨30846943223940377633655115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 164517030527682014046160613 30846943223940377633655115)
    ·
      refine ⟨46270414835910566450482673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30846943223940377633655115 46270414835910566450482673)
      ·
        refine ⟨34702811126932924837862005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46270414835910566450482673 34702811126932924837862005)
        ·
          refine ⟨3253388543149961703549563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 34702811126932924837862005 3253388543149961703549563)
          ·
            refine ⟨4880082814724942555324345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3253388543149961703549563 4880082814724942555324345)
            ·
              refine ⟨3660062111043706916493259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4880082814724942555324345 3660062111043706916493259)
              ·
                refine ⟨5490093166565560374739889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3660062111043706916493259 5490093166565560374739889)
                ·
                  refine ⟨4117569874924170281054917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5490093166565560374739889 4117569874924170281054917)
                  ·
                    refine ⟨772044351548281927697797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4117569874924170281054917 772044351548281927697797)
                    ·
                      rfl

theorem cell23_4510653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 2, 1, 2, 4].length) (baseStart_4510653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4510653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4510653 prefixEnd_4510653 := by exact prefixLift 4510653
  have htrace : WordTrace (prefixWord ++ tailWord_4510653) baseStart_4510653 baseEnd_4510653 := by
    simpa [prefixWord, tailWord_4510653, baseEnd_4510653] using wordTrace_append hprefix tailTrace_4510653
  have hstable : (prefixWord ++ tailWord_4510653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4510653).length < 2 ^ (prefixWord ++ tailWord_4510653).sum := by decide
  have hdescent : baseEnd_4510653 < baseStart_4510653 := by decide
  rcases family_descends (prefixWord ++ tailWord_4510653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4510693 : List Nat := [1, 3, 1, 6, 1, 1, 2, 2, 2, 1, 3]
def baseStart_4510693 : Nat := 118140960795 + 4510693 * 2 ^ 59
def prefixEnd_4510693 : Nat := 4983230072969 + 3 ^ 40 * 4510693 * 2
def baseEnd_4510693 : Nat := 2316153593871025626593207

theorem tailTrace_4510693 : CollatzResearch.WordTrace tailWord_4510693 prefixEnd_4510693 2316153593871025626593207 := by
  unfold tailWord_4510693
  simp only [CollatzResearch.WordTrace]
  refine ⟨164518489447537100877616733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109678992965024733918411155 164518489447537100877616733)
  ·
    refine ⟨61694433542826412829106275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 164518489447537100877616733 61694433542826412829106275)
    ·
      refine ⟨92541650314239619243659413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61694433542826412829106275 92541650314239619243659413)
      ·
        refine ⟨4337889858479982152046535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 92541650314239619243659413 4337889858479982152046535)
        ·
          refine ⟨6506834787719973228069803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4337889858479982152046535 6506834787719973228069803)
          ·
            refine ⟨9760252181579959842104705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6506834787719973228069803 9760252181579959842104705)
            ·
              refine ⟨7320189136184969881578529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9760252181579959842104705 7320189136184969881578529)
              ·
                refine ⟨5490141852138727411183897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7320189136184969881578529 5490141852138727411183897)
                ·
                  refine ⟨4117606389104045558387923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5490141852138727411183897 4117606389104045558387923)
                  ·
                    refine ⟨6176409583656068337581885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4117606389104045558387923 6176409583656068337581885)
                    ·
                      refine ⟨2316153593871025626593207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6176409583656068337581885 2316153593871025626593207)
                      ·
                        rfl

theorem cell23_4510693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_4510693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4510693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4510693 prefixEnd_4510693 := by exact prefixLift 4510693
  have htrace : WordTrace (prefixWord ++ tailWord_4510693) baseStart_4510693 baseEnd_4510693 := by
    simpa [prefixWord, tailWord_4510693, baseEnd_4510693] using wordTrace_append hprefix tailTrace_4510693
  have hstable : (prefixWord ++ tailWord_4510693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4510693).length < 2 ^ (prefixWord ++ tailWord_4510693).sum := by decide
  have hdescent : baseEnd_4510693 < baseStart_4510693 := by decide
  rcases family_descends (prefixWord ++ tailWord_4510693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4510716 : List Nat := [2, 2, 2, 1, 2, 3, 2, 3, 2, 2, 2]
def baseStart_4510716 : Nat := 118140960795 + 4510716 * 2 ^ 59
def prefixEnd_4510716 : Nat := 4983230072969 + 3 ^ 40 * 4510716 * 2
def baseEnd_4510716 : Nat := 2316165403926079036605601

theorem tailTrace_4510716 : CollatzResearch.WordTrace tailWord_4510716 prefixEnd_4510716 2316165403926079036605601 := by
  unfold tailWord_4510716
  simp only [CollatzResearch.WordTrace]
  refine ⟨82259664163226887902852001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109679552217635850537136001 82259664163226887902852001)
  ·
    refine ⟨61694748122420165927139001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82259664163226887902852001 61694748122420165927139001)
    ·
      refine ⟨46271061091815124445354251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61694748122420165927139001 46271061091815124445354251)
      ·
        refine ⟨69406591637722686668031377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46271061091815124445354251 69406591637722686668031377)
        ·
          refine ⟨52054943728292015001023533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69406591637722686668031377 52054943728292015001023533)
          ·
            refine ⟨19520603898109505625383825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52054943728292015001023533 19520603898109505625383825)
            ·
              refine ⟨14640452923582129219037869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19520603898109505625383825 14640452923582129219037869)
              ·
                refine ⟨5490169846343298457139201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14640452923582129219037869 5490169846343298457139201)
                ·
                  refine ⟨4117627384757473842854401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5490169846343298457139201 4117627384757473842854401)
                  ·
                    refine ⟨3088220538568105382140801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4117627384757473842854401 3088220538568105382140801)
                    ·
                      refine ⟨2316165403926079036605601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3088220538568105382140801 2316165403926079036605601)
                      ·
                        rfl

theorem cell23_4510716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 3, 2, 2, 2].length) (baseStart_4510716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4510716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4510716 prefixEnd_4510716 := by exact prefixLift 4510716
  have htrace : WordTrace (prefixWord ++ tailWord_4510716) baseStart_4510716 baseEnd_4510716 := by
    simpa [prefixWord, tailWord_4510716, baseEnd_4510716] using wordTrace_append hprefix tailTrace_4510716
  have hstable : (prefixWord ++ tailWord_4510716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4510716).length < 2 ^ (prefixWord ++ tailWord_4510716).sum := by decide
  have hdescent : baseEnd_4510716 < baseStart_4510716 := by decide
  rcases family_descends (prefixWord ++ tailWord_4510716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4510735 : List Nat := [1, 1, 2, 1, 1, 1, 2, 1, 8, 5]
def baseStart_4510735 : Nat := 118140960795 + 4510735 * 2 ^ 59
def prefixEnd_4510735 : Nat := 4983230072969 + 3 ^ 40 * 4510735 * 2
def baseEnd_4510735 : Nat := 772058386686171487422671

theorem tailTrace_4510735 : CollatzResearch.WordTrace tailWord_4510735 prefixEnd_4510735 772058386686171487422671 := by
  unfold tailWord_4510735
  simp only [CollatzResearch.WordTrace]
  refine ⟨164520021313384942050645659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109680014208923294700430439 164520021313384942050645659)
  ·
    refine ⟨246780031970077413075968489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164520021313384942050645659 246780031970077413075968489)
    ·
      refine ⟨185085023977558059806976367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 246780031970077413075968489 185085023977558059806976367)
      ·
        refine ⟨277627535966337089710464551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185085023977558059806976367 277627535966337089710464551)
        ·
          refine ⟨416441303949505634565696827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 277627535966337089710464551 416441303949505634565696827)
          ·
            refine ⟨624661955924258451848545241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 416441303949505634565696827 624661955924258451848545241)
            ·
              refine ⟨468496466943193838886408931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 624661955924258451848545241 468496466943193838886408931)
              ·
                refine ⟨702744700414790758329613397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 468496466943193838886408931 702744700414790758329613397)
                ·
                  refine ⟨8235289457985829199175157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 702744700414790758329613397 8235289457985829199175157)
                  ·
                    refine ⟨772058386686171487422671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8235289457985829199175157 772058386686171487422671)
                    ·
                      rfl

theorem cell23_4510735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 8, 5].length) (baseStart_4510735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4510735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4510735 prefixEnd_4510735 := by exact prefixLift 4510735
  have htrace : WordTrace (prefixWord ++ tailWord_4510735) baseStart_4510735 baseEnd_4510735 := by
    simpa [prefixWord, tailWord_4510735, baseEnd_4510735] using wordTrace_append hprefix tailTrace_4510735
  have hstable : (prefixWord ++ tailWord_4510735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4510735).length < 2 ^ (prefixWord ++ tailWord_4510735).sum := by decide
  have hdescent : baseEnd_4510735 < baseStart_4510735 := by decide
  rcases family_descends (prefixWord ++ tailWord_4510735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4510745 : List Nat := [1, 2, 1, 2, 1, 1, 4, 1, 3, 2, 5]
def baseStart_4510745 : Nat := 118140960795 + 4510745 * 2 ^ 59
def prefixEnd_4510745 : Nat := 4983230072969 + 3 ^ 40 * 4510745 * 2
def baseEnd_4510745 : Nat := 2316180294865059423142967

theorem tailTrace_4510745 : CollatzResearch.WordTrace tailWord_4510745 prefixEnd_4510745 2316180294865059423142967 := by
  unfold tailWord_4510745
  simp only [CollatzResearch.WordTrace]
  refine ⟨164520386043348713758509689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109680257362232475839006459 164520386043348713758509689)
  ·
    refine ⟨123390289532511535318882267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164520386043348713758509689 123390289532511535318882267)
    ·
      refine ⟨185085434298767302978323401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123390289532511535318882267 185085434298767302978323401)
      ·
        refine ⟨138814075724075477233742551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 185085434298767302978323401 138814075724075477233742551)
        ·
          refine ⟨208221113586113215850613827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138814075724075477233742551 208221113586113215850613827)
          ·
            refine ⟨312331670379169823775920741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 208221113586113215850613827 312331670379169823775920741)
            ·
              refine ⟨58562188196094341957985139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 312331670379169823775920741 58562188196094341957985139)
              ·
                refine ⟨87843282294141512936977709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58562188196094341957985139 87843282294141512936977709)
                ·
                  refine ⟨32941230860303067351366641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 87843282294141512936977709 32941230860303067351366641)
                  ·
                    refine ⟨24705923145227300513524981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32941230860303067351366641 24705923145227300513524981)
                    ·
                      refine ⟨2316180294865059423142967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24705923145227300513524981 2316180294865059423142967)
                      ·
                        rfl

theorem cell23_4510745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 3, 2, 5].length) (baseStart_4510745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4510745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4510745 prefixEnd_4510745 := by exact prefixLift 4510745
  have htrace : WordTrace (prefixWord ++ tailWord_4510745) baseStart_4510745 baseEnd_4510745 := by
    simpa [prefixWord, tailWord_4510745, baseEnd_4510745] using wordTrace_append hprefix tailTrace_4510745
  have hstable : (prefixWord ++ tailWord_4510745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4510745).length < 2 ^ (prefixWord ++ tailWord_4510745).sum := by decide
  have hdescent : baseEnd_4510745 < baseStart_4510745 := by decide
  rcases family_descends (prefixWord ++ tailWord_4510745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4510792 : List Nat := [2, 1, 3, 1, 1, 1, 3, 3, 1, 4, 3]
def baseStart_4510792 : Nat := 118140960795 + 4510792 * 2 ^ 59
def prefixEnd_4510792 : Nat := 4983230072969 + 3 ^ 40 * 4510792 * 2
def baseEnd_4510792 : Nat := 2316204428455820739255251

theorem tailTrace_4510792 : CollatzResearch.WordTrace tailWord_4510792 prefixEnd_4510792 2316204428455820739255251 := by
  unfold tailWord_4510792
  simp only [CollatzResearch.WordTrace]
  refine ⟨82261050137089220392735315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109681400182785627190313753 82261050137089220392735315)
  ·
    refine ⟨123391575205633830589102973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82261050137089220392735315 123391575205633830589102973)
    ·
      refine ⟨46271840702112686470913615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123391575205633830589102973 46271840702112686470913615)
      ·
        refine ⟨69407761053169029706370423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46271840702112686470913615 69407761053169029706370423)
        ·
          refine ⟨104111641579753544559555635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69407761053169029706370423 104111641579753544559555635)
          ·
            refine ⟨156167462369630316839333453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104111641579753544559555635 156167462369630316839333453)
            ·
              refine ⟨58562798388611368814750045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 156167462369630316839333453 58562798388611368814750045)
              ·
                refine ⟨21961049395729263305531267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58562798388611368814750045 21961049395729263305531267)
                ·
                  refine ⟨32941574093593894958296901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21961049395729263305531267 32941574093593894958296901)
                  ·
                    refine ⟨6176545142548855304680669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32941574093593894958296901 6176545142548855304680669)
                    ·
                      refine ⟨2316204428455820739255251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6176545142548855304680669 2316204428455820739255251)
                      ·
                        rfl

theorem cell23_4510792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 3, 1, 4, 3].length) (baseStart_4510792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4510792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4510792 prefixEnd_4510792 := by exact prefixLift 4510792
  have htrace : WordTrace (prefixWord ++ tailWord_4510792) baseStart_4510792 baseEnd_4510792 := by
    simpa [prefixWord, tailWord_4510792, baseEnd_4510792] using wordTrace_append hprefix tailTrace_4510792
  have hstable : (prefixWord ++ tailWord_4510792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4510792).length < 2 ^ (prefixWord ++ tailWord_4510792).sum := by decide
  have hdescent : baseEnd_4510792 < baseStart_4510792 := by decide
  rcases family_descends (prefixWord ++ tailWord_4510792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4510812 : List Nat := [2, 2, 4, 1, 1, 1, 1, 3, 8]
def baseStart_4510812 : Nat := 118140960795 + 4510812 * 2 ^ 59
def prefixEnd_4510812 : Nat := 4983230072969 + 3 ^ 40 * 4510812 * 2
def baseEnd_4510812 : Nat := 257357188674323406778351

theorem tailTrace_4510812 : CollatzResearch.WordTrace tailWord_4510812 prefixEnd_4510812 257357188674323406778351 := by
  unfold tailWord_4510812
  simp only [CollatzResearch.WordTrace]
  refine ⟨82261414867052992100599345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109681886489403989467465793 82261414867052992100599345)
  ·
    refine ⟨61696061150289744075449509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82261414867052992100599345 61696061150289744075449509)
    ·
      refine ⟨11568011465679327014146783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61696061150289744075449509 11568011465679327014146783)
      ·
        refine ⟨17352017198518990521220175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11568011465679327014146783 17352017198518990521220175)
        ·
          refine ⟨26028025797778485781830263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17352017198518990521220175 26028025797778485781830263)
          ·
            refine ⟨39042038696667728672745395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26028025797778485781830263 39042038696667728672745395)
            ·
              refine ⟨58563058045001593009118093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39042038696667728672745395 58563058045001593009118093)
              ·
                refine ⟨21961146766875597378419285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58563058045001593009118093 21961146766875597378419285)
                ·
                  refine ⟨257357188674323406778351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21961146766875597378419285 257357188674323406778351)
                  ·
                    rfl

theorem cell23_4510812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 3, 8].length) (baseStart_4510812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4510812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4510812 prefixEnd_4510812 := by exact prefixLift 4510812
  have htrace : WordTrace (prefixWord ++ tailWord_4510812) baseStart_4510812 baseEnd_4510812 := by
    simpa [prefixWord, tailWord_4510812, baseEnd_4510812] using wordTrace_append hprefix tailTrace_4510812
  have hstable : (prefixWord ++ tailWord_4510812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4510812).length < 2 ^ (prefixWord ++ tailWord_4510812).sum := by decide
  have hdescent : baseEnd_4510812 < baseStart_4510812 := by decide
  rcases family_descends (prefixWord ++ tailWord_4510812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4510829 : List Nat := [1, 5, 1, 1, 2, 3, 1, 3, 6]
def baseStart_4510829 : Nat := 118140960795 + 4510829 * 2 ^ 59
def prefixEnd_4510829 : Nat := 4983230072969 + 3 ^ 40 * 4510829 * 2
def baseEnd_4510829 : Nat := 257358158582226343832509

theorem tailTrace_4510829 : CollatzResearch.WordTrace tailWord_4510829 prefixEnd_4510829 257358158582226343832509 := by
  unfold tailWord_4510829
  simp only [CollatzResearch.WordTrace]
  refine ⟨164523449775044396104567541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109682299850029597403045027 164523449775044396104567541)
  ·
    refine ⟨15424073416410412134803207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 164523449775044396104567541 15424073416410412134803207)
    ·
      refine ⟨23136110124615618202204811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15424073416410412134803207 23136110124615618202204811)
      ·
        refine ⟨34704165186923427303307217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23136110124615618202204811 34704165186923427303307217)
        ·
          refine ⟨26028123890192570477480413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34704165186923427303307217 26028123890192570477480413)
          ·
            refine ⟨9760546458822213929055155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26028123890192570477480413 9760546458822213929055155)
            ·
              refine ⟨14640819688233320893582733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9760546458822213929055155 14640819688233320893582733)
              ·
                refine ⟨5490307383087495335093525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14640819688233320893582733 5490307383087495335093525)
                ·
                  refine ⟨257358158582226343832509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5490307383087495335093525 257358158582226343832509)
                  ·
                    rfl

theorem cell23_4510829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 3, 6].length) (baseStart_4510829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4510829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4510829 prefixEnd_4510829 := by exact prefixLift 4510829
  have htrace : WordTrace (prefixWord ++ tailWord_4510829) baseStart_4510829 baseEnd_4510829 := by
    simpa [prefixWord, tailWord_4510829, baseEnd_4510829] using wordTrace_append hprefix tailTrace_4510829
  have hstable : (prefixWord ++ tailWord_4510829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4510829).length < 2 ^ (prefixWord ++ tailWord_4510829).sum := by decide
  have hdescent : baseEnd_4510829 < baseStart_4510829 := by decide
  rcases family_descends (prefixWord ++ tailWord_4510829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4510839 : List Nat := [1, 1, 3, 1, 1, 4, 2, 1, 5, 1, 3]
def baseStart_4510839 : Nat := 118140960795 + 4510839 * 2 ^ 59
def prefixEnd_4510839 : Nat := 4983230072969 + 3 ^ 40 * 4510839 * 2
def baseEnd_4510839 : Nat := 2316228562046582055367535

theorem tailTrace_4510839 : CollatzResearch.WordTrace tailWord_4510839 prefixEnd_4510839 2316228562046582055367535 := by
  unfold tailWord_4510839
  simp only [CollatzResearch.WordTrace]
  refine ⟨164523814505008167812431571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109682543003338778541621047 164523814505008167812431571)
  ·
    refine ⟨246785721757512251718647357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164523814505008167812431571 246785721757512251718647357)
    ·
      refine ⟨92544645659067094394492759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 246785721757512251718647357 92544645659067094394492759)
      ·
        refine ⟨138816968488600641591739139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92544645659067094394492759 138816968488600641591739139)
        ·
          refine ⟨208225452732900962387608709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138816968488600641591739139 208225452732900962387608709)
          ·
            refine ⟨39042272387418930447676633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 208225452732900962387608709 39042272387418930447676633)
            ·
              refine ⟨29281704290564197835757475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39042272387418930447676633 29281704290564197835757475)
              ·
                refine ⟨43922556435846296753636213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29281704290564197835757475 43922556435846296753636213)
                ·
                  refine ⟨4117739665860590320653395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43922556435846296753636213 4117739665860590320653395)
                  ·
                    refine ⟨6176609498790885480980093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4117739665860590320653395 6176609498790885480980093)
                    ·
                      refine ⟨2316228562046582055367535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6176609498790885480980093 2316228562046582055367535)
                      ·
                        rfl

theorem cell23_4510839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 1, 5, 1, 3].length) (baseStart_4510839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4510839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4510839 prefixEnd_4510839 := by exact prefixLift 4510839
  have htrace : WordTrace (prefixWord ++ tailWord_4510839) baseStart_4510839 baseEnd_4510839 := by
    simpa [prefixWord, tailWord_4510839, baseEnd_4510839] using wordTrace_append hprefix tailTrace_4510839
  have hstable : (prefixWord ++ tailWord_4510839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4510839).length < 2 ^ (prefixWord ++ tailWord_4510839).sum := by decide
  have hdescent : baseEnd_4510839 < baseStart_4510839 := by decide
  rcases family_descends (prefixWord ++ tailWord_4510839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4510896 : List Nat := [2, 1, 1, 1, 2, 1, 2, 6, 3, 2, 2]
def baseStart_4510896 : Nat := 118140960795 + 4510896 * 2 ^ 59
def prefixEnd_4510896 : Nat := 4983230072969 + 3 ^ 40 * 4510896 * 2
def baseEnd_4510896 : Nat := 2316257830443888332354773

theorem tailTrace_4510896 : CollatzResearch.WordTrace tailWord_4510896 prefixEnd_4510896 2316257830443888332354773 := by
  unfold tailWord_4510896
  simp only [CollatzResearch.WordTrace]
  refine ⟨82262946732900833273628271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109683928977201111031504361 82262946732900833273628271)
  ·
    refine ⟨123394420099351249910442407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82262946732900833273628271 123394420099351249910442407)
    ·
      refine ⟨185091630149026874865663611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123394420099351249910442407 185091630149026874865663611)
      ·
        refine ⟨277637445223540312298495417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185091630149026874865663611 277637445223540312298495417)
        ·
          refine ⟨208228083917655234223871563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 277637445223540312298495417 208228083917655234223871563)
          ·
            refine ⟨312342125876482851335807345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 208228083917655234223871563 312342125876482851335807345)
            ·
              refine ⟨234256594407362138501855509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 312342125876482851335807345 234256594407362138501855509)
              ·
                refine ⟨10980777862845100242274477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 234256594407362138501855509 10980777862845100242274477)
                ·
                  refine ⟨4117791698566912590852929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10980777862845100242274477 4117791698566912590852929)
                  ·
                    refine ⟨3088343773925184443139697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4117791698566912590852929 3088343773925184443139697)
                    ·
                      refine ⟨2316257830443888332354773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3088343773925184443139697 2316257830443888332354773)
                      ·
                        rfl

theorem cell23_4510896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 6, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 6, 3, 2, 2].length) (baseStart_4510896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4510896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4510896 prefixEnd_4510896 := by exact prefixLift 4510896
  have htrace : WordTrace (prefixWord ++ tailWord_4510896) baseStart_4510896 baseEnd_4510896 := by
    simpa [prefixWord, tailWord_4510896, baseEnd_4510896] using wordTrace_append hprefix tailTrace_4510896
  have hstable : (prefixWord ++ tailWord_4510896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4510896).length < 2 ^ (prefixWord ++ tailWord_4510896).sum := by decide
  have hdescent : baseEnd_4510896 < baseStart_4510896 := by decide
  rcases family_descends (prefixWord ++ tailWord_4510896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4510899 : List Nat := [1, 1, 1, 2, 3, 2, 4, 1, 3, 2, 3]
def baseStart_4510899 : Nat := 118140960795 + 4510899 * 2 ^ 59
def prefixEnd_4510899 : Nat := 4983230072969 + 3 ^ 40 * 4510899 * 2
def baseEnd_4510899 : Nat := 2316259370885851820617259

theorem tailTrace_4510899 : CollatzResearch.WordTrace tailWord_4510899 prefixEnd_4510899 2316259370885851820617259 := by
  unfold tailWord_4510899
  simp only [CollatzResearch.WordTrace]
  refine ⟨164526002884790798059615751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109684001923193865373077167 164526002884790798059615751)
  ·
    refine ⟨246789004327186197089423627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164526002884790798059615751 246789004327186197089423627)
    ·
      refine ⟨370183506490779295634135441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 246789004327186197089423627 370183506490779295634135441)
      ·
        refine ⟨277637629868084471725601581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 370183506490779295634135441 277637629868084471725601581)
        ·
          refine ⟨104114111200531676897100593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 277637629868084471725601581 104114111200531676897100593)
          ·
            refine ⟨78085583400398757672825445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104114111200531676897100593 78085583400398757672825445)
            ·
              refine ⟨14641046887574767063654771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 78085583400398757672825445 14641046887574767063654771)
              ·
                refine ⟨21961570331362150595482157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14641046887574767063654771 21961570331362150595482157)
                ·
                  refine ⟨8235588874260806473305809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21961570331362150595482157 8235588874260806473305809)
                  ·
                    refine ⟨6176691655695604854979357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8235588874260806473305809 6176691655695604854979357)
                    ·
                      refine ⟨2316259370885851820617259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6176691655695604854979357 2316259370885851820617259)
                      ·
                        rfl

theorem cell23_4510899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 1, 3, 2, 3].length) (baseStart_4510899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4510899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4510899 prefixEnd_4510899 := by exact prefixLift 4510899
  have htrace : WordTrace (prefixWord ++ tailWord_4510899) baseStart_4510899 baseEnd_4510899 := by
    simpa [prefixWord, tailWord_4510899, baseEnd_4510899] using wordTrace_append hprefix tailTrace_4510899
  have hstable : (prefixWord ++ tailWord_4510899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4510899).length < 2 ^ (prefixWord ++ tailWord_4510899).sum := by decide
  have hdescent : baseEnd_4510899 < baseStart_4510899 := by decide
  rcases family_descends (prefixWord ++ tailWord_4510899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4510909 : List Nat := [1, 4, 1, 2, 1, 1, 4, 2, 1, 2, 4]
def baseStart_4510909 : Nat := 118140960795 + 4510909 * 2 ^ 59
def prefixEnd_4510909 : Nat := 4983230072969 + 3 ^ 40 * 4510909 * 2
def baseEnd_4510909 : Nat := 2316264505692396781492213

theorem tailTrace_4510909 : CollatzResearch.WordTrace tailWord_4510909 prefixEnd_4510909 2316264505692396781492213 := by
  unfold tailWord_4510909
  simp only [CollatzResearch.WordTrace]
  refine ⟨164526367614754569767479781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109684245076503046511653187 164526367614754569767479781)
  ·
    refine ⟨30848693927766481831402459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 164526367614754569767479781 30848693927766481831402459)
    ·
      refine ⟨46273040891649722747103689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30848693927766481831402459 46273040891649722747103689)
      ·
        refine ⟨34704780668737292060327767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46273040891649722747103689 34704780668737292060327767)
        ·
          refine ⟨52057171003105938090491651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34704780668737292060327767 52057171003105938090491651)
          ·
            refine ⟨78085756504658907135737477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52057171003105938090491651 78085756504658907135737477)
            ·
              refine ⟨14641079344623545087950777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 78085756504658907135737477 14641079344623545087950777)
              ·
                refine ⟨10980809508467658815963083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14641079344623545087950777 10980809508467658815963083)
                ·
                  refine ⟨16471214262701488223944625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10980809508467658815963083 16471214262701488223944625)
                  ·
                    refine ⟨12353410697026116167958469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16471214262701488223944625 12353410697026116167958469)
                    ·
                      refine ⟨2316264505692396781492213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12353410697026116167958469 2316264505692396781492213)
                      ·
                        rfl

theorem cell23_4510909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 2, 1, 2, 4].length) (baseStart_4510909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4510909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4510909 prefixEnd_4510909 := by exact prefixLift 4510909
  have htrace : WordTrace (prefixWord ++ tailWord_4510909) baseStart_4510909 baseEnd_4510909 := by
    simpa [prefixWord, tailWord_4510909, baseEnd_4510909] using wordTrace_append hprefix tailTrace_4510909
  have hstable : (prefixWord ++ tailWord_4510909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4510909).length < 2 ^ (prefixWord ++ tailWord_4510909).sum := by decide
  have hdescent : baseEnd_4510909 < baseStart_4510909 := by decide
  rcases family_descends (prefixWord ++ tailWord_4510909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4510913 : List Nat := [1, 2, 6, 1, 1, 2, 1, 3, 1, 1, 4]
def baseStart_4510913 : Nat := 118140960795 + 4510913 * 2 ^ 59
def prefixEnd_4510913 : Nat := 4983230072969 + 3 ^ 40 * 4510913 * 2
def baseEnd_4510913 : Nat := 2316266559615014765842195

theorem tailTrace_4510913 : CollatzResearch.WordTrace tailWord_4510913 prefixEnd_4510913 2316266559615014765842195 := by
  unfold tailWord_4510913
  simp only [CollatzResearch.WordTrace]
  refine ⟨164526513506740078450625393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109684342337826718967083595 164526513506740078450625393)
  ·
    refine ⟨123394885130055058837969045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164526513506740078450625393 123394885130055058837969045)
    ·
      refine ⟨5784135240471330883029799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 123394885130055058837969045 5784135240471330883029799)
      ·
        refine ⟨8676202860706996324544699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5784135240471330883029799 8676202860706996324544699)
        ·
          refine ⟨13014304291060494486817049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8676202860706996324544699 13014304291060494486817049)
          ·
            refine ⟨9760728218295370865112787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13014304291060494486817049 9760728218295370865112787)
            ·
              refine ⟨14641092327443056297669181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9760728218295370865112787 14641092327443056297669181)
              ·
                refine ⟨5490409622791146111625943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14641092327443056297669181 5490409622791146111625943)
                ·
                  refine ⟨8235614434186719167438915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5490409622791146111625943 8235614434186719167438915)
                  ·
                    refine ⟨12353421651280078751158373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8235614434186719167438915 12353421651280078751158373)
                    ·
                      refine ⟨2316266559615014765842195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12353421651280078751158373 2316266559615014765842195)
                      ·
                        rfl

theorem cell23_4510913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_4510913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4510913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4510913 prefixEnd_4510913 := by exact prefixLift 4510913
  have htrace : WordTrace (prefixWord ++ tailWord_4510913) baseStart_4510913 baseEnd_4510913 := by
    simpa [prefixWord, tailWord_4510913, baseEnd_4510913] using wordTrace_append hprefix tailTrace_4510913
  have hstable : (prefixWord ++ tailWord_4510913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4510913).length < 2 ^ (prefixWord ++ tailWord_4510913).sum := by decide
  have hdescent : baseEnd_4510913 < baseStart_4510913 := by decide
  rcases family_descends (prefixWord ++ tailWord_4510913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4510930 : List Nat := [3, 2, 2, 2, 1, 1, 1, 6, 1, 2, 2]
def baseStart_4510930 : Nat := 118140960795 + 4510930 * 2 ^ 59
def prefixEnd_4510930 : Nat := 4983230072969 + 3 ^ 40 * 4510930 * 2
def baseEnd_4510930 : Nat := 2316275288786141199329617

theorem tailTrace_4510930 : CollatzResearch.WordTrace tailWord_4510930 prefixEnd_4510930 2316275288786141199329617 := by
  unfold tailWord_4510930
  simp only [CollatzResearch.WordTrace]
  refine ⟨41131783386919622588498561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109684755698452326902662829 41131783386919622588498561)
  ·
    refine ⟨30848837540189716941373921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41131783386919622588498561 30848837540189716941373921)
    ·
      refine ⟨23136628155142287706030441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30848837540189716941373921 23136628155142287706030441)
      ·
        refine ⟨17352471116356715779522831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23136628155142287706030441 17352471116356715779522831)
        ·
          refine ⟨26028706674535073669284247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17352471116356715779522831 26028706674535073669284247)
          ·
            refine ⟨39043060011802610503926371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26028706674535073669284247 39043060011802610503926371)
            ·
              refine ⟨58564590017703915755889557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39043060011802610503926371 58564590017703915755889557)
              ·
                refine ⟨2745215157079871051057323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 58564590017703915755889557 2745215157079871051057323)
                ·
                  refine ⟨4117822735619806576585985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2745215157079871051057323 4117822735619806576585985)
                  ·
                    refine ⟨3088367051714854932439489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4117822735619806576585985 3088367051714854932439489)
                    ·
                      refine ⟨2316275288786141199329617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3088367051714854932439489 2316275288786141199329617)
                      ·
                        rfl

theorem cell23_4510930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 6, 1, 2, 2].length) (baseStart_4510930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4510930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4510930 prefixEnd_4510930 := by exact prefixLift 4510930
  have htrace : WordTrace (prefixWord ++ tailWord_4510930) baseStart_4510930 baseEnd_4510930 := by
    simpa [prefixWord, tailWord_4510930, baseEnd_4510930] using wordTrace_append hprefix tailTrace_4510930
  have hstable : (prefixWord ++ tailWord_4510930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4510930).length < 2 ^ (prefixWord ++ tailWord_4510930).sum := by decide
  have hdescent : baseEnd_4510930 < baseStart_4510930 := by decide
  rcases family_descends (prefixWord ++ tailWord_4510930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4510999 : List Nat := [1, 1, 3, 4, 1, 1, 2, 1, 1, 4, 4]
def baseStart_4510999 : Nat := 118140960795 + 4510999 * 2 ^ 59
def prefixEnd_4510999 : Nat := 4983230072969 + 3 ^ 40 * 4510999 * 2
def baseEnd_4510999 : Nat := 2316310718951301429366799

theorem tailTrace_4510999 : CollatzResearch.WordTrace tailWord_4510999 prefixEnd_4510999 2316310718951301429366799 := by
  unfold tailWord_4510999
  simp only [CollatzResearch.WordTrace]
  refine ⟨164529650184428515138256051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109686433456285676758837367 164529650184428515138256051)
  ·
    refine ⟨246794475276642772707384077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164529650184428515138256051 246794475276642772707384077)
    ·
      refine ⟨92547928228741039765269029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 246794475276642772707384077 92547928228741039765269029)
      ·
        refine ⟨17352736542888944955987943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 92547928228741039765269029 17352736542888944955987943)
        ·
          refine ⟨26029104814333417433981915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17352736542888944955987943 26029104814333417433981915)
          ·
            refine ⟨39043657221500126150972873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26029104814333417433981915 39043657221500126150972873)
            ·
              refine ⟨29282742916125094613229655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39043657221500126150972873 29282742916125094613229655)
              ·
                refine ⟨43924114374187641919844483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29282742916125094613229655 43924114374187641919844483)
                ·
                  refine ⟨65886171561281462879766725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43924114374187641919844483 65886171561281462879766725)
                  ·
                    refine ⟨12353657167740274289956261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 65886171561281462879766725 12353657167740274289956261)
                    ·
                      refine ⟨2316310718951301429366799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12353657167740274289956261 2316310718951301429366799)
                      ·
                        rfl

theorem cell23_4510999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_4510999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4510999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4510999 prefixEnd_4510999 := by exact prefixLift 4510999
  have htrace : WordTrace (prefixWord ++ tailWord_4510999) baseStart_4510999 baseEnd_4510999 := by
    simpa [prefixWord, tailWord_4510999, baseEnd_4510999] using wordTrace_append hprefix tailTrace_4510999
  have hstable : (prefixWord ++ tailWord_4510999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4510999).length < 2 ^ (prefixWord ++ tailWord_4510999).sum := by decide
  have hdescent : baseEnd_4510999 < baseStart_4510999 := by decide
  rcases family_descends (prefixWord ++ tailWord_4510999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4511007 : List Nat := [1, 1, 2, 4, 5, 1, 1, 2, 1, 3, 2]
def baseStart_4511007 : Nat := 118140960795 + 4511007 * 2 ^ 59
def prefixEnd_4511007 : Nat := 4983230072969 + 3 ^ 40 * 4511007 * 2
def baseEnd_4511007 : Nat := 2316314826796537398066763

theorem tailTrace_4511007 : CollatzResearch.WordTrace tailWord_4511007 prefixEnd_4511007 2316314826796537398066763 := by
  unfold tailWord_4511007
  simp only [CollatzResearch.WordTrace]
  refine ⟨164529941968399532504547275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109686627978933021669698183 164529941968399532504547275)
  ·
    refine ⟨246794912952599298756820913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164529941968399532504547275 246794912952599298756820913)
    ·
      refine ⟨185096184714449474067615685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 246794912952599298756820913 185096184714449474067615685)
      ·
        refine ⟨34705534633959276387677941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 185096184714449474067615685 34705534633959276387677941)
        ·
          refine ⟨3253643871933682161344807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 34705534633959276387677941 3253643871933682161344807)
          ·
            refine ⟨4880465807900523242017211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3253643871933682161344807 4880465807900523242017211)
            ·
              refine ⟨7320698711850784863025817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4880465807900523242017211 7320698711850784863025817)
              ·
                refine ⟨5490524033888088647269363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7320698711850784863025817 5490524033888088647269363)
                ·
                  refine ⟨8235786050832132970904045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5490524033888088647269363 8235786050832132970904045)
                  ·
                    refine ⟨3088419769062049864089017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8235786050832132970904045 3088419769062049864089017)
                    ·
                      refine ⟨2316314826796537398066763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3088419769062049864089017 2316314826796537398066763)
                      ·
                        rfl

theorem cell23_4511007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 1, 2, 1, 3, 2].length) (baseStart_4511007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4511007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4511007 prefixEnd_4511007 := by exact prefixLift 4511007
  have htrace : WordTrace (prefixWord ++ tailWord_4511007) baseStart_4511007 baseEnd_4511007 := by
    simpa [prefixWord, tailWord_4511007, baseEnd_4511007] using wordTrace_append hprefix tailTrace_4511007
  have hstable : (prefixWord ++ tailWord_4511007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4511007).length < 2 ^ (prefixWord ++ tailWord_4511007).sum := by decide
  have hdescent : baseEnd_4511007 < baseStart_4511007 := by decide
  rcases family_descends (prefixWord ++ tailWord_4511007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4511049 : List Nat := [1, 2, 1, 1, 2, 3, 4, 1, 1, 2, 5]
def baseStart_4511049 : Nat := 118140960795 + 4511049 * 2 ^ 59
def prefixEnd_4511049 : Nat := 4983230072969 + 3 ^ 40 * 4511049 * 2
def baseEnd_4511049 : Nat := 2316336392984026233741569

theorem tailTrace_4511049 : CollatzResearch.WordTrace tailWord_4511049 prefixEnd_4511049 2316336392984026233741569 := by
  unfold tailWord_4511049
  simp only [CollatzResearch.WordTrace]
  refine ⟨164531473834247373677576201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109687649222831582451717467 164531473834247373677576201)
  ·
    refine ⟨123398605375685530258182151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164531473834247373677576201 123398605375685530258182151)
    ·
      refine ⟨185097908063528295387273227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123398605375685530258182151 185097908063528295387273227)
      ·
        refine ⟨277646862095292443080909841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185097908063528295387273227 277646862095292443080909841)
        ·
          refine ⟨208235146571469332310682381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 277646862095292443080909841 208235146571469332310682381)
          ·
            refine ⟨78088179964300999616505893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 208235146571469332310682381 78088179964300999616505893)
            ·
              refine ⟨14641533743306437428094855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 78088179964300999616505893 14641533743306437428094855)
              ·
                refine ⟨21962300614959656142142283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14641533743306437428094855 21962300614959656142142283)
                ·
                  refine ⟨32943450922439484213213425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21962300614959656142142283 32943450922439484213213425)
                  ·
                    refine ⟨24707588191829613159910069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32943450922439484213213425 24707588191829613159910069)
                    ·
                      refine ⟨2316336392984026233741569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24707588191829613159910069 2316336392984026233741569)
                      ·
                        rfl

theorem cell23_4511049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 1, 1, 2, 5].length) (baseStart_4511049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4511049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4511049 prefixEnd_4511049 := by exact prefixLift 4511049
  have htrace : WordTrace (prefixWord ++ tailWord_4511049) baseStart_4511049 baseEnd_4511049 := by
    simpa [prefixWord, tailWord_4511049, baseEnd_4511049] using wordTrace_append hprefix tailTrace_4511049
  have hstable : (prefixWord ++ tailWord_4511049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4511049).length < 2 ^ (prefixWord ++ tailWord_4511049).sum := by decide
  have hdescent : baseEnd_4511049 < baseStart_4511049 := by decide
  rcases family_descends (prefixWord ++ tailWord_4511049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4511059 : List Nat := [1, 1, 1, 2, 1, 1, 6, 2, 1, 3, 4]
def baseStart_4511059 : Nat := 118140960795 + 4511059 * 2 ^ 59
def prefixEnd_4511059 : Nat := 4983230072969 + 3 ^ 40 * 4511059 * 2
def baseEnd_4511059 : Nat := 2316341527790571194616523

theorem tailTrace_4511059 : CollatzResearch.WordTrace tailWord_4511059 prefixEnd_4511059 2316341527790571194616523 := by
  unfold tailWord_4511059
  simp only [CollatzResearch.WordTrace]
  refine ⟨164531838564211145385440231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109687892376140763590293487 164531838564211145385440231)
  ·
    refine ⟨246797757846316718078160347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164531838564211145385440231 246797757846316718078160347)
    ·
      refine ⟨370196636769475077117240521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 246797757846316718078160347 370196636769475077117240521)
      ·
        refine ⟨277647477577106307837930391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 370196636769475077117240521 277647477577106307837930391)
        ·
          refine ⟨416471216365659461756895587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 277647477577106307837930391 416471216365659461756895587)
          ·
            refine ⟨624706824548489192635343381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 416471216365659461756895587 624706824548489192635343381)
            ·
              refine ⟨29283132400710430904781721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 624706824548489192635343381 29283132400710430904781721)
              ·
                refine ⟨21962349300532823178586291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29283132400710430904781721 21962349300532823178586291)
                ·
                  refine ⟨32943523950799234767879437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21962349300532823178586291 32943523950799234767879437)
                  ·
                    refine ⟨12353821481549713037954789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32943523950799234767879437 12353821481549713037954789)
                    ·
                      refine ⟨2316341527790571194616523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12353821481549713037954789 2316341527790571194616523)
                      ·
                        rfl

theorem cell23_4511059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 2, 1, 3, 4].length) (baseStart_4511059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4511059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4511059 prefixEnd_4511059 := by exact prefixLift 4511059
  have htrace : WordTrace (prefixWord ++ tailWord_4511059) baseStart_4511059 baseEnd_4511059 := by
    simpa [prefixWord, tailWord_4511059, baseEnd_4511059] using wordTrace_append hprefix tailTrace_4511059
  have hstable : (prefixWord ++ tailWord_4511059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4511059).length < 2 ^ (prefixWord ++ tailWord_4511059).sum := by decide
  have hdescent : baseEnd_4511059 < baseStart_4511059 := by decide
  rcases family_descends (prefixWord ++ tailWord_4511059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4511076 : List Nat := [2, 3, 1, 1, 3, 3, 1, 1, 1, 3, 4]
def baseStart_4511076 : Nat := 118140960795 + 4511076 * 2 ^ 59
def prefixEnd_4511076 : Nat := 4983230072969 + 3 ^ 40 * 4511076 * 2
def baseEnd_4511076 : Nat := 2316350256961697628103945

theorem tailTrace_4511076 : CollatzResearch.WordTrace tailWord_4511076 prefixEnd_4511076 2316350256961697628103945 := by
  unfold tailWord_4511076
  simp only [CollatzResearch.WordTrace]
  refine ⟨82266229302574778644404541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109688305736766371525872721 82266229302574778644404541)
  ·
    refine ⟨30849835988465541991651703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82266229302574778644404541 30849835988465541991651703)
    ·
      refine ⟨46274753982698312987477555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30849835988465541991651703 46274753982698312987477555)
      ·
        refine ⟨69412130974047469481216333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46274753982698312987477555 69412130974047469481216333)
        ·
          refine ⟨26029549115267801055456125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69412130974047469481216333 26029549115267801055456125)
          ·
            refine ⟨9761080918225425395796047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26029549115267801055456125 9761080918225425395796047)
            ·
              refine ⟨14641621377338138093694071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9761080918225425395796047 14641621377338138093694071)
              ·
                refine ⟨21962432066007207140541107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14641621377338138093694071 21962432066007207140541107)
                ·
                  refine ⟨32943648099010810710811661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21962432066007207140541107 32943648099010810710811661)
                  ·
                    refine ⟨12353868037129054016554373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32943648099010810710811661 12353868037129054016554373)
                    ·
                      refine ⟨2316350256961697628103945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12353868037129054016554373 2316350256961697628103945)
                      ·
                        rfl

theorem cell23_4511076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 1, 1, 3, 4].length) (baseStart_4511076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4511076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4511076 prefixEnd_4511076 := by exact prefixLift 4511076
  have htrace : WordTrace (prefixWord ++ tailWord_4511076) baseStart_4511076 baseEnd_4511076 := by
    simpa [prefixWord, tailWord_4511076, baseEnd_4511076] using wordTrace_append hprefix tailTrace_4511076
  have hstable : (prefixWord ++ tailWord_4511076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4511076).length < 2 ^ (prefixWord ++ tailWord_4511076).sum := by decide
  have hdescent : baseEnd_4511076 < baseStart_4511076 := by decide
  rcases family_descends (prefixWord ++ tailWord_4511076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4511089 : List Nat := [1, 2, 2, 2, 1, 2, 3, 1, 2, 1, 6]
def baseStart_4511089 : Nat := 118140960795 + 4511089 * 2 ^ 59
def prefixEnd_4511089 : Nat := 4983230072969 + 3 ^ 40 * 4511089 * 2
def baseEnd_4511089 : Nat := 2316356932210206077241385

theorem tailTrace_4511089 : CollatzResearch.WordTrace tailWord_4511089 prefixEnd_4511089 2316356932210206077241385 := by
  unfold tailWord_4511089
  simp only [CollatzResearch.WordTrace]
  refine ⟨164532932754102460509032321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109688621836068307006021547 164532932754102460509032321)
  ·
    refine ⟨123399699565576845381774241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164532932754102460509032321 123399699565576845381774241)
    ·
      refine ⟨92549774674182634036330681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123399699565576845381774241 92549774674182634036330681)
      ·
        refine ⟨69412331005636975527248011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92549774674182634036330681 69412331005636975527248011)
        ·
          refine ⟨104118496508455463290872017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69412331005636975527248011 104118496508455463290872017)
          ·
            refine ⟨78088872381341597468154013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104118496508455463290872017 78088872381341597468154013)
            ·
              refine ⟨29283327143003099050557755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78088872381341597468154013 29283327143003099050557755)
              ·
                refine ⟨43924990714504648575836633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29283327143003099050557755 43924990714504648575836633)
                ·
                  refine ⟨32943743035878486431877475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43924990714504648575836633 32943743035878486431877475)
                  ·
                    refine ⟨49415614553817729647816213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32943743035878486431877475 49415614553817729647816213)
                    ·
                      refine ⟨2316356932210206077241385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49415614553817729647816213 2316356932210206077241385)
                      ·
                        rfl

theorem cell23_4511089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 1, 2, 1, 6].length) (baseStart_4511089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4511089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4511089 prefixEnd_4511089 := by exact prefixLift 4511089
  have htrace : WordTrace (prefixWord ++ tailWord_4511089) baseStart_4511089 baseEnd_4511089 := by
    simpa [prefixWord, tailWord_4511089, baseEnd_4511089] using wordTrace_append hprefix tailTrace_4511089
  have hstable : (prefixWord ++ tailWord_4511089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4511089).length < 2 ^ (prefixWord ++ tailWord_4511089).sum := by decide
  have hdescent : baseEnd_4511089 < baseStart_4511089 := by decide
  rcases family_descends (prefixWord ++ tailWord_4511089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4511099 : List Nat := [1, 1, 1, 1, 1, 6, 3, 1, 8]
def baseStart_4511099 : Nat := 118140960795 + 4511099 * 2 ^ 59
def prefixEnd_4511099 : Nat := 4983230072969 + 3 ^ 40 * 4511099 * 2
def baseEnd_4511099 : Nat := 257373563001861226457371

theorem tailTrace_4511099 : CollatzResearch.WordTrace tailWord_4511099 prefixEnd_4511099 257373563001861226457371 := by
  unfold tailWord_4511099
  simp only [CollatzResearch.WordTrace]
  refine ⟨164533297484066232216896351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109688864989377488144597567 164533297484066232216896351)
  ·
    refine ⟨246799946226099348325344527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164533297484066232216896351 246799946226099348325344527)
    ·
      refine ⟨370199919339149022488016791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 246799946226099348325344527 370199919339149022488016791)
      ·
        refine ⟨555299879008723533732025187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 370199919339149022488016791 555299879008723533732025187)
        ·
          refine ⟨832949818513085300598037781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 555299879008723533732025187 832949818513085300598037781)
          ·
            refine ⟨39044522742800873465533021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 832949818513085300598037781 39044522742800873465533021)
            ·
              refine ⟨14641696028550327549574883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39044522742800873465533021 14641696028550327549574883)
              ·
                refine ⟨21962544042825491324362325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14641696028550327549574883 21962544042825491324362325)
                ·
                  refine ⟨257373563001861226457371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21962544042825491324362325 257373563001861226457371)
                  ·
                    rfl

theorem cell23_4511099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 1, 8].length) (baseStart_4511099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4511099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4511099 prefixEnd_4511099 := by exact prefixLift 4511099
  have htrace : WordTrace (prefixWord ++ tailWord_4511099) baseStart_4511099 baseEnd_4511099 := by
    simpa [prefixWord, tailWord_4511099, baseEnd_4511099] using wordTrace_append hprefix tailTrace_4511099
  have hstable : (prefixWord ++ tailWord_4511099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4511099).length < 2 ^ (prefixWord ++ tailWord_4511099).sum := by decide
  have hdescent : baseEnd_4511099 < baseStart_4511099 := by decide
  rcases family_descends (prefixWord ++ tailWord_4511099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4511160 : List Nat := [2, 1, 2, 1, 2, 2, 2, 6, 1, 1, 3]
def baseStart_4511160 : Nat := 118140960795 + 4511160 * 2 ^ 59
def prefixEnd_4511160 : Nat := 4983230072969 + 3 ^ 40 * 4511160 * 2
def baseEnd_4511160 : Nat := 2316393389336675299453559

theorem tailTrace_4511160 : CollatzResearch.WordTrace tailWord_4511160 prefixEnd_4511160 2316393389336675299453559 := by
  unfold tailWord_4511160
  simp only [CollatzResearch.WordTrace]
  refine ⟨82267761168422619817433467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109690348224563493089911289 82267761168422619817433467)
  ·
    refine ⟨123401641752633929726150201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82267761168422619817433467 123401641752633929726150201)
    ·
      refine ⟨92551231314475447294612651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123401641752633929726150201 92551231314475447294612651)
      ·
        refine ⟨138826846971713170941918977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92551231314475447294612651 138826846971713170941918977)
        ·
          refine ⟨104120135228784878206439233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 138826846971713170941918977 104120135228784878206439233)
          ·
            refine ⟨78090101421588658654829425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104120135228784878206439233 78090101421588658654829425)
            ·
              refine ⟨58567576066191493991122069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78090101421588658654829425 58567576066191493991122069)
              ·
                refine ⟨2745355128102726280833847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 58567576066191493991122069 2745355128102726280833847)
                ·
                  refine ⟨4118032692154089421250771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2745355128102726280833847 4118032692154089421250771)
                  ·
                    refine ⟨6177049038231134131876157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4118032692154089421250771 6177049038231134131876157)
                    ·
                      refine ⟨2316393389336675299453559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6177049038231134131876157 2316393389336675299453559)
                      ·
                        rfl

theorem cell23_4511160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 6, 1, 1, 3].length) (baseStart_4511160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4511160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4511160 prefixEnd_4511160 := by exact prefixLift 4511160
  have htrace : WordTrace (prefixWord ++ tailWord_4511160) baseStart_4511160 baseEnd_4511160 := by
    simpa [prefixWord, tailWord_4511160, baseEnd_4511160] using wordTrace_append hprefix tailTrace_4511160
  have hstable : (prefixWord ++ tailWord_4511160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4511160).length < 2 ^ (prefixWord ++ tailWord_4511160).sum := by decide
  have hdescent : baseEnd_4511160 < baseStart_4511160 := by decide
  rcases family_descends (prefixWord ++ tailWord_4511160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4511166 : List Nat := [4, 2, 1, 1, 1, 1, 1, 1, 2, 5, 4]
def baseStart_4511166 : Nat := 118140960795 + 4511166 * 2 ^ 59
def prefixEnd_4511166 : Nat := 4983230072969 + 3 ^ 40 * 4511166 * 2
def baseEnd_4511166 : Nat := 2316396470220602275978531

theorem tailTrace_4511166 : CollatzResearch.WordTrace tailWord_4511166 prefixEnd_4511166 2316396470220602275978531 := by
  unfold tailWord_4511166
  simp only [CollatzResearch.WordTrace]
  refine ⟨20566967646852937832448169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109690494116549001773056901 20566967646852937832448169)
  ·
    refine ⟨15425225735139703374336127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20566967646852937832448169 15425225735139703374336127)
    ·
      refine ⟨23137838602709555061504191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15425225735139703374336127 23137838602709555061504191)
      ·
        refine ⟨34706757904064332592256287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23137838602709555061504191 34706757904064332592256287)
        ·
          refine ⟨52060136856096498888384431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34706757904064332592256287 52060136856096498888384431)
          ·
            refine ⟨78090205284144748332576647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52060136856096498888384431 78090205284144748332576647)
            ·
              refine ⟨117135307926217122498864971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78090205284144748332576647 117135307926217122498864971)
              ·
                refine ⟨175702961889325683748297457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 117135307926217122498864971 175702961889325683748297457)
                ·
                  refine ⟨131777221416994262811223093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 175702961889325683748297457 131777221416994262811223093)
                  ·
                    refine ⟨12354114507843212138552165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 131777221416994262811223093 12354114507843212138552165)
                    ·
                      refine ⟨2316396470220602275978531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12354114507843212138552165 2316396470220602275978531)
                      ·
                        rfl

theorem cell23_4511166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 2, 5, 4].length) (baseStart_4511166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4511166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4511166 prefixEnd_4511166 := by exact prefixLift 4511166
  have htrace : WordTrace (prefixWord ++ tailWord_4511166) baseStart_4511166 baseEnd_4511166 := by
    simpa [prefixWord, tailWord_4511166, baseEnd_4511166] using wordTrace_append hprefix tailTrace_4511166
  have hstable : (prefixWord ++ tailWord_4511166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4511166).length < 2 ^ (prefixWord ++ tailWord_4511166).sum := by decide
  have hdescent : baseEnd_4511166 < baseStart_4511166 := by decide
  rcases family_descends (prefixWord ++ tailWord_4511166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4511176 : List Nat := [2, 1, 3, 1, 3, 1, 2, 3, 1, 6]
def baseStart_4511176 : Nat := 118140960795 + 4511176 * 2 ^ 59
def prefixEnd_4511176 : Nat := 4983230072969 + 3 ^ 40 * 4511176 * 2
def baseEnd_4511176 : Nat := 772133868342382412284495

theorem tailTrace_4511176 : CollatzResearch.WordTrace tailWord_4511176 prefixEnd_4511176 772133868342382412284495 := by
  unfold tailWord_4511176
  simp only [CollatzResearch.WordTrace]
  refine ⟨82268052952393637183724691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109690737269858182911632921 82268052952393637183724691)
  ·
    refine ⟨123402079428590455775587037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82268052952393637183724691 123402079428590455775587037)
    ·
      refine ⟨46275779785721420915845139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123402079428590455775587037 46275779785721420915845139)
      ·
        refine ⟨69413669678582131373767709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46275779785721420915845139 69413669678582131373767709)
        ·
          refine ⟨26030126129468299265162891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69413669678582131373767709 26030126129468299265162891)
          ·
            refine ⟨39045189194202448897744337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26030126129468299265162891 39045189194202448897744337)
            ·
              refine ⟨29283891895651836673308253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39045189194202448897744337 29283891895651836673308253)
              ·
                refine ⟨10981459460869438752490595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29283891895651836673308253 10981459460869438752490595)
                ·
                  refine ⟨16472189191304158128735893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10981459460869438752490595 16472189191304158128735893)
                  ·
                    refine ⟨772133868342382412284495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16472189191304158128735893 772133868342382412284495)
                    ·
                      rfl

theorem cell23_4511176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 3, 1, 6].length) (baseStart_4511176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4511176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4511176 prefixEnd_4511176 := by exact prefixLift 4511176
  have htrace : WordTrace (prefixWord ++ tailWord_4511176) baseStart_4511176 baseEnd_4511176 := by
    simpa [prefixWord, tailWord_4511176, baseEnd_4511176] using wordTrace_append hprefix tailTrace_4511176
  have hstable : (prefixWord ++ tailWord_4511176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4511176).length < 2 ^ (prefixWord ++ tailWord_4511176).sum := by decide
  have hdescent : baseEnd_4511176 < baseStart_4511176 := by decide
  rcases family_descends (prefixWord ++ tailWord_4511176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4511180 : List Nat := [2, 2, 1, 4, 2, 3, 1, 2, 1, 5]
def baseStart_4511180 : Nat := 118140960795 + 4511180 * 2 ^ 59
def prefixEnd_4511180 : Nat := 4983230072969 + 3 ^ 40 * 4511180 * 2
def baseEnd_4511180 : Nat := 772134552983255073734489

theorem tailTrace_4511180 : CollatzResearch.WordTrace tailWord_4511180 prefixEnd_4511180 772134552983255073734489 := by
  unfold tailWord_4511180
  simp only [CollatzResearch.WordTrace]
  refine ⟨82268125898386391525297497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109690834531181855367063329 82268125898386391525297497)
  ·
    refine ⟨61701094423789793643973123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82268125898386391525297497 61701094423789793643973123)
    ·
      refine ⟨92551641635684690465959685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61701094423789793643973123 92551641635684690465959685)
      ·
        refine ⟨17353432806690879462367441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 92551641635684690465959685 17353432806690879462367441)
        ·
          refine ⟨13015074605018159596775581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17353432806690879462367441 13015074605018159596775581)
          ·
            refine ⟨4880652976881809848790843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13015074605018159596775581 4880652976881809848790843)
            ·
              refine ⟨7320979465322714773186265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4880652976881809848790843 7320979465322714773186265)
              ·
                refine ⟨5490734598992036079889699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7320979465322714773186265 5490734598992036079889699)
                ·
                  refine ⟨8236101898488054119834549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5490734598992036079889699 8236101898488054119834549)
                  ·
                    refine ⟨772134552983255073734489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8236101898488054119834549 772134552983255073734489)
                    ·
                      rfl

theorem cell23_4511180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 1, 2, 1, 5].length) (baseStart_4511180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4511180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4511180 prefixEnd_4511180 := by exact prefixLift 4511180
  have htrace : WordTrace (prefixWord ++ tailWord_4511180) baseStart_4511180 baseEnd_4511180 := by
    simpa [prefixWord, tailWord_4511180, baseEnd_4511180] using wordTrace_append hprefix tailTrace_4511180
  have hstable : (prefixWord ++ tailWord_4511180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4511180).length < 2 ^ (prefixWord ++ tailWord_4511180).sum := by decide
  have hdescent : baseEnd_4511180 < baseStart_4511180 := by decide
  rcases family_descends (prefixWord ++ tailWord_4511180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4511183 : List Nat := [1, 1, 2, 1, 1, 4, 5, 2, 1, 1, 4]
def baseStart_4511183 : Nat := 118140960795 + 4511183 * 2 ^ 59
def prefixEnd_4511183 : Nat := 4983230072969 + 3 ^ 40 * 4511183 * 2
def baseEnd_4511183 : Nat := 2316405199391728709465953

theorem tailTrace_4511183 : CollatzResearch.WordTrace tailWord_4511183 prefixEnd_4511183 2316405199391728709465953 := by
  unfold tailWord_4511183
  simp only [CollatzResearch.WordTrace]
  refine ⟨164536361215761914562954203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109690907477174609708636135 164536361215761914562954203)
  ·
    refine ⟨246804541823642871844431305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164536361215761914562954203 246804541823642871844431305)
    ·
      refine ⟨185103406367732153883323479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 246804541823642871844431305 185103406367732153883323479)
      ·
        refine ⟨277655109551598230824985219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185103406367732153883323479 277655109551598230824985219)
        ·
          refine ⟨416482664327397346237477829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 277655109551598230824985219 416482664327397346237477829)
          ·
            refine ⟨78090499561387002419527093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 416482664327397346237477829 78090499561387002419527093)
            ·
              refine ⟨7320984333880031476830665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 78090499561387002419527093 7320984333880031476830665)
              ·
                refine ⟨5490738250410023607622999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7320984333880031476830665 5490738250410023607622999)
                ·
                  refine ⟨8236107375615035411434499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5490738250410023607622999 8236107375615035411434499)
                  ·
                    refine ⟨12354161063422553117151749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8236107375615035411434499 12354161063422553117151749)
                    ·
                      refine ⟨2316405199391728709465953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12354161063422553117151749 2316405199391728709465953)
                      ·
                        rfl

theorem cell23_4511183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 5, 2, 1, 1, 4].length) (baseStart_4511183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4511183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4511183 prefixEnd_4511183 := by exact prefixLift 4511183
  have htrace : WordTrace (prefixWord ++ tailWord_4511183) baseStart_4511183 baseEnd_4511183 := by
    simpa [prefixWord, tailWord_4511183, baseEnd_4511183] using wordTrace_append hprefix tailTrace_4511183
  have hstable : (prefixWord ++ tailWord_4511183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4511183).length < 2 ^ (prefixWord ++ tailWord_4511183).sum := by decide
  have hdescent : baseEnd_4511183 < baseStart_4511183 := by decide
  rcases family_descends (prefixWord ++ tailWord_4511183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4511203 : List Nat := [1, 1, 1, 6, 2, 1, 3, 1, 1, 1, 5]
def baseStart_4511203 : Nat := 118140960795 + 4511203 * 2 ^ 59
def prefixEnd_4511203 : Nat := 4983230072969 + 3 ^ 40 * 4511203 * 2
def baseEnd_4511203 : Nat := 2316415469004818631215861

theorem tailTrace_4511203 : CollatzResearch.WordTrace tailWord_4511203 prefixEnd_4511203 2316415469004818631215861 := by
  unfold tailWord_4511203
  simp only [CollatzResearch.WordTrace]
  refine ⟨164537090675689457978682263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109691393783792971985788175 164537090675689457978682263)
  ·
    refine ⟨246805636013534186968023395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164537090675689457978682263 246805636013534186968023395)
    ·
      refine ⟨370208454020301280452035093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 246805636013534186968023395 370208454020301280452035093)
      ·
        refine ⟨17353521282201622521189145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 370208454020301280452035093 17353521282201622521189145)
        ·
          refine ⟨13015140961651216890891859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17353521282201622521189145 13015140961651216890891859)
          ·
            refine ⟨19522711442476825336337789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13015140961651216890891859 19522711442476825336337789)
            ·
              refine ⟨7321016790928809501126671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19522711442476825336337789 7321016790928809501126671)
              ·
                refine ⟨10981525186393214251690007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7321016790928809501126671 10981525186393214251690007)
                ·
                  refine ⟨16472287779589821377535011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10981525186393214251690007 16472287779589821377535011)
                  ·
                    refine ⟨24708431669384732066302517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16472287779589821377535011 24708431669384732066302517)
                    ·
                      refine ⟨2316415469004818631215861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24708431669384732066302517 2316415469004818631215861)
                      ·
                        rfl

theorem cell23_4511203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 3, 1, 1, 1, 5].length) (baseStart_4511203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4511203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4511203 prefixEnd_4511203 := by exact prefixLift 4511203
  have htrace : WordTrace (prefixWord ++ tailWord_4511203) baseStart_4511203 baseEnd_4511203 := by
    simpa [prefixWord, tailWord_4511203, baseEnd_4511203] using wordTrace_append hprefix tailTrace_4511203
  have hstable : (prefixWord ++ tailWord_4511203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4511203).length < 2 ^ (prefixWord ++ tailWord_4511203).sum := by decide
  have hdescent : baseEnd_4511203 < baseStart_4511203 := by decide
  rcases family_descends (prefixWord ++ tailWord_4511203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4511234 : List Nat := [3, 4, 1, 2, 1, 2, 1, 2, 3, 2, 2]
def baseStart_4511234 : Nat := 118140960795 + 4511234 * 2 ^ 59
def prefixEnd_4511234 : Nat := 4983230072969 + 3 ^ 40 * 4511234 * 2
def baseEnd_4511234 : Nat := 2316431386905108009928219

theorem tailTrace_4511234 : CollatzResearch.WordTrace tailWord_4511234 prefixEnd_4511234 2316431386905108009928219 := by
  unfold tailWord_4511234
  simp only [CollatzResearch.WordTrace]
  refine ⟨41134555334644287568265189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109692147559051433515373837 41134555334644287568265189)
  ·
    refine ⟨7712729125245803919049723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41134555334644287568265189 7712729125245803919049723)
    ·
      refine ⟨11569093687868705878574585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7712729125245803919049723 11569093687868705878574585)
      ·
        refine ⟨8676820265901529408930939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11569093687868705878574585 8676820265901529408930939)
        ·
          refine ⟨13015230398852294113396409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8676820265901529408930939 13015230398852294113396409)
          ·
            refine ⟨9761422799139220585047307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13015230398852294113396409 9761422799139220585047307)
            ·
              refine ⟨14642134198708830877570961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9761422799139220585047307 14642134198708830877570961)
              ·
                refine ⟨10981600649031623158178221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14642134198708830877570961 10981600649031623158178221)
                ·
                  refine ⟨4118100243386858684316833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10981600649031623158178221 4118100243386858684316833)
                  ·
                    refine ⟨3088575182540144013237625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4118100243386858684316833 3088575182540144013237625)
                    ·
                      refine ⟨2316431386905108009928219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3088575182540144013237625 2316431386905108009928219)
                      ·
                        rfl

theorem cell23_4511234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 2, 3, 2, 2].length) (baseStart_4511234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4511234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4511234 prefixEnd_4511234 := by exact prefixLift 4511234
  have htrace : WordTrace (prefixWord ++ tailWord_4511234) baseStart_4511234 baseEnd_4511234 := by
    simpa [prefixWord, tailWord_4511234, baseEnd_4511234] using wordTrace_append hprefix tailTrace_4511234
  have hstable : (prefixWord ++ tailWord_4511234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4511234).length < 2 ^ (prefixWord ++ tailWord_4511234).sum := by decide
  have hdescent : baseEnd_4511234 < baseStart_4511234 := by decide
  rcases family_descends (prefixWord ++ tailWord_4511234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4511238 : List Nat := [6, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2]
def baseStart_4511238 : Nat := 118140960795 + 4511238 * 2 ^ 59
def prefixEnd_4511238 : Nat := 4983230072969 + 3 ^ 40 * 4511238 * 2
def baseEnd_4511238 : Nat := 2316433440827725994278201

theorem tailTrace_4511238 : CollatzResearch.WordTrace tailWord_4511238 prefixEnd_4511238 2316433440827725994278201 := by
  unfold tailWord_4511238
  simp only [CollatzResearch.WordTrace]
  refine ⟨5141823975955083092381449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 109692244820375105970804245 5141823975955083092381449)
  ·
    refine ⟨3856367981966312319286087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5141823975955083092381449 3856367981966312319286087)
    ·
      refine ⟨5784551972949468478929131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3856367981966312319286087 5784551972949468478929131)
      ·
        refine ⟨8676827959424202718393697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5784551972949468478929131 8676827959424202718393697)
        ·
          refine ⟨6507620969568152038795273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8676827959424202718393697 6507620969568152038795273)
          ·
            refine ⟨4880715727176114029096455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6507620969568152038795273 4880715727176114029096455)
            ·
              refine ⟨7321073590764171043644683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4880715727176114029096455 7321073590764171043644683)
              ·
                refine ⟨10981610386146256565467025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7321073590764171043644683 10981610386146256565467025)
                ·
                  refine ⟨8236207789609692424100269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10981610386146256565467025 8236207789609692424100269)
                  ·
                    refine ⟨3088577921103634659037601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8236207789609692424100269 3088577921103634659037601)
                    ·
                      refine ⟨2316433440827725994278201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3088577921103634659037601 2316433440827725994278201)
                      ·
                        rfl

theorem cell23_4511238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2].length) (baseStart_4511238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4511238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4511238 prefixEnd_4511238 := by exact prefixLift 4511238
  have htrace : WordTrace (prefixWord ++ tailWord_4511238) baseStart_4511238 baseEnd_4511238 := by
    simpa [prefixWord, tailWord_4511238, baseEnd_4511238] using wordTrace_append hprefix tailTrace_4511238
  have hstable : (prefixWord ++ tailWord_4511238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4511238).length < 2 ^ (prefixWord ++ tailWord_4511238).sum := by decide
  have hdescent : baseEnd_4511238 < baseStart_4511238 := by decide
  rcases family_descends (prefixWord ++ tailWord_4511238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4511276 : List Nat := [2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 5]
def baseStart_4511276 : Nat := 118140960795 + 4511276 * 2 ^ 59
def prefixEnd_4511276 : Nat := 4983230072969 + 3 ^ 40 * 4511276 * 2
def baseEnd_4511276 : Nat := 2316452953092596845603025

theorem tailTrace_4511276 : CollatzResearch.WordTrace tailWord_4511276 prefixEnd_4511276 2316452953092596845603025 := by
  unfold tailWord_4511276
  simp only [CollatzResearch.WordTrace]
  refine ⟨82269876602212495723044841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109693168802949994297393121 82269876602212495723044841)
  ·
    refine ⟨61702407451659371792283631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82269876602212495723044841 61702407451659371792283631)
    ·
      refine ⟨92553611177489057688425447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61702407451659371792283631 92553611177489057688425447)
      ·
        refine ⟨138830416766233586532638171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92553611177489057688425447 138830416766233586532638171)
        ·
          refine ⟨208245625149350379798957257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138830416766233586532638171 208245625149350379798957257)
          ·
            refine ⟨156184218862012784849217943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 208245625149350379798957257 156184218862012784849217943)
            ·
              refine ⟨234276328293019177273826915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 156184218862012784849217943 234276328293019177273826915)
              ·
                refine ⟨351414492439528765910740373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 234276328293019177273826915 351414492439528765910740373)
                ·
                  refine ⟨16472554333102910902065955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 351414492439528765910740373 16472554333102910902065955)
                  ·
                    refine ⟨24708831499654366353098933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16472554333102910902065955 24708831499654366353098933)
                    ·
                      refine ⟨2316452953092596845603025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24708831499654366353098933 2316452953092596845603025)
                      ·
                        rfl

theorem cell23_4511276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 5].length) (baseStart_4511276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4511276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4511276 prefixEnd_4511276 := by exact prefixLift 4511276
  have htrace : WordTrace (prefixWord ++ tailWord_4511276) baseStart_4511276 baseEnd_4511276 := by
    simpa [prefixWord, tailWord_4511276, baseEnd_4511276] using wordTrace_append hprefix tailTrace_4511276
  have hstable : (prefixWord ++ tailWord_4511276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4511276).length < 2 ^ (prefixWord ++ tailWord_4511276).sum := by decide
  have hdescent : baseEnd_4511276 < baseStart_4511276 := by decide
  rcases family_descends (prefixWord ++ tailWord_4511276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4511414 : List Nat := [5, 1, 3, 1, 1, 1, 3, 1, 2, 1, 4]
def baseStart_4511414 : Nat := 118140960795 + 4511414 * 2 ^ 59
def prefixEnd_4511414 : Nat := 4983230072969 + 3 ^ 40 * 4511414 * 2
def baseEnd_4511414 : Nat := 2316523813422917305677391

theorem tailTrace_4511414 : CollatzResearch.WordTrace tailWord_4511414 prefixEnd_4511414 2316523813422917305677391 := by
  unfold tailWord_4511414
  simp only [CollatzResearch.WordTrace]
  refine ⟨10284049154870315063413331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 109696524318616694009742197 10284049154870315063413331)
  ·
    refine ⟨15426073732305472595119997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10284049154870315063413331 15426073732305472595119997)
    ·
      refine ⟨5784777649614552223169999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15426073732305472595119997 5784777649614552223169999)
      ·
        refine ⟨8677166474421828334754999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5784777649614552223169999 8677166474421828334754999)
        ·
          refine ⟨13015749711632742502132499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8677166474421828334754999 13015749711632742502132499)
          ·
            refine ⟨19523624567449113753198749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13015749711632742502132499 19523624567449113753198749)
            ·
              refine ⟨7321359212793417657449531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19523624567449113753198749 7321359212793417657449531)
              ·
                refine ⟨10982038819190126486174297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7321359212793417657449531 10982038819190126486174297)
                ·
                  refine ⟨8236529114392594864630723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10982038819190126486174297 8236529114392594864630723)
                  ·
                    refine ⟨12354793671588892296946085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8236529114392594864630723 12354793671588892296946085)
                    ·
                      refine ⟨2316523813422917305677391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12354793671588892296946085 2316523813422917305677391)
                      ·
                        rfl

theorem cell23_4511414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_4511414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4511414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4511414 prefixEnd_4511414 := by exact prefixLift 4511414
  have htrace : WordTrace (prefixWord ++ tailWord_4511414) baseStart_4511414 baseEnd_4511414 := by
    simpa [prefixWord, tailWord_4511414, baseEnd_4511414] using wordTrace_append hprefix tailTrace_4511414
  have hstable : (prefixWord ++ tailWord_4511414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4511414).length < 2 ^ (prefixWord ++ tailWord_4511414).sum := by decide
  have hdescent : baseEnd_4511414 < baseStart_4511414 := by decide
  rcases family_descends (prefixWord ++ tailWord_4511414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4511437 : List Nat := [1, 6, 2, 1, 1, 2, 1, 1, 8]
def baseStart_4511437 : Nat := 118140960795 + 4511437 * 2 ^ 59
def prefixEnd_4511437 : Nat := 4983230072969 + 3 ^ 40 * 4511437 * 2
def baseEnd_4511437 : Nat := 257392847053107857298865

theorem tailTrace_4511437 : CollatzResearch.WordTrace tailWord_4511437 prefixEnd_4511437 257392847053107857298865 := by
  unfold tailWord_4511437
  simp only [CollatzResearch.WordTrace]
  refine ⟨164545625356841715942700565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109697083571227810628467043 164545625356841715942700565)
  ·
    refine ⟨7713076188601955434814089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 164545625356841715942700565 7713076188601955434814089)
    ·
      refine ⟨5784807141451466576110567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7713076188601955434814089 5784807141451466576110567)
      ·
        refine ⟨8677210712177199864165851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5784807141451466576110567 8677210712177199864165851)
        ·
          refine ⟨13015816068265799796248777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8677210712177199864165851 13015816068265799796248777)
          ·
            refine ⟨9761862051199349847186583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13015816068265799796248777 9761862051199349847186583)
            ·
              refine ⟨14642793076799024770779875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9761862051199349847186583 14642793076799024770779875)
              ·
                refine ⟨21964189615198537156169813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14642793076799024770779875 21964189615198537156169813)
                ·
                  refine ⟨257392847053107857298865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21964189615198537156169813 257392847053107857298865)
                  ·
                    rfl

theorem cell23_4511437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 1, 8].length) (baseStart_4511437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4511437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4511437 prefixEnd_4511437 := by exact prefixLift 4511437
  have htrace : WordTrace (prefixWord ++ tailWord_4511437) baseStart_4511437 baseEnd_4511437 := by
    simpa [prefixWord, tailWord_4511437, baseEnd_4511437] using wordTrace_append hprefix tailTrace_4511437
  have hstable : (prefixWord ++ tailWord_4511437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4511437).length < 2 ^ (prefixWord ++ tailWord_4511437).sum := by decide
  have hdescent : baseEnd_4511437 < baseStart_4511437 := by decide
  rcases family_descends (prefixWord ++ tailWord_4511437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4511447 : List Nat := [1, 1, 3, 2, 1, 3, 4, 1, 3, 1, 3]
def baseStart_4511447 : Nat := 118140960795 + 4511447 * 2 ^ 59
def prefixEnd_4511447 : Nat := 4983230072969 + 3 ^ 40 * 4511447 * 2
def baseEnd_4511447 : Nat := 2316540758284515676564739

theorem tailTrace_4511447 : CollatzResearch.WordTrace tailWord_4511447 prefixEnd_4511447 2316540758284515676564739 := by
  unfold tailWord_4511447
  simp only [CollatzResearch.WordTrace]
  refine ⟨164545990086805487650564595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109697326724536991767043063 164545990086805487650564595)
  ·
    refine ⟨246818985130208231475846893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164545990086805487650564595 246818985130208231475846893)
    ·
      refine ⟨92557119423828086803442585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 246818985130208231475846893 92557119423828086803442585)
      ·
        refine ⟨69417839567871065102581939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92557119423828086803442585 69417839567871065102581939)
        ·
          refine ⟨104126759351806597653872909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69417839567871065102581939 104126759351806597653872909)
          ·
            refine ⟨39047534756927474120202341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 104126759351806597653872909 39047534756927474120202341)
            ·
              refine ⟨7321412766923901397537939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39047534756927474120202341 7321412766923901397537939)
              ·
                refine ⟨10982119150385852096306909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7321412766923901397537939 10982119150385852096306909)
                ·
                  refine ⟨4118294681394694536115091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10982119150385852096306909 4118294681394694536115091)
                  ·
                    refine ⟨6177442022092041804172637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4118294681394694536115091 6177442022092041804172637)
                    ·
                      refine ⟨2316540758284515676564739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6177442022092041804172637 2316540758284515676564739)
                      ·
                        rfl

theorem cell23_4511447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 4, 1, 3, 1, 3].length) (baseStart_4511447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4511447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4511447 prefixEnd_4511447 := by exact prefixLift 4511447
  have htrace : WordTrace (prefixWord ++ tailWord_4511447) baseStart_4511447 baseEnd_4511447 := by
    simpa [prefixWord, tailWord_4511447, baseEnd_4511447] using wordTrace_append hprefix tailTrace_4511447
  have hstable : (prefixWord ++ tailWord_4511447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4511447).length < 2 ^ (prefixWord ++ tailWord_4511447).sum := by decide
  have hdescent : baseEnd_4511447 < baseStart_4511447 := by decide
  rcases family_descends (prefixWord ++ tailWord_4511447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4511487 : List Nat := [1, 1, 2, 2, 1, 3, 2, 2, 5, 2, 2]
def baseStart_4511487 : Nat := 118140960795 + 4511487 * 2 ^ 59
def prefixEnd_4511487 : Nat := 4983230072969 + 3 ^ 40 * 4511487 * 2
def baseEnd_4511487 : Nat := 2316561297510695520064555

theorem tailTrace_4511487 : CollatzResearch.WordTrace tailWord_4511487 prefixEnd_4511487 2316561297510695520064555 := by
  unfold tailWord_4511487
  simp only [CollatzResearch.WordTrace]
  refine ⟨164547449006660574482020715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109698299337773716321347143 164547449006660574482020715)
  ·
    refine ⟨246821173509990861723031073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164547449006660574482020715 246821173509990861723031073)
    ·
      refine ⟨185115880132493146292273305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 246821173509990861723031073 185115880132493146292273305)
      ·
        refine ⟨138836910099369859719204979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 185115880132493146292273305 138836910099369859719204979)
        ·
          refine ⟨208255365149054789578807469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138836910099369859719204979 208255365149054789578807469)
          ·
            refine ⟨78095761930895546092052801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 208255365149054789578807469 78095761930895546092052801)
            ·
              refine ⟨58571821448171659569039601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78095761930895546092052801 58571821448171659569039601)
              ·
                refine ⟨43928866086128744676779701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58571821448171659569039601 43928866086128744676779701)
                ·
                  refine ⟨4118331195574569813448097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43928866086128744676779701 4118331195574569813448097)
                  ·
                    refine ⟨3088748396680927360086073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4118331195574569813448097 3088748396680927360086073)
                    ·
                      refine ⟨2316561297510695520064555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3088748396680927360086073 2316561297510695520064555)
                      ·
                        rfl

theorem cell23_4511487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 2, 5, 2, 2].length) (baseStart_4511487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4511487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4511487 prefixEnd_4511487 := by exact prefixLift 4511487
  have htrace : WordTrace (prefixWord ++ tailWord_4511487) baseStart_4511487 baseEnd_4511487 := by
    simpa [prefixWord, tailWord_4511487, baseEnd_4511487] using wordTrace_append hprefix tailTrace_4511487
  have hstable : (prefixWord ++ tailWord_4511487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4511487).length < 2 ^ (prefixWord ++ tailWord_4511487).sum := by decide
  have hdescent : baseEnd_4511487 < baseStart_4511487 := by decide
  rcases family_descends (prefixWord ++ tailWord_4511487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4511514 : List Nat := [3, 1, 1, 3, 2, 2, 4, 1, 2, 4]
def baseStart_4511514 : Nat := 118140960795 + 4511514 * 2 ^ 59
def prefixEnd_4511514 : Nat := 4983230072969 + 3 ^ 40 * 4511514 * 2
def baseEnd_4511514 : Nat := 772191720496122304808977

theorem tailTrace_4511514 : CollatzResearch.WordTrace tailWord_4511514 prefixEnd_4511514 772191720496122304808977 := by
  unfold tailWord_4511514
  simp only [CollatzResearch.WordTrace]
  refine ⟨41137108444390689523313399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109698955851708505395502397 41137108444390689523313399)
  ·
    refine ⟨61705662666586034284970099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41137108444390689523313399 61705662666586034284970099)
    ·
      refine ⟨92558493999879051427455149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61705662666586034284970099 92558493999879051427455149)
      ·
        refine ⟨34709435249954644285295681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92558493999879051427455149 34709435249954644285295681)
        ·
          refine ⟨26032076437465983213971761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34709435249954644285295681 26032076437465983213971761)
          ·
            refine ⟨19524057328099487410478821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26032076437465983213971761 19524057328099487410478821)
            ·
              refine ⟨3660760749018653889464779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19524057328099487410478821 3660760749018653889464779)
              ·
                refine ⟨5491141123527980834197169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3660760749018653889464779 5491141123527980834197169)
                ·
                  refine ⟨4118355842645985625647877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5491141123527980834197169 4118355842645985625647877)
                  ·
                    refine ⟨772191720496122304808977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4118355842645985625647877 772191720496122304808977)
                    ·
                      rfl

theorem cell23_4511514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 4, 1, 2, 4].length) (baseStart_4511514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4511514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4511514 prefixEnd_4511514 := by exact prefixLift 4511514
  have htrace : WordTrace (prefixWord ++ tailWord_4511514) baseStart_4511514 baseEnd_4511514 := by
    simpa [prefixWord, tailWord_4511514, baseEnd_4511514] using wordTrace_append hprefix tailTrace_4511514
  have hstable : (prefixWord ++ tailWord_4511514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4511514).length < 2 ^ (prefixWord ++ tailWord_4511514).sum := by decide
  have hdescent : baseEnd_4511514 < baseStart_4511514 := by decide
  rcases family_descends (prefixWord ++ tailWord_4511514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4511518 : List Nat := [4, 3, 2, 2, 1, 2, 1, 2, 1, 5]
def baseStart_4511518 : Nat := 118140960795 + 4511518 * 2 ^ 59
def prefixEnd_4511518 : Nat := 4983230072969 + 3 ^ 40 * 4511518 * 2
def baseEnd_4511518 : Nat := 772192405136994966258971

theorem tailTrace_4511518 : CollatzResearch.WordTrace tailWord_4511518 prefixEnd_4511518 772192405136994966258971 := by
  unfold tailWord_4511518
  simp only [CollatzResearch.WordTrace]
  refine ⟨20568572458693533347049901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109699053113032177850932805 20568572458693533347049901)
  ·
    refine ⟨7713214672010075005143713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20568572458693533347049901 7713214672010075005143713)
    ·
      refine ⟨5784911004007556253857785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7713214672010075005143713 5784911004007556253857785)
      ·
        refine ⟨4338683253005667190393339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5784911004007556253857785 4338683253005667190393339)
        ·
          refine ⟨6508024879508500785590009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4338683253005667190393339 6508024879508500785590009)
          ·
            refine ⟨4881018659631375589192507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6508024879508500785590009 4881018659631375589192507)
            ·
              refine ⟨7321527989447063383788761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4881018659631375589192507 7321527989447063383788761)
              ·
                refine ⟨5491145992085297537841571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7321527989447063383788761 5491145992085297537841571)
                ·
                  refine ⟨8236718988127946306762357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5491145992085297537841571 8236718988127946306762357)
                  ·
                    refine ⟨772192405136994966258971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8236718988127946306762357 772192405136994966258971)
                    ·
                      rfl

theorem cell23_4511518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_4511518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4511518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4511518 prefixEnd_4511518 := by exact prefixLift 4511518
  have htrace : WordTrace (prefixWord ++ tailWord_4511518) baseStart_4511518 baseEnd_4511518 := by
    simpa [prefixWord, tailWord_4511518, baseEnd_4511518] using wordTrace_append hprefix tailTrace_4511518
  have hstable : (prefixWord ++ tailWord_4511518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4511518).length < 2 ^ (prefixWord ++ tailWord_4511518).sum := by decide
  have hdescent : baseEnd_4511518 < baseStart_4511518 := by decide
  rcases family_descends (prefixWord ++ tailWord_4511518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4511524 : List Nat := [2, 3, 1, 3, 2, 1, 3, 2, 1, 2, 3]
def baseStart_4511524 : Nat := 118140960795 + 4511524 * 2 ^ 59
def prefixEnd_4511524 : Nat := 4983230072969 + 3 ^ 40 * 4511524 * 2
def baseEnd_4511524 : Nat := 2316580296294911875301885

theorem tailTrace_4511524 : CollatzResearch.WordTrace tailWord_4511524 prefixEnd_4511524 2316580296294911875301885 := by
  unfold tailWord_4511524
  simp only [CollatzResearch.WordTrace]
  refine ⟨82274399253763264900558813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109699199005017686534078417 82274399253763264900558813)
  ·
    refine ⟨30852899720161224337709555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82274399253763264900558813 30852899720161224337709555)
    ·
      refine ⟨46279349580241836506564333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30852899720161224337709555 46279349580241836506564333)
      ·
        refine ⟨17354756092590688689961625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46279349580241836506564333 17354756092590688689961625)
        ·
          refine ⟨13016067069443016517471219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17354756092590688689961625 13016067069443016517471219)
          ·
            refine ⟨19524100604164524776206829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13016067069443016517471219 19524100604164524776206829)
            ·
              refine ⟨7321537726561696791077561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19524100604164524776206829 7321537726561696791077561)
              ·
                refine ⟨5491153294921272593308171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7321537726561696791077561 5491153294921272593308171)
                ·
                  refine ⟨8236729942381908889962257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5491153294921272593308171 8236729942381908889962257)
                  ·
                    refine ⟨6177547456786431667471693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8236729942381908889962257 6177547456786431667471693)
                    ·
                      refine ⟨2316580296294911875301885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6177547456786431667471693 2316580296294911875301885)
                      ·
                        rfl

theorem cell23_4511524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 3, 2, 1, 2, 3].length) (baseStart_4511524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4511524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4511524 prefixEnd_4511524 := by exact prefixLift 4511524
  have htrace : WordTrace (prefixWord ++ tailWord_4511524) baseStart_4511524 baseEnd_4511524 := by
    simpa [prefixWord, tailWord_4511524, baseEnd_4511524] using wordTrace_append hprefix tailTrace_4511524
  have hstable : (prefixWord ++ tailWord_4511524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4511524).length < 2 ^ (prefixWord ++ tailWord_4511524).sum := by decide
  have hdescent : baseEnd_4511524 < baseStart_4511524 := by decide
  rcases family_descends (prefixWord ++ tailWord_4511524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4511534 : List Nat := [4, 1, 3, 2, 2, 1, 1, 2, 1, 2, 4]
def baseStart_4511534 : Nat := 118140960795 + 4511534 * 2 ^ 59
def prefixEnd_4511534 : Nat := 4983230072969 + 3 ^ 40 * 4511534 * 2
def baseEnd_4511534 : Nat := 2316585431101456836176839

theorem tailTrace_4511534 : CollatzResearch.WordTrace tailWord_4511534 prefixEnd_4511534 2316585431101456836176839 := by
  unfold tailWord_4511534
  simp only [CollatzResearch.WordTrace]
  refine ⟨20568645404686287688622707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109699442158326867672654437 20568645404686287688622707)
  ·
    refine ⟨30852968107029431532934061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20568645404686287688622707 30852968107029431532934061)
    ·
      refine ⟨11569863040136036824850273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30852968107029431532934061 11569863040136036824850273)
      ·
        refine ⟨8677397280102027618637705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11569863040136036824850273 8677397280102027618637705)
        ·
          refine ⟨6508047960076520713978279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8677397280102027618637705 6508047960076520713978279)
          ·
            refine ⟨9762071940114781070967419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6508047960076520713978279 9762071940114781070967419)
            ·
              refine ⟨14643107910172171606451129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9762071940114781070967419 14643107910172171606451129)
              ·
                refine ⟨10982330932629128704838347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14643107910172171606451129 10982330932629128704838347)
                ·
                  refine ⟨16473496398943693057257521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10982330932629128704838347 16473496398943693057257521)
                  ·
                    refine ⟨12355122299207769792943141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16473496398943693057257521 12355122299207769792943141)
                    ·
                      refine ⟨2316585431101456836176839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12355122299207769792943141 2316585431101456836176839)
                      ·
                        rfl

theorem cell23_4511534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_4511534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4511534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4511534 prefixEnd_4511534 := by exact prefixLift 4511534
  have htrace : WordTrace (prefixWord ++ tailWord_4511534) baseStart_4511534 baseEnd_4511534 := by
    simpa [prefixWord, tailWord_4511534, baseEnd_4511534] using wordTrace_append hprefix tailTrace_4511534
  have hstable : (prefixWord ++ tailWord_4511534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4511534).length < 2 ^ (prefixWord ++ tailWord_4511534).sum := by decide
  have hdescent : baseEnd_4511534 < baseStart_4511534 := by decide
  rcases family_descends (prefixWord ++ tailWord_4511534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4511537 : List Nat := [1, 2, 2, 3, 2, 3, 1, 2, 1, 3, 3]
def baseStart_4511537 : Nat := 118140960795 + 4511537 * 2 ^ 59
def prefixEnd_4511537 : Nat := 4983230072969 + 3 ^ 40 * 4511537 * 2
def baseEnd_4511537 : Nat := 2316586971543420324439325

theorem tailTrace_4511537 : CollatzResearch.WordTrace tailWord_4511537 prefixEnd_4511537 2316586971543420324439325 := by
  unfold tailWord_4511537
  simp only [CollatzResearch.WordTrace]
  refine ⟨164549272656479433021340865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109699515104319622014227243 164549272656479433021340865)
  ·
    refine ⟨123411954492359574766005649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164549272656479433021340865 123411954492359574766005649)
    ·
      refine ⟨92558965869269681074504237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123411954492359574766005649 92558965869269681074504237)
      ·
        refine ⟨34709612200976130402939089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92558965869269681074504237 34709612200976130402939089)
        ·
          refine ⟨26032209150732097802204317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34709612200976130402939089 26032209150732097802204317)
          ·
            refine ⟨9762078431524536675826619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26032209150732097802204317 9762078431524536675826619)
            ·
              refine ⟨14643117647286805013739929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9762078431524536675826619 14643117647286805013739929)
              ·
                refine ⟨10982338235465103760304947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14643117647286805013739929 10982338235465103760304947)
                ·
                  refine ⟨16473507353197655640457421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10982338235465103760304947 16473507353197655640457421)
                  ·
                    refine ⟨6177565257449120865171533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16473507353197655640457421 6177565257449120865171533)
                    ·
                      refine ⟨2316586971543420324439325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6177565257449120865171533 2316586971543420324439325)
                      ·
                        rfl

theorem cell23_4511537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 2, 1, 3, 3].length) (baseStart_4511537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4511537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4511537 prefixEnd_4511537 := by exact prefixLift 4511537
  have htrace : WordTrace (prefixWord ++ tailWord_4511537) baseStart_4511537 baseEnd_4511537 := by
    simpa [prefixWord, tailWord_4511537, baseEnd_4511537] using wordTrace_append hprefix tailTrace_4511537
  have hstable : (prefixWord ++ tailWord_4511537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4511537).length < 2 ^ (prefixWord ++ tailWord_4511537).sum := by decide
  have hdescent : baseEnd_4511537 < baseStart_4511537 := by decide
  rcases family_descends (prefixWord ++ tailWord_4511537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4511541 : List Nat := [1, 3, 3, 1, 4, 1, 3, 1, 1, 2, 3]
def baseStart_4511541 : Nat := 118140960795 + 4511541 * 2 ^ 59
def prefixEnd_4511541 : Nat := 4983230072969 + 3 ^ 40 * 4511541 * 2
def baseEnd_4511541 : Nat := 2316589025466038308789307

theorem tailTrace_4511541 : CollatzResearch.WordTrace tailWord_4511541 prefixEnd_4511541 2316589025466038308789307 := by
  unfold tailWord_4511541
  simp only [CollatzResearch.WordTrace]
  refine ⟨164549418548464941704486477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109699612365643294469657651 164549418548464941704486477)
  ·
    refine ⟨61706031955674353139182429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 164549418548464941704486477 61706031955674353139182429)
    ·
      refine ⟨23139761983377882427193411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61706031955674353139182429 23139761983377882427193411)
      ·
        refine ⟨34709642975066823640790117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23139761983377882427193411 34709642975066823640790117)
        ·
          refine ⟨6508058057825029432648147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34709642975066823640790117 6508058057825029432648147)
          ·
            refine ⟨9762087086737544148972221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6508058057825029432648147 9762087086737544148972221)
            ·
              refine ⟨3660782657526579055864583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9762087086737544148972221 3660782657526579055864583)
              ·
                refine ⟨5491173986289868583796875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3660782657526579055864583 5491173986289868583796875)
                ·
                  refine ⟨8236760979434802875695313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5491173986289868583796875 8236760979434802875695313)
                  ·
                    refine ⟨6177570734576102156771485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8236760979434802875695313 6177570734576102156771485)
                    ·
                      refine ⟨2316589025466038308789307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6177570734576102156771485 2316589025466038308789307)
                      ·
                        rfl

theorem cell23_4511541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 3, 1, 1, 2, 3].length) (baseStart_4511541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4511541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4511541 prefixEnd_4511541 := by exact prefixLift 4511541
  have htrace : WordTrace (prefixWord ++ tailWord_4511541) baseStart_4511541 baseEnd_4511541 := by
    simpa [prefixWord, tailWord_4511541, baseEnd_4511541] using wordTrace_append hprefix tailTrace_4511541
  have hstable : (prefixWord ++ tailWord_4511541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4511541).length < 2 ^ (prefixWord ++ tailWord_4511541).sum := by decide
  have hdescent : baseEnd_4511541 < baseStart_4511541 := by decide
  rcases family_descends (prefixWord ++ tailWord_4511541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4511560 : List Nat := [2, 1, 3, 1, 1, 4, 1, 1, 2, 3, 4]
def baseStart_4511560 : Nat := 118140960795 + 4511560 * 2 ^ 59
def prefixEnd_4511560 : Nat := 4983230072969 + 3 ^ 40 * 4511560 * 2
def baseEnd_4511560 : Nat := 2316598781598473734451719

theorem tailTrace_4511560 : CollatzResearch.WordTrace tailWord_4511560 prefixEnd_4511560 2316598781598473734451719 := by
  unfold tailWord_4511560
  simp only [CollatzResearch.WordTrace]
  refine ⟨82275055767698053974714067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109700074356930738632952089 82275055767698053974714067)
  ·
    refine ⟨123412583651547080962071101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82275055767698053974714067 123412583651547080962071101)
    ·
      refine ⟨46279718869330155360776663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123412583651547080962071101 46279718869330155360776663)
      ·
        refine ⟨69419578303995233041164995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46279718869330155360776663 69419578303995233041164995)
        ·
          refine ⟨104129367455992849561747493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69419578303995233041164995 104129367455992849561747493)
          ·
            refine ⟨19524256397998659292827655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 104129367455992849561747493 19524256397998659292827655)
            ·
              refine ⟨29286384596997988939241483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19524256397998659292827655 29286384596997988939241483)
              ·
                refine ⟨43929576895496983408862225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29286384596997988939241483 43929576895496983408862225)
                ·
                  refine ⟨32947182671622737556646669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43929576895496983408862225 32947182671622737556646669)
                  ·
                    refine ⟨12355193501858526583742501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32947182671622737556646669 12355193501858526583742501)
                    ·
                      refine ⟨2316598781598473734451719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12355193501858526583742501 2316598781598473734451719)
                      ·
                        rfl

theorem cell23_4511560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 1, 2, 3, 4].length) (baseStart_4511560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4511560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4511560 prefixEnd_4511560 := by exact prefixLift 4511560
  have htrace : WordTrace (prefixWord ++ tailWord_4511560) baseStart_4511560 baseEnd_4511560 := by
    simpa [prefixWord, tailWord_4511560, baseEnd_4511560] using wordTrace_append hprefix tailTrace_4511560
  have hstable : (prefixWord ++ tailWord_4511560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4511560).length < 2 ^ (prefixWord ++ tailWord_4511560).sum := by decide
  have hdescent : baseEnd_4511560 < baseStart_4511560 := by decide
  rcases family_descends (prefixWord ++ tailWord_4511560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4511570 : List Nat := [3, 2, 2, 1, 1, 3, 1, 1, 1, 8]
def baseStart_4511570 : Nat := 118140960795 + 4511570 * 2 ^ 59
def prefixEnd_4511570 : Nat := 4983230072969 + 3 ^ 40 * 4511570 * 2
def baseEnd_4511570 : Nat := 772201305468339565108891

theorem tailTrace_4511570 : CollatzResearch.WordTrace tailWord_4511570 prefixEnd_4511570 772201305468339565108891 := by
  unfold tailWord_4511570
  simp only [CollatzResearch.WordTrace]
  refine ⟨41137619066339969914323041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109700317510239919771528109 41137619066339969914323041)
  ·
    refine ⟨30853214299754977435742281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41137619066339969914323041 30853214299754977435742281)
    ·
      refine ⟨23139910724816233076806711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30853214299754977435742281 23139910724816233076806711)
      ·
        refine ⟨34709866087224349615210067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23139910724816233076806711 34709866087224349615210067)
        ·
          refine ⟨52064799130836524422815101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34709866087224349615210067 52064799130836524422815101)
          ·
            refine ⟨19524299674063696658555663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52064799130836524422815101 19524299674063696658555663)
            ·
              refine ⟨29286449511095544987833495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19524299674063696658555663 29286449511095544987833495)
              ·
                refine ⟨43929674266643317481750243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29286449511095544987833495 43929674266643317481750243)
                ·
                  refine ⟨65894511399964976222625365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43929674266643317481750243 65894511399964976222625365)
                  ·
                    refine ⟨772201305468339565108891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 65894511399964976222625365 772201305468339565108891)
                    ·
                      rfl

theorem cell23_4511570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 1, 1, 8].length) (baseStart_4511570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4511570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4511570 prefixEnd_4511570 := by exact prefixLift 4511570
  have htrace : WordTrace (prefixWord ++ tailWord_4511570) baseStart_4511570 baseEnd_4511570 := by
    simpa [prefixWord, tailWord_4511570, baseEnd_4511570] using wordTrace_append hprefix tailTrace_4511570
  have hstable : (prefixWord ++ tailWord_4511570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4511570).length < 2 ^ (prefixWord ++ tailWord_4511570).sum := by decide
  have hdescent : baseEnd_4511570 < baseStart_4511570 := by decide
  rcases family_descends (prefixWord ++ tailWord_4511570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4511598 : List Nat := [4, 1, 2, 3, 1, 1, 4, 1, 1, 3, 2]
def baseStart_4511598 : Nat := 118140960795 + 4511598 * 2 ^ 59
def prefixEnd_4511598 : Nat := 4983230072969 + 3 ^ 40 * 4511598 * 2
def baseEnd_4511598 : Nat := 2316618293863344585776545

theorem tailTrace_4511598 : CollatzResearch.WordTrace tailWord_4511598 prefixEnd_4511598 2316618293863344585776545 := by
  unfold tailWord_4511598
  simp only [CollatzResearch.WordTrace]
  refine ⟨20568937188657305054913931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109700998339505626959540965 20568937188657305054913931)
  ·
    refine ⟨30853405782985957582370897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20568937188657305054913931 30853405782985957582370897)
    ·
      refine ⟨23140054337239468186778173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30853405782985957582370897 23140054337239468186778173)
      ·
        refine ⟨8677520376464800570041815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23140054337239468186778173 8677520376464800570041815)
        ·
          refine ⟨13016280564697200855062723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8677520376464800570041815 13016280564697200855062723)
          ·
            refine ⟨19524420847045801282594085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13016280564697200855062723 19524420847045801282594085)
            ·
              refine ⟨3660828908821087740486391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19524420847045801282594085 3660828908821087740486391)
              ·
                refine ⟨5491243363231631610729587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3660828908821087740486391 5491243363231631610729587)
                ·
                  refine ⟨8236865044847447416094381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5491243363231631610729587 8236865044847447416094381)
                  ·
                    refine ⟨3088824391817792781035393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8236865044847447416094381 3088824391817792781035393)
                    ·
                      refine ⟨2316618293863344585776545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3088824391817792781035393 2316618293863344585776545)
                      ·
                        rfl

theorem cell23_4511598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 4, 1, 1, 3, 2].length) (baseStart_4511598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4511598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4511598 prefixEnd_4511598 := by exact prefixLift 4511598
  have htrace : WordTrace (prefixWord ++ tailWord_4511598) baseStart_4511598 baseEnd_4511598 := by
    simpa [prefixWord, tailWord_4511598, baseEnd_4511598] using wordTrace_append hprefix tailTrace_4511598
  have hstable : (prefixWord ++ tailWord_4511598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4511598).length < 2 ^ (prefixWord ++ tailWord_4511598).sum := by decide
  have hdescent : baseEnd_4511598 < baseStart_4511598 := by decide
  rcases family_descends (prefixWord ++ tailWord_4511598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4511667 : List Nat := [1, 1, 1, 2, 3, 1, 5, 2, 2, 1, 4]
def baseStart_4511667 : Nat := 118140960795 + 4511667 * 2 ^ 59
def prefixEnd_4511667 : Nat := 4983230072969 + 3 ^ 40 * 4511667 * 2
def baseEnd_4511667 : Nat := 2316653724028504815813727

theorem tailTrace_4511667 : CollatzResearch.WordTrace tailWord_4511667 prefixEnd_4511667 2316653724028504815813727 := by
  unfold tailWord_4511667
  simp only [CollatzResearch.WordTrace]
  refine ⟨164554014146008465223573255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109702676097338976815715503 164554014146008465223573255)
  ·
    refine ⟨246831021219012697835359883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164554014146008465223573255 246831021219012697835359883)
    ·
      refine ⟨370246531828519046753039825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 246831021219012697835359883 370246531828519046753039825)
      ·
        refine ⟨277684898871389285064779869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 370246531828519046753039825 277684898871389285064779869)
        ·
          refine ⟨104131837076770981899292451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 277684898871389285064779869 104131837076770981899292451)
          ·
            refine ⟨156197755615156472848938677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104131837076770981899292451 156197755615156472848938677)
            ·
              refine ⟨14643539588920919329588001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 156197755615156472848938677 14643539588920919329588001)
              ·
                refine ⟨10982654691690689497191001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14643539588920919329588001 10982654691690689497191001)
                ·
                  refine ⟨8236991018768017122893251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10982654691690689497191001 8236991018768017122893251)
                  ·
                    refine ⟨12355486528152025684339877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8236991018768017122893251 12355486528152025684339877)
                    ·
                      refine ⟨2316653724028504815813727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12355486528152025684339877 2316653724028504815813727)
                      ·
                        rfl

theorem cell23_4511667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 2, 2, 1, 4].length) (baseStart_4511667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4511667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4511667 prefixEnd_4511667 := by exact prefixLift 4511667
  have htrace : WordTrace (prefixWord ++ tailWord_4511667) baseStart_4511667 baseEnd_4511667 := by
    simpa [prefixWord, tailWord_4511667, baseEnd_4511667] using wordTrace_append hprefix tailTrace_4511667
  have hstable : (prefixWord ++ tailWord_4511667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4511667).length < 2 ^ (prefixWord ++ tailWord_4511667).sum := by decide
  have hdescent : baseEnd_4511667 < baseStart_4511667 := by decide
  rcases family_descends (prefixWord ++ tailWord_4511667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4511668 : List Nat := [2, 5, 2, 1, 3, 1, 1, 1, 7]
def baseStart_4511668 : Nat := 118140960795 + 4511668 * 2 ^ 59
def prefixEnd_4511668 : Nat := 4983230072969 + 3 ^ 40 * 4511668 * 2
def baseEnd_4511668 : Nat := 257406026389906590211247

theorem tailTrace_4511668 : CollatzResearch.WordTrace tailWord_4511668 prefixEnd_4511668 257406026389906590211247 := by
  unfold tailWord_4511668
  simp only [CollatzResearch.WordTrace]
  refine ⟨82277025309502421197179829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109702700412669894929573105 82277025309502421197179829)
  ·
    refine ⟨7713471122765851987235609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 82277025309502421197179829 7713471122765851987235609)
    ·
      refine ⟨5785103342074388990426707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7713471122765851987235609 5785103342074388990426707)
      ·
        refine ⟨8677655013111583485640061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5785103342074388990426707 8677655013111583485640061)
        ·
          refine ⟨3254120629916843807115023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8677655013111583485640061 3254120629916843807115023)
          ·
            refine ⟨4881180944875265710672535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3254120629916843807115023 4881180944875265710672535)
            ·
              refine ⟨7321771417312898566008803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4881180944875265710672535 7321771417312898566008803)
              ·
                refine ⟨10982657125969347849013205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7321771417312898566008803 10982657125969347849013205)
                ·
                  refine ⟨257406026389906590211247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10982657125969347849013205 257406026389906590211247)
                  ·
                    rfl

theorem cell23_4511668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 1, 1, 7].length) (baseStart_4511668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4511668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4511668 prefixEnd_4511668 := by exact prefixLift 4511668
  have htrace : WordTrace (prefixWord ++ tailWord_4511668) baseStart_4511668 baseEnd_4511668 := by
    simpa [prefixWord, tailWord_4511668, baseEnd_4511668] using wordTrace_append hprefix tailTrace_4511668
  have hstable : (prefixWord ++ tailWord_4511668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4511668).length < 2 ^ (prefixWord ++ tailWord_4511668).sum := by decide
  have hdescent : baseEnd_4511668 < baseStart_4511668 := by decide
  rcases family_descends (prefixWord ++ tailWord_4511668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4511687 : List Nat := [1, 1, 4, 1, 1, 2, 1, 1, 6, 2, 3]
def baseStart_4511687 : Nat := 118140960795 + 4511687 * 2 ^ 59
def prefixEnd_4511687 : Nat := 4983230072969 + 3 ^ 40 * 4511687 * 2
def baseEnd_4511687 : Nat := 2316663993641594737563635

theorem tailTrace_4511687 : CollatzResearch.WordTrace tailWord_4511687 prefixEnd_4511687 2316663993641594737563635 := by
  unfold tailWord_4511687
  simp only [CollatzResearch.WordTrace]
  refine ⟨164554743605936008639301315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109703162403957339092867543 164554743605936008639301315)
  ·
    refine ⟨246832115408904012958951973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164554743605936008639301315 246832115408904012958951973)
    ·
      refine ⟨46281021639169502429803495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 246832115408904012958951973 46281021639169502429803495)
      ·
        refine ⟨69421532458754253644705243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46281021639169502429803495 69421532458754253644705243)
        ·
          refine ⟨104132298688131380467057865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69421532458754253644705243 104132298688131380467057865)
          ·
            refine ⟨78099224016098535350293399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104132298688131380467057865 78099224016098535350293399)
            ·
              refine ⟨117148836024147803025440099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78099224016098535350293399 117148836024147803025440099)
              ·
                refine ⟨175723254036221704538160149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 117148836024147803025440099 175723254036221704538160149)
                ·
                  refine ⟨8237027532947892400226257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 175723254036221704538160149 8237027532947892400226257)
                  ·
                    refine ⟨6177770649710919300169693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8237027532947892400226257 6177770649710919300169693)
                    ·
                      refine ⟨2316663993641594737563635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6177770649710919300169693 2316663993641594737563635)
                      ·
                        rfl

theorem cell23_4511687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 6, 2, 3].length) (baseStart_4511687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4511687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4511687 prefixEnd_4511687 := by exact prefixLift 4511687
  have htrace : WordTrace (prefixWord ++ tailWord_4511687) baseStart_4511687 baseEnd_4511687 := by
    simpa [prefixWord, tailWord_4511687, baseEnd_4511687] using wordTrace_append hprefix tailTrace_4511687
  have hstable : (prefixWord ++ tailWord_4511687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4511687).length < 2 ^ (prefixWord ++ tailWord_4511687).sum := by decide
  have hdescent : baseEnd_4511687 < baseStart_4511687 := by decide
  rcases family_descends (prefixWord ++ tailWord_4511687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4511704 : List Nat := [2, 1, 2, 2, 2, 2, 4, 1, 2, 2, 3]
def baseStart_4511704 : Nat := 118140960795 + 4511704 * 2 ^ 59
def prefixEnd_4511704 : Nat := 4983230072969 + 3 ^ 40 * 4511704 * 2
def baseEnd_4511704 : Nat := 2316672722812721171051057

theorem tailTrace_4511704 : CollatzResearch.WordTrace tailWord_4511704 prefixEnd_4511704 2316672722812721171051057 := by
  unfold tailWord_4511704
  simp only [CollatzResearch.WordTrace]
  refine ⟨82277681823437210271335083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109703575764582947028446777 82277681823437210271335083)
  ·
    refine ⟨123416522735155815407002625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82277681823437210271335083 123416522735155815407002625)
    ·
      refine ⟨92562392051366861555251969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123416522735155815407002625 92562392051366861555251969)
      ·
        refine ⟨69421794038525146166438977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92562392051366861555251969 69421794038525146166438977)
        ·
          refine ⟨52066345528893859624829233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69421794038525146166438977 52066345528893859624829233)
          ·
            refine ⟨39049759146670394718621925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52066345528893859624829233 39049759146670394718621925)
            ·
              refine ⟨7321829840000699009741611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39049759146670394718621925 7321829840000699009741611)
              ·
                refine ⟨10982744760001048514612417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7321829840000699009741611 10982744760001048514612417)
                ·
                  refine ⟨8237058570000786385959313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10982744760001048514612417 8237058570000786385959313)
                  ·
                    refine ⟨6177793927500589789469485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8237058570000786385959313 6177793927500589789469485)
                    ·
                      refine ⟨2316672722812721171051057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6177793927500589789469485 2316672722812721171051057)
                      ·
                        rfl

theorem cell23_4511704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 4, 1, 2, 2, 3].length) (baseStart_4511704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4511704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4511704 prefixEnd_4511704 := by exact prefixLift 4511704
  have htrace : WordTrace (prefixWord ++ tailWord_4511704) baseStart_4511704 baseEnd_4511704 := by
    simpa [prefixWord, tailWord_4511704, baseEnd_4511704] using wordTrace_append hprefix tailTrace_4511704
  have hstable : (prefixWord ++ tailWord_4511704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4511704).length < 2 ^ (prefixWord ++ tailWord_4511704).sum := by decide
  have hdescent : baseEnd_4511704 < baseStart_4511704 := by decide
  rcases family_descends (prefixWord ++ tailWord_4511704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4511737 : List Nat := [1, 2, 1, 3, 1, 4, 1, 2, 3, 5]
def baseStart_4511737 : Nat := 118140960795 + 4511737 * 2 ^ 59
def prefixEnd_4511737 : Nat := 4983230072969 + 3 ^ 40 * 4511737 * 2
def baseEnd_4511737 : Nat := 772229889224773180646135

theorem tailTrace_4511737 : CollatzResearch.WordTrace tailWord_4511737 prefixEnd_4511737 772229889224773180646135 := by
  unfold tailWord_4511737
  simp only [CollatzResearch.WordTrace]
  refine ⟨164556567255754867178621465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109704378170503244785747643 164556567255754867178621465)
  ·
    refine ⟨123417425441816150383966099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164556567255754867178621465 123417425441816150383966099)
    ·
      refine ⟨185126138162724225575949149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123417425441816150383966099 185126138162724225575949149)
      ·
        refine ⟨69422301811021584590980931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 185126138162724225575949149 69422301811021584590980931)
        ·
          refine ⟨104133452716532376886471397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69422301811021584590980931 104133452716532376886471397)
          ·
            refine ⟨19525022384349820666213387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 104133452716532376886471397 19525022384349820666213387)
            ·
              refine ⟨29287533576524730999320081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19525022384349820666213387 29287533576524730999320081)
              ·
                refine ⟨21965650182393548249490061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29287533576524730999320081 21965650182393548249490061)
                ·
                  refine ⟨8237118818397580593558773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21965650182393548249490061 8237118818397580593558773)
                  ·
                    refine ⟨772229889224773180646135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8237118818397580593558773 772229889224773180646135)
                    ·
                      rfl

theorem cell23_4511737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 2, 3, 5].length) (baseStart_4511737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4511737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4511737 prefixEnd_4511737 := by exact prefixLift 4511737
  have htrace : WordTrace (prefixWord ++ tailWord_4511737) baseStart_4511737 baseEnd_4511737 := by
    simpa [prefixWord, tailWord_4511737, baseEnd_4511737] using wordTrace_append hprefix tailTrace_4511737
  have hstable : (prefixWord ++ tailWord_4511737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4511737).length < 2 ^ (prefixWord ++ tailWord_4511737).sum := by decide
  have hdescent : baseEnd_4511737 < baseStart_4511737 := by decide
  rcases family_descends (prefixWord ++ tailWord_4511737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4511751 : List Nat := [1, 1, 4, 3, 1, 3, 1, 2, 3, 1, 3]
def baseStart_4511751 : Nat := 118140960795 + 4511751 * 2 ^ 59
def prefixEnd_4511751 : Nat := 4983230072969 + 3 ^ 40 * 4511751 * 2
def baseEnd_4511751 : Nat := 2316696856403482487163341

theorem tailTrace_4511751 : CollatzResearch.WordTrace tailWord_4511751 prefixEnd_4511751 2316696856403482487163341 := by
  unfold tailWord_4511751
  simp only [CollatzResearch.WordTrace]
  refine ⟨164557077877704147569631107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109704718585136098379754071 164557077877704147569631107)
  ·
    refine ⟨246835616816556221354446661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164557077877704147569631107 246835616816556221354446661)
    ·
      refine ⟨46281678153104291503958749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 246835616816556221354446661 46281678153104291503958749)
      ·
        refine ⟨17355629307414109313984531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46281678153104291503958749 17355629307414109313984531)
        ·
          refine ⟨26033443961121163970976797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17355629307414109313984531 26033443961121163970976797)
          ·
            refine ⟨9762541485420436489116299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26033443961121163970976797 9762541485420436489116299)
            ·
              refine ⟨14643812228130654733674449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9762541485420436489116299 14643812228130654733674449)
              ·
                refine ⟨10982859171097991050255837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14643812228130654733674449 10982859171097991050255837)
                ·
                  refine ⟨4118572189161746643845939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10982859171097991050255837 4118572189161746643845939)
                  ·
                    refine ⟨6177858283742619965768909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4118572189161746643845939 6177858283742619965768909)
                    ·
                      refine ⟨2316696856403482487163341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6177858283742619965768909 2316696856403482487163341)
                      ·
                        rfl

theorem cell23_4511751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 2, 3, 1, 3].length) (baseStart_4511751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4511751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4511751 prefixEnd_4511751 := by exact prefixLift 4511751
  have htrace : WordTrace (prefixWord ++ tailWord_4511751) baseStart_4511751 baseEnd_4511751 := by
    simpa [prefixWord, tailWord_4511751, baseEnd_4511751] using wordTrace_append hprefix tailTrace_4511751
  have hstable : (prefixWord ++ tailWord_4511751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4511751).length < 2 ^ (prefixWord ++ tailWord_4511751).sum := by decide
  have hdescent : baseEnd_4511751 < baseStart_4511751 := by decide
  rcases family_descends (prefixWord ++ tailWord_4511751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4511768 : List Nat := [2, 1, 2, 3, 2, 1, 4, 3, 1, 1, 3]
def baseStart_4511768 : Nat := 118140960795 + 4511768 * 2 ^ 59
def prefixEnd_4511768 : Nat := 4983230072969 + 3 ^ 40 * 4511768 * 2
def baseEnd_4511768 : Nat := 2316705585574608920650763

theorem tailTrace_4511768 : CollatzResearch.WordTrace tailWord_4511768 prefixEnd_4511768 2316705585574608920650763 := by
  unfold tailWord_4511768
  simp only [CollatzResearch.WordTrace]
  refine ⟨82278848959321279736499979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109705131945761706315333305 82278848959321279736499979)
  ·
    refine ⟨123418273438981919604749969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82278848959321279736499979 123418273438981919604749969)
    ·
      refine ⟨92563705079236439703562477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123418273438981919604749969 92563705079236439703562477)
      ·
        refine ⟨34711389404713664888835929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92563705079236439703562477 34711389404713664888835929)
        ·
          refine ⟨26033542053535248666626947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34711389404713664888835929 26033542053535248666626947)
          ·
            refine ⟨39050313080302872999940421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26033542053535248666626947 39050313080302872999940421)
            ·
              refine ⟨7321933702556788687488829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39050313080302872999940421 7321933702556788687488829)
              ·
                refine ⟨2745725138458795757808311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7321933702556788687488829 2745725138458795757808311)
                ·
                  refine ⟨4118587707688193636712467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2745725138458795757808311 4118587707688193636712467)
                  ·
                    refine ⟨6177881561532290455068701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4118587707688193636712467 6177881561532290455068701)
                    ·
                      refine ⟨2316705585574608920650763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6177881561532290455068701 2316705585574608920650763)
                      ·
                        rfl

theorem cell23_4511768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 4, 3, 1, 1, 3].length) (baseStart_4511768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4511768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4511768 prefixEnd_4511768 := by exact prefixLift 4511768
  have htrace : WordTrace (prefixWord ++ tailWord_4511768) baseStart_4511768 baseEnd_4511768 := by
    simpa [prefixWord, tailWord_4511768, baseEnd_4511768] using wordTrace_append hprefix tailTrace_4511768
  have hstable : (prefixWord ++ tailWord_4511768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4511768).length < 2 ^ (prefixWord ++ tailWord_4511768).sum := by decide
  have hdescent : baseEnd_4511768 < baseStart_4511768 := by decide
  rcases family_descends (prefixWord ++ tailWord_4511768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4511794 : List Nat := [3, 2, 1, 1, 2, 4, 1, 2, 1, 1, 5]
def baseStart_4511794 : Nat := 118140960795 + 4511794 * 2 ^ 59
def prefixEnd_4511794 : Nat := 4983230072969 + 3 ^ 40 * 4511794 * 2
def baseEnd_4511794 : Nat := 2316718936071625818925643

theorem tailTrace_4511794 : CollatzResearch.WordTrace tailWord_4511794 prefixEnd_4511794 2316718936071625818925643 := by
  unfold tailWord_4511794
  simp only [CollatzResearch.WordTrace]
  refine ⟨41139661554137091478361609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109705764144365577275630957 41139661554137091478361609)
  ·
    refine ⟨30854746165602818608771207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41139661554137091478361609 30854746165602818608771207)
    ·
      refine ⟨46282119248404227913156811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30854746165602818608771207 46282119248404227913156811)
      ·
        refine ⟨69423178872606341869735217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46282119248404227913156811 69423178872606341869735217)
        ·
          refine ⟨52067384154454756402301413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69423178872606341869735217 52067384154454756402301413)
          ·
            refine ⟨9762634528960266825431515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52067384154454756402301413 9762634528960266825431515)
            ·
              refine ⟨14643951793440400238147273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9762634528960266825431515 14643951793440400238147273)
              ·
                refine ⟨10982963845080300178610455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14643951793440400238147273 10982963845080300178610455)
                ·
                  refine ⟨16474445767620450267915683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10982963845080300178610455 16474445767620450267915683)
                  ·
                    refine ⟨24711668651430675401873525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16474445767620450267915683 24711668651430675401873525)
                    ·
                      refine ⟨2316718936071625818925643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24711668651430675401873525 2316718936071625818925643)
                      ·
                        rfl

theorem cell23_4511794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 2, 1, 1, 5].length) (baseStart_4511794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4511794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4511794 prefixEnd_4511794 := by exact prefixLift 4511794
  have htrace : WordTrace (prefixWord ++ tailWord_4511794) baseStart_4511794 baseEnd_4511794 := by
    simpa [prefixWord, tailWord_4511794, baseEnd_4511794] using wordTrace_append hprefix tailTrace_4511794
  have hstable : (prefixWord ++ tailWord_4511794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4511794).length < 2 ^ (prefixWord ++ tailWord_4511794).sum := by decide
  have hdescent : baseEnd_4511794 < baseStart_4511794 := by decide
  rcases family_descends (prefixWord ++ tailWord_4511794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4511801 : List Nat := [1, 2, 1, 5, 3, 2, 1, 1, 1, 6]
def baseStart_4511801 : Nat := 118140960795 + 4511801 * 2 ^ 59
def prefixEnd_4511801 : Nat := 4983230072969 + 3 ^ 40 * 4511801 * 2
def baseEnd_4511801 : Nat := 772240843478735763846037

theorem tailTrace_4511801 : CollatzResearch.WordTrace tailWord_4511801 prefixEnd_4511801 772240843478735763846037 := by
  unfold tailWord_4511801
  simp only [CollatzResearch.WordTrace]
  refine ⟨164558901527523006108951257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109705934351682004072634171 164558901527523006108951257)
  ·
    refine ⟨123419176145642254581713443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164558901527523006108951257 123419176145642254581713443)
    ·
      refine ⟨185128764218463381872570165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123419176145642254581713443 185128764218463381872570165)
      ·
        refine ⟨17355821645480942050553453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 185128764218463381872570165 17355821645480942050553453)
        ·
          refine ⟨6508433117055353268957545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17355821645480942050553453 6508433117055353268957545)
          ·
            refine ⟨4881324837791514951718159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6508433117055353268957545 4881324837791514951718159)
            ·
              refine ⟨7321987256687272427577239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4881324837791514951718159 7321987256687272427577239)
              ·
                refine ⟨10982980885030908641365859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7321987256687272427577239 10982980885030908641365859)
                ·
                  refine ⟨16474471327546362962048789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10982980885030908641365859 16474471327546362962048789)
                  ·
                    refine ⟨772240843478735763846037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16474471327546362962048789 772240843478735763846037)
                    ·
                      rfl

theorem cell23_4511801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 1, 1, 1, 6].length) (baseStart_4511801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4511801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4511801 prefixEnd_4511801 := by exact prefixLift 4511801
  have htrace : WordTrace (prefixWord ++ tailWord_4511801) baseStart_4511801 baseEnd_4511801 := by
    simpa [prefixWord, tailWord_4511801, baseEnd_4511801] using wordTrace_append hprefix tailTrace_4511801
  have hstable : (prefixWord ++ tailWord_4511801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4511801).length < 2 ^ (prefixWord ++ tailWord_4511801).sum := by decide
  have hdescent : baseEnd_4511801 < baseStart_4511801 := by decide
  rcases family_descends (prefixWord ++ tailWord_4511801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4511841 : List Nat := [1, 2, 3, 1, 1, 2, 1, 6, 2, 1, 3]
def baseStart_4511841 : Nat := 118140960795 + 4511841 * 2 ^ 59
def prefixEnd_4511841 : Nat := 4983230072969 + 3 ^ 40 * 4511841 * 2
def baseEnd_4511841 : Nat := 2316743069662387135037927

theorem tailTrace_4511841 : CollatzResearch.WordTrace tailWord_4511841 prefixEnd_4511841 2316743069662387135037927 := by
  unfold tailWord_4511841
  simp only [CollatzResearch.WordTrace]
  refine ⟨164560360447378092940407377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109706906964918728626938251 164560360447378092940407377)
  ·
    refine ⟨123420270335533569705305533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164560360447378092940407377 123420270335533569705305533)
    ·
      refine ⟨46282601375825088639489575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123420270335533569705305533 46282601375825088639489575)
      ·
        refine ⟨69423902063737632959234363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46282601375825088639489575 69423902063737632959234363)
        ·
          refine ⟨104135853095606449438851545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69423902063737632959234363 104135853095606449438851545)
          ·
            refine ⟨78101889821704837079138659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104135853095606449438851545 78101889821704837079138659)
            ·
              refine ⟨117152834732557255618707989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78101889821704837079138659 117152834732557255618707989)
              ·
                refine ⟨5491539128088621357126937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 117152834732557255618707989 5491539128088621357126937)
                ·
                  refine ⟨4118654346066466017845203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5491539128088621357126937 4118654346066466017845203)
                  ·
                    refine ⟨6177981519099699026767805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4118654346066466017845203 6177981519099699026767805)
                    ·
                      refine ⟨2316743069662387135037927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6177981519099699026767805 2316743069662387135037927)
                      ·
                        rfl

theorem cell23_4511841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 6, 2, 1, 3].length) (baseStart_4511841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4511841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4511841 prefixEnd_4511841 := by exact prefixLift 4511841
  have htrace : WordTrace (prefixWord ++ tailWord_4511841) baseStart_4511841 baseEnd_4511841 := by
    simpa [prefixWord, tailWord_4511841, baseEnd_4511841] using wordTrace_append hprefix tailTrace_4511841
  have hstable : (prefixWord ++ tailWord_4511841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4511841).length < 2 ^ (prefixWord ++ tailWord_4511841).sum := by decide
  have hdescent : baseEnd_4511841 < baseStart_4511841 := by decide
  rcases family_descends (prefixWord ++ tailWord_4511841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4511842 : List Nat := [3, 3, 2, 2, 2, 2, 1, 1, 3, 2, 2]
def baseStart_4511842 : Nat := 118140960795 + 4511842 * 2 ^ 59
def prefixEnd_4511842 : Nat := 4983230072969 + 3 ^ 40 * 4511842 * 2
def baseEnd_4511842 : Nat := 2316743583143041631125423

theorem tailTrace_4511842 : CollatzResearch.WordTrace tailWord_4511842 prefixEnd_4511842 2316743583143041631125423 := by
  unfold tailWord_4511842
  simp only [CollatzResearch.WordTrace]
  refine ⟨41140099230093617527798445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109706931280249646740795853 41140099230093617527798445)
  ·
    refine ⟨15427537211285106572924417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41140099230093617527798445 15427537211285106572924417)
    ·
      refine ⟨11570652908463829929693313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15427537211285106572924417 11570652908463829929693313)
      ·
        refine ⟨8677989681347872447269985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11570652908463829929693313 8677989681347872447269985)
        ·
          refine ⟨6508492261010904335452489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8677989681347872447269985 6508492261010904335452489)
          ·
            refine ⟨4881369195758178251589367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6508492261010904335452489 4881369195758178251589367)
            ·
              refine ⟨7322053793637267377384051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4881369195758178251589367 7322053793637267377384051)
              ·
                refine ⟨10983080690455901066076077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7322053793637267377384051 10983080690455901066076077)
                ·
                  refine ⟨4118655258920962899778529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10983080690455901066076077 4118655258920962899778529)
                  ·
                    refine ⟨3088991444190722174833897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4118655258920962899778529 3088991444190722174833897)
                    ·
                      refine ⟨2316743583143041631125423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3088991444190722174833897 2316743583143041631125423)
                      ·
                        rfl

theorem cell23_4511842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 1, 1, 3, 2, 2].length) (baseStart_4511842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4511842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4511842 prefixEnd_4511842 := by exact prefixLift 4511842
  have htrace : WordTrace (prefixWord ++ tailWord_4511842) baseStart_4511842 baseEnd_4511842 := by
    simpa [prefixWord, tailWord_4511842, baseEnd_4511842] using wordTrace_append hprefix tailTrace_4511842
  have hstable : (prefixWord ++ tailWord_4511842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4511842).length < 2 ^ (prefixWord ++ tailWord_4511842).sum := by decide
  have hdescent : baseEnd_4511842 < baseStart_4511842 := by decide
  rcases family_descends (prefixWord ++ tailWord_4511842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4511857 : List Nat := [1, 2, 2, 2, 1, 1, 4, 1, 1, 8]
def baseStart_4511857 : Nat := 118140960795 + 4511857 * 2 ^ 59
def prefixEnd_4511857 : Nat := 4983230072969 + 3 ^ 40 * 4511857 * 2
def baseEnd_4511857 : Nat := 772250428450953024145951

theorem tailTrace_4511857 : CollatzResearch.WordTrace tailWord_4511857 prefixEnd_4511857 772250428450953024145951 := by
  unfold tailWord_4511857
  simp only [CollatzResearch.WordTrace]
  refine ⟨164560944015320127672989825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109707296010213418448659883 164560944015320127672989825)
  ·
    refine ⟨123420708011490095754742369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164560944015320127672989825 123420708011490095754742369)
    ·
      refine ⟨92565531008617571816056777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123420708011490095754742369 92565531008617571816056777)
      ·
        refine ⟨69424148256463178862042583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92565531008617571816056777 69424148256463178862042583)
        ·
          refine ⟨104136222384694768293063875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69424148256463178862042583 104136222384694768293063875)
          ·
            refine ⟨156204333577042152439595813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104136222384694768293063875 156204333577042152439595813)
            ·
              refine ⟨29288312545695403582424215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 156204333577042152439595813 29288312545695403582424215)
              ·
                refine ⟨43932468818543105373636323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29288312545695403582424215 43932468818543105373636323)
                ·
                  refine ⟨65898703227814658060454485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43932468818543105373636323 65898703227814658060454485)
                  ·
                    refine ⟨772250428450953024145951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 65898703227814658060454485 772250428450953024145951)
                    ·
                      rfl

theorem cell23_4511857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 1, 1, 8].length) (baseStart_4511857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4511857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4511857 prefixEnd_4511857 := by exact prefixLift 4511857
  have htrace : WordTrace (prefixWord ++ tailWord_4511857) baseStart_4511857 baseEnd_4511857 := by
    simpa [prefixWord, tailWord_4511857, baseEnd_4511857] using wordTrace_append hprefix tailTrace_4511857
  have hstable : (prefixWord ++ tailWord_4511857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4511857).length < 2 ^ (prefixWord ++ tailWord_4511857).sum := by decide
  have hdescent : baseEnd_4511857 < baseStart_4511857 := by decide
  rcases family_descends (prefixWord ++ tailWord_4511857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4511858 : List Nat := [3, 2, 1, 2, 2, 3, 1, 3, 2, 1, 3]
def baseStart_4511858 : Nat := 118140960795 + 4511858 * 2 ^ 59
def prefixEnd_4511858 : Nat := 4983230072969 + 3 ^ 40 * 4511858 * 2
def baseEnd_4511858 : Nat := 2316751798833513568525349

theorem tailTrace_4511858 : CollatzResearch.WordTrace tailWord_4511858 prefixEnd_4511858 2316751798833513568525349 := by
  unfold tailWord_4511858
  simp only [CollatzResearch.WordTrace]
  refine ⟨41140245122079126210944057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109707320325544336562517485 41140245122079126210944057)
  ·
    refine ⟨30855183841559344658208043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41140245122079126210944057 30855183841559344658208043)
    ·
      refine ⟨46282775762339016987312065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30855183841559344658208043 46282775762339016987312065)
      ·
        refine ⟨34712081821754262740484049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46282775762339016987312065 34712081821754262740484049)
        ·
          refine ⟨26034061366315697055363037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34712081821754262740484049 26034061366315697055363037)
          ·
            refine ⟨9762773012368386395761139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26034061366315697055363037 9762773012368386395761139)
            ·
              refine ⟨14644159518552579593641709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9762773012368386395761139 14644159518552579593641709)
              ·
                refine ⟨5491559819457217347615641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14644159518552579593641709 5491559819457217347615641)
                ·
                  refine ⟨4118669864592913010711731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5491559819457217347615641 4118669864592913010711731)
                  ·
                    refine ⟨6178004796889369516067597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4118669864592913010711731 6178004796889369516067597)
                    ·
                      refine ⟨2316751798833513568525349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6178004796889369516067597 2316751798833513568525349)
                      ·
                        rfl

theorem cell23_4511858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 3, 2, 1, 3].length) (baseStart_4511858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4511858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4511858 prefixEnd_4511858 := by exact prefixLift 4511858
  have htrace : WordTrace (prefixWord ++ tailWord_4511858) baseStart_4511858 baseEnd_4511858 := by
    simpa [prefixWord, tailWord_4511858, baseEnd_4511858] using wordTrace_append hprefix tailTrace_4511858
  have hstable : (prefixWord ++ tailWord_4511858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4511858).length < 2 ^ (prefixWord ++ tailWord_4511858).sum := by decide
  have hdescent : baseEnd_4511858 < baseStart_4511858 := by decide
  rcases family_descends (prefixWord ++ tailWord_4511858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4511868 : List Nat := [2, 2, 2, 1, 1, 4, 3, 2, 1, 3, 2]
def baseStart_4511868 : Nat := 118140960795 + 4511868 * 2 ^ 59
def prefixEnd_4511868 : Nat := 4983230072969 + 3 ^ 40 * 4511868 * 2
def baseEnd_4511868 : Nat := 2316756933640058529400303

theorem tailTrace_4511868 : CollatzResearch.WordTrace tailWord_4511868 prefixEnd_4511868 2316756933640058529400303 := by
  unfold tailWord_4511868
  simp only [CollatzResearch.WordTrace]
  refine ⟨82280672609140138275820129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109707563478853517701093505 82280672609140138275820129)
  ·
    refine ⟨61710504456855103706865097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82280672609140138275820129 61710504456855103706865097)
    ·
      refine ⟨46282878342641327780148823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61710504456855103706865097 46282878342641327780148823)
      ·
        refine ⟨69424317513961991670223235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46282878342641327780148823 69424317513961991670223235)
        ·
          refine ⟨104136476270942987505334853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69424317513961991670223235 104136476270942987505334853)
          ·
            refine ⟨19525589300801810157250285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 104136476270942987505334853 19525589300801810157250285)
            ·
              refine ⟨7322095987800678808968857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19525589300801810157250285 7322095987800678808968857)
              ·
                refine ⟨5491571990850509106726643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7322095987800678808968857 5491571990850509106726643)
                ·
                  refine ⟨8237357986275763660089965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5491571990850509106726643 8237357986275763660089965)
                  ·
                    refine ⟨3089009244853411372533737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8237357986275763660089965 3089009244853411372533737)
                    ·
                      refine ⟨2316756933640058529400303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3089009244853411372533737 2316756933640058529400303)
                      ·
                        rfl

theorem cell23_4511868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 3, 2, 1, 3, 2].length) (baseStart_4511868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4511868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4511868 prefixEnd_4511868 := by exact prefixLift 4511868
  have htrace : WordTrace (prefixWord ++ tailWord_4511868) baseStart_4511868 baseEnd_4511868 := by
    simpa [prefixWord, tailWord_4511868, baseEnd_4511868] using wordTrace_append hprefix tailTrace_4511868
  have hstable : (prefixWord ++ tailWord_4511868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4511868).length < 2 ^ (prefixWord ++ tailWord_4511868).sum := by decide
  have hdescent : baseEnd_4511868 < baseStart_4511868 := by decide
  rcases family_descends (prefixWord ++ tailWord_4511868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4511881 : List Nat := [1, 2, 1, 1, 4, 2, 3, 2, 1, 4, 2]
def baseStart_4511881 : Nat := 118140960795 + 4511881 * 2 ^ 59
def prefixEnd_4511881 : Nat := 4983230072969 + 3 ^ 40 * 4511881 * 2
def baseEnd_4511881 : Nat := 2316763608888566978537743

theorem tailTrace_4511881 : CollatzResearch.WordTrace tailWord_4511881 prefixEnd_4511881 2316763608888566978537743 := by
  unfold tailWord_4511881
  simp only [CollatzResearch.WordTrace]
  refine ⟨164561819367233179771863497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109707879578155453181242331 164561819367233179771863497)
  ·
    refine ⟨123421364525424884828897623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164561819367233179771863497 123421364525424884828897623)
    ·
      refine ⟨185132046788137327243346435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123421364525424884828897623 185132046788137327243346435)
      ·
        refine ⟨277698070182205990865019653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185132046788137327243346435 277698070182205990865019653)
        ·
          refine ⟨52068388159163623287191185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 277698070182205990865019653 52068388159163623287191185)
          ·
            refine ⟨39051291119372717465393389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52068388159163623287191185 39051291119372717465393389)
            ·
              refine ⟨14644234169764769049522521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39051291119372717465393389 14644234169764769049522521)
              ·
                refine ⟨10983175627323576787141891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14644234169764769049522521 10983175627323576787141891)
                ·
                  refine ⟨16474763440985365180712837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10983175627323576787141891 16474763440985365180712837)
                  ·
                    refine ⟨3089018145184755971383657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16474763440985365180712837 3089018145184755971383657)
                    ·
                      refine ⟨2316763608888566978537743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3089018145184755971383657 2316763608888566978537743)
                      ·
                        rfl

theorem cell23_4511881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 2, 1, 4, 2].length) (baseStart_4511881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4511881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4511881 prefixEnd_4511881 := by exact prefixLift 4511881
  have htrace : WordTrace (prefixWord ++ tailWord_4511881) baseStart_4511881 baseEnd_4511881 := by
    simpa [prefixWord, tailWord_4511881, baseEnd_4511881] using wordTrace_append hprefix tailTrace_4511881
  have hstable : (prefixWord ++ tailWord_4511881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4511881).length < 2 ^ (prefixWord ++ tailWord_4511881).sum := by decide
  have hdescent : baseEnd_4511881 < baseStart_4511881 := by decide
  rcases family_descends (prefixWord ++ tailWord_4511881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4511892 : List Nat := [2, 4, 2, 3, 1, 1, 2, 2, 2, 1, 3]
def baseStart_4511892 : Nat := 118140960795 + 4511892 * 2 ^ 59
def prefixEnd_4511892 : Nat := 4983230072969 + 3 ^ 40 * 4511892 * 2
def baseEnd_4511892 : Nat := 2316769257175766435500193

theorem tailTrace_4511892 : CollatzResearch.WordTrace tailWord_4511892 prefixEnd_4511892 2316769257175766435500193 := by
  unfold tailWord_4511892
  simp only [CollatzResearch.WordTrace]
  refine ⟨82281110285096664325256965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109708147046795552433675953 82281110285096664325256965)
  ·
    refine ⟨15427708178455624560985681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82281110285096664325256965 15427708178455624560985681)
    ·
      refine ⟨11570781133841718420739261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15427708178455624560985681 11570781133841718420739261)
      ·
        refine ⟨4339042925190644407777223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11570781133841718420739261 4339042925190644407777223)
        ·
          refine ⟨6508564387785966611665835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4339042925190644407777223 6508564387785966611665835)
          ·
            refine ⟨9762846581678949917498753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6508564387785966611665835 9762846581678949917498753)
            ·
              refine ⟨7322134936259212438124065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9762846581678949917498753 7322134936259212438124065)
              ·
                refine ⟨5491601202194409328593049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7322134936259212438124065 5491601202194409328593049)
                ·
                  refine ⟨4118700901645806996444787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5491601202194409328593049 4118700901645806996444787)
                  ·
                    refine ⟨6178051352468710494667181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4118700901645806996444787 6178051352468710494667181)
                    ·
                      refine ⟨2316769257175766435500193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6178051352468710494667181 2316769257175766435500193)
                      ·
                        rfl

theorem cell23_4511892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_4511892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4511892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4511892 prefixEnd_4511892 := by exact prefixLift 4511892
  have htrace : WordTrace (prefixWord ++ tailWord_4511892) baseStart_4511892 baseEnd_4511892 := by
    simpa [prefixWord, tailWord_4511892, baseEnd_4511892] using wordTrace_append hprefix tailTrace_4511892
  have hstable : (prefixWord ++ tailWord_4511892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4511892).length < 2 ^ (prefixWord ++ tailWord_4511892).sum := by decide
  have hdescent : baseEnd_4511892 < baseStart_4511892 := by decide
  rcases family_descends (prefixWord ++ tailWord_4511892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4511897 : List Nat := [1, 2, 1, 2, 1, 2, 1, 3, 1, 2, 7]
def baseStart_4511897 : Nat := 118140960795 + 4511897 * 2 ^ 59
def prefixEnd_4511897 : Nat := 4983230072969 + 3 ^ 40 * 4511897 * 2
def baseEnd_4511897 : Nat := 2316771824579038915937669

theorem tailTrace_4511897 : CollatzResearch.WordTrace tailWord_4511897 prefixEnd_4511897 2316771824579038915937669 := by
  unfold tailWord_4511897
  simp only [CollatzResearch.WordTrace]
  refine ⟨164562402935175214504445945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109708268623450143002963963 164562402935175214504445945)
  ·
    refine ⟨123421802201381410878334459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164562402935175214504445945 123421802201381410878334459)
    ·
      refine ⟨185132703302072116317501689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123421802201381410878334459 185132703302072116317501689)
      ·
        refine ⟨138849527476554087238126267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 185132703302072116317501689 138849527476554087238126267)
        ·
          refine ⟨208274291214831130857189401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138849527476554087238126267 208274291214831130857189401)
          ·
            refine ⟨156205718411123348142892051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 208274291214831130857189401 156205718411123348142892051)
            ·
              refine ⟨234308577616685022214338077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 156205718411123348142892051 234308577616685022214338077)
              ·
                refine ⟨87865716606256883330376779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 234308577616685022214338077 87865716606256883330376779)
                ·
                  refine ⟨131798574909385324995565169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 87865716606256883330376779 131798574909385324995565169)
                  ·
                    refine ⟨98848931182038993746673877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 131798574909385324995565169 98848931182038993746673877)
                    ·
                      refine ⟨2316771824579038915937669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 98848931182038993746673877 2316771824579038915937669)
                      ·
                        rfl

theorem cell23_4511897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 2, 7].length) (baseStart_4511897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4511897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4511897 prefixEnd_4511897 := by exact prefixLift 4511897
  have htrace : WordTrace (prefixWord ++ tailWord_4511897) baseStart_4511897 baseEnd_4511897 := by
    simpa [prefixWord, tailWord_4511897, baseEnd_4511897] using wordTrace_append hprefix tailTrace_4511897
  have hstable : (prefixWord ++ tailWord_4511897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4511897).length < 2 ^ (prefixWord ++ tailWord_4511897).sum := by decide
  have hdescent : baseEnd_4511897 < baseStart_4511897 := by decide
  rcases family_descends (prefixWord ++ tailWord_4511897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
