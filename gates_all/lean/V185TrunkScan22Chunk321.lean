import V185TrunkScan22Chunk320

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2865956 : List Nat := [2, 3, 1, 3, 3, 1, 1, 3, 2, 3]
def baseStart_2865956 : Nat := 118140960795 + 2865956 * 2 ^ 59
def prefixEnd_2865956 : Nat := 4983230072969 + 3 ^ 40 * 2865956 * 2
def baseEnd_2865956 : Nat := 981075308424729445113143

theorem tailTrace_2865956 : CollatzResearch.WordTrace tailWord_2865956 prefixEnd_2865956 981075308424729445113143 := by
  unfold tailWord_2865956
  simp only [CollatzResearch.WordTrace]
  refine ⟨52265001402569176580752861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69686668536758902107670481 52265001402569176580752861)
  ·
    refine ⟨19599375525963441217782323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52265001402569176580752861 19599375525963441217782323)
    ·
      refine ⟨29399063288945161826673485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19599375525963441217782323 29399063288945161826673485)
      ·
        refine ⟨11024648733354435685002557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29399063288945161826673485 11024648733354435685002557)
        ·
          refine ⟨4134243275007913381875959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11024648733354435685002557 4134243275007913381875959)
          ·
            refine ⟨6201364912511870072813939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4134243275007913381875959 6201364912511870072813939)
            ·
              refine ⟨9302047368767805109220909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6201364912511870072813939 9302047368767805109220909)
              ·
                refine ⟨3488267763287926915957841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9302047368767805109220909 3488267763287926915957841)
                ·
                  refine ⟨2616200822465945186968381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3488267763287926915957841 2616200822465945186968381)
                  ·
                    refine ⟨981075308424729445113143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2616200822465945186968381 981075308424729445113143)
                    ·
                      rfl

theorem cell22_2865956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 3, 2, 3].length) (baseStart_2865956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2865956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2865956 prefixEnd_2865956 := by exact prefixLift 2865956
  have htrace : WordTrace (prefixWord ++ tailWord_2865956) baseStart_2865956 baseEnd_2865956 := by
    simpa [prefixWord, tailWord_2865956, baseEnd_2865956] using wordTrace_append hprefix tailTrace_2865956
  have hstable : (prefixWord ++ tailWord_2865956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2865956).length < 2 ^ (prefixWord ++ tailWord_2865956).sum := by decide
  have hdescent : baseEnd_2865956 < baseStart_2865956 := by decide
  rcases family_descends (prefixWord ++ tailWord_2865956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2865990 : List Nat := [6, 1, 1, 2, 2, 1, 2, 2, 2, 3]
def baseStart_2865990 : Nat := 118140960795 + 2865990 * 2 ^ 59
def prefixEnd_2865990 : Nat := 4983230072969 + 3 ^ 40 * 2865990 * 2
def baseEnd_2865990 : Nat := 981086947319564689763039

theorem tailTrace_2865990 : CollatzResearch.WordTrace tailWord_2865990 prefixEnd_2865990 981086947319564689763039 := by
  unfold tailWord_2865990
  simp only [CollatzResearch.WordTrace]
  refine ⟨3266601340219224280257607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 69687495258010117978828949 3266601340219224280257607)
  ·
    refine ⟨4899902010328836420386411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3266601340219224280257607 4899902010328836420386411)
    ·
      refine ⟨7349853015493254630579617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4899902010328836420386411 7349853015493254630579617)
      ·
        refine ⟨5512389761619940972934713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7349853015493254630579617 5512389761619940972934713)
        ·
          refine ⟨4134292321214955729701035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5512389761619940972934713 4134292321214955729701035)
          ·
            refine ⟨6201438481822433594551553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4134292321214955729701035 6201438481822433594551553)
            ·
              refine ⟨4651078861366825195913665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6201438481822433594551553 4651078861366825195913665)
              ·
                refine ⟨3488309146025118896935249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4651078861366825195913665 3488309146025118896935249)
                ·
                  refine ⟨2616231859518839172701437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3488309146025118896935249 2616231859518839172701437)
                  ·
                    refine ⟨981086947319564689763039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2616231859518839172701437 981086947319564689763039)
                    ·
                      rfl

theorem cell22_2865990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 2, 2, 2, 3].length) (baseStart_2865990 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2865990 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2865990 prefixEnd_2865990 := by exact prefixLift 2865990
  have htrace : WordTrace (prefixWord ++ tailWord_2865990) baseStart_2865990 baseEnd_2865990 := by
    simpa [prefixWord, tailWord_2865990, baseEnd_2865990] using wordTrace_append hprefix tailTrace_2865990
  have hstable : (prefixWord ++ tailWord_2865990).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2865990).length < 2 ^ (prefixWord ++ tailWord_2865990).sum := by decide
  have hdescent : baseEnd_2865990 < baseStart_2865990 := by decide
  rcases family_descends (prefixWord ++ tailWord_2865990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2865995 : List Nat := [1, 1, 1, 1, 3, 1, 1, 1, 5, 7]
def baseStart_2865995 : Nat := 118140960795 + 2865995 * 2 ^ 59
def prefixEnd_2865995 : Nat := 4983230072969 + 3 ^ 40 * 2865995 * 2
def baseEnd_2865995 : Nat := 981088658921746343388023

theorem tailTrace_2865995 : CollatzResearch.WordTrace tailWord_2865995 prefixEnd_2865995 981088658921746343388023 := by
  unfold tailWord_2865995
  simp only [CollatzResearch.WordTrace]
  refine ⟨104531425251997062822175439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69687616834664708548116959 104531425251997062822175439)
  ·
    refine ⟨156797137877995594233263159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104531425251997062822175439 156797137877995594233263159)
    ·
      refine ⟨235195706816993391349894739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156797137877995594233263159 235195706816993391349894739)
      ·
        refine ⟨352793560225490087024842109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235195706816993391349894739 352793560225490087024842109)
        ·
          refine ⟨132297585084558782634315791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 352793560225490087024842109 132297585084558782634315791)
          ·
            refine ⟨198446377626838173951473687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132297585084558782634315791 198446377626838173951473687)
            ·
              refine ⟨297669566440257260927210531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 198446377626838173951473687 297669566440257260927210531)
              ·
                refine ⟨446504349660385891390815797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 297669566440257260927210531 446504349660385891390815797)
                ·
                  refine ⟨41859782780661177317888981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 446504349660385891390815797 41859782780661177317888981)
                  ·
                    refine ⟨981088658921746343388023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41859782780661177317888981 981088658921746343388023)
                    ·
                      rfl

theorem cell22_2865995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 5, 7].length) (baseStart_2865995 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2865995 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2865995 prefixEnd_2865995 := by exact prefixLift 2865995
  have htrace : WordTrace (prefixWord ++ tailWord_2865995) baseStart_2865995 baseEnd_2865995 := by
    simpa [prefixWord, tailWord_2865995, baseEnd_2865995] using wordTrace_append hprefix tailTrace_2865995
  have hstable : (prefixWord ++ tailWord_2865995).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2865995).length < 2 ^ (prefixWord ++ tailWord_2865995).sum := by decide
  have hdescent : baseEnd_2865995 < baseStart_2865995 := by decide
  rcases family_descends (prefixWord ++ tailWord_2865995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2866027 : List Nat := [1, 1, 1, 1, 2, 2, 6, 1, 3, 4]
def baseStart_2866027 : Nat := 118140960795 + 2866027 * 2 ^ 59
def prefixEnd_2866027 : Nat := 4983230072969 + 3 ^ 40 * 2866027 * 2
def baseEnd_2866027 : Nat := 981099613175708926587925

theorem tailTrace_2866027 : CollatzResearch.WordTrace tailWord_2866027 prefixEnd_2866027 981099613175708926587925 := by
  unfold tailWord_2866027
  simp only [CollatzResearch.WordTrace]
  refine ⟨104532592387881132287340335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69688394925254088191560223 104532592387881132287340335)
  ·
    refine ⟨156798888581821698431010503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104532592387881132287340335 156798888581821698431010503)
    ·
      refine ⟨235198332872732547646515755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156798888581821698431010503 235198332872732547646515755)
      ·
        refine ⟨352797499309098821469773633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235198332872732547646515755 352797499309098821469773633)
        ·
          refine ⟨264598124481824116102330225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 352797499309098821469773633 264598124481824116102330225)
          ·
            refine ⟨198448593361368087076747669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 264598124481824116102330225 198448593361368087076747669)
            ·
              refine ⟨9302277813814129081722547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 198448593361368087076747669 9302277813814129081722547)
              ·
                refine ⟨13953416720721193622583821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9302277813814129081722547 13953416720721193622583821)
                ·
                  refine ⟨5232531270270447608468933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13953416720721193622583821 5232531270270447608468933)
                  ·
                    refine ⟨981099613175708926587925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5232531270270447608468933 981099613175708926587925)
                    ·
                      rfl

theorem cell22_2866027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 1, 3, 4].length) (baseStart_2866027 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2866027 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2866027 prefixEnd_2866027 := by exact prefixLift 2866027
  have htrace : WordTrace (prefixWord ++ tailWord_2866027) baseStart_2866027 baseEnd_2866027 := by
    simpa [prefixWord, tailWord_2866027, baseEnd_2866027] using wordTrace_append hprefix tailTrace_2866027
  have hstable : (prefixWord ++ tailWord_2866027).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2866027).length < 2 ^ (prefixWord ++ tailWord_2866027).sum := by decide
  have hdescent : baseEnd_2866027 < baseStart_2866027 := by decide
  rcases family_descends (prefixWord ++ tailWord_2866027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2866059 : List Nat := [1, 1, 1, 1, 4, 2, 4, 4, 4]
def baseStart_2866059 : Nat := 118140960795 + 2866059 * 2 ^ 59
def prefixEnd_2866059 : Nat := 4983230072969 + 3 ^ 40 * 2866059 * 2
def baseEnd_2866059 : Nat := 327036855809890503262609

theorem tailTrace_2866059 : CollatzResearch.WordTrace tailWord_2866059 prefixEnd_2866059 327036855809890503262609 := by
  unfold tailWord_2866059
  simp only [CollatzResearch.WordTrace]
  refine ⟨104533759523765201752505231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69689173015843467835003487 104533759523765201752505231)
  ·
    refine ⟨156800639285647802628757847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104533759523765201752505231 156800639285647802628757847)
    ·
      refine ⟨235200958928471703943136771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156800639285647802628757847 235200958928471703943136771)
      ·
        refine ⟨352801438392707555914705157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235200958928471703943136771 352801438392707555914705157)
        ·
          refine ⟨66150269698632666734007217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 352801438392707555914705157 66150269698632666734007217)
          ·
            refine ⟨49612702273974500050505413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66150269698632666734007217 49612702273974500050505413)
            ·
              refine ⟨9302381676370218759469765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49612702273974500050505413 9302381676370218759469765)
              ·
                refine ⟨1744196564319416017400581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9302381676370218759469765 1744196564319416017400581)
                ·
                  refine ⟨327036855809890503262609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1744196564319416017400581 327036855809890503262609)
                  ·
                    rfl

theorem cell22_2866059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 4, 4].length) (baseStart_2866059 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2866059 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2866059 prefixEnd_2866059 := by exact prefixLift 2866059
  have htrace : WordTrace (prefixWord ++ tailWord_2866059) baseStart_2866059 baseEnd_2866059 := by
    simpa [prefixWord, tailWord_2866059, baseEnd_2866059] using wordTrace_append hprefix tailTrace_2866059
  have hstable : (prefixWord ++ tailWord_2866059).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2866059).length < 2 ^ (prefixWord ++ tailWord_2866059).sum := by decide
  have hdescent : baseEnd_2866059 < baseStart_2866059 := by decide
  rcases family_descends (prefixWord ++ tailWord_2866059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2866166 : List Nat := [5, 1, 1, 1, 3, 1, 1, 4, 5]
def baseStart_2866166 : Nat := 118140960795 + 2866166 * 2 ^ 59
def prefixEnd_2866166 : Nat := 4983230072969 + 3 ^ 40 * 2866166 * 2
def baseEnd_2866166 : Nat := 327049065238786299120833

theorem tailTrace_2866166 : CollatzResearch.WordTrace tailWord_2866166 prefixEnd_2866166 327049065238786299120833 := by
  unfold tailWord_2866166
  simp only [CollatzResearch.WordTrace]
  refine ⟨6533603883398597439165647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 69691774756251706017766901 6533603883398597439165647)
  ·
    refine ⟨9800405825097896158748471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6533603883398597439165647 9800405825097896158748471)
    ·
      refine ⟨14700608737646844238122707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9800405825097896158748471 14700608737646844238122707)
      ·
        refine ⟨22050913106470266357184061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14700608737646844238122707 22050913106470266357184061)
        ·
          refine ⟨8269092414926349883944023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22050913106470266357184061 8269092414926349883944023)
          ·
            refine ⟨12403638622389524825916035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8269092414926349883944023 12403638622389524825916035)
            ·
              refine ⟨18605457933584287238874053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12403638622389524825916035 18605457933584287238874053)
              ·
                refine ⟨3488523362547053857288885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18605457933584287238874053 3488523362547053857288885)
                ·
                  refine ⟨327049065238786299120833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3488523362547053857288885 327049065238786299120833)
                  ·
                    rfl

theorem cell22_2866166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 4, 5].length) (baseStart_2866166 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2866166 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2866166 prefixEnd_2866166 := by exact prefixLift 2866166
  have htrace : WordTrace (prefixWord ++ tailWord_2866166) baseStart_2866166 baseEnd_2866166 := by
    simpa [prefixWord, tailWord_2866166, baseEnd_2866166] using wordTrace_append hprefix tailTrace_2866166
  have hstable : (prefixWord ++ tailWord_2866166).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2866166).length < 2 ^ (prefixWord ++ tailWord_2866166).sum := by decide
  have hdescent : baseEnd_2866166 < baseStart_2866166 := by decide
  rcases family_descends (prefixWord ++ tailWord_2866166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2866211 : List Nat := [1, 1, 1, 4, 3, 2, 1, 5, 4]
def baseStart_2866211 : Nat := 118140960795 + 2866211 * 2 ^ 59
def prefixEnd_2866211 : Nat := 4983230072969 + 3 ^ 40 * 2866211 * 2
def baseEnd_2866211 : Nat := 327054200045331259995787

theorem tailTrace_2866211 : CollatzResearch.WordTrace tailWord_2866211 prefixEnd_2866211 327054200045331259995787 := by
  unfold tailWord_2866211
  simp only [CollatzResearch.WordTrace]
  refine ⟨104539303419214531712038487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69692868946143021141358991 104539303419214531712038487)
  ·
    refine ⟨156808955128821797568057731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104539303419214531712038487 156808955128821797568057731)
    ·
      refine ⟨235213432693232696352086597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156808955128821797568057731 235213432693232696352086597)
      ·
        refine ⟨44102518629981130566016237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 235213432693232696352086597 44102518629981130566016237)
        ·
          refine ⟨16538444486242923962256089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44102518629981130566016237 16538444486242923962256089)
          ·
            refine ⟨12403833364682192971692067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16538444486242923962256089 12403833364682192971692067)
            ·
              refine ⟨18605750047023289457538101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12403833364682192971692067 18605750047023289457538101)
              ·
                refine ⟨1744289066908433386644197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18605750047023289457538101 1744289066908433386644197)
                ·
                  refine ⟨327054200045331259995787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1744289066908433386644197 327054200045331259995787)
                  ·
                    rfl

theorem cell22_2866211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 5, 4].length) (baseStart_2866211 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2866211 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2866211 prefixEnd_2866211 := by exact prefixLift 2866211
  have htrace : WordTrace (prefixWord ++ tailWord_2866211) baseStart_2866211 baseEnd_2866211 := by
    simpa [prefixWord, tailWord_2866211, baseEnd_2866211] using wordTrace_append hprefix tailTrace_2866211
  have hstable : (prefixWord ++ tailWord_2866211).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2866211).length < 2 ^ (prefixWord ++ tailWord_2866211).sum := by decide
  have hdescent : baseEnd_2866211 < baseStart_2866211 := by decide
  rcases family_descends (prefixWord ++ tailWord_2866211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2866224 : List Nat := [2, 1, 1, 1, 2, 4, 2, 1, 4, 4]
def baseStart_2866224 : Nat := 118140960795 + 2866224 * 2 ^ 59
def prefixEnd_2866224 : Nat := 4983230072969 + 3 ^ 40 * 2866224 * 2
def baseEnd_2866224 : Nat := 981167050301666079412321

theorem tailTrace_2866224 : CollatzResearch.WordTrace tailWord_2866224 prefixEnd_2866224 981167050301666079412321 := by
  unfold tailWord_2866224
  simp only [CollatzResearch.WordTrace]
  refine ⟨52269888784083717466130863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69693185045444956621507817 52269888784083717466130863)
  ·
    refine ⟨78404833176125576199196295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52269888784083717466130863 78404833176125576199196295)
    ·
      refine ⟨117607249764188364298794443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78404833176125576199196295 117607249764188364298794443)
      ·
        refine ⟨176410874646282546448191665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117607249764188364298794443 176410874646282546448191665)
        ·
          refine ⟨132308155984711909836143749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176410874646282546448191665 132308155984711909836143749)
          ·
            refine ⟨24807779247133483094276953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 132308155984711909836143749 24807779247133483094276953)
            ·
              refine ⟨18605834435350112320707715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24807779247133483094276953 18605834435350112320707715)
              ·
                refine ⟨27908751653025168481061573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18605834435350112320707715 27908751653025168481061573)
                ·
                  refine ⟨5232890934942219090199045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27908751653025168481061573 5232890934942219090199045)
                  ·
                    refine ⟨981167050301666079412321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5232890934942219090199045 981167050301666079412321)
                    ·
                      rfl

theorem cell22_2866224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 1, 4, 4].length) (baseStart_2866224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2866224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2866224 prefixEnd_2866224 := by exact prefixLift 2866224
  have htrace : WordTrace (prefixWord ++ tailWord_2866224) baseStart_2866224 baseEnd_2866224 := by
    simpa [prefixWord, tailWord_2866224, baseEnd_2866224] using wordTrace_append hprefix tailTrace_2866224
  have hstable : (prefixWord ++ tailWord_2866224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2866224).length < 2 ^ (prefixWord ++ tailWord_2866224).sum := by decide
  have hdescent : baseEnd_2866224 < baseStart_2866224 := by decide
  rcases family_descends (prefixWord ++ tailWord_2866224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2866226 : List Nat := [3, 2, 1, 1, 2, 2, 3, 1, 4, 3]
def baseStart_2866226 : Nat := 118140960795 + 2866226 * 2 ^ 59
def prefixEnd_2866226 : Nat := 4983230072969 + 3 ^ 40 * 2866226 * 2
def baseEnd_2866226 : Nat := 981167734942538740862315

theorem tailTrace_2866226 : CollatzResearch.WordTrace tailWord_2866226 prefixEnd_2866226 981167734942538740862315 := by
  unfold tailWord_2866226
  simp only [CollatzResearch.WordTrace]
  refine ⟨26134962628540047318458633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69693233676106792849223021 26134962628540047318458633)
  ·
    refine ⟨19601221971405035488843975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26134962628540047318458633 19601221971405035488843975)
    ·
      refine ⟨29401832957107553233265963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19601221971405035488843975 29401832957107553233265963)
      ·
        refine ⟨44102749435661329849898945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29401832957107553233265963 44102749435661329849898945)
        ·
          refine ⟨33077062076745997387424209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44102749435661329849898945 33077062076745997387424209)
          ·
            refine ⟨24807796557559498040568157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33077062076745997387424209 24807796557559498040568157)
            ·
              refine ⟨9302923709084811765213059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24807796557559498040568157 9302923709084811765213059)
              ·
                refine ⟨13954385563627217647819589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9302923709084811765213059 13954385563627217647819589)
                ·
                  refine ⟨2616447293180103308966173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13954385563627217647819589 2616447293180103308966173)
                  ·
                    refine ⟨981167734942538740862315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2616447293180103308966173 981167734942538740862315)
                    ·
                      rfl

theorem cell22_2866226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 1, 4, 3].length) (baseStart_2866226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2866226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2866226 prefixEnd_2866226 := by exact prefixLift 2866226
  have htrace : WordTrace (prefixWord ++ tailWord_2866226) baseStart_2866226 baseEnd_2866226 := by
    simpa [prefixWord, tailWord_2866226, baseEnd_2866226] using wordTrace_append hprefix tailTrace_2866226
  have hstable : (prefixWord ++ tailWord_2866226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2866226).length < 2 ^ (prefixWord ++ tailWord_2866226).sum := by decide
  have hdescent : baseEnd_2866226 < baseStart_2866226 := by decide
  rcases family_descends (prefixWord ++ tailWord_2866226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2866228 : List Nat := [2, 5, 1, 2, 1, 2, 2, 1, 6]
def baseStart_2866228 : Nat := 118140960795 + 2866228 * 2 ^ 59
def prefixEnd_2866228 : Nat := 4983230072969 + 3 ^ 40 * 2866228 * 2
def baseEnd_2866228 : Nat := 327056139861137134104103

theorem tailTrace_2866228 : CollatzResearch.WordTrace tailWord_2866228 prefixEnd_2866228 327056139861137134104103 := by
  unfold tailWord_2866228
  simp only [CollatzResearch.WordTrace]
  refine ⟨52269961730076471807703669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69693282306768629076938225 52269961730076471807703669)
  ·
    refine ⟨4900308912194669231972219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 52269961730076471807703669 4900308912194669231972219)
    ·
      refine ⟨7350463368292003847958329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4900308912194669231972219 7350463368292003847958329)
      ·
        refine ⟨5512847526219002885968747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7350463368292003847958329 5512847526219002885968747)
        ·
          refine ⟨8269271289328504328953121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5512847526219002885968747 8269271289328504328953121)
          ·
            refine ⟨6201953466996378246714841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8269271289328504328953121 6201953466996378246714841)
            ·
              refine ⟨4651465100247283685036131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6201953466996378246714841 4651465100247283685036131)
              ·
                refine ⟨6977197650370925527554197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4651465100247283685036131 6977197650370925527554197)
                ·
                  refine ⟨327056139861137134104103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6977197650370925527554197 327056139861137134104103)
                  ·
                    rfl

theorem cell22_2866228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 2, 1, 6].length) (baseStart_2866228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2866228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2866228 prefixEnd_2866228 := by exact prefixLift 2866228
  have htrace : WordTrace (prefixWord ++ tailWord_2866228) baseStart_2866228 baseEnd_2866228 := by
    simpa [prefixWord, tailWord_2866228, baseEnd_2866228] using wordTrace_append hprefix tailTrace_2866228
  have hstable : (prefixWord ++ tailWord_2866228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2866228).length < 2 ^ (prefixWord ++ tailWord_2866228).sum := by decide
  have hdescent : baseEnd_2866228 < baseStart_2866228 := by decide
  rcases family_descends (prefixWord ++ tailWord_2866228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2866243 : List Nat := [1, 1, 1, 3, 1, 2, 7, 1, 2, 3]
def baseStart_2866243 : Nat := 118140960795 + 2866243 * 2 ^ 59
def prefixEnd_2866243 : Nat := 4983230072969 + 3 ^ 40 * 2866243 * 2
def baseEnd_2866243 : Nat := 981173554389956363187263

theorem tailTrace_2866243 : CollatzResearch.WordTrace tailWord_2866243 prefixEnd_2866243 981173554389956363187263 := by
  unfold tailWord_2866243
  simp only [CollatzResearch.WordTrace]
  refine ⟨104540470555098601177203383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69693647036732400784802255 104540470555098601177203383)
  ·
    refine ⟨156810705832647901765805075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104540470555098601177203383 156810705832647901765805075)
    ·
      refine ⟨235216058748971852648707613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156810705832647901765805075 235216058748971852648707613)
      ·
        refine ⟨88206022030864444743265355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 235216058748971852648707613 88206022030864444743265355)
        ·
          refine ⟨132309033046296667114898033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88206022030864444743265355 132309033046296667114898033)
          ·
            refine ⟨99231774784722500336173525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132309033046296667114898033 99231774784722500336173525)
            ·
              refine ⟨2325744721516933601629067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 99231774784722500336173525 2325744721516933601629067)
              ·
                refine ⟨3488617082275400402443601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2325744721516933601629067 3488617082275400402443601)
                ·
                  refine ⟨2616462811706550301832701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3488617082275400402443601 2616462811706550301832701)
                  ·
                    refine ⟨981173554389956363187263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2616462811706550301832701 981173554389956363187263)
                    ·
                      rfl

theorem cell22_2866243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 7, 1, 2, 3].length) (baseStart_2866243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2866243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2866243 prefixEnd_2866243 := by exact prefixLift 2866243
  have htrace : WordTrace (prefixWord ++ tailWord_2866243) baseStart_2866243 baseEnd_2866243 := by
    simpa [prefixWord, tailWord_2866243, baseEnd_2866243] using wordTrace_append hprefix tailTrace_2866243
  have hstable : (prefixWord ++ tailWord_2866243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2866243).length < 2 ^ (prefixWord ++ tailWord_2866243).sum := by decide
  have hdescent : baseEnd_2866243 < baseStart_2866243 := by decide
  rcases family_descends (prefixWord ++ tailWord_2866243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2866254 : List Nat := [4, 1, 1, 1, 1, 3, 1, 1, 2, 7]
def baseStart_2866254 : Nat := 118140960795 + 2866254 * 2 ^ 59
def prefixEnd_2866254 : Nat := 4983230072969 + 3 ^ 40 * 2866254 * 2
def baseEnd_2866254 : Nat := 981177319914756001162229

theorem tailTrace_2866254 : CollatzResearch.WordTrace tailWord_2866254 prefixEnd_2866254 981177319914756001162229 := by
  unfold tailWord_2866254
  simp only [CollatzResearch.WordTrace]
  refine ⟨13067608969757343756981727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69693914505372500037235877 13067608969757343756981727)
  ·
    refine ⟨19601413454636015635472591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13067608969757343756981727 19601413454636015635472591)
    ·
      refine ⟨29402120181954023453208887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19601413454636015635472591 29402120181954023453208887)
      ·
        refine ⟨44103180272931035179813331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29402120181954023453208887 44103180272931035179813331)
        ·
          refine ⟨66154770409396552769719997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44103180272931035179813331 66154770409396552769719997)
          ·
            refine ⟨24808038903523707288644999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66154770409396552769719997 24808038903523707288644999)
            ·
              refine ⟨37212058355285560932967499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24808038903523707288644999 37212058355285560932967499)
              ·
                refine ⟨55818087532928341399451249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37212058355285560932967499 55818087532928341399451249)
                ·
                  refine ⟨41863565649696256049588437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55818087532928341399451249 41863565649696256049588437)
                  ·
                    refine ⟨981177319914756001162229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41863565649696256049588437 981177319914756001162229)
                    ·
                      rfl

theorem cell22_2866254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 2, 7].length) (baseStart_2866254 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2866254 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2866254 prefixEnd_2866254 := by exact prefixLift 2866254
  have htrace : WordTrace (prefixWord ++ tailWord_2866254) baseStart_2866254 baseEnd_2866254 := by
    simpa [prefixWord, tailWord_2866254, baseEnd_2866254] using wordTrace_append hprefix tailTrace_2866254
  have hstable : (prefixWord ++ tailWord_2866254).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2866254).length < 2 ^ (prefixWord ++ tailWord_2866254).sum := by decide
  have hdescent : baseEnd_2866254 < baseStart_2866254 := by decide
  rcases family_descends (prefixWord ++ tailWord_2866254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2866284 : List Nat := [2, 2, 1, 1, 3, 2, 1, 3, 7]
def baseStart_2866284 : Nat := 118140960795 + 2866284 * 2 ^ 59
def prefixEnd_2866284 : Nat := 4983230072969 + 3 ^ 40 * 2866284 * 2
def baseEnd_2866284 : Nat := 327062529842615307637379

theorem tailTrace_2866284 : CollatzResearch.WordTrace tailWord_2866284 prefixEnd_2866284 327062529842615307637379 := by
  unfold tailWord_2866284
  simp only [CollatzResearch.WordTrace]
  refine ⟨52270982973975032589722953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69694643965300043452963937 52270982973975032589722953)
  ·
    refine ⟨39203237230481274442292215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52270982973975032589722953 39203237230481274442292215)
    ·
      refine ⟨58804855845721911663438323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39203237230481274442292215 58804855845721911663438323)
      ·
        refine ⟨88207283768582867495157485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58804855845721911663438323 88207283768582867495157485)
        ·
          refine ⟨33077731413218575310684057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88207283768582867495157485 33077731413218575310684057)
          ·
            refine ⟨24808298559913931483013043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33077731413218575310684057 24808298559913931483013043)
            ·
              refine ⟨37212447839870897224519565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24808298559913931483013043 37212447839870897224519565)
              ·
                refine ⟨13954667939951586459194837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37212447839870897224519565 13954667939951586459194837)
                ·
                  refine ⟨327062529842615307637379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13954667939951586459194837 327062529842615307637379)
                  ·
                    rfl

theorem cell22_2866284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 7].length) (baseStart_2866284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2866284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2866284 prefixEnd_2866284 := by exact prefixLift 2866284
  have htrace : WordTrace (prefixWord ++ tailWord_2866284) baseStart_2866284 baseEnd_2866284 := by
    simpa [prefixWord, tailWord_2866284, baseEnd_2866284] using wordTrace_append hprefix tailTrace_2866284
  have hstable : (prefixWord ++ tailWord_2866284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2866284).length < 2 ^ (prefixWord ++ tailWord_2866284).sum := by decide
  have hdescent : baseEnd_2866284 < baseStart_2866284 := by decide
  rcases family_descends (prefixWord ++ tailWord_2866284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2866299 : List Nat := [1, 1, 1, 1, 1, 4, 1, 5, 2, 5]
def baseStart_2866299 : Nat := 118140960795 + 2866299 * 2 ^ 59
def prefixEnd_2866299 : Nat := 4983230072969 + 3 ^ 40 * 2866299 * 2
def baseEnd_2866299 : Nat := 981192724334390883787091

theorem tailTrace_2866299 : CollatzResearch.WordTrace tailWord_2866299 prefixEnd_2866299 981192724334390883787091 := by
  unfold tailWord_2866299
  simp only [CollatzResearch.WordTrace]
  refine ⟨104542513042895722741241951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69695008695263815160827967 104542513042895722741241951)
  ·
    refine ⟨156813769564343584111862927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104542513042895722741241951 156813769564343584111862927)
    ·
      refine ⟨235220654346515376167794391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156813769564343584111862927 235220654346515376167794391)
      ·
        refine ⟨352830981519773064251691587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235220654346515376167794391 352830981519773064251691587)
        ·
          refine ⟨529246472279659596377537381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 352830981519773064251691587 529246472279659596377537381)
          ·
            refine ⟨99233713552436174320788259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 529246472279659596377537381 99233713552436174320788259)
            ·
              refine ⟨148850570328654261481182389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99233713552436174320788259 148850570328654261481182389)
              ·
                refine ⟨13954740968311337013860849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 148850570328654261481182389 13954740968311337013860849)
                ·
                  refine ⟨10466055726233502760395637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13954740968311337013860849 10466055726233502760395637)
                  ·
                    refine ⟨981192724334390883787091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10466055726233502760395637 981192724334390883787091)
                    ·
                      rfl

theorem cell22_2866299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 5, 2, 5].length) (baseStart_2866299 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2866299 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2866299 prefixEnd_2866299 := by exact prefixLift 2866299
  have htrace : WordTrace (prefixWord ++ tailWord_2866299) baseStart_2866299 baseEnd_2866299 := by
    simpa [prefixWord, tailWord_2866299, baseEnd_2866299] using wordTrace_append hprefix tailTrace_2866299
  have hstable : (prefixWord ++ tailWord_2866299).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2866299).length < 2 ^ (prefixWord ++ tailWord_2866299).sum := by decide
  have hdescent : baseEnd_2866299 < baseStart_2866299 := by decide
  rcases family_descends (prefixWord ++ tailWord_2866299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2866301 : List Nat := [1, 4, 1, 1, 3, 1, 3, 3, 5]
def baseStart_2866301 : Nat := 118140960795 + 2866301 * 2 ^ 59
def prefixEnd_2866301 : Nat := 4983230072969 + 3 ^ 40 * 2866301 * 2
def baseEnd_2866301 : Nat := 327064469658421181745695

theorem tailTrace_2866301 : CollatzResearch.WordTrace tailWord_2866301 prefixEnd_2866301 327064469658421181745695 := by
  unfold tailWord_2866301
  simp only [CollatzResearch.WordTrace]
  refine ⟨104542585988888477082814757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69695057325925651388543171 104542585988888477082814757)
  ·
    refine ⟨19601734872916589453027767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104542585988888477082814757 19601734872916589453027767)
    ·
      refine ⟨29402602309374884179541651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19601734872916589453027767 29402602309374884179541651)
      ·
        refine ⟨44103903464062326269312477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29402602309374884179541651 44103903464062326269312477)
        ·
          refine ⟨16538963799023372350992179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44103903464062326269312477 16538963799023372350992179)
          ·
            refine ⟨24808445698535058526488269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16538963799023372350992179 24808445698535058526488269)
            ·
              refine ⟨9303167136950646947433101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24808445698535058526488269 9303167136950646947433101)
              ·
                refine ⟨3488687676356492605287413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9303167136950646947433101 3488687676356492605287413)
                ·
                  refine ⟨327064469658421181745695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3488687676356492605287413 327064469658421181745695)
                  ·
                    rfl

theorem cell22_2866301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 3, 5].length) (baseStart_2866301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2866301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2866301 prefixEnd_2866301 := by exact prefixLift 2866301
  have htrace : WordTrace (prefixWord ++ tailWord_2866301) baseStart_2866301 baseEnd_2866301 := by
    simpa [prefixWord, tailWord_2866301, baseEnd_2866301] using wordTrace_append hprefix tailTrace_2866301
  have hstable : (prefixWord ++ tailWord_2866301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2866301).length < 2 ^ (prefixWord ++ tailWord_2866301).sum := by decide
  have hdescent : baseEnd_2866301 < baseStart_2866301 := by decide
  rcases family_descends (prefixWord ++ tailWord_2866301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2866361 : List Nat := [1, 2, 1, 4, 1, 3, 1, 3, 1, 5]
def baseStart_2866361 : Nat := 118140960795 + 2866361 * 2 ^ 59
def prefixEnd_2866361 : Nat := 4983230072969 + 3 ^ 40 * 2866361 * 2
def baseEnd_2866361 : Nat := 981213948201443388736901

theorem tailTrace_2866361 : CollatzResearch.WordTrace tailWord_2866361 prefixEnd_2866361 981213948201443388736901 := by
  unfold tailWord_2866361
  simp only [CollatzResearch.WordTrace]
  refine ⟨104544774368671107329998937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69696516245780738219999291 104544774368671107329998937)
  ·
    refine ⟨78408580776503330497499203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104544774368671107329998937 78408580776503330497499203)
    ·
      refine ⟨117612871164754995746248805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78408580776503330497499203 117612871164754995746248805)
      ·
        refine ⟨22052413343391561702421651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 117612871164754995746248805 22052413343391561702421651)
        ·
          refine ⟨33078620015087342553632477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22052413343391561702421651 33078620015087342553632477)
          ·
            refine ⟨12404482505657753457612179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33078620015087342553632477 12404482505657753457612179)
            ·
              refine ⟨18606723758486630186418269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12404482505657753457612179 18606723758486630186418269)
              ·
                refine ⟨6977521409432486319906851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18606723758486630186418269 6977521409432486319906851)
                ·
                  refine ⟨10466282114148729479860277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6977521409432486319906851 10466282114148729479860277)
                  ·
                    refine ⟨981213948201443388736901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10466282114148729479860277 981213948201443388736901)
                    ·
                      rfl

theorem cell22_2866361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 3, 1, 5].length) (baseStart_2866361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2866361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2866361 prefixEnd_2866361 := by exact prefixLift 2866361
  have htrace : WordTrace (prefixWord ++ tailWord_2866361) baseStart_2866361 baseEnd_2866361 := by
    simpa [prefixWord, tailWord_2866361, baseEnd_2866361] using wordTrace_append hprefix tailTrace_2866361
  have hstable : (prefixWord ++ tailWord_2866361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2866361).length < 2 ^ (prefixWord ++ tailWord_2866361).sum := by decide
  have hdescent : baseEnd_2866361 < baseStart_2866361 := by decide
  rcases family_descends (prefixWord ++ tailWord_2866361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2866382 : List Nat := [4, 1, 1, 1, 5, 2, 2, 1, 1, 4]
def baseStart_2866382 : Nat := 118140960795 + 2866382 * 2 ^ 59
def prefixEnd_2866382 : Nat := 4983230072969 + 3 ^ 40 * 2866382 * 2
def baseEnd_2866382 : Nat := 981221136930606333961837

theorem tailTrace_2866382 : CollatzResearch.WordTrace tailWord_2866382 prefixEnd_2866382 981221136930606333961837 := by
  unfold tailWord_2866382
  simp only [CollatzResearch.WordTrace]
  refine ⟨13068192537699378489564175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69697026867730018611008933 13068192537699378489564175)
  ·
    refine ⟨19602288806549067734346263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13068192537699378489564175 19602288806549067734346263)
    ·
      refine ⟨29403433209823601601519395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19602288806549067734346263 29403433209823601601519395)
      ·
        refine ⟨44105149814735402402279093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29403433209823601601519395 44105149814735402402279093)
        ·
          refine ⟨4134857795131443975213665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 44105149814735402402279093 4134857795131443975213665)
          ·
            refine ⟨3101143346348582981410249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4134857795131443975213665 3101143346348582981410249)
            ·
              refine ⟨2325857509761437236057687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3101143346348582981410249 2325857509761437236057687)
              ·
                refine ⟨3488786264642155854086531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2325857509761437236057687 3488786264642155854086531)
                ·
                  refine ⟨5233179396963233781129797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3488786264642155854086531 5233179396963233781129797)
                  ·
                    refine ⟨981221136930606333961837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5233179396963233781129797 981221136930606333961837)
                    ·
                      rfl

theorem cell22_2866382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 2, 1, 1, 4].length) (baseStart_2866382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2866382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2866382 prefixEnd_2866382 := by exact prefixLift 2866382
  have htrace : WordTrace (prefixWord ++ tailWord_2866382) baseStart_2866382 baseEnd_2866382 := by
    simpa [prefixWord, tailWord_2866382, baseEnd_2866382] using wordTrace_append hprefix tailTrace_2866382
  have hstable : (prefixWord ++ tailWord_2866382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2866382).length < 2 ^ (prefixWord ++ tailWord_2866382).sum := by decide
  have hdescent : baseEnd_2866382 < baseStart_2866382 := by decide
  rcases family_descends (prefixWord ++ tailWord_2866382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2866483 : List Nat := [1, 1, 1, 2, 5, 3, 1, 1, 3, 4]
def baseStart_2866483 : Nat := 118140960795 + 2866483 * 2 ^ 59
def prefixEnd_2866483 : Nat := 4983230072969 + 3 ^ 40 * 2866483 * 2
def baseEnd_2866483 : Nat := 981255711294675737186527

theorem tailTrace_2866483 : CollatzResearch.WordTrace tailWord_2866483 prefixEnd_2866483 981255711294675737186527 := by
  unfold tailWord_2866483
  simp only [CollatzResearch.WordTrace]
  refine ⟨104549224074229122165940103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69699482716152748110626735 104549224074229122165940103)
  ·
    refine ⟨156823836111343683248910155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104549224074229122165940103 156823836111343683248910155)
    ·
      refine ⟨235235754167015524873365233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156823836111343683248910155 235235754167015524873365233)
      ·
        refine ⟨176426815625261643655023925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 235235754167015524873365233 176426815625261643655023925)
        ·
          refine ⟨16540013964868279092658493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 176426815625261643655023925 16540013964868279092658493)
          ·
            refine ⟨6202505236825604659746935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16540013964868279092658493 6202505236825604659746935)
            ·
              refine ⟨9303757855238406989620403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6202505236825604659746935 9303757855238406989620403)
              ·
                refine ⟨13955636782857610484430605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9303757855238406989620403 13955636782857610484430605)
                ·
                  refine ⟨5233363793571603931661477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13955636782857610484430605 5233363793571603931661477)
                  ·
                    refine ⟨981255711294675737186527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5233363793571603931661477 981255711294675737186527)
                    ·
                      rfl

theorem cell22_2866483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 1, 3, 4].length) (baseStart_2866483 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2866483 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2866483 prefixEnd_2866483 := by exact prefixLift 2866483
  have htrace : WordTrace (prefixWord ++ tailWord_2866483) baseStart_2866483 baseEnd_2866483 := by
    simpa [prefixWord, tailWord_2866483, baseEnd_2866483] using wordTrace_append hprefix tailTrace_2866483
  have hstable : (prefixWord ++ tailWord_2866483).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2866483).length < 2 ^ (prefixWord ++ tailWord_2866483).sum := by decide
  have hdescent : baseEnd_2866483 < baseStart_2866483 := by decide
  rcases family_descends (prefixWord ++ tailWord_2866483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2866530 : List Nat := [3, 3, 2, 1, 1, 1, 4, 1, 1, 5]
def baseStart_2866530 : Nat := 118140960795 + 2866530 * 2 ^ 59
def prefixEnd_2866530 : Nat := 4983230072969 + 3 ^ 40 * 2866530 * 2
def baseEnd_2866530 : Nat := 981271800355183281261383

theorem tailTrace_2866530 : CollatzResearch.WordTrace tailWord_2866530 prefixEnd_2866530 981271800355183281261383 := by
  unfold tailWord_2866530
  simp only [CollatzResearch.WordTrace]
  refine ⟨26137734576264712298225261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69700625536705899461934029 26137734576264712298225261)
  ·
    refine ⟨9801650466099267111834473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26137734576264712298225261 9801650466099267111834473)
    ·
      refine ⟨7351237849574450333875855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9801650466099267111834473 7351237849574450333875855)
      ·
        refine ⟨11026856774361675500813783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7351237849574450333875855 11026856774361675500813783)
        ·
          refine ⟨16540285161542513251220675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11026856774361675500813783 16540285161542513251220675)
          ·
            refine ⟨24810427742313769876831013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16540285161542513251220675 24810427742313769876831013)
            ·
              refine ⟨4651955201683831851905815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24810427742313769876831013 4651955201683831851905815)
              ·
                refine ⟨6977932802525747777858723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4651955201683831851905815 6977932802525747777858723)
                ·
                  refine ⟨10466899203788621666788085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6977932802525747777858723 10466899203788621666788085)
                  ·
                    refine ⟨981271800355183281261383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10466899203788621666788085 981271800355183281261383)
                    ·
                      rfl

theorem cell22_2866530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_2866530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2866530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2866530 prefixEnd_2866530 := by exact prefixLift 2866530
  have htrace : WordTrace (prefixWord ++ tailWord_2866530) baseStart_2866530 baseEnd_2866530 := by
    simpa [prefixWord, tailWord_2866530, baseEnd_2866530] using wordTrace_append hprefix tailTrace_2866530
  have hstable : (prefixWord ++ tailWord_2866530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2866530).length < 2 ^ (prefixWord ++ tailWord_2866530).sum := by decide
  have hdescent : baseEnd_2866530 < baseStart_2866530 := by decide
  rcases family_descends (prefixWord ++ tailWord_2866530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2866543 : List Nat := [1, 1, 2, 1, 3, 1, 7, 6]
def baseStart_2866543 : Nat := 118140960795 + 2866543 * 2 ^ 59
def prefixEnd_2866543 : Nat := 4983230072969 + 3 ^ 40 * 2866543 * 2
def baseEnd_2866543 : Nat := 109030694502317286742927

theorem tailTrace_2866543 : CollatzResearch.WordTrace tailWord_2866543 prefixEnd_2866543 109030694502317286742927 := by
  unfold tailWord_2866543
  simp only [CollatzResearch.WordTrace]
  refine ⟨104551412454011752413124283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69700941636007834942082855 104551412454011752413124283)
  ·
    refine ⟨156827118681017628619686425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104551412454011752413124283 156827118681017628619686425)
    ·
      refine ⟨117620339010763221464764819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156827118681017628619686425 117620339010763221464764819)
      ·
        refine ⟨176430508516144832197147229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117620339010763221464764819 176430508516144832197147229)
        ·
          refine ⟨66161440693554312073930211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 176430508516144832197147229 66161440693554312073930211)
          ·
            refine ⟨99242161040331468110895317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66161440693554312073930211 99242161040331468110895317)
            ·
              refine ⟨2325988149382768783849109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 99242161040331468110895317 2325988149382768783849109)
              ·
                refine ⟨109030694502317286742927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2325988149382768783849109 109030694502317286742927)
                ·
                  rfl

theorem cell22_2866543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 7, 6].length) (baseStart_2866543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2866543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2866543 prefixEnd_2866543 := by exact prefixLift 2866543
  have htrace : WordTrace (prefixWord ++ tailWord_2866543) baseStart_2866543 baseEnd_2866543 := by
    simpa [prefixWord, tailWord_2866543, baseEnd_2866543] using wordTrace_append hprefix tailTrace_2866543
  have hstable : (prefixWord ++ tailWord_2866543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2866543).length < 2 ^ (prefixWord ++ tailWord_2866543).sum := by decide
  have hdescent : baseEnd_2866543 < baseStart_2866543 := by decide
  rcases family_descends (prefixWord ++ tailWord_2866543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2866605 : List Nat := [1, 5, 2, 2, 1, 1, 1, 2, 7]
def baseStart_2866605 : Nat := 118140960795 + 2866605 * 2 ^ 59
def prefixEnd_2866605 : Nat := 4983230072969 + 3 ^ 40 * 2866605 * 2
def baseEnd_2866605 : Nat := 327099158129302695212051

theorem tailTrace_2866605 : CollatzResearch.WordTrace tailWord_2866605 prefixEnd_2866605 327099158129302695212051 := by
  unfold tailWord_2866605
  simp only [CollatzResearch.WordTrace]
  refine ⟨104553673779787137001881269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69702449186524758001254179 104553673779787137001881269)
  ·
    refine ⟨9801906916855044093926369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 104553673779787137001881269 9801906916855044093926369)
    ·
      refine ⟨7351430187641283070444777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9801906916855044093926369 7351430187641283070444777)
      ·
        refine ⟨5513572640730962302833583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7351430187641283070444777 5513572640730962302833583)
        ·
          refine ⟨8270358961096443454250375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5513572640730962302833583 8270358961096443454250375)
          ·
            refine ⟨12405538441644665181375563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8270358961096443454250375 12405538441644665181375563)
            ·
              refine ⟨18608307662466997772063345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12405538441644665181375563 18608307662466997772063345)
              ·
                refine ⟨13956230746850248329047509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18608307662466997772063345 13956230746850248329047509)
                ·
                  refine ⟨327099158129302695212051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13956230746850248329047509 327099158129302695212051)
                  ·
                    rfl

theorem cell22_2866605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 2, 7].length) (baseStart_2866605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2866605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2866605 prefixEnd_2866605 := by exact prefixLift 2866605
  have htrace : WordTrace (prefixWord ++ tailWord_2866605) baseStart_2866605 baseEnd_2866605 := by
    simpa [prefixWord, tailWord_2866605, baseEnd_2866605] using wordTrace_append hprefix tailTrace_2866605
  have hstable : (prefixWord ++ tailWord_2866605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2866605).length < 2 ^ (prefixWord ++ tailWord_2866605).sum := by decide
  have hdescent : baseEnd_2866605 < baseStart_2866605 := by decide
  rcases family_descends (prefixWord ++ tailWord_2866605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2866618 : List Nat := [3, 1, 1, 1, 2, 1, 1, 1, 7, 4]
def baseStart_2866618 : Nat := 118140960795 + 2866618 * 2 ^ 59
def prefixEnd_2866618 : Nat := 4983230072969 + 3 ^ 40 * 2866618 * 2
def baseEnd_2866618 : Nat := 981301924553580385061113

theorem tailTrace_2866618 : CollatzResearch.WordTrace tailWord_2866618 prefixEnd_2866618 981301924553580385061113 := by
  unfold tailWord_2866618
  simp only [CollatzResearch.WordTrace]
  refine ⟨26138536982185010055526127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69702765285826693481403005 26138536982185010055526127)
  ·
    refine ⟨39207805473277515083289191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26138536982185010055526127 39207805473277515083289191)
    ·
      refine ⟨58811708209916272624933787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39207805473277515083289191 58811708209916272624933787)
      ·
        refine ⟨88217562314874408937400681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58811708209916272624933787 88217562314874408937400681)
        ·
          refine ⟨66163171736155806703050511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88217562314874408937400681 66163171736155806703050511)
          ·
            refine ⟨99244757604233710054575767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66163171736155806703050511 99244757604233710054575767)
            ·
              refine ⟨148867136406350565081863651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99244757604233710054575767 148867136406350565081863651)
              ·
                refine ⟨223300704609525847622795477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 148867136406350565081863651 223300704609525847622795477)
                ·
                  refine ⟨5233610264285762053659269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 223300704609525847622795477 5233610264285762053659269)
                  ·
                    refine ⟨981301924553580385061113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5233610264285762053659269 981301924553580385061113)
                    ·
                      rfl

theorem cell22_2866618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 7, 4].length) (baseStart_2866618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2866618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2866618 prefixEnd_2866618 := by exact prefixLift 2866618
  have htrace : WordTrace (prefixWord ++ tailWord_2866618) baseStart_2866618 baseEnd_2866618 := by
    simpa [prefixWord, tailWord_2866618, baseEnd_2866618] using wordTrace_append hprefix tailTrace_2866618
  have hstable : (prefixWord ++ tailWord_2866618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2866618).length < 2 ^ (prefixWord ++ tailWord_2866618).sum := by decide
  have hdescent : baseEnd_2866618 < baseStart_2866618 := by decide
  rcases family_descends (prefixWord ++ tailWord_2866618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2866680 : List Nat := [2, 1, 2, 1, 1, 5, 2, 2, 2, 4]
def baseStart_2866680 : Nat := 118140960795 + 2866680 * 2 ^ 59
def prefixEnd_2866680 : Nat := 4983230072969 + 3 ^ 40 * 2866680 * 2
def baseEnd_2866680 : Nat := 981323148420632890010923

theorem tailTrace_2866680 : CollatzResearch.WordTrace tailWord_2866680 prefixEnd_2866680 981323148420632890010923 := by
  unfold tailWord_2866680
  simp only [CollatzResearch.WordTrace]
  refine ⟨52278204627257712405430747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69704272836343616540574329 52278204627257712405430747)
  ·
    refine ⟨78417306940886568608146121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52278204627257712405430747 78417306940886568608146121)
    ·
      refine ⟨58812980205664926456109591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78417306940886568608146121 58812980205664926456109591)
      ·
        refine ⟨88219470308497389684164387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58812980205664926456109591 88219470308497389684164387)
        ·
          refine ⟨132329205462746084526246581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88219470308497389684164387 132329205462746084526246581)
          ·
            refine ⟨12405863012132445424335617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 132329205462746084526246581 12405863012132445424335617)
            ·
              refine ⟨9304397259099334068251713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12405863012132445424335617 9304397259099334068251713)
              ·
                refine ⟨6978297944324500551188785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9304397259099334068251713 6978297944324500551188785)
                ·
                  refine ⟨5233723458243375413391589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6978297944324500551188785 5233723458243375413391589)
                  ·
                    refine ⟨981323148420632890010923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5233723458243375413391589 981323148420632890010923)
                    ·
                      rfl

theorem cell22_2866680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 2, 2, 4].length) (baseStart_2866680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2866680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2866680 prefixEnd_2866680 := by exact prefixLift 2866680
  have htrace : WordTrace (prefixWord ++ tailWord_2866680) baseStart_2866680 baseEnd_2866680 := by
    simpa [prefixWord, tailWord_2866680, baseEnd_2866680] using wordTrace_append hprefix tailTrace_2866680
  have hstable : (prefixWord ++ tailWord_2866680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2866680).length < 2 ^ (prefixWord ++ tailWord_2866680).sum := by decide
  have hdescent : baseEnd_2866680 < baseStart_2866680 := by decide
  rcases family_descends (prefixWord ++ tailWord_2866680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2866682 : List Nat := [3, 1, 1, 1, 1, 2, 6, 2, 2, 3]
def baseStart_2866682 : Nat := 118140960795 + 2866682 * 2 ^ 59
def prefixEnd_2866682 : Nat := 4983230072969 + 3 ^ 40 * 2866682 * 2
def baseEnd_2866682 : Nat := 981323833061505551460917

theorem tailTrace_2866682 : CollatzResearch.WordTrace tailWord_2866682 prefixEnd_2866682 981323833061505551460917 := by
  unfold tailWord_2866682
  simp only [CollatzResearch.WordTrace]
  refine ⟨26139120550127044788108575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69704321467005452768289533 26139120550127044788108575)
  ·
    refine ⟨39208680825190567182162863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26139120550127044788108575 39208680825190567182162863)
    ·
      refine ⟨58813021237785850773244295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39208680825190567182162863 58813021237785850773244295)
      ·
        refine ⟨88219531856678776159866443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58813021237785850773244295 88219531856678776159866443)
        ·
          refine ⟨132329297785018164239799665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88219531856678776159866443 132329297785018164239799665)
          ·
            refine ⟨99246973338763623179849749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132329297785018164239799665 99246973338763623179849749)
            ·
              refine ⟨4652201875254544836555457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 99246973338763623179849749 4652201875254544836555457)
              ·
                refine ⟨3489151406440908627416593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4652201875254544836555457 3489151406440908627416593)
                ·
                  refine ⟨2616863554830681470562445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3489151406440908627416593 2616863554830681470562445)
                  ·
                    refine ⟨981323833061505551460917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2616863554830681470562445 981323833061505551460917)
                    ·
                      rfl

theorem cell22_2866682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 6, 2, 2, 3].length) (baseStart_2866682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2866682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2866682 prefixEnd_2866682 := by exact prefixLift 2866682
  have htrace : WordTrace (prefixWord ++ tailWord_2866682) baseStart_2866682 baseEnd_2866682 := by
    simpa [prefixWord, tailWord_2866682, baseEnd_2866682] using wordTrace_append hprefix tailTrace_2866682
  have hstable : (prefixWord ++ tailWord_2866682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2866682).length < 2 ^ (prefixWord ++ tailWord_2866682).sum := by decide
  have hdescent : baseEnd_2866682 < baseStart_2866682 := by decide
  rcases family_descends (prefixWord ++ tailWord_2866682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2866693 : List Nat := [1, 3, 1, 1, 2, 2, 1, 2, 2, 7]
def baseStart_2866693 : Nat := 118140960795 + 2866693 * 2 ^ 59
def prefixEnd_2866693 : Nat := 4983230072969 + 3 ^ 40 * 2866693 * 2
def baseEnd_2866693 : Nat := 981327598586305189435883

theorem tailTrace_2866693 : CollatzResearch.WordTrace tailWord_2866693 prefixEnd_2866693 981327598586305189435883 := by
  unfold tailWord_2866693
  simp only [CollatzResearch.WordTrace]
  refine ⟨104556883403468328031084733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69704588935645552020723155 104556883403468328031084733)
  ·
    refine ⟨39208831276300623011656775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104556883403468328031084733 39208831276300623011656775)
    ·
      refine ⟨58813246914450934517485163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39208831276300623011656775 58813246914450934517485163)
      ·
        refine ⟨88219870371676401776227745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58813246914450934517485163 88219870371676401776227745)
        ·
          refine ⟨66164902778757301332170809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88219870371676401776227745 66164902778757301332170809)
          ·
            refine ⟨49623677084067975999128107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66164902778757301332170809 49623677084067975999128107)
            ·
              refine ⟨74435515626101963998692161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49623677084067975999128107 74435515626101963998692161)
              ·
                refine ⟨55826636719576472999019121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74435515626101963998692161 55826636719576472999019121)
                ·
                  refine ⟨41869977539682354749264341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55826636719576472999019121 41869977539682354749264341)
                  ·
                    refine ⟨981327598586305189435883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41869977539682354749264341 981327598586305189435883)
                    ·
                      rfl

theorem cell22_2866693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 2, 7].length) (baseStart_2866693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2866693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2866693 prefixEnd_2866693 := by exact prefixLift 2866693
  have htrace : WordTrace (prefixWord ++ tailWord_2866693) baseStart_2866693 baseEnd_2866693 := by
    simpa [prefixWord, tailWord_2866693, baseEnd_2866693] using wordTrace_append hprefix tailTrace_2866693
  have hstable : (prefixWord ++ tailWord_2866693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2866693).length < 2 ^ (prefixWord ++ tailWord_2866693).sum := by decide
  have hdescent : baseEnd_2866693 < baseStart_2866693 := by decide
  rcases family_descends (prefixWord ++ tailWord_2866693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2866695 : List Nat := [1, 1, 4, 3, 2, 1, 3, 7]
def baseStart_2866695 : Nat := 118140960795 + 2866695 * 2 ^ 59
def prefixEnd_2866695 : Nat := 4983230072969 + 3 ^ 40 * 2866695 * 2
def baseEnd_2866695 : Nat := 109036475914130872320653

theorem tailTrace_2866695 : CollatzResearch.WordTrace tailWord_2866695 prefixEnd_2866695 109036475914130872320653 := by
  unfold tailWord_2866695
  simp only [CollatzResearch.WordTrace]
  refine ⟨104556956349461082372657539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69704637566307388248438359 104556956349461082372657539)
  ·
    refine ⟨156835434524191623558986309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104556956349461082372657539 156835434524191623558986309)
    ·
      refine ⟨29406643973285929417309933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 156835434524191623558986309 29406643973285929417309933)
      ·
        refine ⟨11027491489982223531491225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29406643973285929417309933 11027491489982223531491225)
        ·
          refine ⟨8270618617486667648618419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11027491489982223531491225 8270618617486667648618419)
          ·
            refine ⟨12405927926230001472927629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8270618617486667648618419 12405927926230001472927629)
            ·
              refine ⟨4652222972336250552347861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12405927926230001472927629 4652222972336250552347861)
              ·
                refine ⟨109036475914130872320653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4652222972336250552347861 109036475914130872320653)
                ·
                  rfl

theorem cell22_2866695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 3, 7].length) (baseStart_2866695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2866695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2866695 prefixEnd_2866695 := by exact prefixLift 2866695
  have htrace : WordTrace (prefixWord ++ tailWord_2866695) baseStart_2866695 baseEnd_2866695 := by
    simpa [prefixWord, tailWord_2866695, baseEnd_2866695] using wordTrace_append hprefix tailTrace_2866695
  have hstable : (prefixWord ++ tailWord_2866695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2866695).length < 2 ^ (prefixWord ++ tailWord_2866695).sum := by decide
  have hdescent : baseEnd_2866695 < baseStart_2866695 := by decide
  rcases family_descends (prefixWord ++ tailWord_2866695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2866712 : List Nat := [2, 1, 2, 3, 4, 1, 3, 6]
def baseStart_2866712 : Nat := 118140960795 + 2866712 * 2 ^ 59
def prefixEnd_2866712 : Nat := 4983230072969 + 3 ^ 40 * 2866712 * 2
def baseEnd_2866712 : Nat := 109037122519399497023425

theorem tailTrace_2866712 : CollatzResearch.WordTrace tailWord_2866712 prefixEnd_2866712 109037122519399497023425 := by
  unfold tailWord_2866712
  simp only [CollatzResearch.WordTrace]
  refine ⟨52278788195199747138013195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69705050926932996184017593 52278788195199747138013195)
  ·
    refine ⟨78418182292799620707019793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52278788195199747138013195 78418182292799620707019793)
    ·
      refine ⟨58813636719599715530264845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78418182292799620707019793 58813636719599715530264845)
      ·
        refine ⟨22055113769849893323849317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58813636719599715530264845 22055113769849893323849317)
        ·
          refine ⟨4135333831846854998221747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22055113769849893323849317 4135333831846854998221747)
          ·
            refine ⟨6203000747770282497332621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4135333831846854998221747 6203000747770282497332621)
            ·
              refine ⟨2326125280413855936499733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6203000747770282497332621 2326125280413855936499733)
              ·
                refine ⟨109037122519399497023425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2326125280413855936499733 109037122519399497023425)
                ·
                  rfl

theorem cell22_2866712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 3, 6].length) (baseStart_2866712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2866712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2866712 prefixEnd_2866712 := by exact prefixLift 2866712
  have htrace : WordTrace (prefixWord ++ tailWord_2866712) baseStart_2866712 baseEnd_2866712 := by
    simpa [prefixWord, tailWord_2866712, baseEnd_2866712] using wordTrace_append hprefix tailTrace_2866712
  have hstable : (prefixWord ++ tailWord_2866712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2866712).length < 2 ^ (prefixWord ++ tailWord_2866712).sum := by decide
  have hdescent : baseEnd_2866712 < baseStart_2866712 := by decide
  rcases family_descends (prefixWord ++ tailWord_2866712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2866744 : List Nat := [2, 1, 2, 1, 4, 2, 2, 4, 1, 3]
def baseStart_2866744 : Nat := 118140960795 + 2866744 * 2 ^ 59
def prefixEnd_2866744 : Nat := 4983230072969 + 3 ^ 40 * 2866744 * 2
def baseEnd_2866744 : Nat := 981345056928558056410727

theorem tailTrace_2866744 : CollatzResearch.WordTrace tailWord_2866744 prefixEnd_2866744 981345056928558056410727 := by
  unfold tailWord_2866744
  simp only [CollatzResearch.WordTrace]
  refine ⟨52279371763141781870595643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69705829017522375827460857 52279371763141781870595643)
  ·
    refine ⟨78419057644712672805893465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52279371763141781870595643 78419057644712672805893465)
    ·
      refine ⟨58814293233534504604420099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78419057644712672805893465 58814293233534504604420099)
      ·
        refine ⟨88221439850301756906630149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58814293233534504604420099 88221439850301756906630149)
        ·
          refine ⟨16541519971931579419993153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 88221439850301756906630149 16541519971931579419993153)
          ·
            refine ⟨12406139978948684564994865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16541519971931579419993153 12406139978948684564994865)
            ·
              refine ⟨9304604984211513423746149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12406139978948684564994865 9304604984211513423746149)
              ·
                refine ⟨1744613434539658766952403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9304604984211513423746149 1744613434539658766952403)
                ·
                  refine ⟨2616920151809488150428605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1744613434539658766952403 2616920151809488150428605)
                  ·
                    refine ⟨981345056928558056410727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2616920151809488150428605 981345056928558056410727)
                    ·
                      rfl

theorem cell22_2866744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 4, 1, 3].length) (baseStart_2866744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2866744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2866744 prefixEnd_2866744 := by exact prefixLift 2866744
  have htrace : WordTrace (prefixWord ++ tailWord_2866744) baseStart_2866744 baseEnd_2866744 := by
    simpa [prefixWord, tailWord_2866744, baseEnd_2866744] using wordTrace_append hprefix tailTrace_2866744
  have hstable : (prefixWord ++ tailWord_2866744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2866744).length < 2 ^ (prefixWord ++ tailWord_2866744).sum := by decide
  have hdescent : baseEnd_2866744 < baseStart_2866744 := by decide
  rcases family_descends (prefixWord ++ tailWord_2866744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2866757 : List Nat := [1, 3, 1, 1, 1, 4, 5, 1, 5]
def baseStart_2866757 : Nat := 118140960795 + 2866757 * 2 ^ 59
def prefixEnd_2866757 : Nat := 4983230072969 + 3 ^ 40 * 2866757 * 2
def baseEnd_2866757 : Nat := 327116502364743451945229

theorem tailTrace_2866757 : CollatzResearch.WordTrace tailWord_2866757 prefixEnd_2866757 327116502364743451945229 := by
  unfold tailWord_2866757
  simp only [CollatzResearch.WordTrace]
  refine ⟨104559217675236466961414525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69706145116824311307609683 104559217675236466961414525)
  ·
    refine ⟨39209706628213675110530447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104559217675236466961414525 39209706628213675110530447)
    ·
      refine ⟨58814559942320512665795671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39209706628213675110530447 58814559942320512665795671)
      ·
        refine ⟨88221839913480768998693507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58814559942320512665795671 88221839913480768998693507)
        ·
          refine ⟨132332759870221153498040261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88221839913480768998693507 132332759870221153498040261)
          ·
            refine ⟨24812392475666466280882549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 132332759870221153498040261 24812392475666466280882549)
            ·
              refine ⟨2326161794593731213832739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24812392475666466280882549 2326161794593731213832739)
              ·
                refine ⟨3489242691890596820749109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2326161794593731213832739 3489242691890596820749109)
                ·
                  refine ⟨327116502364743451945229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3489242691890596820749109 327116502364743451945229)
                  ·
                    rfl

theorem cell22_2866757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 5, 1, 5].length) (baseStart_2866757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2866757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2866757 prefixEnd_2866757 := by exact prefixLift 2866757
  have htrace : WordTrace (prefixWord ++ tailWord_2866757) baseStart_2866757 baseEnd_2866757 := by
    simpa [prefixWord, tailWord_2866757, baseEnd_2866757] using wordTrace_append hprefix tailTrace_2866757
  have hstable : (prefixWord ++ tailWord_2866757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2866757).length < 2 ^ (prefixWord ++ tailWord_2866757).sum := by decide
  have hdescent : baseEnd_2866757 < baseStart_2866757 := by decide
  rcases family_descends (prefixWord ++ tailWord_2866757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2866787 : List Nat := [1, 1, 1, 5, 1, 3, 2, 3, 1, 4]
def baseStart_2866787 : Nat := 118140960795 + 2866787 * 2 ^ 59
def prefixEnd_2866787 : Nat := 4983230072969 + 3 ^ 40 * 2866787 * 2
def baseEnd_2866787 : Nat := 981359776707320277585595

theorem tailTrace_2866787 : CollatzResearch.WordTrace tailWord_2866787 prefixEnd_2866787 981359776707320277585595 := by
  unfold tailWord_2866787
  simp only [CollatzResearch.WordTrace]
  refine ⟨104560311865127782085006615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69706874576751854723337743 104560311865127782085006615)
  ·
    refine ⟨156840467797691673127509923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104560311865127782085006615 156840467797691673127509923)
    ·
      refine ⟨235260701696537509691264885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156840467797691673127509923 235260701696537509691264885)
      ·
        refine ⟨22055690784050391533556083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 235260701696537509691264885 22055690784050391533556083)
        ·
          refine ⟨33083536176075587300334125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22055690784050391533556083 33083536176075587300334125)
          ·
            refine ⟨12406326066028345237625297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33083536176075587300334125 12406326066028345237625297)
            ·
              refine ⟨9304744549521258928218973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12406326066028345237625297 9304744549521258928218973)
              ·
                refine ⟨3489279206070472098082115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9304744549521258928218973 3489279206070472098082115)
                ·
                  refine ⟨5233918809105708147123173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3489279206070472098082115 5233918809105708147123173)
                  ·
                    refine ⟨981359776707320277585595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5233918809105708147123173 981359776707320277585595)
                    ·
                      rfl

theorem cell22_2866787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 3, 1, 4].length) (baseStart_2866787 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2866787 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2866787 prefixEnd_2866787 := by exact prefixLift 2866787
  have htrace : WordTrace (prefixWord ++ tailWord_2866787) baseStart_2866787 baseEnd_2866787 := by
    simpa [prefixWord, tailWord_2866787, baseEnd_2866787] using wordTrace_append hprefix tailTrace_2866787
  have hstable : (prefixWord ++ tailWord_2866787).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2866787).length < 2 ^ (prefixWord ++ tailWord_2866787).sum := by decide
  have hdescent : baseEnd_2866787 < baseStart_2866787 := by decide
  rcases family_descends (prefixWord ++ tailWord_2866787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2866802 : List Nat := [3, 2, 1, 2, 3, 1, 3, 1, 6]
def baseStart_2866802 : Nat := 118140960795 + 2866802 * 2 ^ 59
def prefixEnd_2866802 : Nat := 4983230072969 + 3 ^ 40 * 2866802 * 2
def baseEnd_2866802 : Nat := 327121637171288412820183

theorem tailTrace_2866802 : CollatzResearch.WordTrace tailWord_2866802 prefixEnd_2866802 327121637171288412820183 := by
  unfold tailWord_2866802
  simp only [CollatzResearch.WordTrace]
  refine ⟨26140214740018359911700665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69707239306715626431201773 26140214740018359911700665)
  ·
    refine ⟨19605161055013769933775499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26140214740018359911700665 19605161055013769933775499)
    ·
      refine ⟨29407741582520654900663249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19605161055013769933775499 29407741582520654900663249)
      ·
        refine ⟨22055806186890491175497437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29407741582520654900663249 22055806186890491175497437)
        ·
          refine ⟨8270927320083934190811539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22055806186890491175497437 8270927320083934190811539)
          ·
            refine ⟨12406390980125901286217309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8270927320083934190811539 12406390980125901286217309)
            ·
              refine ⟨4652396617547212982331491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12406390980125901286217309 4652396617547212982331491)
              ·
                refine ⟨6978594926320819473497237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4652396617547212982331491 6978594926320819473497237)
                ·
                  refine ⟨327121637171288412820183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6978594926320819473497237 327121637171288412820183)
                  ·
                    rfl

theorem cell22_2866802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 3, 1, 6].length) (baseStart_2866802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2866802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2866802 prefixEnd_2866802 := by exact prefixLift 2866802
  have htrace : WordTrace (prefixWord ++ tailWord_2866802) baseStart_2866802 baseEnd_2866802 := by
    simpa [prefixWord, tailWord_2866802, baseEnd_2866802] using wordTrace_append hprefix tailTrace_2866802
  have hstable : (prefixWord ++ tailWord_2866802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2866802).length < 2 ^ (prefixWord ++ tailWord_2866802).sum := by decide
  have hdescent : baseEnd_2866802 < baseStart_2866802 := by decide
  rcases family_descends (prefixWord ++ tailWord_2866802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2866834 : List Nat := [3, 2, 3, 1, 3, 1, 1, 2, 1, 5]
def baseStart_2866834 : Nat := 118140960795 + 2866834 * 2 ^ 59
def prefixEnd_2866834 : Nat := 4983230072969 + 3 ^ 40 * 2866834 * 2
def baseEnd_2866834 : Nat := 981375865767827821660451

theorem tailTrace_2866834 : CollatzResearch.WordTrace tailWord_2866834 prefixEnd_2866834 981375865767827821660451 := by
  unfold tailWord_2866834
  simp only [CollatzResearch.WordTrace]
  refine ⟨26140506523989377277991889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69708017397305006074645037 26140506523989377277991889)
  ·
    refine ⟨19605379892992032958493917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26140506523989377277991889 19605379892992032958493917)
    ·
      refine ⟨7352017459872012359435219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19605379892992032958493917 7352017459872012359435219)
      ·
        refine ⟨11028026189808018539152829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7352017459872012359435219 11028026189808018539152829)
        ·
          refine ⟨4135509821178006952182311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11028026189808018539152829 4135509821178006952182311)
          ·
            refine ⟨6203264731767010428273467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4135509821178006952182311 6203264731767010428273467)
            ·
              refine ⟨9304897097650515642410201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6203264731767010428273467 9304897097650515642410201)
              ·
                refine ⟨6978672823237886731807651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9304897097650515642410201 6978672823237886731807651)
                ·
                  refine ⟨10468009234856830097711477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6978672823237886731807651 10468009234856830097711477)
                  ·
                    refine ⟨981375865767827821660451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10468009234856830097711477 981375865767827821660451)
                    ·
                      rfl

theorem cell22_2866834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_2866834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2866834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2866834 prefixEnd_2866834 := by exact prefixLift 2866834
  have htrace : WordTrace (prefixWord ++ tailWord_2866834) baseStart_2866834 baseEnd_2866834 := by
    simpa [prefixWord, tailWord_2866834, baseEnd_2866834] using wordTrace_append hprefix tailTrace_2866834
  have hstable : (prefixWord ++ tailWord_2866834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2866834).length < 2 ^ (prefixWord ++ tailWord_2866834).sum := by decide
  have hdescent : baseEnd_2866834 < baseStart_2866834 := by decide
  rcases family_descends (prefixWord ++ tailWord_2866834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2866847 : List Nat := [1, 1, 2, 7, 1, 10]
def baseStart_2866847 : Nat := 118140960795 + 2866847 * 2 ^ 59
def prefixEnd_2866847 : Nat := 4983230072969 + 3 ^ 40 * 2866847 * 2
def baseEnd_2866847 : Nat := 12115806369549384210931

theorem tailTrace_2866847 : CollatzResearch.WordTrace tailWord_2866847 prefixEnd_2866847 12115806369549384210931 := by
  unfold tailWord_2866847
  simp only [CollatzResearch.WordTrace]
  refine ⟨104562500244910412332190795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69708333496606941554793863 104562500244910412332190795)
  ·
    refine ⟨156843750367365618498286193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104562500244910412332190795 156843750367365618498286193)
    ·
      refine ⟨117632812775524213873714645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156843750367365618498286193 117632812775524213873714645)
      ·
        refine ⟨2757019049426348762665187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 117632812775524213873714645 2757019049426348762665187)
        ·
          refine ⟨4135528574139523143997781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2757019049426348762665187 4135528574139523143997781)
          ·
            refine ⟨12115806369549384210931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4135528574139523143997781 12115806369549384210931)
            ·
              rfl

theorem cell22_2866847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 10].length) (baseStart_2866847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2866847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2866847 prefixEnd_2866847 := by exact prefixLift 2866847
  have htrace : WordTrace (prefixWord ++ tailWord_2866847) baseStart_2866847 baseEnd_2866847 := by
    simpa [prefixWord, tailWord_2866847, baseEnd_2866847] using wordTrace_append hprefix tailTrace_2866847
  have hstable : (prefixWord ++ tailWord_2866847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2866847).length < 2 ^ (prefixWord ++ tailWord_2866847).sum := by decide
  have hdescent : baseEnd_2866847 < baseStart_2866847 := by decide
  rcases family_descends (prefixWord ++ tailWord_2866847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2866902 : List Nat := [5, 2, 1, 3, 2, 1, 1, 2, 2, 3]
def baseStart_2866902 : Nat := 118140960795 + 2866902 * 2 ^ 59
def prefixEnd_2866902 : Nat := 4983230072969 + 3 ^ 40 * 2866902 * 2
def baseEnd_2866902 : Nat := 981399143557498310960243

theorem tailTrace_2866902 : CollatzResearch.WordTrace tailWord_2866902 prefixEnd_2866902 981399143557498310960243 := by
  unfold tailWord_2866902
  simp only [CollatzResearch.WordTrace]
  refine ⟨6535281641231947295340185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 69709670839807437816961973 6535281641231947295340185)
  ·
    refine ⟨4901461230923960471505139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6535281641231947295340185 4901461230923960471505139)
    ·
      refine ⟨7352191846385940707257709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4901461230923960471505139 7352191846385940707257709)
      ·
        refine ⟨2757071942394727765221641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7352191846385940707257709 2757071942394727765221641)
        ·
          refine ⟨2067803956796045823916231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2757071942394727765221641 2067803956796045823916231)
          ·
            refine ⟨3101705935194068735874347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2067803956796045823916231 3101705935194068735874347)
            ·
              refine ⟨4652558902791103103811521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3101705935194068735874347 4652558902791103103811521)
              ·
                refine ⟨3489419177093327327858641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4652558902791103103811521 3489419177093327327858641)
                ·
                  refine ⟨2617064382819995495893981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3489419177093327327858641 2617064382819995495893981)
                  ·
                    refine ⟨981399143557498310960243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2617064382819995495893981 981399143557498310960243)
                    ·
                      rfl

theorem cell22_2866902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 1, 2, 2, 3].length) (baseStart_2866902 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2866902 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2866902 prefixEnd_2866902 := by exact prefixLift 2866902
  have htrace : WordTrace (prefixWord ++ tailWord_2866902) baseStart_2866902 baseEnd_2866902 := by
    simpa [prefixWord, tailWord_2866902, baseEnd_2866902] using wordTrace_append hprefix tailTrace_2866902
  have hstable : (prefixWord ++ tailWord_2866902).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2866902).length < 2 ^ (prefixWord ++ tailWord_2866902).sum := by decide
  have hdescent : baseEnd_2866902 < baseStart_2866902 := by decide
  rcases family_descends (prefixWord ++ tailWord_2866902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2866922 : List Nat := [3, 1, 3, 1, 1, 1, 2, 1, 5, 4]
def baseStart_2866922 : Nat := 118140960795 + 2866922 * 2 ^ 59
def prefixEnd_2866922 : Nat := 4983230072969 + 3 ^ 40 * 2866922 * 2
def baseEnd_2866922 : Nat := 981405989966224925460181

theorem tailTrace_2866922 : CollatzResearch.WordTrace tailWord_2866922 prefixEnd_2866922 981405989966224925460181 := by
  unfold tailWord_2866922
  simp only [CollatzResearch.WordTrace]
  refine ⟨26141308929909675035292755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69710157146425800094114013 26141308929909675035292755)
  ·
    refine ⟨39211963394864512552939133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26141308929909675035292755 39211963394864512552939133)
    ·
      refine ⟨14704486273074192207352175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39211963394864512552939133 14704486273074192207352175)
      ·
        refine ⟨22056729409611288311028263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14704486273074192207352175 22056729409611288311028263)
        ·
          refine ⟨33085094114416932466542395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22056729409611288311028263 33085094114416932466542395)
          ·
            refine ⟨49627641171625398699813593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33085094114416932466542395 49627641171625398699813593)
            ·
              refine ⟨37220730878719049024860195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49627641171625398699813593 37220730878719049024860195)
              ·
                refine ⟨55831096318078573537290293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37220730878719049024860195 55831096318078573537290293)
                ·
                  refine ⟨5234165279819866269120965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55831096318078573537290293 5234165279819866269120965)
                  ·
                    refine ⟨981405989966224925460181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5234165279819866269120965 981405989966224925460181)
                    ·
                      rfl

theorem cell22_2866922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 5, 4].length) (baseStart_2866922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2866922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2866922 prefixEnd_2866922 := by exact prefixLift 2866922
  have htrace : WordTrace (prefixWord ++ tailWord_2866922) baseStart_2866922 baseEnd_2866922 := by
    simpa [prefixWord, tailWord_2866922, baseEnd_2866922] using wordTrace_append hprefix tailTrace_2866922
  have hstable : (prefixWord ++ tailWord_2866922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2866922).length < 2 ^ (prefixWord ++ tailWord_2866922).sum := by decide
  have hdescent : baseEnd_2866922 < baseStart_2866922 := by decide
  rcases family_descends (prefixWord ++ tailWord_2866922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2866952 : List Nat := [2, 1, 3, 2, 2, 1, 2, 1, 3, 5]
def baseStart_2866952 : Nat := 118140960795 + 2866952 * 2 ^ 59
def prefixEnd_2866952 : Nat := 4983230072969 + 3 ^ 40 * 2866952 * 2
def baseEnd_2866952 : Nat := 981416259579314847210089

theorem tailTrace_2866952 : CollatzResearch.WordTrace tailWord_2866952 prefixEnd_2866952 981416259579314847210089 := by
  unfold tailWord_2866952
  simp only [CollatzResearch.WordTrace]
  refine ⟨52283164954765007632381555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69710886606353343509842073 52283164954765007632381555)
  ·
    refine ⟨78424747432147511448572333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52283164954765007632381555 78424747432147511448572333)
    ·
      refine ⟨29409280287055316793214625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78424747432147511448572333 29409280287055316793214625)
      ·
        refine ⟨22056960215291487594910969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29409280287055316793214625 22056960215291487594910969)
        ·
          refine ⟨16542720161468615696183227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22056960215291487594910969 16542720161468615696183227)
          ·
            refine ⟨24814080242202923544274841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16542720161468615696183227 24814080242202923544274841)
            ·
              refine ⟨18610560181652192658206131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24814080242202923544274841 18610560181652192658206131)
              ·
                refine ⟨27915840272478288987309197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18610560181652192658206131 27915840272478288987309197)
                ·
                  refine ⟨10468440102179358370240949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27915840272478288987309197 10468440102179358370240949)
                  ·
                    refine ⟨981416259579314847210089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10468440102179358370240949 981416259579314847210089)
                    ·
                      rfl

theorem cell22_2866952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 1, 3, 5].length) (baseStart_2866952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2866952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2866952 prefixEnd_2866952 := by exact prefixLift 2866952
  have htrace : WordTrace (prefixWord ++ tailWord_2866952) baseStart_2866952 baseEnd_2866952 := by
    simpa [prefixWord, tailWord_2866952, baseEnd_2866952] using wordTrace_append hprefix tailTrace_2866952
  have hstable : (prefixWord ++ tailWord_2866952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2866952).length < 2 ^ (prefixWord ++ tailWord_2866952).sum := by decide
  have hdescent : baseEnd_2866952 < baseStart_2866952 := by decide
  rcases family_descends (prefixWord ++ tailWord_2866952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2866964 : List Nat := [2, 4, 4, 1, 1, 1, 3, 2, 1, 3]
def baseStart_2866964 : Nat := 118140960795 + 2866964 * 2 ^ 59
def prefixEnd_2866964 : Nat := 4983230072969 + 3 ^ 40 * 2866964 * 2
def baseEnd_2866964 : Nat := 981420367424550815910053

theorem tailTrace_2866964 : CollatzResearch.WordTrace tailWord_2866964 prefixEnd_2866964 981420367424550815910053 := by
  unfold tailWord_2866964
  simp only [CollatzResearch.WordTrace]
  refine ⟨52283383792743270657099973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69711178390324360876133297 52283383792743270657099973)
  ·
    refine ⟨9803134461139363248206245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52283383792743270657099973 9803134461139363248206245)
    ·
      refine ⟨1838087711463630609038671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9803134461139363248206245 1838087711463630609038671)
      ·
        refine ⟨2757131567195445913558007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1838087711463630609038671 2757131567195445913558007)
        ·
          refine ⟨4135697350793168870337011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2757131567195445913558007 4135697350793168870337011)
          ·
            refine ⟨6203546026189753305505517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4135697350793168870337011 6203546026189753305505517)
            ·
              refine ⟨2326329759821157489564569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6203546026189753305505517 2326329759821157489564569)
              ·
                refine ⟨1744747319865868117173427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2326329759821157489564569 1744747319865868117173427)
                ·
                  refine ⟨2617120979798802175760141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1744747319865868117173427 2617120979798802175760141)
                  ·
                    refine ⟨981420367424550815910053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2617120979798802175760141 981420367424550815910053)
                    ·
                      rfl

theorem cell22_2866964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_2866964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2866964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2866964 prefixEnd_2866964 := by exact prefixLift 2866964
  have htrace : WordTrace (prefixWord ++ tailWord_2866964) baseStart_2866964 baseEnd_2866964 := by
    simpa [prefixWord, tailWord_2866964, baseEnd_2866964] using wordTrace_append hprefix tailTrace_2866964
  have hstable : (prefixWord ++ tailWord_2866964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2866964).length < 2 ^ (prefixWord ++ tailWord_2866964).sum := by decide
  have hdescent : baseEnd_2866964 < baseStart_2866964 := by decide
  rcases family_descends (prefixWord ++ tailWord_2866964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2866990 : List Nat := [4, 1, 3, 2, 3, 1, 1, 2, 1, 4]
def baseStart_2866990 : Nat := 118140960795 + 2866990 * 2 ^ 59
def prefixEnd_2866990 : Nat := 4983230072969 + 3 ^ 40 * 2866990 * 2
def baseEnd_2866990 : Nat := 981429267755895414759973

theorem tailTrace_2866990 : CollatzResearch.WordTrace tailWord_2866990 prefixEnd_2866990 981429267755895414759973 := by
  unfold tailWord_2866990
  simp only [CollatzResearch.WordTrace]
  refine ⟨13070964485424043469330803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69711810588928231836430949 13070964485424043469330803)
  ·
    refine ⟨19606446728136065203996205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13070964485424043469330803 19606446728136065203996205)
    ·
      refine ⟨7352417523051024451498577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19606446728136065203996205 7352417523051024451498577)
      ·
        refine ⟨5514313142288268338623933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7352417523051024451498577 5514313142288268338623933)
        ·
          refine ⟨2067867428358100626983975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5514313142288268338623933 2067867428358100626983975)
          ·
            refine ⟨3101801142537150940475963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2067867428358100626983975 3101801142537150940475963)
            ·
              refine ⟨4652701713805726410713945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3101801142537150940475963 4652701713805726410713945)
              ·
                refine ⟨3489526285354294808035459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4652701713805726410713945 3489526285354294808035459)
                ·
                  refine ⟨5234289428031442212053189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3489526285354294808035459 5234289428031442212053189)
                  ·
                    refine ⟨981429267755895414759973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5234289428031442212053189 981429267755895414759973)
                    ·
                      rfl

theorem cell22_2866990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 1, 2, 1, 4].length) (baseStart_2866990 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2866990 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2866990 prefixEnd_2866990 := by exact prefixLift 2866990
  have htrace : WordTrace (prefixWord ++ tailWord_2866990) baseStart_2866990 baseEnd_2866990 := by
    simpa [prefixWord, tailWord_2866990, baseEnd_2866990] using wordTrace_append hprefix tailTrace_2866990
  have hstable : (prefixWord ++ tailWord_2866990).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2866990).length < 2 ^ (prefixWord ++ tailWord_2866990).sum := by decide
  have hdescent : baseEnd_2866990 < baseStart_2866990 := by decide
  rcases family_descends (prefixWord ++ tailWord_2866990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2867072 : List Nat := [2, 1, 1, 2, 1, 2, 3, 2, 8]
def baseStart_2867072 : Nat := 118140960795 + 2867072 * 2 ^ 59
def prefixEnd_2867072 : Nat := 4983230072969 + 3 ^ 40 * 2867072 * 2
def baseEnd_2867072 : Nat := 327152446010558178069907

theorem tailTrace_2867072 : CollatzResearch.WordTrace tailWord_2867072 prefixEnd_2867072 327152446010558178069907 := by
  unfold tailWord_2867072
  simp only [CollatzResearch.WordTrace]
  refine ⟨52285353334547637879565735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69713804446063517172754313 52285353334547637879565735)
  ·
    refine ⟨78428030001821456819348603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52285353334547637879565735 78428030001821456819348603)
    ·
      refine ⟨117642045002732185229022905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78428030001821456819348603 117642045002732185229022905)
      ·
        refine ⟨88231533752049138921767179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117642045002732185229022905 88231533752049138921767179)
        ·
          refine ⟨132347300628073708382650769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88231533752049138921767179 132347300628073708382650769)
          ·
            refine ⟨99260475471055281286988077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132347300628073708382650769 99260475471055281286988077)
            ·
              refine ⟨37222678301645730482620529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99260475471055281286988077 37222678301645730482620529)
              ·
                refine ⟨27917008726234297861965397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37222678301645730482620529 27917008726234297861965397)
                ·
                  refine ⟨327152446010558178069907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27917008726234297861965397 327152446010558178069907)
                  ·
                    rfl

theorem cell22_2867072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 2, 8].length) (baseStart_2867072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2867072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2867072 prefixEnd_2867072 := by exact prefixLift 2867072
  have htrace : WordTrace (prefixWord ++ tailWord_2867072) baseStart_2867072 baseEnd_2867072 := by
    simpa [prefixWord, tailWord_2867072, baseEnd_2867072] using wordTrace_append hprefix tailTrace_2867072
  have hstable : (prefixWord ++ tailWord_2867072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2867072).length < 2 ^ (prefixWord ++ tailWord_2867072).sum := by decide
  have hdescent : baseEnd_2867072 < baseStart_2867072 := by decide
  rcases family_descends (prefixWord ++ tailWord_2867072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2867119 : List Nat := [1, 1, 2, 1, 2, 2, 4, 3, 2, 4]
def baseStart_2867119 : Nat := 118140960795 + 2867119 * 2 ^ 59
def prefixEnd_2867119 : Nat := 4983230072969 + 3 ^ 40 * 2867119 * 2
def baseEnd_2867119 : Nat := 981473427092182078284577

theorem tailTrace_2867119 : CollatzResearch.WordTrace tailWord_2867119 prefixEnd_2867119 981473427092182078284577 := by
  unfold tailWord_2867119
  simp only [CollatzResearch.WordTrace]
  refine ⟨104572420899925002786092411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69714947266616668524061607 104572420899925002786092411)
  ·
    refine ⟨156858631349887504179138617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104572420899925002786092411 156858631349887504179138617)
    ·
      refine ⟨117643973512415628134353963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156858631349887504179138617 117643973512415628134353963)
      ·
        refine ⟨176465960268623442201530945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117643973512415628134353963 176465960268623442201530945)
        ·
          refine ⟨132349470201467581651148209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176465960268623442201530945 132349470201467581651148209)
          ·
            refine ⟨99262102651100686238361157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132349470201467581651148209 99262102651100686238361157)
            ·
              refine ⟨18611644247081378669692717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 99262102651100686238361157 18611644247081378669692717)
              ·
                refine ⟨6979366592655517001134769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18611644247081378669692717 6979366592655517001134769)
                ·
                  refine ⟨5234524944491637750851077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6979366592655517001134769 5234524944491637750851077)
                  ·
                    refine ⟨981473427092182078284577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5234524944491637750851077 981473427092182078284577)
                    ·
                      rfl

theorem cell22_2867119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 3, 2, 4].length) (baseStart_2867119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2867119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2867119 prefixEnd_2867119 := by exact prefixLift 2867119
  have htrace : WordTrace (prefixWord ++ tailWord_2867119) baseStart_2867119 baseEnd_2867119 := by
    simpa [prefixWord, tailWord_2867119, baseEnd_2867119] using wordTrace_append hprefix tailTrace_2867119
  have hstable : (prefixWord ++ tailWord_2867119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2867119).length < 2 ^ (prefixWord ++ tailWord_2867119).sum := by decide
  have hdescent : baseEnd_2867119 < baseStart_2867119 := by decide
  rcases family_descends (prefixWord ++ tailWord_2867119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2867121 : List Nat := [1, 2, 2, 4, 2, 1, 1, 2, 4, 3]
def baseStart_2867121 : Nat := 118140960795 + 2867121 * 2 ^ 59
def prefixEnd_2867121 : Nat := 4983230072969 + 3 ^ 40 * 2867121 * 2
def baseEnd_2867121 : Nat := 981474111733054739734571

theorem tailTrace_2867121 : CollatzResearch.WordTrace tailWord_2867121 prefixEnd_2867121 981474111733054739734571 := by
  unfold tailWord_2867121
  simp only [CollatzResearch.WordTrace]
  refine ⟨104572493845917757127665217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69714995897278504751776811 104572493845917757127665217)
  ·
    refine ⟨78429370384438317845748913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104572493845917757127665217 78429370384438317845748913)
    ·
      refine ⟨58822027788328738384311685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78429370384438317845748913 58822027788328738384311685)
      ·
        refine ⟨11029130210311638447058441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58822027788328738384311685 11029130210311638447058441)
        ·
          refine ⟨8271847657733728835293831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11029130210311638447058441 8271847657733728835293831)
          ·
            refine ⟨12407771486600593252940747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8271847657733728835293831 12407771486600593252940747)
            ·
              refine ⟨18611657229900889879411121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12407771486600593252940747 18611657229900889879411121)
              ·
                refine ⟨13958742922425667409558341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18611657229900889879411121 13958742922425667409558341)
                ·
                  refine ⟨2617264297954812639292189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13958742922425667409558341 2617264297954812639292189)
                  ·
                    refine ⟨981474111733054739734571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2617264297954812639292189 981474111733054739734571)
                    ·
                      rfl

theorem cell22_2867121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 2, 4, 3].length) (baseStart_2867121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2867121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2867121 prefixEnd_2867121 := by exact prefixLift 2867121
  have htrace : WordTrace (prefixWord ++ tailWord_2867121) baseStart_2867121 baseEnd_2867121 := by
    simpa [prefixWord, tailWord_2867121, baseEnd_2867121] using wordTrace_append hprefix tailTrace_2867121
  have hstable : (prefixWord ++ tailWord_2867121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2867121).length < 2 ^ (prefixWord ++ tailWord_2867121).sum := by decide
  have hdescent : baseEnd_2867121 < baseStart_2867121 := by decide
  rcases family_descends (prefixWord ++ tailWord_2867121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2867134 : List Nat := [4, 2, 1, 1, 1, 3, 10]
def baseStart_2867134 : Nat := 118140960795 + 2867134 * 2 ^ 59
def prefixEnd_2867134 : Nat := 4983230072969 + 3 ^ 40 * 2867134 * 2
def baseEnd_2867134 : Nat := 36351057848101001450353

theorem tailTrace_2867134 : CollatzResearch.WordTrace tailWord_2867134 prefixEnd_2867134 36351057848101001450353 := by
  unfold tailWord_2867134
  simp only [CollatzResearch.WordTrace]
  refine ⟨13071620999358832543486057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69715311996580440231925637 13071620999358832543486057)
  ·
    refine ⟨9803715749519124407614543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13071620999358832543486057 9803715749519124407614543)
    ·
      refine ⟨14705573624278686611421815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9803715749519124407614543 14705573624278686611421815)
      ·
        refine ⟨22058360436418029917132723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14705573624278686611421815 22058360436418029917132723)
        ·
          refine ⟨33087540654627044875699085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22058360436418029917132723 33087540654627044875699085)
          ·
            refine ⟨12407827745485141828387157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33087540654627044875699085 12407827745485141828387157)
            ·
              refine ⟨36351057848101001450353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 12407827745485141828387157 36351057848101001450353)
              ·
                rfl

theorem cell22_2867134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 10].length) (baseStart_2867134 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2867134 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2867134 prefixEnd_2867134 := by exact prefixLift 2867134
  have htrace : WordTrace (prefixWord ++ tailWord_2867134) baseStart_2867134 baseEnd_2867134 := by
    simpa [prefixWord, tailWord_2867134, baseEnd_2867134] using wordTrace_append hprefix tailTrace_2867134
  have hstable : (prefixWord ++ tailWord_2867134).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2867134).length < 2 ^ (prefixWord ++ tailWord_2867134).sum := by decide
  have hdescent : baseEnd_2867134 < baseStart_2867134 := by decide
  rcases family_descends (prefixWord ++ tailWord_2867134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2867170 : List Nat := [3, 3, 3, 1, 2, 1, 2, 1, 2, 4]
def baseStart_2867170 : Nat := 118140960795 + 2867170 * 2 ^ 59
def prefixEnd_2867170 : Nat := 4983230072969 + 3 ^ 40 * 2867170 * 2
def baseEnd_2867170 : Nat := 981490885434434945259421

theorem tailTrace_2867170 : CollatzResearch.WordTrace tailWord_2867170 prefixEnd_2867170 981490885434434945259421 := by
  unfold tailWord_2867170
  simp only [CollatzResearch.WordTrace]
  refine ⟨26143570255685059624049741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69716187348493492330799309 26143570255685059624049741)
  ·
    refine ⟨9803838845881897359018653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26143570255685059624049741 9803838845881897359018653)
    ·
      refine ⟨3676439567205711509631995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9803838845881897359018653 3676439567205711509631995)
      ·
        refine ⟨5514659350808567264447993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3676439567205711509631995 5514659350808567264447993)
        ·
          refine ⟨4135994513106425448335995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5514659350808567264447993 4135994513106425448335995)
          ·
            refine ⟨6203991769659638172503993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4135994513106425448335995 6203991769659638172503993)
            ·
              refine ⟨4652993827244728629377995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6203991769659638172503993 4652993827244728629377995)
              ·
                refine ⟨6979490740867092944066993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4652993827244728629377995 6979490740867092944066993)
                ·
                  refine ⟨5234618055650319708050245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6979490740867092944066993 5234618055650319708050245)
                  ·
                    refine ⟨981490885434434945259421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5234618055650319708050245 981490885434434945259421)
                    ·
                      rfl

theorem cell22_2867170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_2867170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2867170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2867170 prefixEnd_2867170 := by exact prefixLift 2867170
  have htrace : WordTrace (prefixWord ++ tailWord_2867170) baseStart_2867170 baseEnd_2867170 := by
    simpa [prefixWord, tailWord_2867170, baseEnd_2867170] using wordTrace_append hprefix tailTrace_2867170
  have hstable : (prefixWord ++ tailWord_2867170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2867170).length < 2 ^ (prefixWord ++ tailWord_2867170).sum := by decide
  have hdescent : baseEnd_2867170 < baseStart_2867170 := by decide
  rcases family_descends (prefixWord ++ tailWord_2867170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2867183 : List Nat := [1, 1, 2, 1, 4, 2, 2, 5, 1, 3]
def baseStart_2867183 : Nat := 118140960795 + 2867183 * 2 ^ 59
def prefixEnd_2867183 : Nat := 4983230072969 + 3 ^ 40 * 2867183 * 2
def baseEnd_2867183 : Nat := 981495335600107244684381

theorem tailTrace_2867183 : CollatzResearch.WordTrace tailWord_2867183 prefixEnd_2867183 981495335600107244684381 := by
  unfold tailWord_2867183
  simp only [CollatzResearch.WordTrace]
  refine ⟨104574755171693141716422203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69716503447795427810948135 104574755171693141716422203)
  ·
    refine ⟨156862132757539712574633305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104574755171693141716422203 156862132757539712574633305)
    ·
      refine ⟨117646599568154784430974979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156862132757539712574633305 117646599568154784430974979)
      ·
        refine ⟨176469899352232176646462469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117646599568154784430974979 176469899352232176646462469)
        ·
          refine ⟨33088106128543533121211713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 176469899352232176646462469 33088106128543533121211713)
          ·
            refine ⟨24816079596407649840908785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33088106128543533121211713 24816079596407649840908785)
            ·
              refine ⟨18612059697305737380681589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24816079596407649840908785 18612059697305737380681589)
              ·
                refine ⟨1744880596622412879438899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18612059697305737380681589 1744880596622412879438899)
                ·
                  refine ⟨2617320894933619319158349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1744880596622412879438899 2617320894933619319158349)
                  ·
                    refine ⟨981495335600107244684381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2617320894933619319158349 981495335600107244684381)
                    ·
                      rfl

theorem cell22_2867183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 5, 1, 3].length) (baseStart_2867183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2867183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2867183 prefixEnd_2867183 := by exact prefixLift 2867183
  have htrace : WordTrace (prefixWord ++ tailWord_2867183) baseStart_2867183 baseEnd_2867183 := by
    simpa [prefixWord, tailWord_2867183, baseEnd_2867183] using wordTrace_append hprefix tailTrace_2867183
  have hstable : (prefixWord ++ tailWord_2867183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2867183).length < 2 ^ (prefixWord ++ tailWord_2867183).sum := by decide
  have hdescent : baseEnd_2867183 < baseStart_2867183 := by decide
  rcases family_descends (prefixWord ++ tailWord_2867183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2867196 : List Nat := [2, 2, 2, 1, 2, 2, 4, 2, 5]
def baseStart_2867196 : Nat := 118140960795 + 2867196 * 2 ^ 59
def prefixEnd_2867196 : Nat := 4983230072969 + 3 ^ 40 * 2867196 * 2
def baseEnd_2867196 : Nat := 327166595255259848036447

theorem tailTrace_2867196 : CollatzResearch.WordTrace tailWord_2867196 prefixEnd_2867196 327166595255259848036447 := by
  unfold tailWord_2867196
  simp only [CollatzResearch.WordTrace]
  refine ⟨52287614660323022468322721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69716819547097363291096961 52287614660323022468322721)
  ·
    refine ⟨39215710995242266851242041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52287614660323022468322721 39215710995242266851242041)
    ·
      refine ⟨29411783246431700138431531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39215710995242266851242041 29411783246431700138431531)
      ·
        refine ⟨44117674869647550207647297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29411783246431700138431531 44117674869647550207647297)
        ·
          refine ⟨33088256152235662655735473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44117674869647550207647297 33088256152235662655735473)
          ·
            refine ⟨24816192114176746991801605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33088256152235662655735473 24816192114176746991801605)
            ·
              refine ⟨4653036021408140060962801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24816192114176746991801605 4653036021408140060962801)
              ·
                refine ⟨3489777016056105045722101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4653036021408140060962801 3489777016056105045722101)
                ·
                  refine ⟨327166595255259848036447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3489777016056105045722101 327166595255259848036447)
                  ·
                    rfl

theorem cell22_2867196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 4, 2, 5].length) (baseStart_2867196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2867196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2867196 prefixEnd_2867196 := by exact prefixLift 2867196
  have htrace : WordTrace (prefixWord ++ tailWord_2867196) baseStart_2867196 baseEnd_2867196 := by
    simpa [prefixWord, tailWord_2867196, baseEnd_2867196] using wordTrace_append hprefix tailTrace_2867196
  have hstable : (prefixWord ++ tailWord_2867196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2867196).length < 2 ^ (prefixWord ++ tailWord_2867196).sum := by decide
  have hdescent : baseEnd_2867196 < baseStart_2867196 := by decide
  rcases family_descends (prefixWord ++ tailWord_2867196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2867226 : List Nat := [3, 1, 1, 3, 1, 3, 2, 1, 3, 4]
def baseStart_2867226 : Nat := 118140960795 + 2867226 * 2 ^ 59
def prefixEnd_2867226 : Nat := 4983230072969 + 3 ^ 40 * 2867226 * 2
def baseEnd_2867226 : Nat := 981510055378869465859249

theorem tailTrace_2867226 : CollatzResearch.WordTrace tailWord_2867226 prefixEnd_2867226 981510055378869465859249 := by
  unfold tailWord_2867226
  simp only [CollatzResearch.WordTrace]
  refine ⟨26144080877634340015059383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69717549007024906706825021 26144080877634340015059383)
  ·
    refine ⟨39216121316451510022589075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26144080877634340015059383 39216121316451510022589075)
    ·
      refine ⟨58824181974677265033883613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39216121316451510022589075 58824181974677265033883613)
      ·
        refine ⟨22059068240503974387706355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58824181974677265033883613 22059068240503974387706355)
        ·
          refine ⟨33088602360755961581559533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22059068240503974387706355 33088602360755961581559533)
          ·
            refine ⟨12408225885283485593084825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33088602360755961581559533 12408225885283485593084825)
            ·
              refine ⟨9306169413962614194813619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12408225885283485593084825 9306169413962614194813619)
              ·
                refine ⟨13959254120943921292220429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9306169413962614194813619 13959254120943921292220429)
                ·
                  refine ⟨5234720295353970484582661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13959254120943921292220429 5234720295353970484582661)
                  ·
                    refine ⟨981510055378869465859249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5234720295353970484582661 981510055378869465859249)
                    ·
                      rfl

theorem cell22_2867226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 1, 3, 4].length) (baseStart_2867226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2867226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2867226 prefixEnd_2867226 := by exact prefixLift 2867226
  have htrace : WordTrace (prefixWord ++ tailWord_2867226) baseStart_2867226 baseEnd_2867226 := by
    simpa [prefixWord, tailWord_2867226, baseEnd_2867226] using wordTrace_append hprefix tailTrace_2867226
  have hstable : (prefixWord ++ tailWord_2867226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2867226).length < 2 ^ (prefixWord ++ tailWord_2867226).sum := by decide
  have hdescent : baseEnd_2867226 < baseStart_2867226 := by decide
  rcases family_descends (prefixWord ++ tailWord_2867226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2867269 : List Nat := [1, 3, 1, 1, 1, 3, 1, 11]
def baseStart_2867269 : Nat := 118140960795 + 2867269 * 2 ^ 59
def prefixEnd_2867269 : Nat := 4983230072969 + 3 ^ 40 * 2867269 * 2
def baseEnd_2867269 : Nat := 109058308350847965226013

theorem tailTrace_2867269 : CollatzResearch.WordTrace tailWord_2867269 prefixEnd_2867269 109058308350847965226013 := by
  unfold tailWord_2867269
  simp only [CollatzResearch.WordTrace]
  refine ⟨104577891849381578404052861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69718594566254385602701907 104577891849381578404052861)
  ·
    refine ⟨39216709443518091901519823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104577891849381578404052861 39216709443518091901519823)
    ·
      refine ⟨58825064165277137852279735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39216709443518091901519823 58825064165277137852279735)
      ·
        refine ⟨88237596247915706778419603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58825064165277137852279735 88237596247915706778419603)
        ·
          refine ⟨132356394371873560167629405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88237596247915706778419603 132356394371873560167629405)
          ·
            refine ⟨49633647889452585062861027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 132356394371873560167629405 49633647889452585062861027)
            ·
              refine ⟨74450471834178877594291541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49633647889452585062861027 74450471834178877594291541)
              ·
                refine ⟨109058308350847965226013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 74450471834178877594291541 109058308350847965226013)
                ·
                  rfl

theorem cell22_2867269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 11].length) (baseStart_2867269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2867269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2867269 prefixEnd_2867269 := by exact prefixLift 2867269
  have htrace : WordTrace (prefixWord ++ tailWord_2867269) baseStart_2867269 baseEnd_2867269 := by
    simpa [prefixWord, tailWord_2867269, baseEnd_2867269] using wordTrace_append hprefix tailTrace_2867269
  have hstable : (prefixWord ++ tailWord_2867269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2867269).length < 2 ^ (prefixWord ++ tailWord_2867269).sum := by decide
  have hdescent : baseEnd_2867269 < baseStart_2867269 := by decide
  rcases family_descends (prefixWord ++ tailWord_2867269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2867410 : List Nat := [3, 2, 2, 2, 1, 2, 1, 5, 4]
def baseStart_2867410 : Nat := 118140960795 + 2867410 * 2 ^ 59
def prefixEnd_2867410 : Nat := 4983230072969 + 3 ^ 40 * 2867410 * 2
def baseEnd_2867410 : Nat := 327191014113051439752895

theorem tailTrace_2867410 : CollatzResearch.WordTrace tailWord_2867410 prefixEnd_2867410 327191014113051439752895 := by
  unfold tailWord_2867410
  simp only [CollatzResearch.WordTrace]
  refine ⟨26145758635467689871233921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69722023027913839656623789 26145758635467689871233921)
  ·
    refine ⟨19609318976600767403425441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26145758635467689871233921 19609318976600767403425441)
    ·
      refine ⟨14706989232450575552569081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19609318976600767403425441 14706989232450575552569081)
      ·
        refine ⟨11030241924337931664426811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14706989232450575552569081 11030241924337931664426811)
        ·
          refine ⟨16545362886506897496640217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11030241924337931664426811 16545362886506897496640217)
          ·
            refine ⟨12409022164880173122480163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16545362886506897496640217 12409022164880173122480163)
            ·
              refine ⟨18613533247320259683720245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12409022164880173122480163 18613533247320259683720245)
              ·
                refine ⟨1745018741936274345348773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18613533247320259683720245 1745018741936274345348773)
                ·
                  refine ⟨327191014113051439752895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1745018741936274345348773 327191014113051439752895)
                  ·
                    rfl

theorem cell22_2867410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 5, 4].length) (baseStart_2867410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2867410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2867410 prefixEnd_2867410 := by exact prefixLift 2867410
  have htrace : WordTrace (prefixWord ++ tailWord_2867410) baseStart_2867410 baseEnd_2867410 := by
    simpa [prefixWord, tailWord_2867410, baseEnd_2867410] using wordTrace_append hprefix tailTrace_2867410
  have hstable : (prefixWord ++ tailWord_2867410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2867410).length < 2 ^ (prefixWord ++ tailWord_2867410).sum := by decide
  have hdescent : baseEnd_2867410 < baseStart_2867410 := by decide
  rcases family_descends (prefixWord ++ tailWord_2867410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2867487 : List Nat := [1, 1, 2, 4, 3, 3, 1, 1, 3, 3]
def baseStart_2867487 : Nat := 118140960795 + 2867487 * 2 ^ 59
def prefixEnd_2867487 : Nat := 4983230072969 + 3 ^ 40 * 2867487 * 2
def baseEnd_2867487 : Nat := 981599401012751785083449

theorem tailTrace_2867487 : CollatzResearch.WordTrace tailWord_2867487 prefixEnd_2867487 981599401012751785083449 := by
  unfold tailWord_2867487
  simp only [CollatzResearch.WordTrace]
  refine ⟨104585842962591801635488715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69723895308394534423659143 104585842962591801635488715)
  ·
    refine ⟨156878764443887702453233073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104585842962591801635488715 156878764443887702453233073)
    ·
      refine ⟨117659073332915776839924805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156878764443887702453233073 117659073332915776839924805)
      ·
        refine ⟨22061076249921708157485901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 117659073332915776839924805 22061076249921708157485901)
        ·
          refine ⟨8272903593720640559057213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22061076249921708157485901 8272903593720640559057213)
          ·
            refine ⟨3102338847645240209646455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8272903593720640559057213 3102338847645240209646455)
            ·
              refine ⟨4653508271467860314469683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3102338847645240209646455 4653508271467860314469683)
              ·
                refine ⟨6980262407201790471704525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4653508271467860314469683 6980262407201790471704525)
                ·
                  refine ⟨2617598402700671426889197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6980262407201790471704525 2617598402700671426889197)
                  ·
                    refine ⟨981599401012751785083449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2617598402700671426889197 981599401012751785083449)
                    ·
                      rfl

theorem cell22_2867487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 1, 1, 3, 3].length) (baseStart_2867487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2867487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2867487 prefixEnd_2867487 := by exact prefixLift 2867487
  have htrace : WordTrace (prefixWord ++ tailWord_2867487) baseStart_2867487 baseEnd_2867487 := by
    simpa [prefixWord, tailWord_2867487, baseEnd_2867487] using wordTrace_append hprefix tailTrace_2867487
  have hstable : (prefixWord ++ tailWord_2867487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2867487).length < 2 ^ (prefixWord ++ tailWord_2867487).sum := by decide
  have hdescent : baseEnd_2867487 < baseStart_2867487 := by decide
  rcases family_descends (prefixWord ++ tailWord_2867487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2867500 : List Nat := [2, 2, 1, 1, 1, 3, 6, 1, 5]
def baseStart_2867500 : Nat := 118140960795 + 2867500 * 2 ^ 59
def prefixEnd_2867500 : Nat := 4983230072969 + 3 ^ 40 * 2867500 * 2
def baseEnd_2867500 : Nat := 327201283726141361502803

theorem tailTrace_2867500 : CollatzResearch.WordTrace tailWord_2867500 prefixEnd_2867500 327201283726141361502803 := by
  unfold tailWord_2867500
  simp only [CollatzResearch.WordTrace]
  refine ⟨52293158555772352427855977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69724211407696469903807969 52293158555772352427855977)
  ·
    refine ⟨39219868916829264320891983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52293158555772352427855977 39219868916829264320891983)
    ·
      refine ⟨58829803375243896481337975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39219868916829264320891983 58829803375243896481337975)
      ·
        refine ⟨88244705062865844722006963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58829803375243896481337975 88244705062865844722006963)
        ·
          refine ⟨132367057594298767083010445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88244705062865844722006963 132367057594298767083010445)
          ·
            refine ⟨49637646597862037656128917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 132367057594298767083010445 49637646597862037656128917)
            ·
              refine ⟨2326764684274783015131043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 49637646597862037656128917 2326764684274783015131043)
              ·
                refine ⟨3490147026412174522696565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2326764684274783015131043 3490147026412174522696565)
                ·
                  refine ⟨327201283726141361502803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3490147026412174522696565 327201283726141361502803)
                  ·
                    rfl

theorem cell22_2867500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 5].length) (baseStart_2867500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2867500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2867500 prefixEnd_2867500 := by exact prefixLift 2867500
  have htrace : WordTrace (prefixWord ++ tailWord_2867500) baseStart_2867500 baseEnd_2867500 := by
    simpa [prefixWord, tailWord_2867500, baseEnd_2867500] using wordTrace_append hprefix tailTrace_2867500
  have hstable : (prefixWord ++ tailWord_2867500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2867500).length < 2 ^ (prefixWord ++ tailWord_2867500).sum := by decide
  have hdescent : baseEnd_2867500 < baseStart_2867500 := by decide
  rcases family_descends (prefixWord ++ tailWord_2867500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2867543 : List Nat := [1, 1, 3, 2, 3, 1, 1, 2, 3, 5]
def baseStart_2867543 : Nat := 118140960795 + 2867543 * 2 ^ 59
def prefixEnd_2867543 : Nat := 4983230072969 + 3 ^ 40 * 2867543 * 2
def baseEnd_2867543 : Nat := 981618570957186305683277

theorem tailTrace_2867543 : CollatzResearch.WordTrace tailWord_2867543 prefixEnd_2867543 981618570957186305683277 := by
  unfold tailWord_2867543
  simp only [CollatzResearch.WordTrace]
  refine ⟨104587885450388923199527283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69725256966925948799684855 104587885450388923199527283)
  ·
    refine ⟨156881828175583384799290925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104587885450388923199527283 156881828175583384799290925)
    ·
      refine ⟨58830685565843769299734097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156881828175583384799290925 58830685565843769299734097)
      ·
        refine ⟨44123014174382826974800573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58830685565843769299734097 44123014174382826974800573)
        ·
          refine ⟨16546130315393560115550215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44123014174382826974800573 16546130315393560115550215)
          ·
            refine ⟨24819195473090340173325323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16546130315393560115550215 24819195473090340173325323)
            ·
              refine ⟨37228793209635510259987985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24819195473090340173325323 37228793209635510259987985)
              ·
                refine ⟨27921594907226632694990989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37228793209635510259987985 27921594907226632694990989)
                ·
                  refine ⟨10470598090209987260621621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27921594907226632694990989 10470598090209987260621621)
                  ·
                    refine ⟨981618570957186305683277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10470598090209987260621621 981618570957186305683277)
                    ·
                      rfl

theorem cell22_2867543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 2, 3, 5].length) (baseStart_2867543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2867543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2867543 prefixEnd_2867543 := by exact prefixLift 2867543
  have htrace : WordTrace (prefixWord ++ tailWord_2867543) baseStart_2867543 baseEnd_2867543 := by
    simpa [prefixWord, tailWord_2867543, baseEnd_2867543] using wordTrace_append hprefix tailTrace_2867543
  have hstable : (prefixWord ++ tailWord_2867543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2867543).length < 2 ^ (prefixWord ++ tailWord_2867543).sum := by decide
  have hdescent : baseEnd_2867543 < baseStart_2867543 := by decide
  rcases family_descends (prefixWord ++ tailWord_2867543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2867560 : List Nat := [2, 1, 4, 2, 2, 1, 1, 3, 1, 5]
def baseStart_2867560 : Nat := 118140960795 + 2867560 * 2 ^ 59
def prefixEnd_2867560 : Nat := 4983230072969 + 3 ^ 40 * 2867560 * 2
def baseEnd_2867560 : Nat := 981624390404603928008225

theorem tailTrace_2867560 : CollatzResearch.WordTrace tailWord_2867560 prefixEnd_2867560 981624390404603928008225 := by
  unfold tailWord_2867560
  simp only [CollatzResearch.WordTrace]
  refine ⟨52294252745663667551448067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69725670327551556735264089 52294252745663667551448067)
  ·
    refine ⟨78441379118495501327172101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52294252745663667551448067 78441379118495501327172101)
    ·
      refine ⟨14707758584717906498844769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78441379118495501327172101 14707758584717906498844769)
      ·
        refine ⟨11030818938538429874133577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14707758584717906498844769 11030818938538429874133577)
        ·
          refine ⟨8273114203903822405600183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11030818938538429874133577 8273114203903822405600183)
          ·
            refine ⟨12409671305855733608400275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8273114203903822405600183 12409671305855733608400275)
            ·
              refine ⟨18614506958783600412600413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12409671305855733608400275 18614506958783600412600413)
              ·
                refine ⟨6980440109543850154725155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18614506958783600412600413 6980440109543850154725155)
                ·
                  refine ⟨10470660164315775232087733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6980440109543850154725155 10470660164315775232087733)
                  ·
                    refine ⟨981624390404603928008225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10470660164315775232087733 981624390404603928008225)
                    ·
                      rfl

theorem cell22_2867560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 3, 1, 5].length) (baseStart_2867560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2867560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2867560 prefixEnd_2867560 := by exact prefixLift 2867560
  have htrace : WordTrace (prefixWord ++ tailWord_2867560) baseStart_2867560 baseEnd_2867560 := by
    simpa [prefixWord, tailWord_2867560, baseEnd_2867560] using wordTrace_append hprefix tailTrace_2867560
  have hstable : (prefixWord ++ tailWord_2867560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2867560).length < 2 ^ (prefixWord ++ tailWord_2867560).sum := by decide
  have hdescent : baseEnd_2867560 < baseStart_2867560 := by decide
  rcases family_descends (prefixWord ++ tailWord_2867560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2867594 : List Nat := [3, 1, 2, 5, 1, 1, 1, 1, 4, 3]
def baseStart_2867594 : Nat := 118140960795 + 2867594 * 2 ^ 59
def prefixEnd_2867594 : Nat := 4983230072969 + 3 ^ 40 * 2867594 * 2
def baseEnd_2867594 : Nat := 981636029299439172658121

theorem tailTrace_2867594 : CollatzResearch.WordTrace tailWord_2867594 prefixEnd_2867594 981636029299439172658121 := by
  unfold tailWord_2867594
  simp only [CollatzResearch.WordTrace]
  refine ⟨26147436393301039727408459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69726497048802772606422557 26147436393301039727408459)
  ·
    refine ⟨39221154589951559591112689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26147436393301039727408459 39221154589951559591112689)
    ·
      refine ⟨29415865942463669693334517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39221154589951559591112689 29415865942463669693334517)
      ·
        refine ⟨2757737432105969033750111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29415865942463669693334517 2757737432105969033750111)
        ·
          refine ⟨4136606148158953550625167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2757737432105969033750111 4136606148158953550625167)
          ·
            refine ⟨6204909222238430325937751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4136606148158953550625167 6204909222238430325937751)
            ·
              refine ⟨9307363833357645488906627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6204909222238430325937751 9307363833357645488906627)
              ·
                refine ⟨13961045750036468233359941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9307363833357645488906627 13961045750036468233359941)
                ·
                  refine ⟨2617696078131837793754989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13961045750036468233359941 2617696078131837793754989)
                  ·
                    refine ⟨981636029299439172658121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2617696078131837793754989 981636029299439172658121)
                    ·
                      rfl

theorem cell22_2867594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 1, 4, 3].length) (baseStart_2867594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2867594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2867594 prefixEnd_2867594 := by exact prefixLift 2867594
  have htrace : WordTrace (prefixWord ++ tailWord_2867594) baseStart_2867594 baseEnd_2867594 := by
    simpa [prefixWord, tailWord_2867594, baseEnd_2867594] using wordTrace_append hprefix tailTrace_2867594
  have hstable : (prefixWord ++ tailWord_2867594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2867594).length < 2 ^ (prefixWord ++ tailWord_2867594).sum := by decide
  have hdescent : baseEnd_2867594 < baseStart_2867594 := by decide
  rcases family_descends (prefixWord ++ tailWord_2867594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2867624 : List Nat := [2, 1, 6, 1, 1, 3, 2, 6]
def baseStart_2867624 : Nat := 118140960795 + 2867624 * 2 ^ 59
def prefixEnd_2867624 : Nat := 4983230072969 + 3 ^ 40 * 2867624 * 2
def baseEnd_2867624 : Nat := 109071810990281010489781

theorem tailTrace_2867624 : CollatzResearch.WordTrace tailWord_2867624 prefixEnd_2867624 109071810990281010489781 := by
  unfold tailWord_2867624
  simp only [CollatzResearch.WordTrace]
  refine ⟨52295419881547737016612963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69727226508730316022150617 52295419881547737016612963)
  ·
    refine ⟨78443129822321605524919445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52295419881547737016612963 78443129822321605524919445)
    ·
      refine ⟨3677021710421325258980599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 78443129822321605524919445 3677021710421325258980599)
      ·
        refine ⟨5515532565631987888470899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3677021710421325258980599 5515532565631987888470899)
        ·
          refine ⟨8273298848447981832706349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5515532565631987888470899 8273298848447981832706349)
          ·
            refine ⟨3102487068167993187264881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8273298848447981832706349 3102487068167993187264881)
            ·
              refine ⟨2326865301125994890448661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3102487068167993187264881 2326865301125994890448661)
              ·
                refine ⟨109071810990281010489781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2326865301125994890448661 109071810990281010489781)
                ·
                  rfl

theorem cell22_2867624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 2, 6].length) (baseStart_2867624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2867624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2867624 prefixEnd_2867624 := by exact prefixLift 2867624
  have htrace : WordTrace (prefixWord ++ tailWord_2867624) baseStart_2867624 baseEnd_2867624 := by
    simpa [prefixWord, tailWord_2867624, baseEnd_2867624] using wordTrace_append hprefix tailTrace_2867624
  have hstable : (prefixWord ++ tailWord_2867624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2867624).length < 2 ^ (prefixWord ++ tailWord_2867624).sum := by decide
  have hdescent : baseEnd_2867624 < baseStart_2867624 := by decide
  rcases family_descends (prefixWord ++ tailWord_2867624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2867639 : List Nat := [1, 1, 3, 1, 3, 3, 3, 3, 1, 3]
def baseStart_2867639 : Nat := 118140960795 + 2867639 * 2 ^ 59
def prefixEnd_2867639 : Nat := 4983230072969 + 3 ^ 40 * 2867639 * 2
def baseEnd_2867639 : Nat := 981651433719074055282983

theorem tailTrace_2867639 : CollatzResearch.WordTrace tailWord_2867639 prefixEnd_2867639 981651433719074055282983 := by
  unfold tailWord_2867639
  simp only [CollatzResearch.WordTrace]
  refine ⟨104591386858041131595021971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69727591238694087730014647 104591386858041131595021971)
  ·
    refine ⟨156887080287061697392532957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104591386858041131595021971 156887080287061697392532957)
    ·
      refine ⟨58832655107648136522199859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156887080287061697392532957 58832655107648136522199859)
      ·
        refine ⟨88248982661472204783299789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58832655107648136522199859 88248982661472204783299789)
        ·
          refine ⟨33093368498052076793737421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88248982661472204783299789 33093368498052076793737421)
          ·
            refine ⟨12410013186769528797651533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33093368498052076793737421 12410013186769528797651533)
            ·
              refine ⟨4653754945038573299119325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12410013186769528797651533 4653754945038573299119325)
              ·
                refine ⟨1745158104389464987169747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4653754945038573299119325 1745158104389464987169747)
                ·
                  refine ⟨2617737156584197480754621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1745158104389464987169747 2617737156584197480754621)
                  ·
                    refine ⟨981651433719074055282983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2617737156584197480754621 981651433719074055282983)
                    ·
                      rfl

theorem cell22_2867639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 3, 3, 1, 3].length) (baseStart_2867639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2867639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2867639 prefixEnd_2867639 := by exact prefixLift 2867639
  have htrace : WordTrace (prefixWord ++ tailWord_2867639) baseStart_2867639 baseEnd_2867639 := by
    simpa [prefixWord, tailWord_2867639, baseEnd_2867639] using wordTrace_append hprefix tailTrace_2867639
  have hstable : (prefixWord ++ tailWord_2867639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2867639).length < 2 ^ (prefixWord ++ tailWord_2867639).sum := by decide
  have hdescent : baseEnd_2867639 < baseStart_2867639 := by decide
  rcases family_descends (prefixWord ++ tailWord_2867639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2867656 : List Nat := [2, 1, 3, 1, 3, 3, 3, 2, 1, 3]
def baseStart_2867656 : Nat := 118140960795 + 2867656 * 2 ^ 59
def prefixEnd_2867656 : Nat := 4983230072969 + 3 ^ 40 * 2867656 * 2
def baseEnd_2867656 : Nat := 981657253166491677607931

theorem tailTrace_2867656 : CollatzResearch.WordTrace tailWord_2867656 prefixEnd_2867656 981657253166491677607931 := by
  unfold tailWord_2867656
  simp only [CollatzResearch.WordTrace]
  refine ⟨52296003449489771749195411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69728004599319695665593881 52296003449489771749195411)
  ·
    refine ⟨78444005174234657623793117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52296003449489771749195411 78444005174234657623793117)
    ·
      refine ⟨29416501940337996608922419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78444005174234657623793117 29416501940337996608922419)
      ·
        refine ⟨44124752910506994913383629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29416501940337996608922419 44124752910506994913383629)
        ·
          refine ⟨16546782341440123092518861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44124752910506994913383629 16546782341440123092518861)
          ·
            refine ⟨6205043378040046159694573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16546782341440123092518861 6205043378040046159694573)
            ·
              refine ⟨2326891266765017309885465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6205043378040046159694573 2326891266765017309885465)
              ·
                refine ⟨1745168450073762982414099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2326891266765017309885465 1745168450073762982414099)
                ·
                  refine ⟨2617752675110644473621149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1745168450073762982414099 2617752675110644473621149)
                  ·
                    refine ⟨981657253166491677607931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2617752675110644473621149 981657253166491677607931)
                    ·
                      rfl

theorem cell22_2867656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 3, 2, 1, 3].length) (baseStart_2867656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2867656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2867656 prefixEnd_2867656 := by exact prefixLift 2867656
  have htrace : WordTrace (prefixWord ++ tailWord_2867656) baseStart_2867656 baseEnd_2867656 := by
    simpa [prefixWord, tailWord_2867656, baseEnd_2867656] using wordTrace_append hprefix tailTrace_2867656
  have hstable : (prefixWord ++ tailWord_2867656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2867656).length < 2 ^ (prefixWord ++ tailWord_2867656).sum := by decide
  have hdescent : baseEnd_2867656 < baseStart_2867656 := by decide
  rcases family_descends (prefixWord ++ tailWord_2867656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2867669 : List Nat := [1, 3, 2, 3, 1, 4, 2, 1, 5]
def baseStart_2867669 : Nat := 118140960795 + 2867669 * 2 ^ 59
def prefixEnd_2867669 : Nat := 4983230072969 + 3 ^ 40 * 2867669 * 2
def baseEnd_2867669 : Nat := 327220567777387992344297

theorem tailTrace_2867669 : CollatzResearch.WordTrace tailWord_2867669 prefixEnd_2867669 327220567777387992344297 := by
  unfold tailWord_2867669
  simp only [CollatzResearch.WordTrace]
  refine ⟨104592481047932446718614061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69728320698621631145742707 104592481047932446718614061)
  ·
    refine ⟨39222180392974667519480273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104592481047932446718614061 39222180392974667519480273)
    ·
      refine ⟨29416635294731000639610205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39222180392974667519480273 29416635294731000639610205)
      ·
        refine ⟨11031238235524125239853827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29416635294731000639610205 11031238235524125239853827)
        ·
          refine ⟨16546857353286187859780741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11031238235524125239853827 16546857353286187859780741)
          ·
            refine ⟨3102535753741160223708889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16546857353286187859780741 3102535753741160223708889)
            ·
              refine ⟨2326901815305870167781667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3102535753741160223708889 2326901815305870167781667)
              ·
                refine ⟨3490352722958805251672501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2326901815305870167781667 3490352722958805251672501)
                ·
                  refine ⟨327220567777387992344297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3490352722958805251672501 327220567777387992344297)
                  ·
                    rfl

theorem cell22_2867669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 2, 1, 5].length) (baseStart_2867669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2867669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2867669 prefixEnd_2867669 := by exact prefixLift 2867669
  have htrace : WordTrace (prefixWord ++ tailWord_2867669) baseStart_2867669 baseEnd_2867669 := by
    simpa [prefixWord, tailWord_2867669, baseEnd_2867669] using wordTrace_append hprefix tailTrace_2867669
  have hstable : (prefixWord ++ tailWord_2867669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2867669).length < 2 ^ (prefixWord ++ tailWord_2867669).sum := by decide
  have hdescent : baseEnd_2867669 < baseStart_2867669 := by decide
  rcases family_descends (prefixWord ++ tailWord_2867669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2867697 : List Nat := [1, 2, 2, 2, 3, 1, 2, 5, 4]
def baseStart_2867697 : Nat := 118140960795 + 2867697 * 2 ^ 59
def prefixEnd_2867697 : Nat := 4983230072969 + 3 ^ 40 * 2867697 * 2
def baseEnd_2867697 : Nat := 327223762768127079110935

theorem tailTrace_2867697 : CollatzResearch.WordTrace tailWord_2867697 prefixEnd_2867697 327223762768127079110935 := by
  unfold tailWord_2867697
  simp only [CollatzResearch.WordTrace]
  refine ⟨104593502291831007500633345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69729001527887338333755563 104593502291831007500633345)
  ·
    refine ⟨78445126718873255625475009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104593502291831007500633345 78445126718873255625475009)
    ·
      refine ⟨58833845039154941719106257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78445126718873255625475009 58833845039154941719106257)
      ·
        refine ⟨44125383779366206289329693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58833845039154941719106257 44125383779366206289329693)
        ·
          refine ⟨16547018917262327358498635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44125383779366206289329693 16547018917262327358498635)
          ·
            refine ⟨24820528375893491037747953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16547018917262327358498635 24820528375893491037747953)
            ·
              refine ⟨18615396281920118278310965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24820528375893491037747953 18615396281920118278310965)
              ·
                refine ⟨1745193401430011088591653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18615396281920118278310965 1745193401430011088591653)
                ·
                  refine ⟨327223762768127079110935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1745193401430011088591653 327223762768127079110935)
                  ·
                    rfl

theorem cell22_2867697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 5, 4].length) (baseStart_2867697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2867697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2867697 prefixEnd_2867697 := by exact prefixLift 2867697
  have htrace : WordTrace (prefixWord ++ tailWord_2867697) baseStart_2867697 baseEnd_2867697 := by
    simpa [prefixWord, tailWord_2867697, baseEnd_2867697] using wordTrace_append hprefix tailTrace_2867697
  have hstable : (prefixWord ++ tailWord_2867697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2867697).length < 2 ^ (prefixWord ++ tailWord_2867697).sum := by decide
  have hdescent : baseEnd_2867697 < baseStart_2867697 := by decide
  rcases family_descends (prefixWord ++ tailWord_2867697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2867780 : List Nat := [2, 3, 5, 1, 2, 1, 1, 1, 1, 5]
def baseStart_2867780 : Nat := 118140960795 + 2867780 * 2 ^ 59
def prefixEnd_2867780 : Nat := 4983230072969 + 3 ^ 40 * 2867780 * 2
def baseEnd_2867780 : Nat := 981699700900596687507551

theorem tailTrace_2867780 : CollatzResearch.WordTrace tailWord_2867780 prefixEnd_2867780 981699700900596687507551 := by
  unfold tailWord_2867780
  simp only [CollatzResearch.WordTrace]
  refine ⟨52298264775265156337952397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69731019700353541783936529 52298264775265156337952397)
  ·
    refine ⟨19611849290724433626732149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52298264775265156337952397 19611849290724433626732149)
    ·
      refine ⟨1838610871005415652506139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19611849290724433626732149 1838610871005415652506139)
      ·
        refine ⟨2757916306508123478759209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1838610871005415652506139 2757916306508123478759209)
        ·
          refine ⟨2068437229881092609069407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2757916306508123478759209 2068437229881092609069407)
          ·
            refine ⟨3102655844821638913604111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2068437229881092609069407 3102655844821638913604111)
            ·
              refine ⟨4653983767232458370406167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3102655844821638913604111 4653983767232458370406167)
              ·
                refine ⟨6980975650848687555609251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4653983767232458370406167 6980975650848687555609251)
                ·
                  refine ⟨10471463476273031333413877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6980975650848687555609251 10471463476273031333413877)
                  ·
                    refine ⟨981699700900596687507551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10471463476273031333413877 981699700900596687507551)
                    ·
                      rfl

theorem cell22_2867780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_2867780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2867780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2867780 prefixEnd_2867780 := by exact prefixLift 2867780
  have htrace : WordTrace (prefixWord ++ tailWord_2867780) baseStart_2867780 baseEnd_2867780 := by
    simpa [prefixWord, tailWord_2867780, baseEnd_2867780] using wordTrace_append hprefix tailTrace_2867780
  have hstable : (prefixWord ++ tailWord_2867780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2867780).length < 2 ^ (prefixWord ++ tailWord_2867780).sum := by decide
  have hdescent : baseEnd_2867780 < baseStart_2867780 := by decide
  rcases family_descends (prefixWord ++ tailWord_2867780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2867847 : List Nat := [1, 1, 4, 2, 1, 2, 2, 3, 1, 5]
def baseStart_2867847 : Nat := 118140960795 + 2867847 * 2 ^ 59
def prefixEnd_2867847 : Nat := 4983230072969 + 3 ^ 40 * 2867847 * 2
def baseEnd_2867847 : Nat := 981722636369830846082345

theorem tailTrace_2867847 : CollatzResearch.WordTrace tailWord_2867847 prefixEnd_2867847 981722636369830846082345 := by
  unfold tailWord_2867847
  simp only [CollatzResearch.WordTrace]
  refine ⟨104598973241287583118593795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69732648827525055412395863 104598973241287583118593795)
  ·
    refine ⟨156898459861931374677890693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104598973241287583118593795 156898459861931374677890693)
    ·
      refine ⟨29418461224112132752104505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 156898459861931374677890693 29418461224112132752104505)
      ·
        refine ⟨22063845918084099564078379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29418461224112132752104505 22063845918084099564078379)
        ·
          refine ⟨33095768877126149346117569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22063845918084099564078379 33095768877126149346117569)
          ·
            refine ⟨24821826657844612009588177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33095768877126149346117569 24821826657844612009588177)
            ·
              refine ⟨18616369993383459007191133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24821826657844612009588177 18616369993383459007191133)
              ·
                refine ⟨6981138747518797127696675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18616369993383459007191133 6981138747518797127696675)
                ·
                  refine ⟨10471708121278195691545013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6981138747518797127696675 10471708121278195691545013)
                  ·
                    refine ⟨981722636369830846082345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10471708121278195691545013 981722636369830846082345)
                    ·
                      rfl

theorem cell22_2867847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 3, 1, 5].length) (baseStart_2867847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2867847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2867847 prefixEnd_2867847 := by exact prefixLift 2867847
  have htrace : WordTrace (prefixWord ++ tailWord_2867847) baseStart_2867847 baseEnd_2867847 := by
    simpa [prefixWord, tailWord_2867847, baseEnd_2867847] using wordTrace_append hprefix tailTrace_2867847
  have hstable : (prefixWord ++ tailWord_2867847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2867847).length < 2 ^ (prefixWord ++ tailWord_2867847).sum := by decide
  have hdescent : baseEnd_2867847 < baseStart_2867847 := by decide
  rcases family_descends (prefixWord ++ tailWord_2867847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2867939 : List Nat := [1, 1, 1, 7, 1, 2, 1, 1, 7]
def baseStart_2867939 : Nat := 118140960795 + 2867939 * 2 ^ 59
def prefixEnd_2867939 : Nat := 4983230072969 + 3 ^ 40 * 2867939 * 2
def baseEnd_2867939 : Nat := 327251376616657757594021

theorem tailTrace_2867939 : CollatzResearch.WordTrace tailWord_2867939 prefixEnd_2867939 327251376616657757594021 := by
  unfold tailWord_2867939
  simp only [CollatzResearch.WordTrace]
  refine ⟨104602328756954282830942871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69734885837969521887295247 104602328756954282830942871)
  ·
    refine ⟨156903493135431424246414307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104602328756954282830942871 156903493135431424246414307)
    ·
      refine ⟨235355239703147136369621461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156903493135431424246414307 235355239703147136369621461)
      ·
        refine ⟨5516138430542511008663003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 235355239703147136369621461 5516138430542511008663003)
        ·
          refine ⟨8274207645813766512994505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5516138430542511008663003 8274207645813766512994505)
          ·
            refine ⟨6205655734360324884745879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8274207645813766512994505 6205655734360324884745879)
            ·
              refine ⟨9308483601540487327118819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6205655734360324884745879 9308483601540487327118819)
              ·
                refine ⟨13962725402310730990678229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9308483601540487327118819 13962725402310730990678229)
                ·
                  refine ⟨327251376616657757594021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13962725402310730990678229 327251376616657757594021)
                  ·
                    rfl

theorem cell22_2867939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 1, 7].length) (baseStart_2867939 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2867939 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2867939 prefixEnd_2867939 := by exact prefixLift 2867939
  have htrace : WordTrace (prefixWord ++ tailWord_2867939) baseStart_2867939 baseEnd_2867939 := by
    simpa [prefixWord, tailWord_2867939, baseEnd_2867939] using wordTrace_append hprefix tailTrace_2867939
  have hstable : (prefixWord ++ tailWord_2867939).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2867939).length < 2 ^ (prefixWord ++ tailWord_2867939).sum := by decide
  have hdescent : baseEnd_2867939 < baseStart_2867939 := by decide
  rcases family_descends (prefixWord ++ tailWord_2867939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2867954 : List Nat := [3, 2, 1, 3, 1, 2, 2, 1, 2, 5]
def baseStart_2867954 : Nat := 118140960795 + 2867954 * 2 ^ 59
def prefixEnd_2867954 : Nat := 4983230072969 + 3 ^ 40 * 2867954 * 2
def baseEnd_2867954 : Nat := 981759264656518233657017

theorem tailTrace_2867954 : CollatzResearch.WordTrace tailWord_2867954 prefixEnd_2867954 981759264656518233657017 := by
  unfold tailWord_2867954
  simp only [CollatzResearch.WordTrace]
  refine ⟨26150718962974985098184729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69735250567933293595159277 26150718962974985098184729)
  ·
    refine ⟨19613039222231238823638547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26150718962974985098184729 19613039222231238823638547)
    ·
      refine ⟨29419558833346858235457821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19613039222231238823638547 29419558833346858235457821)
      ·
        refine ⟨11032334562505071838296683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29419558833346858235457821 11032334562505071838296683)
        ·
          refine ⟨16548501843757607757445025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11032334562505071838296683 16548501843757607757445025)
          ·
            refine ⟨12411376382818205818083769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16548501843757607757445025 12411376382818205818083769)
            ·
              refine ⟨9308532287113654363562827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12411376382818205818083769 9308532287113654363562827)
              ·
                refine ⟨13962798430670481545344241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9308532287113654363562827 13962798430670481545344241)
                ·
                  refine ⟨10472098823002861159008181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13962798430670481545344241 10472098823002861159008181)
                  ·
                    refine ⟨981759264656518233657017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10472098823002861159008181 981759264656518233657017)
                    ·
                      rfl

theorem cell22_2867954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 1, 2, 5].length) (baseStart_2867954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2867954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2867954 prefixEnd_2867954 := by exact prefixLift 2867954
  have htrace : WordTrace (prefixWord ++ tailWord_2867954) baseStart_2867954 baseEnd_2867954 := by
    simpa [prefixWord, tailWord_2867954, baseEnd_2867954] using wordTrace_append hprefix tailTrace_2867954
  have hstable : (prefixWord ++ tailWord_2867954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2867954).length < 2 ^ (prefixWord ++ tailWord_2867954).sum := by decide
  have hdescent : baseEnd_2867954 < baseStart_2867954 := by decide
  rcases family_descends (prefixWord ++ tailWord_2867954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2868020 : List Nat := [2, 5, 1, 1, 3, 2, 1, 2, 1, 4]
def baseStart_2868020 : Nat := 118140960795 + 2868020 * 2 ^ 59
def prefixEnd_2868020 : Nat := 4983230072969 + 3 ^ 40 * 2868020 * 2
def baseEnd_2868020 : Nat := 981781857805316061506815

theorem tailTrace_2868020 : CollatzResearch.WordTrace tailWord_2868020 prefixEnd_2868020 981781857805316061506815 := by
  unfold tailWord_2868020
  simp only [CollatzResearch.WordTrace]
  refine ⟨52302641534830416832320757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69736855379773889109761009 52302641534830416832320757)
  ·
    refine ⟨4903372643890351578030071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 52302641534830416832320757 4903372643890351578030071)
    ·
      refine ⟨7355058965835527367045107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4903372643890351578030071 7355058965835527367045107)
      ·
        refine ⟨11032588448753291050567661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7355058965835527367045107 11032588448753291050567661)
        ·
          refine ⟨4137220668282484143962873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11032588448753291050567661 4137220668282484143962873)
          ·
            refine ⟨3102915501211863107972155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4137220668282484143962873 3102915501211863107972155)
            ·
              refine ⟨4654373251817794661958233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3102915501211863107972155 4654373251817794661958233)
              ·
                refine ⟨3490779938863345996468675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4654373251817794661958233 3490779938863345996468675)
                ·
                  refine ⟨5236169908295018994703013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3490779938863345996468675 5236169908295018994703013)
                  ·
                    refine ⟨981781857805316061506815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5236169908295018994703013 981781857805316061506815)
                    ·
                      rfl

theorem cell22_2868020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 1, 2, 1, 4].length) (baseStart_2868020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2868020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2868020 prefixEnd_2868020 := by exact prefixLift 2868020
  have htrace : WordTrace (prefixWord ++ tailWord_2868020) baseStart_2868020 baseEnd_2868020 := by
    simpa [prefixWord, tailWord_2868020, baseEnd_2868020] using wordTrace_append hprefix tailTrace_2868020
  have hstable : (prefixWord ++ tailWord_2868020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2868020).length < 2 ^ (prefixWord ++ tailWord_2868020).sum := by decide
  have hdescent : baseEnd_2868020 < baseStart_2868020 := by decide
  rcases family_descends (prefixWord ++ tailWord_2868020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2868031 : List Nat := [1, 1, 2, 2, 5, 2, 2, 1, 2, 4]
def baseStart_2868031 : Nat := 118140960795 + 2868031 * 2 ^ 59
def prefixEnd_2868031 : Nat := 4983230072969 + 3 ^ 40 * 2868031 * 2
def baseEnd_2868031 : Nat := 981785623330115699481781

theorem tailTrace_2868031 : CollatzResearch.WordTrace tailWord_2868031 prefixEnd_2868031 981785623330115699481781 := by
  unfold tailWord_2868031
  simp only [CollatzResearch.WordTrace]
  refine ⟨104605684272620982543291947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69737122848413988362194631 104605684272620982543291947)
  ·
    refine ⟨156908526408931473814937921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104605684272620982543291947 156908526408931473814937921)
    ·
      refine ⟨117681394806698605361203441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156908526408931473814937921 117681394806698605361203441)
      ·
        refine ⟨88261046105023954020902581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117681394806698605361203441 88261046105023954020902581)
        ·
          refine ⟨8274473072345995689459617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 88261046105023954020902581 8274473072345995689459617)
          ·
            refine ⟨6205854804259496767094713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8274473072345995689459617 6205854804259496767094713)
            ·
              refine ⟨4654391103194622575321035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6205854804259496767094713 4654391103194622575321035)
              ·
                refine ⟨6981586654791933862981553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4654391103194622575321035 6981586654791933862981553)
                ·
                  refine ⟨5236189991093950397236165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6981586654791933862981553 5236189991093950397236165)
                  ·
                    refine ⟨981785623330115699481781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5236189991093950397236165 981785623330115699481781)
                    ·
                      rfl

theorem cell22_2868031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 2, 1, 2, 4].length) (baseStart_2868031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2868031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2868031 prefixEnd_2868031 := by exact prefixLift 2868031
  have htrace : WordTrace (prefixWord ++ tailWord_2868031) baseStart_2868031 baseEnd_2868031 := by
    simpa [prefixWord, tailWord_2868031, baseEnd_2868031] using wordTrace_append hprefix tailTrace_2868031
  have hstable : (prefixWord ++ tailWord_2868031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2868031).length < 2 ^ (prefixWord ++ tailWord_2868031).sum := by decide
  have hdescent : baseEnd_2868031 < baseStart_2868031 := by decide
  rcases family_descends (prefixWord ++ tailWord_2868031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2868033 : List Nat := [1, 2, 5, 3, 1, 1, 1, 2, 1, 5]
def baseStart_2868033 : Nat := 118140960795 + 2868033 * 2 ^ 59
def prefixEnd_2868033 : Nat := 4983230072969 + 3 ^ 40 * 2868033 * 2
def baseEnd_2868033 : Nat := 981786307970988360931775

theorem tailTrace_2868033 : CollatzResearch.WordTrace tailWord_2868033 prefixEnd_2868033 981786307970988360931775 := by
  unfold tailWord_2868033
  simp only [CollatzResearch.WordTrace]
  refine ⟨104605757218613736884864753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69737171479075824589909835 104605757218613736884864753)
  ·
    refine ⟨78454317913960302663648565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104605757218613736884864753 78454317913960302663648565)
    ·
      refine ⟨7355092304433778374717053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 78454317913960302663648565 7355092304433778374717053)
      ·
        refine ⟨2758159614162666890518895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7355092304433778374717053 2758159614162666890518895)
        ·
          refine ⟨4137239421244000335778343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2758159614162666890518895 4137239421244000335778343)
          ·
            refine ⟨6205859131866000503667515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4137239421244000335778343 6205859131866000503667515)
            ·
              refine ⟨9308788697799000755501273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6205859131866000503667515 9308788697799000755501273)
              ·
                refine ⟨6981591523349250566625955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9308788697799000755501273 6981591523349250566625955)
                ·
                  refine ⟨10472387285023875849938933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6981591523349250566625955 10472387285023875849938933)
                  ·
                    refine ⟨981786307970988360931775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10472387285023875849938933 981786307970988360931775)
                    ·
                      rfl

theorem cell22_2868033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 2, 1, 5].length) (baseStart_2868033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2868033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2868033 prefixEnd_2868033 := by exact prefixLift 2868033
  have htrace : WordTrace (prefixWord ++ tailWord_2868033) baseStart_2868033 baseEnd_2868033 := by
    simpa [prefixWord, tailWord_2868033, baseEnd_2868033] using wordTrace_append hprefix tailTrace_2868033
  have hstable : (prefixWord ++ tailWord_2868033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2868033).length < 2 ^ (prefixWord ++ tailWord_2868033).sum := by decide
  have hdescent : baseEnd_2868033 < baseStart_2868033 := by decide
  rcases family_descends (prefixWord ++ tailWord_2868033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2868052 : List Nat := [2, 4, 1, 1, 5, 1, 2, 2, 4]
def baseStart_2868052 : Nat := 118140960795 + 2868052 * 2 ^ 59
def prefixEnd_2868052 : Nat := 4983230072969 + 3 ^ 40 * 2868052 * 2
def baseEnd_2868052 : Nat := 327264270686426214902239

theorem tailTrace_2868052 : CollatzResearch.WordTrace tailWord_2868052 prefixEnd_2868052 327264270686426214902239 := by
  unfold tailWord_2868052
  simp only [CollatzResearch.WordTrace]
  refine ⟨52303225102772451564903205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69737633470363268753204273 52303225102772451564903205)
  ·
    refine ⟨9806854706769834668419351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52303225102772451564903205 9806854706769834668419351)
    ·
      refine ⟨14710282060154752002629027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9806854706769834668419351 14710282060154752002629027)
      ·
        refine ⟨22065423090232128003943541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14710282060154752002629027 22065423090232128003943541)
        ·
          refine ⟨2068633414709262000369707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22065423090232128003943541 2068633414709262000369707)
          ·
            refine ⟨3102950122063893000554561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2068633414709262000369707 3102950122063893000554561)
            ·
              refine ⟨2327212591547919750415921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3102950122063893000554561 2327212591547919750415921)
              ·
                refine ⟨1745409443660939812811941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2327212591547919750415921 1745409443660939812811941)
                ·
                  refine ⟨327264270686426214902239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1745409443660939812811941 327264270686426214902239)
                  ·
                    rfl

theorem cell22_2868052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 2, 2, 4].length) (baseStart_2868052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2868052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2868052 prefixEnd_2868052 := by exact prefixLift 2868052
  have htrace : WordTrace (prefixWord ++ tailWord_2868052) baseStart_2868052 baseEnd_2868052 := by
    simpa [prefixWord, tailWord_2868052, baseEnd_2868052] using wordTrace_append hprefix tailTrace_2868052
  have hstable : (prefixWord ++ tailWord_2868052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2868052).length < 2 ^ (prefixWord ++ tailWord_2868052).sum := by decide
  have hdescent : baseEnd_2868052 < baseStart_2868052 := by decide
  rcases family_descends (prefixWord ++ tailWord_2868052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2868106 : List Nat := [3, 1, 2, 4, 1, 1, 1, 2, 2, 5]
def baseStart_2868106 : Nat := 118140960795 + 2868106 * 2 ^ 59
def prefixEnd_2868106 : Nat := 4983230072969 + 3 ^ 40 * 2868106 * 2
def baseEnd_2868106 : Nat := 981811297362840503856551

theorem tailTrace_2868106 : CollatzResearch.WordTrace tailWord_2868106 prefixEnd_2868106 981811297362840503856551 := by
  unfold tailWord_2868106
  simp only [CollatzResearch.WordTrace]
  refine ⟨26152104936837317588068043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69738946498232846901514781 26152104936837317588068043)
  ·
    refine ⟨39228157405255976382102065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26152104936837317588068043 39228157405255976382102065)
    ·
      refine ⟨29421118053941982286576549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39228157405255976382102065 29421118053941982286576549)
      ·
        refine ⟨5516459635114121678733103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29421118053941982286576549 5516459635114121678733103)
        ·
          refine ⟨8274689452671182518099655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5516459635114121678733103 8274689452671182518099655)
          ·
            refine ⟨12412034179006773777149483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8274689452671182518099655 12412034179006773777149483)
            ·
              refine ⟨18618051268510160665724225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12412034179006773777149483 18618051268510160665724225)
              ·
                refine ⟨13963538451382620499293169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18618051268510160665724225 13963538451382620499293169)
                ·
                  refine ⟨10472653838536965374469877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13963538451382620499293169 10472653838536965374469877)
                  ·
                    refine ⟨981811297362840503856551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10472653838536965374469877 981811297362840503856551)
                    ·
                      rfl

theorem cell22_2868106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 2, 2, 5].length) (baseStart_2868106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2868106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2868106 prefixEnd_2868106 := by exact prefixLift 2868106
  have htrace : WordTrace (prefixWord ++ tailWord_2868106) baseStart_2868106 baseEnd_2868106 := by
    simpa [prefixWord, tailWord_2868106, baseEnd_2868106] using wordTrace_append hprefix tailTrace_2868106
  have hstable : (prefixWord ++ tailWord_2868106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2868106).length < 2 ^ (prefixWord ++ tailWord_2868106).sum := by decide
  have hdescent : baseEnd_2868106 < baseStart_2868106 := by decide
  rcases family_descends (prefixWord ++ tailWord_2868106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2868151 : List Nat := [1, 1, 3, 1, 3, 1, 3, 2, 4, 3]
def baseStart_2868151 : Nat := 118140960795 + 2868151 * 2 ^ 59
def prefixEnd_2868151 : Nat := 4983230072969 + 3 ^ 40 * 2868151 * 2
def baseEnd_2868151 : Nat := 981826701782475386481413

theorem tailTrace_2868151 : CollatzResearch.WordTrace tailWord_2868151 prefixEnd_2868151 981826701782475386481413 := by
  unfold tailWord_2868151
  simp only [CollatzResearch.WordTrace]
  refine ⟨104610061032186243037660307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69740040688124162025106871 104610061032186243037660307)
  ·
    refine ⟨156915091548279364556490461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104610061032186243037660307 156915091548279364556490461)
    ·
      refine ⟨58843159330604761708683923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156915091548279364556490461 58843159330604761708683923)
      ·
        refine ⟨88264738995907142563025885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58843159330604761708683923 88264738995907142563025885)
        ·
          refine ⟨33099277123465178461134707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88264738995907142563025885 33099277123465178461134707)
          ·
            refine ⟨49648915685197767691702061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33099277123465178461134707 49648915685197767691702061)
            ·
              refine ⟨18618343381949162884388273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49648915685197767691702061 18618343381949162884388273)
              ·
                refine ⟨13963757536461872163291205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18618343381949162884388273 13963757536461872163291205)
                ·
                  refine ⟨2618204538086601030617101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13963757536461872163291205 2618204538086601030617101)
                  ·
                    refine ⟨981826701782475386481413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2618204538086601030617101 981826701782475386481413)
                    ·
                      rfl

theorem cell22_2868151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 2, 4, 3].length) (baseStart_2868151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2868151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2868151 prefixEnd_2868151 := by exact prefixLift 2868151
  have htrace : WordTrace (prefixWord ++ tailWord_2868151) baseStart_2868151 baseEnd_2868151 := by
    simpa [prefixWord, tailWord_2868151, baseEnd_2868151] using wordTrace_append hprefix tailTrace_2868151
  have hstable : (prefixWord ++ tailWord_2868151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2868151).length < 2 ^ (prefixWord ++ tailWord_2868151).sum := by decide
  have hdescent : baseEnd_2868151 < baseStart_2868151 := by decide
  rcases family_descends (prefixWord ++ tailWord_2868151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2868153 : List Nat := [1, 2, 1, 4, 2, 2, 3, 3, 4]
def baseStart_2868153 : Nat := 118140960795 + 2868153 * 2 ^ 59
def prefixEnd_2868153 : Nat := 4983230072969 + 3 ^ 40 * 2868153 * 2
def baseEnd_2868153 : Nat := 327275795474449349310469

theorem tailTrace_2868153 : CollatzResearch.WordTrace tailWord_2868153 prefixEnd_2868153 327275795474449349310469 := by
  unfold tailWord_2868153
  simp only [CollatzResearch.WordTrace]
  refine ⟨104610133978178997379233113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69740089318785998252822075 104610133978178997379233113)
  ·
    refine ⟨78457600483634248034424835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104610133978178997379233113 78457600483634248034424835)
    ·
      refine ⟨117686400725451372051637253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78457600483634248034424835 117686400725451372051637253)
      ·
        refine ⟨22066200136022132259681985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 117686400725451372051637253 22066200136022132259681985)
        ·
          refine ⟨16549650102016599194761489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22066200136022132259681985 16549650102016599194761489)
          ·
            refine ⟨12412237576512449396071117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16549650102016599194761489 12412237576512449396071117)
            ·
              refine ⟨4654589091192168523526669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12412237576512449396071117 4654589091192168523526669)
              ·
                refine ⟨1745470909197063196322501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4654589091192168523526669 1745470909197063196322501)
                ·
                  refine ⟨327275795474449349310469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1745470909197063196322501 327275795474449349310469)
                  ·
                    rfl

theorem cell22_2868153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 3, 3, 4].length) (baseStart_2868153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2868153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2868153 prefixEnd_2868153 := by exact prefixLift 2868153
  have htrace : WordTrace (prefixWord ++ tailWord_2868153) baseStart_2868153 baseEnd_2868153 := by
    simpa [prefixWord, tailWord_2868153, baseEnd_2868153] using wordTrace_append hprefix tailTrace_2868153
  have hstable : (prefixWord ++ tailWord_2868153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2868153).length < 2 ^ (prefixWord ++ tailWord_2868153).sum := by decide
  have hdescent : baseEnd_2868153 < baseStart_2868153 := by decide
  rcases family_descends (prefixWord ++ tailWord_2868153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2868185 : List Nat := [1, 2, 1, 2, 5, 1, 4, 1, 2, 3]
def baseStart_2868185 : Nat := 118140960795 + 2868185 * 2 ^ 59
def prefixEnd_2868185 : Nat := 4983230072969 + 3 ^ 40 * 2868185 * 2
def baseEnd_2868185 : Nat := 981838340677310631131309

theorem tailTrace_2868185 : CollatzResearch.WordTrace tailWord_2868185 prefixEnd_2868185 981838340677310631131309 := by
  unfold tailWord_2868185
  simp only [CollatzResearch.WordTrace]
  refine ⟨104611301114063066844398009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69740867409375377896265339 104611301114063066844398009)
  ·
    refine ⟨78458475835547300133298507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104611301114063066844398009 78458475835547300133298507)
    ·
      refine ⟨117687713753320950199947761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78458475835547300133298507 117687713753320950199947761)
      ·
        refine ⟨88265785314990712649960821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117687713753320950199947761 88265785314990712649960821)
        ·
          refine ⟨8274917373280379310933827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 88265785314990712649960821 8274917373280379310933827)
          ·
            refine ⟨12412376059920568966400741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8274917373280379310933827 12412376059920568966400741)
            ·
              refine ⟨2327320511235106681200139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12412376059920568966400741 2327320511235106681200139)
              ·
                refine ⟨3490980766852660021800209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2327320511235106681200139 3490980766852660021800209)
                ·
                  refine ⟨2618235575139495016350157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3490980766852660021800209 2618235575139495016350157)
                  ·
                    refine ⟨981838340677310631131309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2618235575139495016350157 981838340677310631131309)
                    ·
                      rfl

theorem cell22_2868185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 4, 1, 2, 3].length) (baseStart_2868185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2868185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2868185 prefixEnd_2868185 := by exact prefixLift 2868185
  have htrace : WordTrace (prefixWord ++ tailWord_2868185) baseStart_2868185 baseEnd_2868185 := by
    simpa [prefixWord, tailWord_2868185, baseEnd_2868185] using wordTrace_append hprefix tailTrace_2868185
  have hstable : (prefixWord ++ tailWord_2868185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2868185).length < 2 ^ (prefixWord ++ tailWord_2868185).sum := by decide
  have hdescent : baseEnd_2868185 < baseStart_2868185 := by decide
  rcases family_descends (prefixWord ++ tailWord_2868185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2868273 : List Nat := [1, 2, 2, 3, 1, 2, 3, 3, 1, 4]
def baseStart_2868273 : Nat := 118140960795 + 2868273 * 2 ^ 59
def prefixEnd_2868273 : Nat := 4983230072969 + 3 ^ 40 * 2868273 * 2
def baseEnd_2868273 : Nat := 981868464875707734931039

theorem tailTrace_2868273 : CollatzResearch.WordTrace tailWord_2868273 prefixEnd_2868273 981868464875707734931039 := by
  unfold tailWord_2868273
  simp only [CollatzResearch.WordTrace]
  refine ⟨104614510737744257873601473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69743007158496171915734315 104614510737744257873601473)
  ·
    refine ⟨78460883053308193405201105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104614510737744257873601473 78460883053308193405201105)
    ·
      refine ⟨58845662289981145053900829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78460883053308193405201105 58845662289981145053900829)
      ·
        refine ⟨22067123358742929395212811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58845662289981145053900829 22067123358742929395212811)
        ·
          refine ⟨33100685038114394092819217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22067123358742929395212811 33100685038114394092819217)
          ·
            refine ⟨24825513778585795569614413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33100685038114394092819217 24825513778585795569614413)
            ·
              refine ⟨9309567666969673338605405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24825513778585795569614413 9309567666969673338605405)
              ·
                refine ⟨3491087875113627501977027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9309567666969673338605405 3491087875113627501977027)
                ·
                  refine ⟨5236631812670441252965541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3491087875113627501977027 5236631812670441252965541)
                  ·
                    refine ⟨981868464875707734931039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5236631812670441252965541 981868464875707734931039)
                    ·
                      rfl

theorem cell22_2868273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 3, 1, 4].length) (baseStart_2868273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2868273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2868273 prefixEnd_2868273 := by exact prefixLift 2868273
  have htrace : WordTrace (prefixWord ++ tailWord_2868273) baseStart_2868273 baseEnd_2868273 := by
    simpa [prefixWord, tailWord_2868273, baseEnd_2868273] using wordTrace_append hprefix tailTrace_2868273
  have hstable : (prefixWord ++ tailWord_2868273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2868273).length < 2 ^ (prefixWord ++ tailWord_2868273).sum := by decide
  have hdescent : baseEnd_2868273 < baseStart_2868273 := by decide
  rcases family_descends (prefixWord ++ tailWord_2868273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2868288 : List Nat := [2, 1, 1, 2, 2, 3, 1, 6, 4]
def baseStart_2868288 : Nat := 118140960795 + 2868288 * 2 ^ 59
def prefixEnd_2868288 : Nat := 4983230072969 + 3 ^ 40 * 2868288 * 2
def baseEnd_2868288 : Nat := 327291199894084231935331

theorem tailTrace_2868288 : CollatzResearch.WordTrace tailWord_2868288 prefixEnd_2868288 327291199894084231935331 := by
  unfold tailWord_2868288
  simp only [CollatzResearch.WordTrace]
  refine ⟨52307528916344957717698759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69743371888459943623598345 52307528916344957717698759)
  ·
    refine ⟨78461293374517436576548139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52307528916344957717698759 78461293374517436576548139)
    ·
      refine ⟨117691940061776154864822209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78461293374517436576548139 117691940061776154864822209)
      ·
        refine ⟨88268955046332116148616657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117691940061776154864822209 88268955046332116148616657)
        ·
          refine ⟨66201716284749087111462493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88268955046332116148616657 66201716284749087111462493)
          ·
            refine ⟨24825643606780907666798435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66201716284749087111462493 24825643606780907666798435)
            ·
              refine ⟨37238465410171361500197653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24825643606780907666798435 37238465410171361500197653)
              ·
                refine ⟨1745553066101782570321765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 37238465410171361500197653 1745553066101782570321765)
                ·
                  refine ⟨327291199894084231935331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1745553066101782570321765 327291199894084231935331)
                  ·
                    rfl

theorem cell22_2868288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 6, 4].length) (baseStart_2868288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2868288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2868288 prefixEnd_2868288 := by exact prefixLift 2868288
  have htrace : WordTrace (prefixWord ++ tailWord_2868288) baseStart_2868288 baseEnd_2868288 := by
    simpa [prefixWord, tailWord_2868288, baseEnd_2868288] using wordTrace_append hprefix tailTrace_2868288
  have hstable : (prefixWord ++ tailWord_2868288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2868288).length < 2 ^ (prefixWord ++ tailWord_2868288).sum := by decide
  have hdescent : baseEnd_2868288 < baseStart_2868288 := by decide
  rcases family_descends (prefixWord ++ tailWord_2868288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2868322 : List Nat := [3, 3, 2, 2, 1, 1, 3, 3, 4]
def baseStart_2868322 : Nat := 118140960795 + 2868322 * 2 ^ 59
def prefixEnd_2868322 : Nat := 4983230072969 + 3 ^ 40 * 2868322 * 2
def baseEnd_2868322 : Nat := 327295079525695980151963

theorem tailTrace_2868322 : CollatzResearch.WordTrace tailWord_2868322 prefixEnd_2868322 327295079525695980151963 := by
  unfold tailWord_2868322
  simp only [CollatzResearch.WordTrace]
  refine ⟨26154074478641684810533805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69744198609711159494756813 26154074478641684810533805)
  ·
    refine ⟨9807777929490631803950177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26154074478641684810533805 9807777929490631803950177)
    ·
      refine ⟨7355833447117973852962633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9807777929490631803950177 7355833447117973852962633)
      ·
        refine ⟨5516875085338480389721975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7355833447117973852962633 5516875085338480389721975)
        ·
          refine ⟨8275312628007720584582963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5516875085338480389721975 8275312628007720584582963)
          ·
            refine ⟨12412968942011580876874445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8275312628007720584582963 12412968942011580876874445)
            ·
              refine ⟨4654863353254342828827917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12412968942011580876874445 4654863353254342828827917)
              ·
                refine ⟨1745573757470378560810469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4654863353254342828827917 1745573757470378560810469)
                ·
                  refine ⟨327295079525695980151963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1745573757470378560810469 327295079525695980151963)
                  ·
                    rfl

theorem cell22_2868322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 3, 3, 4].length) (baseStart_2868322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2868322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2868322 prefixEnd_2868322 := by exact prefixLift 2868322
  have htrace : WordTrace (prefixWord ++ tailWord_2868322) baseStart_2868322 baseEnd_2868322 := by
    simpa [prefixWord, tailWord_2868322, baseEnd_2868322] using wordTrace_append hprefix tailTrace_2868322
  have hstable : (prefixWord ++ tailWord_2868322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2868322).length < 2 ^ (prefixWord ++ tailWord_2868322).sum := by decide
  have hdescent : baseEnd_2868322 < baseStart_2868322 := by decide
  rcases family_descends (prefixWord ++ tailWord_2868322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2868333 : List Nat := [1, 5, 1, 1, 2, 4, 8]
def baseStart_2868333 : Nat := 118140960795 + 2868333 * 2 ^ 59
def prefixEnd_2868333 : Nat := 4983230072969 + 3 ^ 40 * 2868333 * 2
def baseEnd_2868333 : Nat := 36366259411181021423365

theorem tailTrace_2868333 : CollatzResearch.WordTrace tailWord_2868333 prefixEnd_2868333 36366259411181021423365 := by
  unfold tailWord_2868333
  simp only [CollatzResearch.WordTrace]
  refine ⟨104616699117526888120785653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69744466078351258747190435 104616699117526888120785653)
  ·
    refine ⟨9807815542268145761323655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 104616699117526888120785653 9807815542268145761323655)
    ·
      refine ⟨14711723313402218641985483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9807815542268145761323655 14711723313402218641985483)
      ·
        refine ⟨22067584970103327962978225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14711723313402218641985483 22067584970103327962978225)
        ·
          refine ⟨16550688727577495972233669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22067584970103327962978225 16550688727577495972233669)
          ·
            refine ⟨3103254136420780494793813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16550688727577495972233669 3103254136420780494793813)
            ·
              refine ⟨36366259411181021423365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3103254136420780494793813 36366259411181021423365)
              ·
                rfl

theorem cell22_2868333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 8].length) (baseStart_2868333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2868333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2868333 prefixEnd_2868333 := by exact prefixLift 2868333
  have htrace : WordTrace (prefixWord ++ tailWord_2868333) baseStart_2868333 baseEnd_2868333 := by
    simpa [prefixWord, tailWord_2868333, baseEnd_2868333] using wordTrace_append hprefix tailTrace_2868333
  have hstable : (prefixWord ++ tailWord_2868333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2868333).length < 2 ^ (prefixWord ++ tailWord_2868333).sum := by decide
  have hdescent : baseEnd_2868333 < baseStart_2868333 := by decide
  rcases family_descends (prefixWord ++ tailWord_2868333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2868517 : List Nat := [1, 3, 1, 2, 4, 1, 3, 1, 3, 3]
def baseStart_2868517 : Nat := 118140960795 + 2868517 * 2 ^ 59
def prefixEnd_2868517 : Nat := 4983230072969 + 3 ^ 40 * 2868517 * 2
def baseEnd_2868517 : Nat := 981951991062172431830291

theorem tailTrace_2868517 : CollatzResearch.WordTrace tailWord_2868517 prefixEnd_2868517 981951991062172431830291 := by
  unfold tailWord_2868517
  simp only [CollatzResearch.WordTrace]
  refine ⟨104623410148860287545483805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69748940099240191696989203 104623410148860287545483805)
  ·
    refine ⟨39233778805822607829556427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104623410148860287545483805 39233778805822607829556427)
    ·
      refine ⟨58850668208733911744334641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39233778805822607829556427 58850668208733911744334641)
      ·
        refine ⟨44138001156550433808250981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58850668208733911744334641 44138001156550433808250981)
        ·
          refine ⟨8275875216853206339047059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44138001156550433808250981 8275875216853206339047059)
          ·
            refine ⟨12413812825279809508570589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8275875216853206339047059 12413812825279809508570589)
            ·
              refine ⟨4655179809479928565713971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12413812825279809508570589 4655179809479928565713971)
              ·
                refine ⟨6982769714219892848570957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4655179809479928565713971 6982769714219892848570957)
                ·
                  refine ⟨2618538642832459818214109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6982769714219892848570957 2618538642832459818214109)
                  ·
                    refine ⟨981951991062172431830291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2618538642832459818214109 981951991062172431830291)
                    ·
                      rfl

theorem cell22_2868517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 3, 1, 3, 3].length) (baseStart_2868517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2868517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2868517 prefixEnd_2868517 := by exact prefixLift 2868517
  have htrace : WordTrace (prefixWord ++ tailWord_2868517) baseStart_2868517 baseEnd_2868517 := by
    simpa [prefixWord, tailWord_2868517, baseEnd_2868517] using wordTrace_append hprefix tailTrace_2868517
  have hstable : (prefixWord ++ tailWord_2868517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2868517).length < 2 ^ (prefixWord ++ tailWord_2868517).sum := by decide
  have hdescent : baseEnd_2868517 < baseStart_2868517 := by decide
  rcases family_descends (prefixWord ++ tailWord_2868517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2868528 : List Nat := [2, 1, 1, 1, 2, 2, 4, 1, 1, 7]
def baseStart_2868528 : Nat := 118140960795 + 2868528 * 2 ^ 59
def prefixEnd_2868528 : Nat := 4983230072969 + 3 ^ 40 * 2868528 * 2
def baseEnd_2868528 : Nat := 981955756586972069805257

theorem tailTrace_2868528 : CollatzResearch.WordTrace tailWord_2868528 prefixEnd_2868528 981955756586972069805257 := by
  unfold tailWord_2868528
  simp only [CollatzResearch.WordTrace]
  refine ⟨52311905675910218212067119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69749207567880290949422825 52311905675910218212067119)
  ·
    refine ⟨78467858513865327318100679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52311905675910218212067119 78467858513865327318100679)
    ·
      refine ⟨117701787770797990977151019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78467858513865327318100679 117701787770797990977151019)
      ·
        refine ⟨176552681656196986465726529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117701787770797990977151019 176552681656196986465726529)
        ·
          refine ⟨132414511242147739849294897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176552681656196986465726529 132414511242147739849294897)
          ·
            refine ⟨99310883431610804886971173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132414511242147739849294897 99310883431610804886971173)
            ·
              refine ⟨18620790643427025916307095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 99310883431610804886971173 18620790643427025916307095)
              ·
                refine ⟨27931185965140538874460643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18620790643427025916307095 27931185965140538874460643)
                ·
                  refine ⟨41896778947710808311690965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27931185965140538874460643 41896778947710808311690965)
                  ·
                    refine ⟨981955756586972069805257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41896778947710808311690965 981955756586972069805257)
                    ·
                      rfl

theorem cell22_2868528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 1, 1, 7].length) (baseStart_2868528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2868528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2868528 prefixEnd_2868528 := by exact prefixLift 2868528
  have htrace : WordTrace (prefixWord ++ tailWord_2868528) baseStart_2868528 baseEnd_2868528 := by
    simpa [prefixWord, tailWord_2868528, baseEnd_2868528] using wordTrace_append hprefix tailTrace_2868528
  have hstable : (prefixWord ++ tailWord_2868528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2868528).length < 2 ^ (prefixWord ++ tailWord_2868528).sum := by decide
  have hdescent : baseEnd_2868528 < baseStart_2868528 := by decide
  rcases family_descends (prefixWord ++ tailWord_2868528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2868605 : List Nat := [1, 4, 1, 1, 2, 2, 3, 1, 1, 6]
def baseStart_2868605 : Nat := 118140960795 + 2868605 * 2 ^ 59
def prefixEnd_2868605 : Nat := 4983230072969 + 3 ^ 40 * 2868605 * 2
def baseEnd_2868605 : Nat := 981982115260569535630021

theorem tailTrace_2868605 : CollatzResearch.WordTrace tailWord_2868605 prefixEnd_2868605 981982115260569535630021 := by
  unfold tailWord_2868605
  simp only [CollatzResearch.WordTrace]
  refine ⟨104626619772541478574687269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69751079848360985716458179 104626619772541478574687269)
  ·
    refine ⟨19617491207351527232753863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104626619772541478574687269 19617491207351527232753863)
    ·
      refine ⟨29426236811027290849130795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19617491207351527232753863 29426236811027290849130795)
      ·
        refine ⟨44139355216540936273696193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29426236811027290849130795 44139355216540936273696193)
        ·
          refine ⟨33104516412405702205272145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44139355216540936273696193 33104516412405702205272145)
          ·
            refine ⟨24828387309304276653954109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33104516412405702205272145 24828387309304276653954109)
            ·
              refine ⟨9310645240989103745232791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24828387309304276653954109 9310645240989103745232791)
              ·
                refine ⟨13965967861483655617849187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9310645240989103745232791 13965967861483655617849187)
                ·
                  refine ⟨20948951792225483426773781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13965967861483655617849187 20948951792225483426773781)
                  ·
                    refine ⟨981982115260569535630021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20948951792225483426773781 981982115260569535630021)
                    ·
                      rfl

theorem cell22_2868605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 1, 1, 6].length) (baseStart_2868605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2868605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2868605 prefixEnd_2868605 := by exact prefixLift 2868605
  have htrace : WordTrace (prefixWord ++ tailWord_2868605) baseStart_2868605 baseEnd_2868605 := by
    simpa [prefixWord, tailWord_2868605, baseEnd_2868605] using wordTrace_append hprefix tailTrace_2868605
  have hstable : (prefixWord ++ tailWord_2868605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2868605).length < 2 ^ (prefixWord ++ tailWord_2868605).sum := by decide
  have hdescent : baseEnd_2868605 < baseStart_2868605 := by decide
  rcases family_descends (prefixWord ++ tailWord_2868605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2868652 : List Nat := [2, 2, 1, 1, 1, 1, 6, 2, 3, 3]
def baseStart_2868652 : Nat := 118140960795 + 2868652 * 2 ^ 59
def prefixEnd_2868652 : Nat := 4983230072969 + 3 ^ 40 * 2868652 * 2
def baseEnd_2868652 : Nat := 981998204321077079704877

theorem tailTrace_2868652 : CollatzResearch.WordTrace tailWord_2868652 prefixEnd_2868652 981998204321077079704877 := by
  unfold tailWord_2868652
  simp only [CollatzResearch.WordTrace]
  refine ⟨52314167001685602800824105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69752222668914137067765473 52314167001685602800824105)
  ·
    refine ⟨39235625251264202100618079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52314167001685602800824105 39235625251264202100618079)
    ·
      refine ⟨58853437876896303150927119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39235625251264202100618079 58853437876896303150927119)
      ·
        refine ⟨88280156815344454726390679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58853437876896303150927119 88280156815344454726390679)
        ·
          refine ⟨132420235223016682089586019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88280156815344454726390679 132420235223016682089586019)
          ·
            refine ⟨198630352834525023134379029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132420235223016682089586019 198630352834525023134379029)
            ·
              refine ⟨9310797789118360459424017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 198630352834525023134379029 9310797789118360459424017)
              ·
                refine ⟨6983098341838770344568013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9310797789118360459424017 6983098341838770344568013)
                ·
                  refine ⟨2618661878189538879213005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6983098341838770344568013 2618661878189538879213005)
                  ·
                    refine ⟨981998204321077079704877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2618661878189538879213005 981998204321077079704877)
                    ·
                      rfl

theorem cell22_2868652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 3].length) (baseStart_2868652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2868652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2868652 prefixEnd_2868652 := by exact prefixLift 2868652
  have htrace : WordTrace (prefixWord ++ tailWord_2868652) baseStart_2868652 baseEnd_2868652 := by
    simpa [prefixWord, tailWord_2868652, baseEnd_2868652] using wordTrace_append hprefix tailTrace_2868652
  have hstable : (prefixWord ++ tailWord_2868652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2868652).length < 2 ^ (prefixWord ++ tailWord_2868652).sum := by decide
  have hdescent : baseEnd_2868652 < baseStart_2868652 := by decide
  rcases family_descends (prefixWord ++ tailWord_2868652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2868712 : List Nat := [2, 1, 4, 1, 1, 2, 3, 1, 3, 4]
def baseStart_2868712 : Nat := 118140960795 + 2868712 * 2 ^ 59
def prefixEnd_2868712 : Nat := 4983230072969 + 3 ^ 40 * 2868712 * 2
def baseEnd_2868712 : Nat := 982018743547256923204693

theorem tailTrace_2868712 : CollatzResearch.WordTrace tailWord_2868712 prefixEnd_2868712 982018743547256923204693 := by
  unfold tailWord_2868712
  simp only [CollatzResearch.WordTrace]
  refine ⟨52315261191576917924416195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69753681588769223899221593 52315261191576917924416195)
  ·
    refine ⟨78472891787365376886624293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52315261191576917924416195 78472891787365376886624293)
    ·
      refine ⟨14713667210131008166242055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78472891787365376886624293 14713667210131008166242055)
      ·
        refine ⟨22070500815196512249363083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14713667210131008166242055 22070500815196512249363083)
        ·
          refine ⟨33105751222794768374044625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22070500815196512249363083 33105751222794768374044625)
          ·
            refine ⟨24829313417096076280533469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33105751222794768374044625 24829313417096076280533469)
            ·
              refine ⟨9310992531411028605200051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24829313417096076280533469 9310992531411028605200051)
              ·
                refine ⟨13966488797116542907800077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9310992531411028605200051 13966488797116542907800077)
                ·
                  refine ⟨5237433298918703590425029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13966488797116542907800077 5237433298918703590425029)
                  ·
                    refine ⟨982018743547256923204693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5237433298918703590425029 982018743547256923204693)
                    ·
                      rfl

theorem cell22_2868712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 1, 3, 4].length) (baseStart_2868712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2868712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2868712 prefixEnd_2868712 := by exact prefixLift 2868712
  have htrace : WordTrace (prefixWord ++ tailWord_2868712) baseStart_2868712 baseEnd_2868712 := by
    simpa [prefixWord, tailWord_2868712, baseEnd_2868712] using wordTrace_append hprefix tailTrace_2868712
  have hstable : (prefixWord ++ tailWord_2868712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2868712).length < 2 ^ (prefixWord ++ tailWord_2868712).sum := by decide
  have hdescent : baseEnd_2868712 < baseStart_2868712 := by decide
  rcases family_descends (prefixWord ++ tailWord_2868712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2868847 : List Nat := [1, 1, 2, 1, 3, 2, 1, 2, 5, 4]
def baseStart_2868847 : Nat := 118140960795 + 2868847 * 2 ^ 59
def prefixEnd_2868847 : Nat := 4983230072969 + 3 ^ 40 * 2868847 * 2
def baseEnd_2868847 : Nat := 982064956806161571079279

theorem tailTrace_2868847 : CollatzResearch.WordTrace tailWord_2868847 prefixEnd_2868847 982064956806161571079279 := by
  unfold tailWord_2868847
  simp only [CollatzResearch.WordTrace]
  refine ⟨104635446237664753904996795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69756964158443169269997863 104635446237664753904996795)
  ·
    refine ⟨156953169356497130857495193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104635446237664753904996795 156953169356497130857495193)
    ·
      refine ⟨117714877017372848143121395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156953169356497130857495193 117714877017372848143121395)
      ·
        refine ⟨176572315526059272214682093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117714877017372848143121395 176572315526059272214682093)
        ·
          refine ⟨66214618322272227080505785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 176572315526059272214682093 66214618322272227080505785)
          ·
            refine ⟨49660963741704170310379339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66214618322272227080505785 49660963741704170310379339)
            ·
              refine ⟨74491445612556255465569009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49660963741704170310379339 74491445612556255465569009)
              ·
                refine ⟨55868584209417191599176757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74491445612556255465569009 55868584209417191599176757)
                ·
                  refine ⟨5237679769632861712422821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55868584209417191599176757 5237679769632861712422821)
                  ·
                    refine ⟨982064956806161571079279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5237679769632861712422821 982064956806161571079279)
                    ·
                      rfl

theorem cell22_2868847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 5, 4].length) (baseStart_2868847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2868847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2868847 prefixEnd_2868847 := by exact prefixLift 2868847
  have htrace : WordTrace (prefixWord ++ tailWord_2868847) baseStart_2868847 baseEnd_2868847 := by
    simpa [prefixWord, tailWord_2868847, baseEnd_2868847] using wordTrace_append hprefix tailTrace_2868847
  have hstable : (prefixWord ++ tailWord_2868847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2868847).length < 2 ^ (prefixWord ++ tailWord_2868847).sum := by decide
  have hdescent : baseEnd_2868847 < baseStart_2868847 := by decide
  rcases family_descends (prefixWord ++ tailWord_2868847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2868868 : List Nat := [2, 3, 2, 1, 4, 2, 2, 1, 5]
def baseStart_2868868 : Nat := 118140960795 + 2868868 * 2 ^ 59
def prefixEnd_2868868 : Nat := 4983230072969 + 3 ^ 40 * 2868868 * 2
def baseEnd_2868868 : Nat := 327357381845108172101405

theorem tailTrace_2868868 : CollatzResearch.WordTrace tailWord_2868868 prefixEnd_2868868 327357381845108172101405 := by
  unfold tailWord_2868868
  simp only [CollatzResearch.WordTrace]
  refine ⟨52318106085294337245755629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69757474780392449661007505 52318106085294337245755629)
  ·
    refine ⟨19619289781985376467158361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52318106085294337245755629 19619289781985376467158361)
    ·
      refine ⟨14714467336489032350368771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19619289781985376467158361 14714467336489032350368771)
      ·
        refine ⟨22071701004733548525553157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14714467336489032350368771 22071701004733548525553157)
        ·
          refine ⟨4138443938387540348541217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22071701004733548525553157 4138443938387540348541217)
          ·
            refine ⟨3103832953790655261405913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4138443938387540348541217 3103832953790655261405913)
            ·
              refine ⟨2327874715342991446054435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3103832953790655261405913 2327874715342991446054435)
              ·
                refine ⟨3491812073014487169081653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2327874715342991446054435 3491812073014487169081653)
                ·
                  refine ⟨327357381845108172101405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3491812073014487169081653 327357381845108172101405)
                  ·
                    rfl

theorem cell22_2868868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 2, 1, 5].length) (baseStart_2868868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2868868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2868868 prefixEnd_2868868 := by exact prefixLift 2868868
  have htrace : WordTrace (prefixWord ++ tailWord_2868868) baseStart_2868868 baseEnd_2868868 := by
    simpa [prefixWord, tailWord_2868868, baseEnd_2868868] using wordTrace_append hprefix tailTrace_2868868
  have hstable : (prefixWord ++ tailWord_2868868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2868868).length < 2 ^ (prefixWord ++ tailWord_2868868).sum := by decide
  have hdescent : baseEnd_2868868 < baseStart_2868868 := by decide
  rcases family_descends (prefixWord ++ tailWord_2868868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2868911 : List Nat := [1, 1, 2, 1, 2, 4, 4, 2, 2, 3]
def baseStart_2868911 : Nat := 118140960795 + 2868911 * 2 ^ 59
def prefixEnd_2868911 : Nat := 4983230072969 + 3 ^ 40 * 2868911 * 2
def baseEnd_2868911 : Nat := 982086865314086737479083

theorem tailTrace_2868911 : CollatzResearch.WordTrace tailWord_2868911 prefixEnd_2868911 982086865314086737479083 := by
  unfold tailWord_2868911
  simp only [CollatzResearch.WordTrace]
  refine ⟨104637780509432892835326587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69758520339621928556884391 104637780509432892835326587)
  ·
    refine ⟨156956670764149339252989881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104637780509432892835326587 156956670764149339252989881)
    ·
      refine ⟨117717503073112004439742411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156956670764149339252989881 117717503073112004439742411)
      ·
        refine ⟨176576254609668006659613617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117717503073112004439742411 176576254609668006659613617)
        ·
          refine ⟨132432190957251004994710213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176576254609668006659613617 132432190957251004994710213)
          ·
            refine ⟨24831035804484563436508165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 132432190957251004994710213 24831035804484563436508165)
            ·
              refine ⟨4655819213340855644345281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24831035804484563436508165 4655819213340855644345281)
              ·
                refine ⟨3491864410005641733258961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4655819213340855644345281 3491864410005641733258961)
                ·
                  refine ⟨2618898307504231299944221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3491864410005641733258961 2618898307504231299944221)
                  ·
                    refine ⟨982086865314086737479083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2618898307504231299944221 982086865314086737479083)
                    ·
                      rfl

theorem cell22_2868911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 4, 2, 2, 3].length) (baseStart_2868911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2868911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2868911 prefixEnd_2868911 := by exact prefixLift 2868911
  have htrace : WordTrace (prefixWord ++ tailWord_2868911) baseStart_2868911 baseEnd_2868911 := by
    simpa [prefixWord, tailWord_2868911, baseEnd_2868911] using wordTrace_append hprefix tailTrace_2868911
  have hstable : (prefixWord ++ tailWord_2868911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2868911).length < 2 ^ (prefixWord ++ tailWord_2868911).sum := by decide
  have hdescent : baseEnd_2868911 < baseStart_2868911 := by decide
  rcases family_descends (prefixWord ++ tailWord_2868911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2868924 : List Nat := [2, 2, 2, 3, 1, 2, 3, 7]
def baseStart_2868924 : Nat := 118140960795 + 2868924 * 2 ^ 59
def prefixEnd_2868924 : Nat := 4983230072969 + 3 ^ 40 * 2868924 * 2
def baseEnd_2868924 : Nat := 109121257275528781878227

theorem tailTrace_2868924 : CollatzResearch.WordTrace tailWord_2868924 prefixEnd_2868924 109121257275528781878227 := by
  unfold tailWord_2868924
  simp only [CollatzResearch.WordTrace]
  refine ⟨52319127329192898027774913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69758836438923864037033217 52319127329192898027774913)
  ·
    refine ⟨39239345496894673520831185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52319127329192898027774913 39239345496894673520831185)
    ·
      refine ⟨29429509122671005140623389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39239345496894673520831185 29429509122671005140623389)
      ·
        refine ⟨11036065921001626927733771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29429509122671005140623389 11036065921001626927733771)
        ·
          refine ⟨16554098881502440391600657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11036065921001626927733771 16554098881502440391600657)
          ·
            refine ⟨12415574161126830293700493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16554098881502440391600657 12415574161126830293700493)
            ·
              refine ⟨4655840310422561360137685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12415574161126830293700493 4655840310422561360137685)
              ·
                refine ⟨109121257275528781878227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4655840310422561360137685 109121257275528781878227)
                ·
                  rfl

theorem cell22_2868924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 3, 7].length) (baseStart_2868924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2868924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2868924 prefixEnd_2868924 := by exact prefixLift 2868924
  have htrace : WordTrace (prefixWord ++ tailWord_2868924) baseStart_2868924 baseEnd_2868924 := by
    simpa [prefixWord, tailWord_2868924, baseEnd_2868924] using wordTrace_append hprefix tailTrace_2868924
  have hstable : (prefixWord ++ tailWord_2868924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2868924).length < 2 ^ (prefixWord ++ tailWord_2868924).sum := by decide
  have hdescent : baseEnd_2868924 < baseStart_2868924 := by decide
  rcases family_descends (prefixWord ++ tailWord_2868924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2868930 : List Nat := [3, 5, 1, 2, 1, 1, 1, 2, 6]
def baseStart_2868930 : Nat := 118140960795 + 2868930 * 2 ^ 59
def prefixEnd_2868930 : Nat := 4983230072969 + 3 ^ 40 * 2868930 * 2
def baseEnd_2868930 : Nat := 327364456467459007084675

theorem tailTrace_2868930 : CollatzResearch.WordTrace tailWord_2868930 prefixEnd_2868930 327364456467459007084675 := by
  unfold tailWord_2868930
  simp only [CollatzResearch.WordTrace]
  refine ⟨26159618374091014770067061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69758982330909372720178829 26159618374091014770067061)
  ·
    refine ⟨2452464222571032634693787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26159618374091014770067061 2452464222571032634693787)
    ·
      refine ⟨3678696333856548952040681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2452464222571032634693787 3678696333856548952040681)
      ·
        refine ⟨2759022250392411714030511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3678696333856548952040681 2759022250392411714030511)
        ·
          refine ⟨4138533375588617571045767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2759022250392411714030511 4138533375588617571045767)
          ·
            refine ⟨6207800063382926356568651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4138533375588617571045767 6207800063382926356568651)
            ·
              refine ⟨9311700095074389534852977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6207800063382926356568651 9311700095074389534852977)
              ·
                refine ⟨6983775071305792151139733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9311700095074389534852977 6983775071305792151139733)
                ·
                  refine ⟨327364456467459007084675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6983775071305792151139733 327364456467459007084675)
                  ·
                    rfl

theorem cell22_2868930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_2868930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2868930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2868930 prefixEnd_2868930 := by exact prefixLift 2868930
  have htrace : WordTrace (prefixWord ++ tailWord_2868930) baseStart_2868930 baseEnd_2868930 := by
    simpa [prefixWord, tailWord_2868930, baseEnd_2868930] using wordTrace_append hprefix tailTrace_2868930
  have hstable : (prefixWord ++ tailWord_2868930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2868930).length < 2 ^ (prefixWord ++ tailWord_2868930).sum := by decide
  have hdescent : baseEnd_2868930 < baseStart_2868930 := by decide
  rcases family_descends (prefixWord ++ tailWord_2868930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2868973 : List Nat := [1, 5, 1, 2, 1, 3, 2, 1, 3, 3]
def baseStart_2868973 : Nat := 118140960795 + 2868973 * 2 ^ 59
def prefixEnd_2868973 : Nat := 4983230072969 + 3 ^ 40 * 2868973 * 2
def baseEnd_2868973 : Nat := 982108089181139242428893

theorem tailTrace_2868973 : CollatzResearch.WordTrace tailWord_2868973 prefixEnd_2868973 982108089181139242428893 := by
  unfold tailWord_2868973
  simp only [CollatzResearch.WordTrace]
  refine ⟨104640041835208277424083573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69760027890138851616055715 104640041835208277424083573)
  ·
    refine ⟨9810003922050776008507835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 104640041835208277424083573 9810003922050776008507835)
    ·
      refine ⟨14715005883076164012761753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9810003922050776008507835 14715005883076164012761753)
      ·
        refine ⟨11036254412307123009571315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14715005883076164012761753 11036254412307123009571315)
        ·
          refine ⟨16554381618460684514356973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11036254412307123009571315 16554381618460684514356973)
          ·
            refine ⟨6207893106922756692883865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16554381618460684514356973 6207893106922756692883865)
            ·
              refine ⟨4655919830192067519662899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6207893106922756692883865 4655919830192067519662899)
              ·
                refine ⟨6983879745288101279494349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4655919830192067519662899 6983879745288101279494349)
                ·
                  refine ⟨2618954904483037979810381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6983879745288101279494349 2618954904483037979810381)
                  ·
                    refine ⟨982108089181139242428893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2618954904483037979810381 982108089181139242428893)
                    ·
                      rfl

theorem cell22_2868973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 2, 1, 3, 3].length) (baseStart_2868973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2868973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2868973 prefixEnd_2868973 := by exact prefixLift 2868973
  have htrace : WordTrace (prefixWord ++ tailWord_2868973) baseStart_2868973 baseEnd_2868973 := by
    simpa [prefixWord, tailWord_2868973, baseEnd_2868973] using wordTrace_append hprefix tailTrace_2868973
  have hstable : (prefixWord ++ tailWord_2868973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2868973).length < 2 ^ (prefixWord ++ tailWord_2868973).sum := by decide
  have hdescent : baseEnd_2868973 < baseStart_2868973 := by decide
  rcases family_descends (prefixWord ++ tailWord_2868973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2868998 : List Nat := [6, 2, 2, 1, 2, 1, 1, 3, 4]
def baseStart_2868998 : Nat := 118140960795 + 2868998 * 2 ^ 59
def prefixEnd_2868998 : Nat := 4983230072969 + 3 ^ 40 * 2868998 * 2
def baseEnd_2868998 : Nat := 327372215730682503517939

theorem tailTrace_2868998 : CollatzResearch.WordTrace tailWord_2868998 prefixEnd_2868998 327372215730682503517939 := by
  unfold tailWord_2868998
  simp only [CollatzResearch.WordTrace]
  refine ⟨3270029801878678334179489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 69760635773411804462495765 3270029801878678334179489)
  ·
    refine ⟨2452522351409008750634617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3270029801878678334179489 2452522351409008750634617)
    ·
      refine ⟨1839391763556756562975963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2452522351409008750634617 1839391763556756562975963)
      ·
        refine ⟨2759087645335134844463945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1839391763556756562975963 2759087645335134844463945)
        ·
          refine ⟨2069315734001351133347959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2759087645335134844463945 2069315734001351133347959)
          ·
            refine ⟨3103973601002026700021939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2069315734001351133347959 3103973601002026700021939)
            ·
              refine ⟨4655960401503040050032909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3103973601002026700021939 4655960401503040050032909)
              ·
                refine ⟨1745985150563640018762341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4655960401503040050032909 1745985150563640018762341)
                ·
                  refine ⟨327372215730682503517939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1745985150563640018762341 327372215730682503517939)
                  ·
                    rfl

theorem cell22_2868998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_2868998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2868998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2868998 prefixEnd_2868998 := by exact prefixLift 2868998
  have htrace : WordTrace (prefixWord ++ tailWord_2868998) baseStart_2868998 baseEnd_2868998 := by
    simpa [prefixWord, tailWord_2868998, baseEnd_2868998] using wordTrace_append hprefix tailTrace_2868998
  have hstable : (prefixWord ++ tailWord_2868998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2868998).length < 2 ^ (prefixWord ++ tailWord_2868998).sum := by decide
  have hdescent : baseEnd_2868998 < baseStart_2868998 := by decide
  rcases family_descends (prefixWord ++ tailWord_2868998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2869016 : List Nat := [2, 1, 2, 3, 1, 1, 4, 3, 1, 4]
def baseStart_2869016 : Nat := 118140960795 + 2869016 * 2 ^ 59
def prefixEnd_2869016 : Nat := 4983230072969 + 3 ^ 40 * 2869016 * 2
def baseEnd_2869016 : Nat := 982122808959901463603761

theorem tailTrace_2869016 : CollatzResearch.WordTrace tailWord_2869016 prefixEnd_2869016 982122808959901463603761 := by
  unfold tailWord_2869016
  simp only [CollatzResearch.WordTrace]
  refine ⟨52320805087026247883949451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69761073449368330511932601 52320805087026247883949451)
  ·
    refine ⟨78481207630539371825924177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52320805087026247883949451 78481207630539371825924177)
    ·
      refine ⟨58860905722904528869443133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78481207630539371825924177 58860905722904528869443133)
      ·
        refine ⟨22072839646089198326041175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58860905722904528869443133 22072839646089198326041175)
        ·
          refine ⟨33109259469133797489061763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22072839646089198326041175 33109259469133797489061763)
          ·
            refine ⟨49663889203700696233592645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33109259469133797489061763 49663889203700696233592645)
            ·
              refine ⟨9311979225693880543798621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49663889203700696233592645 9311979225693880543798621)
              ·
                refine ⟨3491992209635205203924483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9311979225693880543798621 3491992209635205203924483)
                ·
                  refine ⟨5237988314452807805886725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3491992209635205203924483 5237988314452807805886725)
                  ·
                    refine ⟨982122808959901463603761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5237988314452807805886725 982122808959901463603761)
                    ·
                      rfl

theorem cell22_2869016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 3, 1, 4].length) (baseStart_2869016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2869016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2869016 prefixEnd_2869016 := by exact prefixLift 2869016
  have htrace : WordTrace (prefixWord ++ tailWord_2869016) baseStart_2869016 baseEnd_2869016 := by
    simpa [prefixWord, tailWord_2869016, baseEnd_2869016] using wordTrace_append hprefix tailTrace_2869016
  have hstable : (prefixWord ++ tailWord_2869016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2869016).length < 2 ^ (prefixWord ++ tailWord_2869016).sum := by decide
  have hdescent : baseEnd_2869016 < baseStart_2869016 := by decide
  rcases family_descends (prefixWord ++ tailWord_2869016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2869059 : List Nat := [1, 1, 1, 3, 1, 5, 2, 8]
def baseStart_2869059 : Nat := 118140960795 + 2869059 * 2 ^ 59
def prefixEnd_2869059 : Nat := 4983230072969 + 3 ^ 40 * 2869059 * 2
def baseEnd_2869059 : Nat := 109126392082073742753181

theorem tailTrace_2869059 : CollatzResearch.WordTrace tailWord_2869059 prefixEnd_2869059 109126392082073742753181 := by
  unfold tailWord_2869059
  simp only [CollatzResearch.WordTrace]
  refine ⟨104643178512896714111714231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69762119008597809407809487 104643178512896714111714231)
  ·
    refine ⟨156964767769345071167571347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104643178512896714111714231 156964767769345071167571347)
    ·
      refine ⟨235447151654017606751357021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156964767769345071167571347 235447151654017606751357021)
      ·
        refine ⟨88292681870256602531758883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 235447151654017606751357021 88292681870256602531758883)
        ·
          refine ⟨132439022805384903797638325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88292681870256602531758883 132439022805384903797638325)
          ·
            refine ⟨12416158388004834731028593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 132439022805384903797638325 12416158388004834731028593)
            ·
              refine ⟨9312118791003626048271445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12416158388004834731028593 9312118791003626048271445)
              ·
                refine ⟨109126392082073742753181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9312118791003626048271445 109126392082073742753181)
                ·
                  rfl

theorem cell22_2869059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 8].length) (baseStart_2869059 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2869059 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2869059 prefixEnd_2869059 := by exact prefixLift 2869059
  have htrace : WordTrace (prefixWord ++ tailWord_2869059) baseStart_2869059 baseEnd_2869059 := by
    simpa [prefixWord, tailWord_2869059, baseEnd_2869059] using wordTrace_append hprefix tailTrace_2869059
  have hstable : (prefixWord ++ tailWord_2869059).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2869059).length < 2 ^ (prefixWord ++ tailWord_2869059).sum := by decide
  have hdescent : baseEnd_2869059 < baseStart_2869059 := by decide
  rcases family_descends (prefixWord ++ tailWord_2869059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2869061 : List Nat := [1, 3, 1, 1, 1, 2, 6, 1, 2, 4]
def baseStart_2869061 : Nat := 118140960795 + 2869061 * 2 ^ 59
def prefixEnd_2869061 : Nat := 4983230072969 + 3 ^ 40 * 2869061 * 2
def baseEnd_2869061 : Nat := 982138213379536346228623

theorem tailTrace_2869061 : CollatzResearch.WordTrace tailWord_2869061 prefixEnd_2869061 982138213379536346228623 := by
  unfold tailWord_2869061
  simp only [CollatzResearch.WordTrace]
  refine ⟨104643251458889468453287037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69762167639259645635524691 104643251458889468453287037)
  ·
    refine ⟨39241219297083550669982639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104643251458889468453287037 39241219297083550669982639)
    ·
      refine ⟨58861828945625326004973959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39241219297083550669982639 58861828945625326004973959)
      ·
        refine ⟨88292743418437989007460939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58861828945625326004973959 88292743418437989007460939)
        ·
          refine ⟨132439115127656983511191409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88292743418437989007460939 132439115127656983511191409)
          ·
            refine ⟨99329336345742737633393557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132439115127656983511191409 99329336345742737633393557)
            ·
              refine ⟨4656062641206690826565323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 99329336345742737633393557 4656062641206690826565323)
              ·
                refine ⟨6984093961810036239847985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4656062641206690826565323 6984093961810036239847985)
                ·
                  refine ⟨5238070471357527179885989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6984093961810036239847985 5238070471357527179885989)
                  ·
                    refine ⟨982138213379536346228623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5238070471357527179885989 982138213379536346228623)
                    ·
                      rfl

theorem cell22_2869061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 6, 1, 2, 4].length) (baseStart_2869061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2869061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2869061 prefixEnd_2869061 := by exact prefixLift 2869061
  have htrace : WordTrace (prefixWord ++ tailWord_2869061) baseStart_2869061 baseEnd_2869061 := by
    simpa [prefixWord, tailWord_2869061, baseEnd_2869061] using wordTrace_append hprefix tailTrace_2869061
  have hstable : (prefixWord ++ tailWord_2869061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2869061).length < 2 ^ (prefixWord ++ tailWord_2869061).sum := by decide
  have hdescent : baseEnd_2869061 < baseStart_2869061 := by decide
  rcases family_descends (prefixWord ++ tailWord_2869061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2869089 : List Nat := [1, 2, 3, 1, 1, 1, 3, 1, 1, 8]
def baseStart_2869089 : Nat := 118140960795 + 2869089 * 2 ^ 59
def prefixEnd_2869089 : Nat := 4983230072969 + 3 ^ 40 * 2869089 * 2
def baseEnd_2869089 : Nat := 982147798351753606528537

theorem tailTrace_2869089 : CollatzResearch.WordTrace tailWord_2869089 prefixEnd_2869089 982147798351753606528537 := by
  unfold tailWord_2869089
  simp only [CollatzResearch.WordTrace]
  refine ⟨104644272702788029235306321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69762848468525352823537547 104644272702788029235306321)
  ·
    refine ⟨78483204527091021926479741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104644272702788029235306321 78483204527091021926479741)
    ·
      refine ⟨29431201697659133222429903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78483204527091021926479741 29431201697659133222429903)
      ·
        refine ⟨44146802546488699833644855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29431201697659133222429903 44146802546488699833644855)
        ·
          refine ⟨66220203819733049750467283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44146802546488699833644855 66220203819733049750467283)
          ·
            refine ⟨99330305729599574625700925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66220203819733049750467283 99330305729599574625700925)
            ·
              refine ⟨37248864648599840484637847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99330305729599574625700925 37248864648599840484637847)
              ·
                refine ⟨55873296972899760726956771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37248864648599840484637847 55873296972899760726956771)
                ·
                  refine ⟨83809945459349641090435157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55873296972899760726956771 83809945459349641090435157)
                  ·
                    refine ⟨982147798351753606528537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 83809945459349641090435157 982147798351753606528537)
                    ·
                      rfl

theorem cell22_2869089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 8].length) (baseStart_2869089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2869089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2869089 prefixEnd_2869089 := by exact prefixLift 2869089
  have htrace : WordTrace (prefixWord ++ tailWord_2869089) baseStart_2869089 baseEnd_2869089 := by
    simpa [prefixWord, tailWord_2869089, baseEnd_2869089] using wordTrace_append hprefix tailTrace_2869089
  have hstable : (prefixWord ++ tailWord_2869089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2869089).length < 2 ^ (prefixWord ++ tailWord_2869089).sum := by decide
  have hdescent : baseEnd_2869089 < baseStart_2869089 := by decide
  rcases family_descends (prefixWord ++ tailWord_2869089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2869104 : List Nat := [2, 1, 1, 1, 4, 1, 1, 2, 9]
def baseStart_2869104 : Nat := 118140960795 + 2869104 * 2 ^ 59
def prefixEnd_2869104 : Nat := 4983230072969 + 3 ^ 40 * 2869104 * 2
def baseEnd_2869104 : Nat := 327384311052766189134497

theorem tailTrace_2869104 : CollatzResearch.WordTrace tailWord_2869104 prefixEnd_2869104 327384311052766189134497 := by
  unfold tailWord_2869104
  simp only [CollatzResearch.WordTrace]
  refine ⟨52322409898866843398551183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69763213198489124531401577 52322409898866843398551183)
  ·
    refine ⟨78483614848300265097826775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52322409898866843398551183 78483614848300265097826775)
    ·
      refine ⟨117725422272450397646740163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78483614848300265097826775 117725422272450397646740163)
      ·
        refine ⟨176588133408675596470110245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117725422272450397646740163 176588133408675596470110245)
        ·
          refine ⟨33110275014126674338145671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 176588133408675596470110245 33110275014126674338145671)
          ·
            refine ⟨49665412521190011507218507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33110275014126674338145671 49665412521190011507218507)
            ·
              refine ⟨74498118781785017260827761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49665412521190011507218507 74498118781785017260827761)
              ·
                refine ⟨55873589086338762945620821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74498118781785017260827761 55873589086338762945620821)
                ·
                  refine ⟨327384311052766189134497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 55873589086338762945620821 327384311052766189134497)
                  ·
                    rfl

theorem cell22_2869104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 9].length) (baseStart_2869104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2869104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2869104 prefixEnd_2869104 := by exact prefixLift 2869104
  have htrace : WordTrace (prefixWord ++ tailWord_2869104) baseStart_2869104 baseEnd_2869104 := by
    simpa [prefixWord, tailWord_2869104, baseEnd_2869104] using wordTrace_append hprefix tailTrace_2869104
  have hstable : (prefixWord ++ tailWord_2869104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2869104).length < 2 ^ (prefixWord ++ tailWord_2869104).sum := by decide
  have hdescent : baseEnd_2869104 < baseStart_2869104 := by decide
  rcases family_descends (prefixWord ++ tailWord_2869104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2869110 : List Nat := [5, 1, 1, 3, 2, 1, 3, 6]
def baseStart_2869110 : Nat := 118140960795 + 2869110 * 2 ^ 59
def prefixEnd_2869110 : Nat := 4983230072969 + 3 ^ 40 * 2869110 * 2
def baseEnd_2869110 : Nat := 109128331897879616861497

theorem tailTrace_2869110 : CollatzResearch.WordTrace tailWord_2869110 prefixEnd_2869110 109128331897879616861497 := by
  unfold tailWord_2869110
  simp only [CollatzResearch.WordTrace]
  refine ⟨6540314914731996863863799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 69763359090474633214547189 6540314914731996863863799)
  ·
    refine ⟨9810472372097995295795699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6540314914731996863863799 9810472372097995295795699)
    ·
      refine ⟨14715708558146992943693549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9810472372097995295795699 14715708558146992943693549)
      ·
        refine ⟨5518390709305122353885081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14715708558146992943693549 5518390709305122353885081)
        ·
          refine ⟨4138793031978841765413811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5518390709305122353885081 4138793031978841765413811)
          ·
            refine ⟨6208189547968262648120717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4138793031978841765413811 6208189547968262648120717)
            ·
              refine ⟨2328071080488098493045269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6208189547968262648120717 2328071080488098493045269)
              ·
                refine ⟨109128331897879616861497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2328071080488098493045269 109128331897879616861497)
                ·
                  rfl

theorem cell22_2869110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 3, 6].length) (baseStart_2869110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2869110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2869110 prefixEnd_2869110 := by exact prefixLift 2869110
  have htrace : WordTrace (prefixWord ++ tailWord_2869110) baseStart_2869110 baseEnd_2869110 := by
    simpa [prefixWord, tailWord_2869110, baseEnd_2869110] using wordTrace_append hprefix tailTrace_2869110
  have hstable : (prefixWord ++ tailWord_2869110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2869110).length < 2 ^ (prefixWord ++ tailWord_2869110).sum := by decide
  have hdescent : baseEnd_2869110 < baseStart_2869110 := by decide
  rcases family_descends (prefixWord ++ tailWord_2869110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2869119 : List Nat := [1, 1, 2, 2, 1, 1, 3, 1, 3, 7]
def baseStart_2869119 : Nat := 118140960795 + 2869119 * 2 ^ 59
def prefixEnd_2869119 : Nat := 4983230072969 + 3 ^ 40 * 2869119 * 2
def baseEnd_2869119 : Nat := 982158067964843528278445

theorem tailTrace_2869119 : CollatzResearch.WordTrace tailWord_2869119 prefixEnd_2869119 982158067964843528278445 := by
  unfold tailWord_2869119
  simp only [CollatzResearch.WordTrace]
  refine ⟨104645366892679344358898411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69763577928452896239265607 104645366892679344358898411)
  ·
    refine ⟨156968050339019016538347617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104645366892679344358898411 156968050339019016538347617)
    ·
      refine ⟨117726037754264262403760713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156968050339019016538347617 117726037754264262403760713)
      ·
        refine ⟨88294528315698196802820535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117726037754264262403760713 88294528315698196802820535)
        ·
          refine ⟨132441792473547295204230803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88294528315698196802820535 132441792473547295204230803)
          ·
            refine ⟨198662688710320942806346205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132441792473547295204230803 198662688710320942806346205)
            ·
              refine ⟨74498508266370353552379827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 198662688710320942806346205 74498508266370353552379827)
              ·
                refine ⟨111747762399555530328569741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74498508266370353552379827 111747762399555530328569741)
                ·
                  refine ⟨41905410899833323873213653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 111747762399555530328569741 41905410899833323873213653)
                  ·
                    refine ⟨982158067964843528278445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41905410899833323873213653 982158067964843528278445)
                    ·
                      rfl

theorem cell22_2869119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 3, 7].length) (baseStart_2869119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2869119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2869119 prefixEnd_2869119 := by exact prefixLift 2869119
  have htrace : WordTrace (prefixWord ++ tailWord_2869119) baseStart_2869119 baseEnd_2869119 := by
    simpa [prefixWord, tailWord_2869119, baseEnd_2869119] using wordTrace_append hprefix tailTrace_2869119
  have hstable : (prefixWord ++ tailWord_2869119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2869119).length < 2 ^ (prefixWord ++ tailWord_2869119).sum := by decide
  have hdescent : baseEnd_2869119 < baseStart_2869119 := by decide
  rcases family_descends (prefixWord ++ tailWord_2869119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2869125 : List Nat := [1, 3, 1, 1, 3, 2, 4, 3, 1, 3]
def baseStart_2869125 : Nat := 118140960795 + 2869125 * 2 ^ 59
def prefixEnd_2869125 : Nat := 4983230072969 + 3 ^ 40 * 2869125 * 2
def baseEnd_2869125 : Nat := 982160121887461512628427

theorem tailTrace_2869125 : CollatzResearch.WordTrace tailWord_2869125 prefixEnd_2869125 982160121887461512628427 := by
  unfold tailWord_2869125
  simp only [CollatzResearch.WordTrace]
  refine ⟨104645585730657607383616829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69763723820438404922411219 104645585730657607383616829)
  ·
    refine ⟨39242094648996602768856311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104645585730657607383616829 39242094648996602768856311)
    ·
      refine ⟨58863141973494904153284467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39242094648996602768856311 58863141973494904153284467)
      ·
        refine ⟨88294712960242356229926701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58863141973494904153284467 88294712960242356229926701)
        ·
          refine ⟨33110517360090883586222513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88294712960242356229926701 33110517360090883586222513)
          ·
            refine ⟨24832888020068162689666885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33110517360090883586222513 24832888020068162689666885)
            ·
              refine ⟨4656166503762780504312541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24832888020068162689666885 4656166503762780504312541)
              ·
                refine ⟨1746062438911042689117203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4656166503762780504312541 1746062438911042689117203)
                ·
                  refine ⟨2619093658366564033675805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1746062438911042689117203 2619093658366564033675805)
                  ·
                    refine ⟨982160121887461512628427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2619093658366564033675805 982160121887461512628427)
                    ·
                      rfl

theorem cell22_2869125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 4, 3, 1, 3].length) (baseStart_2869125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2869125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2869125 prefixEnd_2869125 := by exact prefixLift 2869125
  have htrace : WordTrace (prefixWord ++ tailWord_2869125) baseStart_2869125 baseEnd_2869125 := by
    simpa [prefixWord, tailWord_2869125, baseEnd_2869125] using wordTrace_append hprefix tailTrace_2869125
  have hstable : (prefixWord ++ tailWord_2869125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2869125).length < 2 ^ (prefixWord ++ tailWord_2869125).sum := by decide
  have hdescent : baseEnd_2869125 < baseStart_2869125 := by decide
  rcases family_descends (prefixWord ++ tailWord_2869125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2869138 : List Nat := [3, 2, 3, 2, 1, 2, 1, 1, 7]
def baseStart_2869138 : Nat := 118140960795 + 2869138 * 2 ^ 59
def prefixEnd_2869138 : Nat := 4983230072969 + 3 ^ 40 * 2869138 * 2
def baseEnd_2869138 : Nat := 327388190684377937351129

theorem tailTrace_2869138 : CollatzResearch.WordTrace tailWord_2869138 prefixEnd_2869138 327388190684377937351129 := by
  unfold tailWord_2869138
  simp only [CollatzResearch.WordTrace]
  refine ⟨26161514969902627650960017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69764039919740340402560045 26161514969902627650960017)
  ·
    refine ⟨19621136227426970738220013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26161514969902627650960017 19621136227426970738220013)
    ·
      refine ⟨7357926085285114026832505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19621136227426970738220013 7357926085285114026832505)
      ·
        refine ⟨5518444563963835520124379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7357926085285114026832505 5518444563963835520124379)
        ·
          refine ⟨8277666845945753280186569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5518444563963835520124379 8277666845945753280186569)
          ·
            refine ⟨6208250134459314960139927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8277666845945753280186569 6208250134459314960139927)
            ·
              refine ⟨9312375201688972440209891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6208250134459314960139927 9312375201688972440209891)
              ·
                refine ⟨13968562802533458660314837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9312375201688972440209891 13968562802533458660314837)
                ·
                  refine ⟨327388190684377937351129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13968562802533458660314837 327388190684377937351129)
                  ·
                    rfl

theorem cell22_2869138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 1, 7].length) (baseStart_2869138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2869138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2869138 prefixEnd_2869138 := by exact prefixLift 2869138
  have htrace : WordTrace (prefixWord ++ tailWord_2869138) baseStart_2869138 baseEnd_2869138 := by
    simpa [prefixWord, tailWord_2869138, baseEnd_2869138] using wordTrace_append hprefix tailTrace_2869138
  have hstable : (prefixWord ++ tailWord_2869138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2869138).length < 2 ^ (prefixWord ++ tailWord_2869138).sum := by decide
  have hdescent : baseEnd_2869138 < baseStart_2869138 := by decide
  rcases family_descends (prefixWord ++ tailWord_2869138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2869198 : List Nat := [4, 1, 1, 1, 2, 2, 1, 3, 4, 3]
def baseStart_2869198 : Nat := 118140960795 + 2869198 * 2 ^ 59
def prefixEnd_2869198 : Nat := 4983230072969 + 3 ^ 40 * 2869198 * 2
def baseEnd_2869198 : Nat := 982185111279313655553203

theorem tailTrace_2869198 : CollatzResearch.WordTrace tailWord_2869198 prefixEnd_2869198 982185111279313655553203 := by
  unfold tailWord_2869198
  simp only [CollatzResearch.WordTrace]
  refine ⟨13081031032424142606378031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69765498839595427234016165 13081031032424142606378031)
  ·
    refine ⟨19621546548636213909567047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13081031032424142606378031 19621546548636213909567047)
    ·
      refine ⟨29432319822954320864350571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19621546548636213909567047 29432319822954320864350571)
      ·
        refine ⟨44148479734431481296525857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29432319822954320864350571 44148479734431481296525857)
        ·
          refine ⟨33111359800823610972394393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44148479734431481296525857 33111359800823610972394393)
          ·
            refine ⟨24833519850617708229295795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33111359800823610972394393 24833519850617708229295795)
            ·
              refine ⟨37250279775926562343943693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24833519850617708229295795 37250279775926562343943693)
              ·
                refine ⟨13968854915972460878978885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37250279775926562343943693 13968854915972460878978885)
                ·
                  refine ⟨2619160296744836414808541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13968854915972460878978885 2619160296744836414808541)
                  ·
                    refine ⟨982185111279313655553203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2619160296744836414808541 982185111279313655553203)
                    ·
                      rfl

theorem cell22_2869198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 3, 4, 3].length) (baseStart_2869198 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2869198 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2869198 prefixEnd_2869198 := by exact prefixLift 2869198
  have htrace : WordTrace (prefixWord ++ tailWord_2869198) baseStart_2869198 baseEnd_2869198 := by
    simpa [prefixWord, tailWord_2869198, baseEnd_2869198] using wordTrace_append hprefix tailTrace_2869198
  have hstable : (prefixWord ++ tailWord_2869198).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2869198).length < 2 ^ (prefixWord ++ tailWord_2869198).sum := by decide
  have hdescent : baseEnd_2869198 < baseStart_2869198 := by decide
  rcases family_descends (prefixWord ++ tailWord_2869198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2869215 : List Nat := [1, 1, 2, 3, 4, 2, 1, 3, 2, 3]
def baseStart_2869215 : Nat := 118140960795 + 2869215 * 2 ^ 59
def prefixEnd_2869215 : Nat := 4983230072969 + 3 ^ 40 * 2869215 * 2
def baseEnd_2869215 : Nat := 982190930726731277878151

theorem tailTrace_2869215 : CollatzResearch.WordTrace tailWord_2869215 prefixEnd_2869215 982190930726731277878151 := by
  unfold tailWord_2869215
  simp only [CollatzResearch.WordTrace]
  refine ⟨104648868300331552754393099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69765912200221035169595399 104648868300331552754393099)
  ·
    refine ⟨156973302450497329131589649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104648868300331552754393099 156973302450497329131589649)
    ·
      refine ⟨117729976837872996848692237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156973302450497329131589649 117729976837872996848692237)
      ·
        refine ⟨44148741314202373818259589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117729976837872996848692237 44148741314202373818259589)
        ·
          refine ⟨8277888996412945090923673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44148741314202373818259589 8277888996412945090923673)
          ·
            refine ⟨6208416747309708818192755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8277888996412945090923673 6208416747309708818192755)
            ·
              refine ⟨9312625120964563227289133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6208416747309708818192755 9312625120964563227289133)
              ·
                refine ⟨3492234420361711210233425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9312625120964563227289133 3492234420361711210233425)
                ·
                  refine ⟨2619175815271283407675069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3492234420361711210233425 2619175815271283407675069)
                  ·
                    refine ⟨982190930726731277878151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2619175815271283407675069 982190930726731277878151)
                    ·
                      rfl

theorem cell22_2869215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 3, 2, 3].length) (baseStart_2869215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2869215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2869215 prefixEnd_2869215 := by exact prefixLift 2869215
  have htrace : WordTrace (prefixWord ++ tailWord_2869215) baseStart_2869215 baseEnd_2869215 := by
    simpa [prefixWord, tailWord_2869215, baseEnd_2869215] using wordTrace_append hprefix tailTrace_2869215
  have hstable : (prefixWord ++ tailWord_2869215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2869215).length < 2 ^ (prefixWord ++ tailWord_2869215).sum := by decide
  have hdescent : baseEnd_2869215 < baseStart_2869215 := by decide
  rcases family_descends (prefixWord ++ tailWord_2869215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2869230 : List Nat := [4, 1, 2, 1, 3, 2, 2, 1, 2, 4]
def baseStart_2869230 : Nat := 118140960795 + 2869230 * 2 ^ 59
def prefixEnd_2869230 : Nat := 4983230072969 + 3 ^ 40 * 2869230 * 2
def baseEnd_2869230 : Nat := 982196065533276238753105

theorem tailTrace_2869230 : CollatzResearch.WordTrace tailWord_2869230 prefixEnd_2869230 982196065533276238753105 := by
  unfold tailWord_2869230
  simp only [CollatzResearch.WordTrace]
  refine ⟨13081176924409651289523643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69766276930184806877459429 13081176924409651289523643)
  ·
    refine ⟨19621765386614476934285465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13081176924409651289523643 19621765386614476934285465)
    ·
      refine ⟨14716324039960857700714099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19621765386614476934285465 14716324039960857700714099)
      ·
        refine ⟨22074486059941286551071149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14716324039960857700714099 22074486059941286551071149)
        ·
          refine ⟨8277932272477982456651681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22074486059941286551071149 8277932272477982456651681)
          ·
            refine ⟨6208449204358486842488761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8277932272477982456651681 6208449204358486842488761)
            ·
              refine ⟨4656336903268865131866571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6208449204358486842488761 4656336903268865131866571)
              ·
                refine ⟨6984505354903297697799857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4656336903268865131866571 6984505354903297697799857)
                ·
                  refine ⟨5238379016177473273349893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6984505354903297697799857 5238379016177473273349893)
                  ·
                    refine ⟨982196065533276238753105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5238379016177473273349893 982196065533276238753105)
                    ·
                      rfl

theorem cell22_2869230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 2, 1, 2, 4].length) (baseStart_2869230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2869230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2869230 prefixEnd_2869230 := by exact prefixLift 2869230
  have htrace : WordTrace (prefixWord ++ tailWord_2869230) baseStart_2869230 baseEnd_2869230 := by
    simpa [prefixWord, tailWord_2869230, baseEnd_2869230] using wordTrace_append hprefix tailTrace_2869230
  have hstable : (prefixWord ++ tailWord_2869230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2869230).length < 2 ^ (prefixWord ++ tailWord_2869230).sum := by decide
  have hdescent : baseEnd_2869230 < baseStart_2869230 := by decide
  rcases family_descends (prefixWord ++ tailWord_2869230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2869294 : List Nat := [4, 1, 3, 1, 1, 3, 2, 3, 1, 3]
def baseStart_2869294 : Nat := 118140960795 + 2869294 * 2 ^ 59
def prefixEnd_2869294 : Nat := 4983230072969 + 3 ^ 40 * 2869294 * 2
def baseEnd_2869294 : Nat := 982217974041201405152909

theorem tailTrace_2869294 : CollatzResearch.WordTrace tailWord_2869294 prefixEnd_2869294 982217974041201405152909 := by
  unfold tailWord_2869294
  simp only [CollatzResearch.WordTrace]
  refine ⟨13081468708380668655814867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69767833111363566164345957 13081468708380668655814867)
  ·
    refine ⟨19622203062571002983722301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13081468708380668655814867 19622203062571002983722301)
    ·
      refine ⟨7358326148464126118895863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19622203062571002983722301 7358326148464126118895863)
      ·
        refine ⟨11037489222696189178343795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7358326148464126118895863 11037489222696189178343795)
        ·
          refine ⟨16556233834044283767515693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11037489222696189178343795 16556233834044283767515693)
          ·
            refine ⟨6208587687766606412818385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16556233834044283767515693 6208587687766606412818385)
            ·
              refine ⟨4656440765824954809613789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6208587687766606412818385 4656440765824954809613789)
              ·
                refine ⟨1746165287184358053605171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4656440765824954809613789 1746165287184358053605171)
                ·
                  refine ⟨2619247930776537080407757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1746165287184358053605171 2619247930776537080407757)
                  ·
                    refine ⟨982217974041201405152909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2619247930776537080407757 982217974041201405152909)
                    ·
                      rfl

theorem cell22_2869294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 2, 3, 1, 3].length) (baseStart_2869294 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2869294 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2869294 prefixEnd_2869294 := by exact prefixLift 2869294
  have htrace : WordTrace (prefixWord ++ tailWord_2869294) baseStart_2869294 baseEnd_2869294 := by
    simpa [prefixWord, tailWord_2869294, baseEnd_2869294] using wordTrace_append hprefix tailTrace_2869294
  have hstable : (prefixWord ++ tailWord_2869294).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2869294).length < 2 ^ (prefixWord ++ tailWord_2869294).sum := by decide
  have hdescent : baseEnd_2869294 < baseStart_2869294 := by decide
  rcases family_descends (prefixWord ++ tailWord_2869294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2869348 : List Nat := [2, 3, 1, 1, 2, 1, 4, 1, 1, 6]
def baseStart_2869348 : Nat := 118140960795 + 2869348 * 2 ^ 59
def prefixEnd_2869348 : Nat := 4983230072969 + 3 ^ 40 * 2869348 * 2
def baseEnd_2869348 : Nat := 982236459344763264302743

theorem tailTrace_2869348 : CollatzResearch.WordTrace tailWord_2869348 prefixEnd_2869348 982236459344763264302743 := by
  unfold tailWord_2869348
  simp only [CollatzResearch.WordTrace]
  refine ⟨52326859604424858234492349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69769146139233144312656465 52326859604424858234492349)
  ·
    refine ⟨19622572351659321837934631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52326859604424858234492349 19622572351659321837934631)
    ·
      refine ⟨29433858527488982756901947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19622572351659321837934631 29433858527488982756901947)
      ·
        refine ⟨44150787791233474135352921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29433858527488982756901947 44150787791233474135352921)
        ·
          refine ⟨33113090843425105601514691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44150787791233474135352921 33113090843425105601514691)
          ·
            refine ⟨49669636265137658402272037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33113090843425105601514691 49669636265137658402272037)
            ·
              refine ⟨9313056799713310950426007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49669636265137658402272037 9313056799713310950426007)
              ·
                refine ⟨13969585199569966425639011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9313056799713310950426007 13969585199569966425639011)
                ·
                  refine ⟨20954377799354949638458517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13969585199569966425639011 20954377799354949638458517)
                  ·
                    refine ⟨982236459344763264302743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20954377799354949638458517 982236459344763264302743)
                    ·
                      rfl

theorem cell22_2869348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 1, 1, 6].length) (baseStart_2869348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2869348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2869348 prefixEnd_2869348 := by exact prefixLift 2869348
  have htrace : WordTrace (prefixWord ++ tailWord_2869348) baseStart_2869348 baseEnd_2869348 := by
    simpa [prefixWord, tailWord_2869348, baseEnd_2869348] using wordTrace_append hprefix tailTrace_2869348
  have hstable : (prefixWord ++ tailWord_2869348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2869348).length < 2 ^ (prefixWord ++ tailWord_2869348).sum := by decide
  have hdescent : baseEnd_2869348 < baseStart_2869348 := by decide
  rcases family_descends (prefixWord ++ tailWord_2869348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2869384 : List Nat := [2, 1, 3, 4, 1, 1, 4, 1, 2, 3]
def baseStart_2869384 : Nat := 118140960795 + 2869384 * 2 ^ 59
def prefixEnd_2869384 : Nat := 4983230072969 + 3 ^ 40 * 2869384 * 2
def baseEnd_2869384 : Nat := 982248782880471170402633

theorem tailTrace_2869384 : CollatzResearch.WordTrace tailWord_2869384 prefixEnd_2869384 982248782880471170402633 := by
  unfold tailWord_2869384
  simp only [CollatzResearch.WordTrace]
  refine ⟨52327516118359647308647603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69770021491146196411530137 52327516118359647308647603)
  ·
    refine ⟨78491274177539470962971405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52327516118359647308647603 78491274177539470962971405)
    ·
      refine ⟨29434227816577301611114277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78491274177539470962971405 29434227816577301611114277)
      ·
        refine ⟨5518917715608244052083927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29434227816577301611114277 5518917715608244052083927)
        ·
          refine ⟨8278376573412366078125891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5518917715608244052083927 8278376573412366078125891)
          ·
            refine ⟨12417564860118549117188837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8278376573412366078125891 12417564860118549117188837)
            ·
              refine ⟨2328293411272227959472907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12417564860118549117188837 2328293411272227959472907)
              ·
                refine ⟨3492440116908341939209361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2328293411272227959472907 3492440116908341939209361)
                ·
                  refine ⟨2619330087681256454407021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3492440116908341939209361 2619330087681256454407021)
                  ·
                    refine ⟨982248782880471170402633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2619330087681256454407021 982248782880471170402633)
                    ·
                      rfl

theorem cell22_2869384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 4, 1, 2, 3].length) (baseStart_2869384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2869384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2869384 prefixEnd_2869384 := by exact prefixLift 2869384
  have htrace : WordTrace (prefixWord ++ tailWord_2869384) baseStart_2869384 baseEnd_2869384 := by
    simpa [prefixWord, tailWord_2869384, baseEnd_2869384] using wordTrace_append hprefix tailTrace_2869384
  have hstable : (prefixWord ++ tailWord_2869384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2869384).length < 2 ^ (prefixWord ++ tailWord_2869384).sum := by decide
  have hdescent : baseEnd_2869384 < baseStart_2869384 := by decide
  rcases family_descends (prefixWord ++ tailWord_2869384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2869423 : List Nat := [1, 1, 2, 1, 2, 3, 1, 4, 2, 5]
def baseStart_2869423 : Nat := 118140960795 + 2869423 * 2 ^ 59
def prefixEnd_2869423 : Nat := 4983230072969 + 3 ^ 40 * 2869423 * 2
def baseEnd_2869423 : Nat := 982262133377488068677513

theorem tailTrace_2869423 : CollatzResearch.WordTrace tailWord_2869423 prefixEnd_2869423 982262133377488068677513 := by
  unfold tailWord_2869423
  simp only [CollatzResearch.WordTrace]
  refine ⟨104656454683578004277964923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69770969789052002851976615 104656454683578004277964923)
  ·
    refine ⟨156984682025367006416947385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104656454683578004277964923 156984682025367006416947385)
    ·
      refine ⟨117738511519025254812710539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156984682025367006416947385 117738511519025254812710539)
      ·
        refine ⟨176607767278537882219065809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117738511519025254812710539 176607767278537882219065809)
        ·
          refine ⟨132455825458903411664299357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176607767278537882219065809 132455825458903411664299357)
          ·
            refine ⟨49670934547088779374112259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 132455825458903411664299357 49670934547088779374112259)
            ·
              refine ⟨74506401820633169061168389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49670934547088779374112259 74506401820633169061168389)
              ·
                refine ⟨13969950341368719198969073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74506401820633169061168389 13969950341368719198969073)
                ·
                  refine ⟨10477462756026539399226805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13969950341368719198969073 10477462756026539399226805)
                  ·
                    refine ⟨982262133377488068677513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10477462756026539399226805 982262133377488068677513)
                    ·
                      rfl

theorem cell22_2869423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 4, 2, 5].length) (baseStart_2869423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2869423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2869423 prefixEnd_2869423 := by exact prefixLift 2869423
  have htrace : WordTrace (prefixWord ++ tailWord_2869423) baseStart_2869423 baseEnd_2869423 := by
    simpa [prefixWord, tailWord_2869423, baseEnd_2869423] using wordTrace_append hprefix tailTrace_2869423
  have hstable : (prefixWord ++ tailWord_2869423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2869423).length < 2 ^ (prefixWord ++ tailWord_2869423).sum := by decide
  have hdescent : baseEnd_2869423 < baseStart_2869423 := by decide
  rcases family_descends (prefixWord ++ tailWord_2869423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2869440 : List Nat := [2, 1, 1, 2, 5, 2, 1, 1, 2, 5]
def baseStart_2869440 : Nat := 118140960795 + 2869440 * 2 ^ 59
def prefixEnd_2869440 : Nat := 4983230072969 + 3 ^ 40 * 2869440 * 2
def baseEnd_2869440 : Nat := 982267952824905691002461

theorem tailTrace_2869440 : CollatzResearch.WordTrace tailWord_2869440 prefixEnd_2869440 982267952824905691002461 := by
  unfold tailWord_2869440
  simp only [CollatzResearch.WordTrace]
  refine ⟨52328537362258208090666887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69771383149677610787555849 52328537362258208090666887)
  ·
    refine ⟨78492806043387312136000331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52328537362258208090666887 78492806043387312136000331)
    ·
      refine ⟨117739209065080968204000497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78492806043387312136000331 117739209065080968204000497)
      ·
        refine ⟨88304406798810726153000373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117739209065080968204000497 88304406798810726153000373)
        ·
          refine ⟨8278538137388505576843785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 88304406798810726153000373 8278538137388505576843785)
          ·
            refine ⟨6208903603041379182632839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8278538137388505576843785 6208903603041379182632839)
            ·
              refine ⟨9313355404562068773949259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6208903603041379182632839 9313355404562068773949259)
              ·
                refine ⟨13970033106843103160923889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9313355404562068773949259 13970033106843103160923889)
                ·
                  refine ⟨10477524830132327370692917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13970033106843103160923889 10477524830132327370692917)
                  ·
                    refine ⟨982267952824905691002461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10477524830132327370692917 982267952824905691002461)
                    ·
                      rfl

theorem cell22_2869440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 1, 2, 5].length) (baseStart_2869440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2869440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2869440 prefixEnd_2869440 := by exact prefixLift 2869440
  have htrace : WordTrace (prefixWord ++ tailWord_2869440) baseStart_2869440 baseEnd_2869440 := by
    simpa [prefixWord, tailWord_2869440, baseEnd_2869440] using wordTrace_append hprefix tailTrace_2869440
  have hstable : (prefixWord ++ tailWord_2869440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2869440).length < 2 ^ (prefixWord ++ tailWord_2869440).sum := by decide
  have hdescent : baseEnd_2869440 < baseStart_2869440 := by decide
  rcases family_descends (prefixWord ++ tailWord_2869440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2869455 : List Nat := [1, 1, 2, 1, 1, 3, 4, 4, 1, 4]
def baseStart_2869455 : Nat := 118140960795 + 2869455 * 2 ^ 59
def prefixEnd_2869455 : Nat := 4983230072969 + 3 ^ 40 * 2869455 * 2
def baseEnd_2869455 : Nat := 982273087631450651877415

theorem tailTrace_2869455 : CollatzResearch.WordTrace tailWord_2869455 prefixEnd_2869455 982273087631450651877415 := by
  unfold tailWord_2869455
  simp only [CollatzResearch.WordTrace]
  refine ⟨104657621819462073743129819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69771747879641382495419879 104657621819462073743129819)
  ·
    refine ⟨156986432729193110614694729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104657621819462073743129819 156986432729193110614694729)
    ·
      refine ⟨117739824546894832961021047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156986432729193110614694729 117739824546894832961021047)
      ·
        refine ⟨176609736820342249441531571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117739824546894832961021047 176609736820342249441531571)
        ·
          refine ⟨264914605230513374162297357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176609736820342249441531571 264914605230513374162297357)
          ·
            refine ⟨99342976961442515310861509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 264914605230513374162297357 99342976961442515310861509)
            ·
              refine ⟨18626808180270471620786533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 99342976961442515310861509 18626808180270471620786533)
              ·
                refine ⟨3492526533800713428897475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18626808180270471620786533 3492526533800713428897475)
                ·
                  refine ⟨5238789800701070143346213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3492526533800713428897475 5238789800701070143346213)
                  ·
                    refine ⟨982273087631450651877415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5238789800701070143346213 982273087631450651877415)
                    ·
                      rfl

theorem cell22_2869455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 4, 1, 4].length) (baseStart_2869455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2869455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2869455 prefixEnd_2869455 := by exact prefixLift 2869455
  have htrace : WordTrace (prefixWord ++ tailWord_2869455) baseStart_2869455 baseEnd_2869455 := by
    simpa [prefixWord, tailWord_2869455, baseEnd_2869455] using wordTrace_append hprefix tailTrace_2869455
  have hstable : (prefixWord ++ tailWord_2869455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2869455).length < 2 ^ (prefixWord ++ tailWord_2869455).sum := by decide
  have hdescent : baseEnd_2869455 < baseStart_2869455 := by decide
  rcases family_descends (prefixWord ++ tailWord_2869455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2869487 : List Nat := [1, 1, 2, 1, 6, 1, 2, 4, 4]
def baseStart_2869487 : Nat := 118140960795 + 2869487 * 2 ^ 59
def prefixEnd_2869487 : Nat := 4983230072969 + 3 ^ 40 * 2869487 * 2
def baseEnd_2869487 : Nat := 327428013961804411692439

theorem tailTrace_2869487 : CollatzResearch.WordTrace tailWord_2869487 prefixEnd_2869487 327428013961804411692439 := by
  unfold tailWord_2869487
  simp only [CollatzResearch.WordTrace]
  refine ⟨104658788955346143208294715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69772525970230762138863143 104658788955346143208294715)
  ·
    refine ⟨156988183433019214812442073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104658788955346143208294715 156988183433019214812442073)
    ·
      refine ⟨117741137574764411109331555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156988183433019214812442073 117741137574764411109331555)
      ·
        refine ⟨176611706362146616663997333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117741137574764411109331555 176611706362146616663997333)
        ·
          refine ⟨8278673735725622656124875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 176611706362146616663997333 8278673735725622656124875)
          ·
            refine ⟨12418010603588433984187313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8278673735725622656124875 12418010603588433984187313)
            ·
              refine ⟨9313507952691325488140485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12418010603588433984187313 9313507952691325488140485)
              ·
                refine ⟨1746282741129623529026341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9313507952691325488140485 1746282741129623529026341)
                ·
                  refine ⟨327428013961804411692439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1746282741129623529026341 327428013961804411692439)
                  ·
                    rfl

theorem cell22_2869487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 4, 4].length) (baseStart_2869487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2869487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2869487 prefixEnd_2869487 := by exact prefixLift 2869487
  have htrace : WordTrace (prefixWord ++ tailWord_2869487) baseStart_2869487 baseEnd_2869487 := by
    simpa [prefixWord, tailWord_2869487, baseEnd_2869487] using wordTrace_append hprefix tailTrace_2869487
  have hstable : (prefixWord ++ tailWord_2869487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2869487).length < 2 ^ (prefixWord ++ tailWord_2869487).sum := by decide
  have hdescent : baseEnd_2869487 < baseStart_2869487 := by decide
  rcases family_descends (prefixWord ++ tailWord_2869487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2869500 : List Nat := [2, 2, 2, 1, 4, 1, 1, 2, 1, 6]
def baseStart_2869500 : Nat := 118140960795 + 2869500 * 2 ^ 59
def prefixEnd_2869500 : Nat := 4983230072969 + 3 ^ 40 * 2869500 * 2
def baseEnd_2869500 : Nat := 982288492051085534502277

theorem tailTrace_2869500 : CollatzResearch.WordTrace tailWord_2869500 prefixEnd_2869500 982288492051085534502277 := by
  unfold tailWord_2869500
  simp only [CollatzResearch.WordTrace]
  refine ⟨52329631552149523214258977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69772842069532697619011969 52329631552149523214258977)
  ·
    refine ⟨39247223664112142410694233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52329631552149523214258977 39247223664112142410694233)
    ·
      refine ⟨29435417748084106808020675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39247223664112142410694233 29435417748084106808020675)
      ·
        refine ⟨44153126622126160212031013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29435417748084106808020675 44153126622126160212031013)
        ·
          refine ⟨8278711241648655039755815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44153126622126160212031013 8278711241648655039755815)
          ·
            refine ⟨12418066862472982559633723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8278711241648655039755815 12418066862472982559633723)
            ·
              refine ⟨18627100293709473839450585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12418066862472982559633723 18627100293709473839450585)
              ·
                refine ⟨13970325220282105379587939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18627100293709473839450585 13970325220282105379587939)
                ·
                  refine ⟨20955487830423158069381909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13970325220282105379587939 20955487830423158069381909)
                  ·
                    refine ⟨982288492051085534502277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20955487830423158069381909 982288492051085534502277)
                    ·
                      rfl

theorem cell22_2869500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 2, 1, 6].length) (baseStart_2869500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2869500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2869500 prefixEnd_2869500 := by exact prefixLift 2869500
  have htrace : WordTrace (prefixWord ++ tailWord_2869500) baseStart_2869500 baseEnd_2869500 := by
    simpa [prefixWord, tailWord_2869500, baseEnd_2869500] using wordTrace_append hprefix tailTrace_2869500
  have hstable : (prefixWord ++ tailWord_2869500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2869500).length < 2 ^ (prefixWord ++ tailWord_2869500).sum := by decide
  have hdescent : baseEnd_2869500 < baseStart_2869500 := by decide
  rcases family_descends (prefixWord ++ tailWord_2869500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2869534 : List Nat := [4, 3, 2, 1, 1, 1, 1, 1, 4, 4]
def baseStart_2869534 : Nat := 118140960795 + 2869534 * 2 ^ 59
def prefixEnd_2869534 : Nat := 4983230072969 + 3 ^ 40 * 2869534 * 2
def baseEnd_2869534 : Nat := 982300130945920779152173

theorem tailTrace_2869534 : CollatzResearch.WordTrace tailWord_2869534 prefixEnd_2869534 982300130945920779152173 := by
  unfold tailWord_2869534
  simp only [CollatzResearch.WordTrace]
  refine ⟨13082562898271983779406957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69773668790783913490170437 13082562898271983779406957)
  ·
    refine ⟨4905961086851993917277609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13082562898271983779406957 4905961086851993917277609)
    ·
      refine ⟨3679470815138995437958207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4905961086851993917277609 3679470815138995437958207)
      ·
        refine ⟨5519206222708493156937311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3679470815138995437958207 5519206222708493156937311)
        ·
          refine ⟨8278809334062739735405967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5519206222708493156937311 8278809334062739735405967)
          ·
            refine ⟨12418214001094109603108951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8278809334062739735405967 12418214001094109603108951)
            ·
              refine ⟨18627321001641164404663427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12418214001094109603108951 18627321001641164404663427)
              ·
                refine ⟨27940981502461746606995141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18627321001641164404663427 27940981502461746606995141)
                ·
                  refine ⟨5238934031711577488811589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27940981502461746606995141 5238934031711577488811589)
                  ·
                    refine ⟨982300130945920779152173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5238934031711577488811589 982300130945920779152173)
                    ·
                      rfl

theorem cell22_2869534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_2869534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2869534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2869534 prefixEnd_2869534 := by exact prefixLift 2869534
  have htrace : WordTrace (prefixWord ++ tailWord_2869534) baseStart_2869534 baseEnd_2869534 := by
    simpa [prefixWord, tailWord_2869534, baseEnd_2869534] using wordTrace_append hprefix tailTrace_2869534
  have hstable : (prefixWord ++ tailWord_2869534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2869534).length < 2 ^ (prefixWord ++ tailWord_2869534).sum := by decide
  have hdescent : baseEnd_2869534 < baseStart_2869534 := by decide
  rcases family_descends (prefixWord ++ tailWord_2869534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2869549 : List Nat := [1, 5, 3, 1, 2, 1, 2, 7]
def baseStart_2869549 : Nat := 118140960795 + 2869549 * 2 ^ 59
def prefixEnd_2869549 : Nat := 4983230072969 + 3 ^ 40 * 2869549 * 2
def baseEnd_2869549 : Nat := 109145029528051748891903

theorem tailTrace_2869549 : CollatzResearch.WordTrace tailWord_2869549 prefixEnd_2869549 109145029528051748891903 := by
  unfold tailWord_2869549
  simp only [CollatzResearch.WordTrace]
  refine ⟨104661050281121527797051701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69774033520747685198034467 104661050281121527797051701)
  ·
    refine ⟨9811973463855143230973597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 104661050281121527797051701 9811973463855143230973597)
    ·
      refine ⟨3679490048945678711615099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9811973463855143230973597 3679490048945678711615099)
      ·
        refine ⟨5519235073418518067422649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3679490048945678711615099 5519235073418518067422649)
        ·
          refine ⟨4139426305063888550566987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5519235073418518067422649 4139426305063888550566987)
          ·
            refine ⟨6209139457595832825850481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4139426305063888550566987 6209139457595832825850481)
            ·
              refine ⟨4656854593196874619387861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6209139457595832825850481 4656854593196874619387861)
              ·
                refine ⟨109145029528051748891903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4656854593196874619387861 109145029528051748891903)
                ·
                  rfl

theorem cell22_2869549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 2, 7].length) (baseStart_2869549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2869549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2869549 prefixEnd_2869549 := by exact prefixLift 2869549
  have htrace : WordTrace (prefixWord ++ tailWord_2869549) baseStart_2869549 baseEnd_2869549 := by
    simpa [prefixWord, tailWord_2869549, baseEnd_2869549] using wordTrace_append hprefix tailTrace_2869549
  have hstable : (prefixWord ++ tailWord_2869549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2869549).length < 2 ^ (prefixWord ++ tailWord_2869549).sum := by decide
  have hdescent : baseEnd_2869549 < baseStart_2869549 := by decide
  rcases family_descends (prefixWord ++ tailWord_2869549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2869553 : List Nat := [1, 2, 2, 3, 5, 1, 2, 1, 2, 3]
def baseStart_2869553 : Nat := 118140960795 + 2869553 * 2 ^ 59
def prefixEnd_2869553 : Nat := 4983230072969 + 3 ^ 40 * 2869553 * 2
def baseEnd_2869553 : Nat := 982306635034211062927115

theorem tailTrace_2869553 : CollatzResearch.WordTrace tailWord_2869553 prefixEnd_2869553 982306635034211062927115 := by
  unfold tailWord_2869553
  simp only [CollatzResearch.WordTrace]
  refine ⟨104661196173107036480197313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69774130782071357653464875 104661196173107036480197313)
  ·
    refine ⟨78495897129830277360147985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104661196173107036480197313 78495897129830277360147985)
    ·
      refine ⟨58871922847372708020110989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78495897129830277360147985 58871922847372708020110989)
      ·
        refine ⟨22076971067764765507541621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58871922847372708020110989 22076971067764765507541621)
        ·
          refine ⟨2069716037602946766332027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22076971067764765507541621 2069716037602946766332027)
          ·
            refine ⟨3104574056404420149498041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2069716037602946766332027 3104574056404420149498041)
            ·
              refine ⟨2328430542303315112123531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3104574056404420149498041 2328430542303315112123531)
              ·
                refine ⟨3492645813454972668185297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2328430542303315112123531 3492645813454972668185297)
                ·
                  refine ⟨2619484360091229501138973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3492645813454972668185297 2619484360091229501138973)
                  ·
                    refine ⟨982306635034211062927115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2619484360091229501138973 982306635034211062927115)
                    ·
                      rfl

theorem cell22_2869553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 2, 1, 2, 3].length) (baseStart_2869553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2869553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2869553 prefixEnd_2869553 := by exact prefixLift 2869553
  have htrace : WordTrace (prefixWord ++ tailWord_2869553) baseStart_2869553 baseEnd_2869553 := by
    simpa [prefixWord, tailWord_2869553, baseEnd_2869553] using wordTrace_append hprefix tailTrace_2869553
  have hstable : (prefixWord ++ tailWord_2869553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2869553).length < 2 ^ (prefixWord ++ tailWord_2869553).sum := by decide
  have hdescent : baseEnd_2869553 < baseStart_2869553 := by decide
  rcases family_descends (prefixWord ++ tailWord_2869553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2869607 : List Nat := [1, 1, 5, 1, 3, 1, 1, 2, 3, 4]
def baseStart_2869607 : Nat := 118140960795 + 2869607 * 2 ^ 59
def prefixEnd_2869607 : Nat := 4983230072969 + 3 ^ 40 * 2869607 * 2
def baseEnd_2869607 : Nat := 982325120337772922076949

theorem tailTrace_2869607 : CollatzResearch.WordTrace tailWord_2869607 prefixEnd_2869607 982325120337772922076949 := by
  unfold tailWord_2869607
  simp only [CollatzResearch.WordTrace]
  refine ⟨104663165714911403702663075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69775443809940935801775383 104663165714911403702663075)
  ·
    refine ⟨156994748572367105553994613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104663165714911403702663075 156994748572367105553994613)
    ·
      refine ⟨14718257678659416145686995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 156994748572367105553994613 14718257678659416145686995)
      ·
        refine ⟨22077386517989124218530493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14718257678659416145686995 22077386517989124218530493)
        ·
          refine ⟨8279019944245921581948935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22077386517989124218530493 8279019944245921581948935)
          ·
            refine ⟨12418529916368882372923403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8279019944245921581948935 12418529916368882372923403)
            ·
              refine ⟨18627794874553323559385105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12418529916368882372923403 18627794874553323559385105)
              ·
                refine ⟨13970846155914992669538829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18627794874553323559385105 13970846155914992669538829)
                ·
                  refine ⟨5239067308468122251077061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13970846155914992669538829 5239067308468122251077061)
                  ·
                    refine ⟨982325120337772922076949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5239067308468122251077061 982325120337772922076949)
                    ·
                      rfl

theorem cell22_2869607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 2, 3, 4].length) (baseStart_2869607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2869607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2869607 prefixEnd_2869607 := by exact prefixLift 2869607
  have htrace : WordTrace (prefixWord ++ tailWord_2869607) baseStart_2869607 baseEnd_2869607 := by
    simpa [prefixWord, tailWord_2869607, baseEnd_2869607] using wordTrace_append hprefix tailTrace_2869607
  have hstable : (prefixWord ++ tailWord_2869607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2869607).length < 2 ^ (prefixWord ++ tailWord_2869607).sum := by decide
  have hdescent : baseEnd_2869607 < baseStart_2869607 := by decide
  rcases family_descends (prefixWord ++ tailWord_2869607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2869637 : List Nat := [1, 3, 1, 1, 3, 1, 1, 4, 4, 3]
def baseStart_2869637 : Nat := 118140960795 + 2869637 * 2 ^ 59
def prefixEnd_2869637 : Nat := 4983230072969 + 3 ^ 40 * 2869637 * 2
def baseEnd_2869637 : Nat := 982335389950862843826857

theorem tailTrace_2869637 : CollatzResearch.WordTrace tailWord_2869637 prefixEnd_2869637 982335389950862843826857 := by
  unfold tailWord_2869637
  simp only [CollatzResearch.WordTrace]
  refine ⟨104664259904802718826255165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69776173269868479217503443 104664259904802718826255165)
  ·
    refine ⟨39249097464301019559845687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104664259904802718826255165 39249097464301019559845687)
    ·
      refine ⟨58873646196451529339768531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39249097464301019559845687 58873646196451529339768531)
      ·
        refine ⟨88310469294677294009652797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58873646196451529339768531 88310469294677294009652797)
        ·
          refine ⟨33116425985503985253619799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88310469294677294009652797 33116425985503985253619799)
          ·
            refine ⟨49674638978255977880429699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33116425985503985253619799 49674638978255977880429699)
            ·
              refine ⟨74511958467383966820644549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49674638978255977880429699 74511958467383966820644549)
              ·
                refine ⟨13970992212634493778870853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74511958467383966820644549 13970992212634493778870853)
                ·
                  refine ⟨2619561039868967583538285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13970992212634493778870853 2619561039868967583538285)
                  ·
                    refine ⟨982335389950862843826857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2619561039868967583538285 982335389950862843826857)
                    ·
                      rfl

theorem cell22_2869637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 4, 4, 3].length) (baseStart_2869637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2869637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2869637 prefixEnd_2869637 := by exact prefixLift 2869637
  have htrace : WordTrace (prefixWord ++ tailWord_2869637) baseStart_2869637 baseEnd_2869637 := by
    simpa [prefixWord, tailWord_2869637, baseEnd_2869637] using wordTrace_append hprefix tailTrace_2869637
  have hstable : (prefixWord ++ tailWord_2869637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2869637).length < 2 ^ (prefixWord ++ tailWord_2869637).sum := by decide
  have hdescent : baseEnd_2869637 < baseStart_2869637 := by decide
  rcases family_descends (prefixWord ++ tailWord_2869637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2869639 : List Nat := [1, 1, 4, 2, 2, 1, 4, 3, 4]
def baseStart_2869639 : Nat := 118140960795 + 2869639 * 2 ^ 59
def prefixEnd_2869639 : Nat := 4983230072969 + 3 ^ 40 * 2869639 * 2
def baseEnd_2869639 : Nat := 327445358197245168425617

theorem tailTrace_2869639 : CollatzResearch.WordTrace tailWord_2869639 prefixEnd_2869639 327445358197245168425617 := by
  unfold tailWord_2869639
  simp only [CollatzResearch.WordTrace]
  refine ⟨104664332850795473167827971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69776221900530315445218647 104664332850795473167827971)
  ·
    refine ⟨156996499276193209751741957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104664332850795473167827971 156996499276193209751741957)
    ·
      refine ⟨29436843614286226828451617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 156996499276193209751741957 29436843614286226828451617)
      ·
        refine ⟨22077632710714670121338713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29436843614286226828451617 22077632710714670121338713)
        ·
          refine ⟨16558224533036002591004035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22077632710714670121338713 16558224533036002591004035)
          ·
            refine ⟨24837336799554003886506053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16558224533036002591004035 24837336799554003886506053)
            ·
              refine ⟨4657000649916375728719885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24837336799554003886506053 4657000649916375728719885)
              ·
                refine ⟨1746375243718640898269957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4657000649916375728719885 1746375243718640898269957)
                ·
                  refine ⟨327445358197245168425617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1746375243718640898269957 327445358197245168425617)
                  ·
                    rfl

theorem cell22_2869639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 4, 3, 4].length) (baseStart_2869639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2869639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2869639 prefixEnd_2869639 := by exact prefixLift 2869639
  have htrace : WordTrace (prefixWord ++ tailWord_2869639) baseStart_2869639 baseEnd_2869639 := by
    simpa [prefixWord, tailWord_2869639, baseEnd_2869639] using wordTrace_append hprefix tailTrace_2869639
  have hstable : (prefixWord ++ tailWord_2869639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2869639).length < 2 ^ (prefixWord ++ tailWord_2869639).sum := by decide
  have hdescent : baseEnd_2869639 < baseStart_2869639 := by decide
  rcases family_descends (prefixWord ++ tailWord_2869639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2869641 : List Nat := [1, 2, 1, 1, 6, 3, 2, 1, 1, 4]
def baseStart_2869641 : Nat := 118140960795 + 2869641 * 2 ^ 59
def prefixEnd_2869641 : Nat := 4983230072969 + 3 ^ 40 * 2869641 * 2
def baseEnd_2869641 : Nat := 982336759232608166726845

theorem tailTrace_2869641 : CollatzResearch.WordTrace tailWord_2869641 prefixEnd_2869641 982336759232608166726845 := by
  unfold tailWord_2869641
  simp only [CollatzResearch.WordTrace]
  refine ⟨104664405796788227509400777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69776270531192151672933851 104664405796788227509400777)
  ·
    refine ⟨78498304347591170632050583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104664405796788227509400777 78498304347591170632050583)
    ·
      refine ⟨117747456521386755948075875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78498304347591170632050583 117747456521386755948075875)
      ·
        refine ⟨176621184782080133922113813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117747456521386755948075875 176621184782080133922113813)
        ·
          refine ⟨8279118036660006277599085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 176621184782080133922113813 8279118036660006277599085)
          ·
            refine ⟨3104669263747502354099657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8279118036660006277599085 3104669263747502354099657)
            ·
              refine ⟨2328501947810626765574743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3104669263747502354099657 2328501947810626765574743)
              ·
                refine ⟨3492752921715940148362115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2328501947810626765574743 3492752921715940148362115)
                ·
                  refine ⟨5239129382573910222543173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3492752921715940148362115 5239129382573910222543173)
                  ·
                    refine ⟨982336759232608166726845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5239129382573910222543173 982336759232608166726845)
                    ·
                      rfl

theorem cell22_2869641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 2, 1, 1, 4].length) (baseStart_2869641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2869641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2869641 prefixEnd_2869641 := by exact prefixLift 2869641
  have htrace : WordTrace (prefixWord ++ tailWord_2869641) baseStart_2869641 baseEnd_2869641 := by
    simpa [prefixWord, tailWord_2869641, baseEnd_2869641] using wordTrace_append hprefix tailTrace_2869641
  have hstable : (prefixWord ++ tailWord_2869641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2869641).length < 2 ^ (prefixWord ++ tailWord_2869641).sum := by decide
  have hdescent : baseEnd_2869641 < baseStart_2869641 := by decide
  rcases family_descends (prefixWord ++ tailWord_2869641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2869680 : List Nat := [2, 1, 1, 1, 2, 1, 1, 2, 3, 8]
def baseStart_2869680 : Nat := 118140960795 + 2869680 * 2 ^ 59
def prefixEnd_2869680 : Nat := 4983230072969 + 3 ^ 40 * 2869680 * 2
def baseEnd_2869680 : Nat := 982350109729625065001725

theorem tailTrace_2869680 : CollatzResearch.WordTrace tailWord_2869680 prefixEnd_2869680 982350109729625065001725 := by
  unfold tailWord_2869680
  simp only [CollatzResearch.WordTrace]
  refine ⟨52332914121823468585035247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69777218829097958113380329 52332914121823468585035247)
  ·
    refine ⟨78499371182735202877552871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52332914121823468585035247 78499371182735202877552871)
    ·
      refine ⟨117749056774102804316329307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78499371182735202877552871 117749056774102804316329307)
      ·
        refine ⟨176623585161154206474493961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117749056774102804316329307 176623585161154206474493961)
        ·
          refine ⟨132467688870865654855870471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176623585161154206474493961 132467688870865654855870471)
          ·
            refine ⟨198701533306298482283805707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132467688870865654855870471 198701533306298482283805707)
            ·
              refine ⟨298052299959447723425708561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 198701533306298482283805707 298052299959447723425708561)
              ·
                refine ⟨223539224969585792569281421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 298052299959447723425708561 223539224969585792569281421)
                ·
                  refine ⟨83827209363594672213480533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 223539224969585792569281421 83827209363594672213480533)
                  ·
                    refine ⟨982350109729625065001725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 83827209363594672213480533 982350109729625065001725)
                    ·
                      rfl

theorem cell22_2869680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 3, 8].length) (baseStart_2869680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2869680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2869680 prefixEnd_2869680 := by exact prefixLift 2869680
  have htrace : WordTrace (prefixWord ++ tailWord_2869680) baseStart_2869680 baseEnd_2869680 := by
    simpa [prefixWord, tailWord_2869680, baseEnd_2869680] using wordTrace_append hprefix tailTrace_2869680
  have hstable : (prefixWord ++ tailWord_2869680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2869680).length < 2 ^ (prefixWord ++ tailWord_2869680).sum := by decide
  have hdescent : baseEnd_2869680 < baseStart_2869680 := by decide
  rcases family_descends (prefixWord ++ tailWord_2869680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2869716 : List Nat := [2, 4, 1, 2, 2, 1, 3, 1, 3, 3]
def baseStart_2869716 : Nat := 118140960795 + 2869716 * 2 ^ 59
def prefixEnd_2869716 : Nat := 4983230072969 + 3 ^ 40 * 2869716 * 2
def baseEnd_2869716 : Nat := 982362433265332971101615

theorem tailTrace_2869716 : CollatzResearch.WordTrace tailWord_2869716 prefixEnd_2869716 982362433265332971101615 := by
  unfold tailWord_2869716
  simp only [CollatzResearch.WordTrace]
  refine ⟨52333570635758257659190501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69778094181011010212254001 52333570635758257659190501)
  ·
    refine ⟨9812544494204673311098219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52333570635758257659190501 9812544494204673311098219)
    ·
      refine ⟨14718816741307009966647329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9812544494204673311098219 14718816741307009966647329)
      ·
        refine ⟨11039112555980257474985497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14718816741307009966647329 11039112555980257474985497)
        ·
          refine ⟨8279334416985193106239123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11039112555980257474985497 8279334416985193106239123)
          ·
            refine ⟨12419001625477789659358685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8279334416985193106239123 12419001625477789659358685)
            ·
              refine ⟨4657125609554171122259507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12419001625477789659358685 4657125609554171122259507)
              ·
                refine ⟨6985688414331256683389261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4657125609554171122259507 6985688414331256683389261)
                ·
                  refine ⟨2619633155374221256270973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6985688414331256683389261 2619633155374221256270973)
                  ·
                    refine ⟨982362433265332971101615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2619633155374221256270973 982362433265332971101615)
                    ·
                      rfl

theorem cell22_2869716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 3, 1, 3, 3].length) (baseStart_2869716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2869716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2869716 prefixEnd_2869716 := by exact prefixLift 2869716
  have htrace : WordTrace (prefixWord ++ tailWord_2869716) baseStart_2869716 baseEnd_2869716 := by
    simpa [prefixWord, tailWord_2869716, baseEnd_2869716] using wordTrace_append hprefix tailTrace_2869716
  have hstable : (prefixWord ++ tailWord_2869716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2869716).length < 2 ^ (prefixWord ++ tailWord_2869716).sum := by decide
  have hdescent : baseEnd_2869716 < baseStart_2869716 := by decide
  rcases family_descends (prefixWord ++ tailWord_2869716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2869767 : List Nat := [1, 1, 4, 3, 4, 1, 2, 2, 1, 3]
def baseStart_2869767 : Nat := 118140960795 + 2869767 * 2 ^ 59
def prefixEnd_2869767 : Nat := 4983230072969 + 3 ^ 40 * 2869767 * 2
def baseEnd_2869767 : Nat := 982379891607585838076459

theorem tailTrace_2869767 : CollatzResearch.WordTrace tailWord_2869767 prefixEnd_2869767 982379891607585838076459 := by
  unfold tailWord_2869767
  simp only [CollatzResearch.WordTrace]
  refine ⟨104669001394331751028487555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69779334262887834018991703 104669001394331751028487555)
  ·
    refine ⟨157003502091497626542731333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104669001394331751028487555 157003502091497626542731333)
    ·
      refine ⟨29438156642155804976762125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 157003502091497626542731333 29438156642155804976762125)
      ·
        refine ⟨11039308740808426866285797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29438156642155804976762125 11039308740808426866285797)
        ·
          refine ⟨2069870388901580037428587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11039308740808426866285797 2069870388901580037428587)
          ·
            refine ⟨3104805583352370056142881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2069870388901580037428587 3104805583352370056142881)
            ·
              refine ⟨2328604187514277542107161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3104805583352370056142881 2328604187514277542107161)
              ·
                refine ⟨1746453140635708156580371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2328604187514277542107161 1746453140635708156580371)
                ·
                  refine ⟨2619679710953562234870557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1746453140635708156580371 2619679710953562234870557)
                  ·
                    refine ⟨982379891607585838076459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2619679710953562234870557 982379891607585838076459)
                    ·
                      rfl

theorem cell22_2869767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 2, 2, 1, 3].length) (baseStart_2869767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2869767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2869767 prefixEnd_2869767 := by exact prefixLift 2869767
  have htrace : WordTrace (prefixWord ++ tailWord_2869767) baseStart_2869767 baseEnd_2869767 := by
    simpa [prefixWord, tailWord_2869767, baseEnd_2869767] using wordTrace_append hprefix tailTrace_2869767
  have hstable : (prefixWord ++ tailWord_2869767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2869767).length < 2 ^ (prefixWord ++ tailWord_2869767).sum := by decide
  have hdescent : baseEnd_2869767 < baseStart_2869767 := by decide
  rcases family_descends (prefixWord ++ tailWord_2869767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2869789 : List Nat := [1, 4, 2, 2, 1, 2, 1, 3, 1, 5]
def baseStart_2869789 : Nat := 118140960795 + 2869789 * 2 ^ 59
def prefixEnd_2869789 : Nat := 4983230072969 + 3 ^ 40 * 2869789 * 2
def baseEnd_2869789 : Nat := 982387422657185114026391

theorem tailTrace_2869789 : CollatzResearch.WordTrace tailWord_2869789 prefixEnd_2869789 982387422657185114026391 := by
  unfold tailWord_2869789
  simp only [CollatzResearch.WordTrace]
  refine ⟨104669803800252048785788421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69779869200168032523858947 104669803800252048785788421)
  ·
    refine ⟨19625588212547259147335329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104669803800252048785788421 19625588212547259147335329)
    ·
      refine ⟨14719191159410444360501497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19625588212547259147335329 14719191159410444360501497)
      ·
        refine ⟨11039393369557833270376123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14719191159410444360501497 11039393369557833270376123)
        ·
          refine ⟨16559090054336749905564185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11039393369557833270376123 16559090054336749905564185)
          ·
            refine ⟨12419317540752562429173139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16559090054336749905564185 12419317540752562429173139)
            ·
              refine ⟨18628976311128843643759709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12419317540752562429173139 18628976311128843643759709)
              ·
                refine ⟨6985866116673316366409891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18628976311128843643759709 6985866116673316366409891)
                ·
                  refine ⟨10478799175009974549614837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6985866116673316366409891 10478799175009974549614837)
                  ·
                    refine ⟨982387422657185114026391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10478799175009974549614837 982387422657185114026391)
                    ·
                      rfl

theorem cell22_2869789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 3, 1, 5].length) (baseStart_2869789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2869789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2869789 prefixEnd_2869789 := by exact prefixLift 2869789
  have htrace : WordTrace (prefixWord ++ tailWord_2869789) baseStart_2869789 baseEnd_2869789 := by
    simpa [prefixWord, tailWord_2869789, baseEnd_2869789] using wordTrace_append hprefix tailTrace_2869789
  have hstable : (prefixWord ++ tailWord_2869789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2869789).length < 2 ^ (prefixWord ++ tailWord_2869789).sum := by decide
  have hdescent : baseEnd_2869789 < baseStart_2869789 := by decide
  rcases family_descends (prefixWord ++ tailWord_2869789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2869832 : List Nat := [2, 1, 3, 1, 1, 1, 1, 3, 1, 8]
def baseStart_2869832 : Nat := 118140960795 + 2869832 * 2 ^ 59
def prefixEnd_2869832 : Nat := 4983230072969 + 3 ^ 40 * 2869832 * 2
def baseEnd_2869832 : Nat := 982402142435947335201259

theorem tailTrace_2869832 : CollatzResearch.WordTrace tailWord_2869832 prefixEnd_2869832 982402142435947335201259 := by
  unfold tailWord_2869832
  simp only [CollatzResearch.WordTrace]
  refine ⟨52335686069548133564801875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69780914759397511419735833 52335686069548133564801875)
  ·
    refine ⟨78503529104322200347202813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52335686069548133564801875 78503529104322200347202813)
    ·
      refine ⟨29438823414120825130201055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78503529104322200347202813 29438823414120825130201055)
      ·
        refine ⟨44158235121181237695301583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29438823414120825130201055 44158235121181237695301583)
        ·
          refine ⟨66237352681771856542952375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44158235121181237695301583 66237352681771856542952375)
          ·
            refine ⟨99356029022657784814428563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66237352681771856542952375 99356029022657784814428563)
            ·
              refine ⟨149034043533986677221642845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99356029022657784814428563 149034043533986677221642845)
              ·
                refine ⟨55887766325245003958116067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 149034043533986677221642845 55887766325245003958116067)
                ·
                  refine ⟨83831649487867505937174101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55887766325245003958116067 83831649487867505937174101)
                  ·
                    refine ⟨982402142435947335201259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 83831649487867505937174101 982402142435947335201259)
                    ·
                      rfl

theorem cell22_2869832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 1, 8].length) (baseStart_2869832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2869832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2869832 prefixEnd_2869832 := by exact prefixLift 2869832
  have htrace : WordTrace (prefixWord ++ tailWord_2869832) baseStart_2869832 baseEnd_2869832 := by
    simpa [prefixWord, tailWord_2869832, baseEnd_2869832] using wordTrace_append hprefix tailTrace_2869832
  have hstable : (prefixWord ++ tailWord_2869832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2869832).length < 2 ^ (prefixWord ++ tailWord_2869832).sum := by decide
  have hdescent : baseEnd_2869832 < baseStart_2869832 := by decide
  rcases family_descends (prefixWord ++ tailWord_2869832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2869868 : List Nat := [2, 2, 1, 1, 3, 1, 5, 3, 1, 3]
def baseStart_2869868 : Nat := 118140960795 + 2869868 * 2 ^ 59
def prefixEnd_2869868 : Nat := 4983230072969 + 3 ^ 40 * 2869868 * 2
def baseEnd_2869868 : Nat := 982414465971655241301149

theorem tailTrace_2869868 : CollatzResearch.WordTrace tailWord_2869868 prefixEnd_2869868 982414465971655241301149 := by
  unfold tailWord_2869868
  simp only [CollatzResearch.WordTrace]
  refine ⟨52336342583482922638957129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69781790111310563518609505 52336342583482922638957129)
  ·
    refine ⟨39252256937612191979217847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52336342583482922638957129 39252256937612191979217847)
    ·
      refine ⟨58878385406418287968826771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39252256937612191979217847 58878385406418287968826771)
      ·
        refine ⟨88317578109627431953240157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58878385406418287968826771 88317578109627431953240157)
        ·
          refine ⟨33119091791110286982465059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88317578109627431953240157 33119091791110286982465059)
          ·
            refine ⟨49678637686665430473697589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33119091791110286982465059 49678637686665430473697589)
            ·
              refine ⟨4657372283124884106909149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49678637686665430473697589 4657372283124884106909149)
              ·
                refine ⟨1746514606171831540090931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4657372283124884106909149 1746514606171831540090931)
                ·
                  refine ⟨2619771909257747310136397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1746514606171831540090931 2619771909257747310136397)
                  ·
                    refine ⟨982414465971655241301149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2619771909257747310136397 982414465971655241301149)
                    ·
                      rfl

theorem cell22_2869868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 5, 3, 1, 3].length) (baseStart_2869868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2869868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2869868 prefixEnd_2869868 := by exact prefixLift 2869868
  have htrace : WordTrace (prefixWord ++ tailWord_2869868) baseStart_2869868 baseEnd_2869868 := by
    simpa [prefixWord, tailWord_2869868, baseEnd_2869868] using wordTrace_append hprefix tailTrace_2869868
  have hstable : (prefixWord ++ tailWord_2869868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2869868).length < 2 ^ (prefixWord ++ tailWord_2869868).sum := by decide
  have hdescent : baseEnd_2869868 < baseStart_2869868 := by decide
  rcases family_descends (prefixWord ++ tailWord_2869868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2869885 : List Nat := [1, 4, 1, 1, 6, 1, 1, 1, 3, 3]
def baseStart_2869885 : Nat := 118140960795 + 2869885 * 2 ^ 59
def prefixEnd_2869885 : Nat := 4983230072969 + 3 ^ 40 * 2869885 * 2
def baseEnd_2869885 : Nat := 982420285419072863626097

theorem tailTrace_2869885 : CollatzResearch.WordTrace tailWord_2869885 prefixEnd_2869885 982420285419072863626097 := by
  unfold tailWord_2869885
  simp only [CollatzResearch.WordTrace]
  refine ⟨104673305207904257181283109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69782203471936171454188739 104673305207904257181283109)
  ·
    refine ⟨19626244726482048221490583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104673305207904257181283109 19626244726482048221490583)
    ·
      refine ⟨29439367089723072332235875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19626244726482048221490583 29439367089723072332235875)
      ·
        refine ⟨44159050634584608498353813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29439367089723072332235875 44159050634584608498353813)
        ·
          refine ⟨2069955498496153523360335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 44159050634584608498353813 2069955498496153523360335)
          ·
            refine ⟨3104933247744230285040503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2069955498496153523360335 3104933247744230285040503)
            ·
              refine ⟨4657399871616345427560755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3104933247744230285040503 4657399871616345427560755)
              ·
                refine ⟨6986099807424518141341133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4657399871616345427560755 6986099807424518141341133)
                ·
                  refine ⟨2619787427784194303002925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6986099807424518141341133 2619787427784194303002925)
                  ·
                    refine ⟨982420285419072863626097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2619787427784194303002925 982420285419072863626097)
                    ·
                      rfl

theorem cell22_2869885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 1, 1, 3, 3].length) (baseStart_2869885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2869885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2869885 prefixEnd_2869885 := by exact prefixLift 2869885
  have htrace : WordTrace (prefixWord ++ tailWord_2869885) baseStart_2869885 baseEnd_2869885 := by
    simpa [prefixWord, tailWord_2869885, baseEnd_2869885] using wordTrace_append hprefix tailTrace_2869885
  have hstable : (prefixWord ++ tailWord_2869885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2869885).length < 2 ^ (prefixWord ++ tailWord_2869885).sum := by decide
  have hdescent : baseEnd_2869885 < baseStart_2869885 := by decide
  rcases family_descends (prefixWord ++ tailWord_2869885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2869943 : List Nat := [1, 1, 3, 1, 6, 1, 1, 4, 4]
def baseStart_2869943 : Nat := 118140960795 + 2869943 * 2 ^ 59
def prefixEnd_2869943 : Nat := 4983230072969 + 3 ^ 40 * 2869943 * 2
def baseEnd_2869943 : Nat := 327480046668126681891973

theorem tailTrace_2869943 : CollatzResearch.WordTrace tailWord_2869943 prefixEnd_2869943 327480046668126681891973 := by
  unfold tailWord_2869943
  simp only [CollatzResearch.WordTrace]
  refine ⟨104675420641694133086894483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69783613761129422057929655 104675420641694133086894483)
  ·
    refine ⟨157013130962541199630341725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104675420641694133086894483 157013130962541199630341725)
    ·
      refine ⟨58879924110952949861378147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157013130962541199630341725 58879924110952949861378147)
      ·
        refine ⟨88319886166429424792067221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58879924110952949861378147 88319886166429424792067221)
        ·
          refine ⟨4139994664051379287128151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 88319886166429424792067221 4139994664051379287128151)
          ·
            refine ⟨6209991996077068930692227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4139994664051379287128151 6209991996077068930692227)
            ·
              refine ⟨9314987994115603396038341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6209991996077068930692227 9314987994115603396038341)
              ·
                refine ⟨1746560248896675636757189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9314987994115603396038341 1746560248896675636757189)
                ·
                  refine ⟨327480046668126681891973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1746560248896675636757189 327480046668126681891973)
                  ·
                    rfl

theorem cell22_2869943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 4, 4].length) (baseStart_2869943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2869943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2869943 prefixEnd_2869943 := by exact prefixLift 2869943
  have htrace : WordTrace (prefixWord ++ tailWord_2869943) baseStart_2869943 baseEnd_2869943 := by
    simpa [prefixWord, tailWord_2869943, baseEnd_2869943] using wordTrace_append hprefix tailTrace_2869943
  have hstable : (prefixWord ++ tailWord_2869943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2869943).length < 2 ^ (prefixWord ++ tailWord_2869943).sum := by decide
  have hdescent : baseEnd_2869943 < baseStart_2869943 := by decide
  rcases family_descends (prefixWord ++ tailWord_2869943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2869973 : List Nat := [1, 3, 2, 5, 1, 1, 1, 1, 1, 6]
def baseStart_2869973 : Nat := 118140960795 + 2869973 * 2 ^ 59
def prefixEnd_2869973 : Nat := 4983230072969 + 3 ^ 40 * 2869973 * 2
def baseEnd_2869973 : Nat := 982450409617469967425827

theorem tailTrace_2869973 : CollatzResearch.WordTrace tailWord_2869973 prefixEnd_2869973 982450409617469967425827 := by
  unfold tailWord_2869973
  simp only [CollatzResearch.WordTrace]
  refine ⟨104676514831585448210486573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69784343221056965473657715 104676514831585448210486573)
  ·
    refine ⟨39253693061844543078932465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104676514831585448210486573 39253693061844543078932465)
    ·
      refine ⟨29440269796383407309199349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39253693061844543078932465 29440269796383407309199349)
      ·
        refine ⟨2760025293410944435237439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29440269796383407309199349 2760025293410944435237439)
        ·
          refine ⟨4140037940116416652856159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2760025293410944435237439 4140037940116416652856159)
          ·
            refine ⟨6210056910174624979284239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4140037940116416652856159 6210056910174624979284239)
            ·
              refine ⟨9315085365261937468926359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6210056910174624979284239 9315085365261937468926359)
              ·
                refine ⟨13972628047892906203389539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9315085365261937468926359 13972628047892906203389539)
                ·
                  refine ⟨20958942071839359305084309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13972628047892906203389539 20958942071839359305084309)
                  ·
                    refine ⟨982450409617469967425827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20958942071839359305084309 982450409617469967425827)
                    ·
                      rfl

theorem cell22_2869973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 1, 1, 6].length) (baseStart_2869973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2869973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2869973 prefixEnd_2869973 := by exact prefixLift 2869973
  have htrace : WordTrace (prefixWord ++ tailWord_2869973) baseStart_2869973 baseEnd_2869973 := by
    simpa [prefixWord, tailWord_2869973, baseEnd_2869973] using wordTrace_append hprefix tailTrace_2869973
  have hstable : (prefixWord ++ tailWord_2869973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2869973).length < 2 ^ (prefixWord ++ tailWord_2869973).sum := by decide
  have hdescent : baseEnd_2869973 < baseStart_2869973 := by decide
  rcases family_descends (prefixWord ++ tailWord_2869973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2869992 : List Nat := [2, 1, 4, 1, 5, 1, 1, 2, 2, 3]
def baseStart_2869992 : Nat := 118140960795 + 2869992 * 2 ^ 59
def prefixEnd_2869992 : Nat := 4983230072969 + 3 ^ 40 * 2869992 * 2
def baseEnd_2869992 : Nat := 982456913705760251200769

theorem tailTrace_2869992 : CollatzResearch.WordTrace tailWord_2869992 prefixEnd_2869992 982456913705760251200769 := by
  unfold tailWord_2869992
  simp only [CollatzResearch.WordTrace]
  refine ⟨52338603909258307227714115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69784805212344409636952153 52338603909258307227714115)
  ·
    refine ⟨78507905863887460841571173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52338603909258307227714115 78507905863887460841571173)
    ·
      refine ⟨14720232349478898907794595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78507905863887460841571173 14720232349478898907794595)
      ·
        refine ⟨22080348524218348361691893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14720232349478898907794595 22080348524218348361691893)
        ·
          refine ⟨2070032674145470158908615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22080348524218348361691893 2070032674145470158908615)
          ·
            refine ⟨3105049011218205238362923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2070032674145470158908615 3105049011218205238362923)
            ·
              refine ⟨4657573516827307857544385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3105049011218205238362923 4657573516827307857544385)
              ·
                refine ⟨3493180137620480893158289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4657573516827307857544385 3493180137620480893158289)
                ·
                  refine ⟨2619885103215360669868717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3493180137620480893158289 2619885103215360669868717)
                  ·
                    refine ⟨982456913705760251200769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2619885103215360669868717 982456913705760251200769)
                    ·
                      rfl

theorem cell22_2869992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 1, 2, 2, 3].length) (baseStart_2869992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2869992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2869992 prefixEnd_2869992 := by exact prefixLift 2869992
  have htrace : WordTrace (prefixWord ++ tailWord_2869992) baseStart_2869992 baseEnd_2869992 := by
    simpa [prefixWord, tailWord_2869992, baseEnd_2869992] using wordTrace_append hprefix tailTrace_2869992
  have hstable : (prefixWord ++ tailWord_2869992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2869992).length < 2 ^ (prefixWord ++ tailWord_2869992).sum := by decide
  have hdescent : baseEnd_2869992 < baseStart_2869992 := by decide
  rcases family_descends (prefixWord ++ tailWord_2869992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2870076 : List Nat := [2, 2, 2, 2, 1, 1, 1, 5, 1, 5]
def baseStart_2870076 : Nat := 118140960795 + 2870076 * 2 ^ 59
def prefixEnd_2870076 : Nat := 4983230072969 + 3 ^ 40 * 2870076 * 2
def baseEnd_2870076 : Nat := 982485668622412032100511

theorem tailTrace_2870076 : CollatzResearch.WordTrace tailWord_2870076 prefixEnd_2870076 982485668622412032100511 := by
  unfold tailWord_2870076
  simp only [CollatzResearch.WordTrace]
  refine ⟨52340135775106148400743041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69786847700141531200990721 52340135775106148400743041)
  ·
    refine ⟨39255101831329611300557281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52340135775106148400743041 39255101831329611300557281)
    ·
      refine ⟨29441326373497208475417961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39255101831329611300557281 29441326373497208475417961)
      ·
        refine ⟨22080994780122906356563471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29441326373497208475417961 22080994780122906356563471)
        ·
          refine ⟨33121492170184359534845207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22080994780122906356563471 33121492170184359534845207)
          ·
            refine ⟨49682238255276539302267811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33121492170184359534845207 49682238255276539302267811)
            ·
              refine ⟨74523357382914808953401717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49682238255276539302267811 74523357382914808953401717)
              ·
                refine ⟨6986564754648263339381411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 74523357382914808953401717 6986564754648263339381411)
                ·
                  refine ⟨10479847131972395009072117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6986564754648263339381411 10479847131972395009072117)
                  ·
                    refine ⟨982485668622412032100511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10479847131972395009072117 982485668622412032100511)
                    ·
                      rfl

theorem cell22_2870076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 5, 1, 5].length) (baseStart_2870076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2870076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2870076 prefixEnd_2870076 := by exact prefixLift 2870076
  have htrace : WordTrace (prefixWord ++ tailWord_2870076) baseStart_2870076 baseEnd_2870076 := by
    simpa [prefixWord, tailWord_2870076, baseEnd_2870076] using wordTrace_append hprefix tailTrace_2870076
  have hstable : (prefixWord ++ tailWord_2870076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2870076).length < 2 ^ (prefixWord ++ tailWord_2870076).sum := by decide
  have hdescent : baseEnd_2870076 < baseStart_2870076 := by decide
  rcases family_descends (prefixWord ++ tailWord_2870076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2870155 : List Nat := [1, 1, 1, 1, 4, 2, 3, 5, 1, 3]
def baseStart_2870155 : Nat := 118140960795 + 2870155 * 2 ^ 59
def prefixEnd_2870155 : Nat := 4983230072969 + 3 ^ 40 * 2870155 * 2
def baseEnd_2870155 : Nat := 982512711936882159375269

theorem tailTrace_2870155 : CollatzResearch.WordTrace tailWord_2870155 prefixEnd_2870155 982512711936882159375269 := by
  unfold tailWord_2870155
  simp only [CollatzResearch.WordTrace]
  refine ⟨104683152916926093293611919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69788768611284062195741279 104683152916926093293611919)
  ·
    refine ⟨157024729375389139940417879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104683152916926093293611919 157024729375389139940417879)
    ·
      refine ⟨235537094063083709910626819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157024729375389139940417879 235537094063083709910626819)
      ·
        refine ⟨353305641094625564865940229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235537094063083709910626819 353305641094625564865940229)
        ·
          refine ⟨66244807705242293412363793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 353305641094625564865940229 66244807705242293412363793)
          ·
            refine ⟨49683605778931720059272845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66244807705242293412363793 49683605778931720059272845)
            ·
              refine ⟨18631352167099395022227317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49683605778931720059272845 18631352167099395022227317)
              ·
                refine ⟨1746689265665568283333811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18631352167099395022227317 1746689265665568283333811)
                ·
                  refine ⟨2620033898498352425000717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1746689265665568283333811 2620033898498352425000717)
                  ·
                    refine ⟨982512711936882159375269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2620033898498352425000717 982512711936882159375269)
                    ·
                      rfl

theorem cell22_2870155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 5, 1, 3].length) (baseStart_2870155 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2870155 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2870155 prefixEnd_2870155 := by exact prefixLift 2870155
  have htrace : WordTrace (prefixWord ++ tailWord_2870155) baseStart_2870155 baseEnd_2870155 := by
    simpa [prefixWord, tailWord_2870155, baseEnd_2870155] using wordTrace_append hprefix tailTrace_2870155
  have hstable : (prefixWord ++ tailWord_2870155).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2870155).length < 2 ^ (prefixWord ++ tailWord_2870155).sum := by decide
  have hdescent : baseEnd_2870155 < baseStart_2870155 := by decide
  rcases family_descends (prefixWord ++ tailWord_2870155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2870172 : List Nat := [2, 2, 3, 3, 2, 1, 2, 1, 3, 3]
def baseStart_2870172 : Nat := 118140960795 + 2870172 * 2 ^ 59
def prefixEnd_2870172 : Nat := 4983230072969 + 3 ^ 40 * 2870172 * 2
def baseEnd_2870172 : Nat := 982518531384299781700217

theorem tailTrace_2870172 : CollatzResearch.WordTrace tailWord_2870172 prefixEnd_2870172 982518531384299781700217 := by
  unfold tailWord_2870172
  simp only [CollatzResearch.WordTrace]
  refine ⟨52341886478932252598490385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69789181971909670131320513 52341886478932252598490385)
  ·
    refine ⟨39256414859199189448867789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52341886478932252598490385 39256414859199189448867789)
    ·
      refine ⟨14721155572199696043325421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39256414859199189448867789 14721155572199696043325421)
      ·
        refine ⟨5520433339574886016247033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14721155572199696043325421 5520433339574886016247033)
        ·
          refine ⟨4140325004681164512185275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5520433339574886016247033 4140325004681164512185275)
          ·
            refine ⟨6210487507021746768277913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4140325004681164512185275 6210487507021746768277913)
            ·
              refine ⟨4657865630266310076208435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6210487507021746768277913 4657865630266310076208435)
              ·
                refine ⟨6986798445399465114312653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4657865630266310076208435 6986798445399465114312653)
                ·
                  refine ⟨2620049417024799417867245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6986798445399465114312653 2620049417024799417867245)
                  ·
                    refine ⟨982518531384299781700217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2620049417024799417867245 982518531384299781700217)
                    ·
                      rfl

theorem cell22_2870172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 2, 1, 3, 3].length) (baseStart_2870172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2870172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2870172 prefixEnd_2870172 := by exact prefixLift 2870172
  have htrace : WordTrace (prefixWord ++ tailWord_2870172) baseStart_2870172 baseEnd_2870172 := by
    simpa [prefixWord, tailWord_2870172, baseEnd_2870172] using wordTrace_append hprefix tailTrace_2870172
  have hstable : (prefixWord ++ tailWord_2870172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2870172).length < 2 ^ (prefixWord ++ tailWord_2870172).sum := by decide
  have hdescent : baseEnd_2870172 < baseStart_2870172 := by decide
  rcases family_descends (prefixWord ++ tailWord_2870172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2870243 : List Nat := [1, 1, 1, 6, 1, 1, 1, 2, 4, 4]
def baseStart_2870243 : Nat := 118140960795 + 2870243 * 2 ^ 59
def prefixEnd_2870243 : Nat := 4983230072969 + 3 ^ 40 * 2870243 * 2
def baseEnd_2870243 : Nat := 982542836135279263174999

theorem tailTrace_2870243 : CollatzResearch.WordTrace tailWord_2870243 prefixEnd_2870243 982542836135279263174999 := by
  unfold tailWord_2870243
  simp only [CollatzResearch.WordTrace]
  refine ⟨104686362540607284322815383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69790908360404856215210255 104686362540607284322815383)
  ·
    refine ⟨157029543810910926484223075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104686362540607284322815383 157029543810910926484223075)
    ·
      refine ⟨235544315716366389726334613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157029543810910926484223075 235544315716366389726334613)
      ·
        refine ⟨11041139799204674518421935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 235544315716366389726334613 11041139799204674518421935)
        ·
          refine ⟨16561709698807011777632903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11041139799204674518421935 16561709698807011777632903)
          ·
            refine ⟨24842564548210517666449355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16561709698807011777632903 24842564548210517666449355)
            ·
              refine ⟨37263846822315776499674033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24842564548210517666449355 37263846822315776499674033)
              ·
                refine ⟨27947885116736832374755525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37263846822315776499674033 27947885116736832374755525)
                ·
                  refine ⟨5240228459388156070266661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27947885116736832374755525 5240228459388156070266661)
                  ·
                    refine ⟨982542836135279263174999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5240228459388156070266661 982542836135279263174999)
                    ·
                      rfl

theorem cell22_2870243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 2, 4, 4].length) (baseStart_2870243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2870243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2870243 prefixEnd_2870243 := by exact prefixLift 2870243
  have htrace : WordTrace (prefixWord ++ tailWord_2870243) baseStart_2870243 baseEnd_2870243 := by
    simpa [prefixWord, tailWord_2870243, baseEnd_2870243] using wordTrace_append hprefix tailTrace_2870243
  have hstable : (prefixWord ++ tailWord_2870243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2870243).length < 2 ^ (prefixWord ++ tailWord_2870243).sum := by decide
  have hdescent : baseEnd_2870243 < baseStart_2870243 := by decide
  rcases family_descends (prefixWord ++ tailWord_2870243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2870380 : List Nat := [2, 2, 1, 1, 3, 2, 1, 1, 6, 3]
def baseStart_2870380 : Nat := 118140960795 + 2870380 * 2 ^ 59
def prefixEnd_2870380 : Nat := 4983230072969 + 3 ^ 40 * 2870380 * 2
def baseEnd_2870380 : Nat := 982589734035056572499579

theorem tailTrace_2870380 : CollatzResearch.WordTrace tailWord_2870380 prefixEnd_2870380 982589734035056572499579 := by
  unfold tailWord_2870380
  simp only [CollatzResearch.WordTrace]
  refine ⟨52345679670555478360276297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69794239560740637813701729 52345679670555478360276297)
  ·
    refine ⟨39259259752916608770207223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52345679670555478360276297 39259259752916608770207223)
    ·
      refine ⟨58888889629374913155310835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39259259752916608770207223 58888889629374913155310835)
      ·
        refine ⟨88333334444062369732966253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58888889629374913155310835 88333334444062369732966253)
        ·
          refine ⟨33125000416523388649862345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88333334444062369732966253 33125000416523388649862345)
          ·
            refine ⟨24843750312392541487396759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33125000416523388649862345 24843750312392541487396759)
            ·
              refine ⟨37265625468588812231095139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24843750312392541487396759 37265625468588812231095139)
              ·
                refine ⟨55898438202883218346642709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37265625468588812231095139 55898438202883218346642709)
                ·
                  refine ⟨2620239290760150859998877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 55898438202883218346642709 2620239290760150859998877)
                  ·
                    refine ⟨982589734035056572499579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2620239290760150859998877 982589734035056572499579)
                    ·
                      rfl

theorem cell22_2870380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 3].length) (baseStart_2870380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2870380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2870380 prefixEnd_2870380 := by exact prefixLift 2870380
  have htrace : WordTrace (prefixWord ++ tailWord_2870380) baseStart_2870380 baseEnd_2870380 := by
    simpa [prefixWord, tailWord_2870380, baseEnd_2870380] using wordTrace_append hprefix tailTrace_2870380
  have hstable : (prefixWord ++ tailWord_2870380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2870380).length < 2 ^ (prefixWord ++ tailWord_2870380).sum := by decide
  have hdescent : baseEnd_2870380 < baseStart_2870380 := by decide
  rcases family_descends (prefixWord ++ tailWord_2870380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2870397 : List Nat := [1, 4, 1, 1, 3, 1, 2, 4, 2, 3]
def baseStart_2870397 : Nat := 118140960795 + 2870397 * 2 ^ 59
def prefixEnd_2870397 : Nat := 4983230072969 + 3 ^ 40 * 2870397 * 2
def baseEnd_2870397 : Nat := 982595553482474194824527

theorem tailTrace_2870397 : CollatzResearch.WordTrace tailWord_2870397 prefixEnd_2870397 982595553482474194824527 := by
  unfold tailWord_2870397
  simp only [CollatzResearch.WordTrace]
  refine ⟨104691979382049368623921445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69794652921366245749280963 104691979382049368623921445)
  ·
    refine ⟨19629746134134256616985271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104691979382049368623921445 19629746134134256616985271)
    ·
      refine ⟨29444619201201384925477907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19629746134134256616985271 29444619201201384925477907)
      ·
        refine ⟨44166928801802077388216861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29444619201201384925477907 44166928801802077388216861)
        ·
          refine ⟨16562598300675779020581323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44166928801802077388216861 16562598300675779020581323)
          ·
            refine ⟨24843897451013668530871985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16562598300675779020581323 24843897451013668530871985)
            ·
              refine ⟨18632923088260251398153989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24843897451013668530871985 18632923088260251398153989)
              ·
                refine ⟨3493673079048797137153873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18632923088260251398153989 3493673079048797137153873)
                ·
                  refine ⟨2620254809286597852865405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3493673079048797137153873 2620254809286597852865405)
                  ·
                    refine ⟨982595553482474194824527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2620254809286597852865405 982595553482474194824527)
                    ·
                      rfl

theorem cell22_2870397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 4, 2, 3].length) (baseStart_2870397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2870397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2870397 prefixEnd_2870397 := by exact prefixLift 2870397
  have htrace : WordTrace (prefixWord ++ tailWord_2870397) baseStart_2870397 baseEnd_2870397 := by
    simpa [prefixWord, tailWord_2870397, baseEnd_2870397] using wordTrace_append hprefix tailTrace_2870397
  have hstable : (prefixWord ++ tailWord_2870397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2870397).length < 2 ^ (prefixWord ++ tailWord_2870397).sum := by decide
  have hdescent : baseEnd_2870397 < baseStart_2870397 := by decide
  rcases family_descends (prefixWord ++ tailWord_2870397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2870410 : List Nat := [3, 1, 2, 3, 1, 1, 4, 7]
def baseStart_2870410 : Nat := 118140960795 + 2870410 * 2 ^ 59
def prefixEnd_2870410 : Nat := 4983230072969 + 3 ^ 40 * 2870410 * 2
def baseEnd_2870410 : Nat := 109177778183127388249943

theorem tailTrace_2870410 : CollatzResearch.WordTrace tailWord_2870410 prefixEnd_2870410 109177778183127388249943 := by
  unfold tailWord_2870410
  simp only [CollatzResearch.WordTrace]
  refine ⟨26173113382750567961036171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69794969020668181229429789 26173113382750567961036171)
  ·
    refine ⟨39259670074125851941554257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26173113382750567961036171 39259670074125851941554257)
    ·
      refine ⟨29444752555594388956165693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39259670074125851941554257 29444752555594388956165693)
      ·
        refine ⟨11041782208347895858562135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29444752555594388956165693 11041782208347895858562135)
        ·
          refine ⟨16562673312521843787843203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11041782208347895858562135 16562673312521843787843203)
          ·
            refine ⟨24844009968782765681764805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16562673312521843787843203 24844009968782765681764805)
            ·
              refine ⟨4658251869146768565330901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24844009968782765681764805 4658251869146768565330901)
              ·
                refine ⟨109177778183127388249943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4658251869146768565330901 109177778183127388249943)
                ·
                  rfl

theorem cell22_2870410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 4, 7].length) (baseStart_2870410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2870410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2870410 prefixEnd_2870410 := by exact prefixLift 2870410
  have htrace : WordTrace (prefixWord ++ tailWord_2870410) baseStart_2870410 baseEnd_2870410 := by
    simpa [prefixWord, tailWord_2870410, baseEnd_2870410] using wordTrace_append hprefix tailTrace_2870410
  have hstable : (prefixWord ++ tailWord_2870410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2870410).length < 2 ^ (prefixWord ++ tailWord_2870410).sum := by decide
  have hdescent : baseEnd_2870410 < baseStart_2870410 := by decide
  rcases family_descends (prefixWord ++ tailWord_2870410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2870414 : List Nat := [4, 1, 1, 3, 2, 2, 1, 3, 2, 3]
def baseStart_2870414 : Nat := 118140960795 + 2870414 * 2 ^ 59
def prefixEnd_2870414 : Nat := 4983230072969 + 3 ^ 40 * 2870414 * 2
def baseEnd_2870414 : Nat := 982601372929891817149475

theorem tailTrace_2870414 : CollatzResearch.WordTrace tailWord_2870414 prefixEnd_2870414 982601372929891817149475 := by
  unfold tailWord_2870414
  simp only [CollatzResearch.WordTrace]
  refine ⟨13086574927873472565911287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69795066281991853684860197 13086574927873472565911287)
  ·
    refine ⟨19629862391810208848866931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13086574927873472565911287 19629862391810208848866931)
    ·
      refine ⟨29444793587715313273300397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19629862391810208848866931 29444793587715313273300397)
      ·
        refine ⟨11041797595393242477487649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29444793587715313273300397 11041797595393242477487649)
        ·
          refine ⟨8281348196544931858115737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11041797595393242477487649 8281348196544931858115737)
          ·
            refine ⟨6211011147408698893586803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8281348196544931858115737 6211011147408698893586803)
            ·
              refine ⟨9316516721113048340380205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6211011147408698893586803 9316516721113048340380205)
              ·
                refine ⟨3493693770417393127642577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9316516721113048340380205 3493693770417393127642577)
                ·
                  refine ⟨2620270327813044845731933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3493693770417393127642577 2620270327813044845731933)
                  ·
                    refine ⟨982601372929891817149475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2620270327813044845731933 982601372929891817149475)
                    ·
                      rfl

theorem cell22_2870414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 3, 2, 3].length) (baseStart_2870414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2870414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2870414 prefixEnd_2870414 := by exact prefixLift 2870414
  have htrace : WordTrace (prefixWord ++ tailWord_2870414) baseStart_2870414 baseEnd_2870414 := by
    simpa [prefixWord, tailWord_2870414, baseEnd_2870414] using wordTrace_append hprefix tailTrace_2870414
  have hstable : (prefixWord ++ tailWord_2870414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2870414).length < 2 ^ (prefixWord ++ tailWord_2870414).sum := by decide
  have hdescent : baseEnd_2870414 < baseStart_2870414 := by decide
  rcases family_descends (prefixWord ++ tailWord_2870414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2870493 : List Nat := [1, 4, 3, 2, 2, 1, 2, 3, 1, 3]
def baseStart_2870493 : Nat := 118140960795 + 2870493 * 2 ^ 59
def prefixEnd_2870493 : Nat := 4983230072969 + 3 ^ 40 * 2870493 * 2
def baseEnd_2870493 : Nat := 982628416244361944424233

theorem tailTrace_2870493 : CollatzResearch.WordTrace tailWord_2870493 prefixEnd_2870493 982628416244361944424233 := by
  unfold tailWord_2870493
  simp only [CollatzResearch.WordTrace]
  refine ⟨104695480789701577019416133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69796987193134384679610755 104695480789701577019416133)
  ·
    refine ⟨19630402648069045691140525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104695480789701577019416133 19630402648069045691140525)
    ·
      refine ⟨7361400993025892134177697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19630402648069045691140525 7361400993025892134177697)
      ·
        refine ⟨5521050744769419100633273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7361400993025892134177697 5521050744769419100633273)
        ·
          refine ⟨4140788058577064325474955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5521050744769419100633273 4140788058577064325474955)
          ·
            refine ⟨6211182087865596488212433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4140788058577064325474955 6211182087865596488212433)
            ·
              refine ⟨4658386565899197366159325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6211182087865596488212433 4658386565899197366159325)
              ·
                refine ⟨1746894962212199012309747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4658386565899197366159325 1746894962212199012309747)
                ·
                  refine ⟨2620342443318298518464621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1746894962212199012309747 2620342443318298518464621)
                  ·
                    refine ⟨982628416244361944424233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2620342443318298518464621 982628416244361944424233)
                    ·
                      rfl

theorem cell22_2870493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 2, 3, 1, 3].length) (baseStart_2870493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2870493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2870493 prefixEnd_2870493 := by exact prefixLift 2870493
  have htrace : WordTrace (prefixWord ++ tailWord_2870493) baseStart_2870493 baseEnd_2870493 := by
    simpa [prefixWord, tailWord_2870493, baseEnd_2870493] using wordTrace_append hprefix tailTrace_2870493
  have hstable : (prefixWord ++ tailWord_2870493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2870493).length < 2 ^ (prefixWord ++ tailWord_2870493).sum := by decide
  have hdescent : baseEnd_2870493 < baseStart_2870493 := by decide
  rcases family_descends (prefixWord ++ tailWord_2870493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2870545 : List Nat := [1, 2, 2, 1, 1, 4, 3, 8]
def baseStart_2870545 : Nat := 118140960795 + 2870545 * 2 ^ 59
def prefixEnd_2870545 : Nat := 4983230072969 + 3 ^ 40 * 2870545 * 2
def baseEnd_2870545 : Nat := 109182912989672349124897

theorem tailTrace_2870545 : CollatzResearch.WordTrace tailWord_2870545 prefixEnd_2870545 109182912989672349124897 := by
  unfold tailWord_2870545
  simp only [CollatzResearch.WordTrace]
  refine ⟨104697377385513189900309089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69798251590342126600206059 104697377385513189900309089)
  ·
    refine ⟨78523033039134892425231817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104697377385513189900309089 78523033039134892425231817)
    ·
      refine ⟨58892274779351169318923863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78523033039134892425231817 58892274779351169318923863)
      ·
        refine ⟨88338412169026753978385795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58892274779351169318923863 88338412169026753978385795)
        ·
          refine ⟨132507618253540130967578693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88338412169026753978385795 132507618253540130967578693)
          ·
            refine ⟨24845178422538774556421005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 132507618253540130967578693 24845178422538774556421005)
            ·
              refine ⟨9316941908452040458657877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24845178422538774556421005 9316941908452040458657877)
              ·
                refine ⟨109182912989672349124897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9316941908452040458657877 109182912989672349124897)
                ·
                  rfl

theorem cell22_2870545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 8].length) (baseStart_2870545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2870545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2870545 prefixEnd_2870545 := by exact prefixLift 2870545
  have htrace : WordTrace (prefixWord ++ tailWord_2870545) baseStart_2870545 baseEnd_2870545 := by
    simpa [prefixWord, tailWord_2870545, baseEnd_2870545] using wordTrace_append hprefix tailTrace_2870545
  have hstable : (prefixWord ++ tailWord_2870545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2870545).length < 2 ^ (prefixWord ++ tailWord_2870545).sum := by decide
  have hdescent : baseEnd_2870545 < baseStart_2870545 := by decide
  rcases family_descends (prefixWord ++ tailWord_2870545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2870575 : List Nat := [1, 1, 2, 1, 2, 1, 3, 3, 2, 6]
def baseStart_2870575 : Nat := 118140960795 + 2870575 * 2 ^ 59
def prefixEnd_2870575 : Nat := 4983230072969 + 3 ^ 40 * 2870575 * 2
def baseEnd_2870575 : Nat := 982656486520141063873981

theorem tailTrace_2870575 : CollatzResearch.WordTrace tailWord_2870575 prefixEnd_2870575 982656486520141063873981 := by
  unfold tailWord_2870575
  simp only [CollatzResearch.WordTrace]
  refine ⟨104698471575404505023901179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69798981050269670015934119 104698471575404505023901179)
  ·
    refine ⟨157047707363106757535851769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104698471575404505023901179 157047707363106757535851769)
    ·
      refine ⟨117785780522330068151888827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157047707363106757535851769 117785780522330068151888827)
      ·
        refine ⟨176678670783495102227833241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117785780522330068151888827 176678670783495102227833241)
        ·
          refine ⟨132509003087621326670874931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176678670783495102227833241 132509003087621326670874931)
          ·
            refine ⟨198763504631431990006312397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132509003087621326670874931 198763504631431990006312397)
            ·
              refine ⟨74536314236786996252367149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 198763504631431990006312397 74536314236786996252367149)
              ·
                refine ⟨27951117838795123594637681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74536314236786996252367149 27951117838795123594637681)
                ·
                  refine ⟨20963338379096342695978261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27951117838795123594637681 20963338379096342695978261)
                  ·
                    refine ⟨982656486520141063873981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20963338379096342695978261 982656486520141063873981)
                    ·
                      rfl

theorem cell22_2870575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 3, 2, 6].length) (baseStart_2870575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2870575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2870575 prefixEnd_2870575 := by exact prefixLift 2870575
  have htrace : WordTrace (prefixWord ++ tailWord_2870575) baseStart_2870575 baseEnd_2870575 := by
    simpa [prefixWord, tailWord_2870575, baseEnd_2870575] using wordTrace_append hprefix tailTrace_2870575
  have hstable : (prefixWord ++ tailWord_2870575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2870575).length < 2 ^ (prefixWord ++ tailWord_2870575).sum := by decide
  have hdescent : baseEnd_2870575 < baseStart_2870575 := by decide
  rcases family_descends (prefixWord ++ tailWord_2870575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2870624 : List Nat := [2, 1, 1, 3, 4, 2, 2, 2, 5]
def baseStart_2870624 : Nat := 118140960795 + 2870624 * 2 ^ 59
def prefixEnd_2870624 : Nat := 4983230072969 + 3 ^ 40 * 2870624 * 2
def baseEnd_2870624 : Nat := 327557753407173756466277

theorem tailTrace_2870624 : CollatzResearch.WordTrace tailWord_2870624 prefixEnd_2870624 327557753407173756466277 := by
  unfold tailWord_2870624
  simp only [CollatzResearch.WordTrace]
  refine ⟨52350129376113493196217463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69800172501484657594956617 52350129376113493196217463)
  ·
    refine ⟨78525194064170239794326195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52350129376113493196217463 78525194064170239794326195)
    ·
      refine ⟨117787791096255359691489293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78525194064170239794326195 117787791096255359691489293)
      ·
        refine ⟨44170421661095759884308485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117787791096255359691489293 44170421661095759884308485)
        ·
          refine ⟨8281954061455454978307841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44170421661095759884308485 8281954061455454978307841)
          ·
            refine ⟨6211465546091591233730881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8281954061455454978307841 6211465546091591233730881)
            ·
              refine ⟨4658599159568693425298161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6211465546091591233730881 4658599159568693425298161)
              ·
                refine ⟨3493949369676520068973621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4658599159568693425298161 3493949369676520068973621)
                ·
                  refine ⟨327557753407173756466277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3493949369676520068973621 327557753407173756466277)
                  ·
                    rfl

theorem cell22_2870624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 2, 2, 5].length) (baseStart_2870624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2870624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2870624 prefixEnd_2870624 := by exact prefixLift 2870624
  have htrace : WordTrace (prefixWord ++ tailWord_2870624) baseStart_2870624 baseEnd_2870624 := by
    simpa [prefixWord, tailWord_2870624, baseEnd_2870624] using wordTrace_append hprefix tailTrace_2870624
  have hstable : (prefixWord ++ tailWord_2870624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2870624).length < 2 ^ (prefixWord ++ tailWord_2870624).sum := by decide
  have hdescent : baseEnd_2870624 < baseStart_2870624 := by decide
  rcases family_descends (prefixWord ++ tailWord_2870624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2870628 : List Nat := [2, 3, 1, 1, 3, 2, 4, 2, 1, 3]
def baseStart_2870628 : Nat := 118140960795 + 2870628 * 2 ^ 59
def prefixEnd_2870628 : Nat := 4983230072969 + 3 ^ 40 * 2870628 * 2
def baseEnd_2870628 : Nat := 982674629503266592298819

theorem tailTrace_2870628 : CollatzResearch.WordTrace tailWord_2870628 prefixEnd_2870628 982674629503266592298819 := by
  unfold tailWord_2870628
  simp only [CollatzResearch.WordTrace]
  refine ⟨52350202322106247537790269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69800269762808330050387025 52350202322106247537790269)
  ·
    refine ⟨19631325870789842826671351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52350202322106247537790269 19631325870789842826671351)
    ·
      refine ⟨29446988806184764240007027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19631325870789842826671351 29446988806184764240007027)
      ·
        refine ⟨44170483209277146360010541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29446988806184764240007027 44170483209277146360010541)
        ·
          refine ⟨16563931203478929885003953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44170483209277146360010541 16563931203478929885003953)
          ·
            refine ⟨12422948402609197413752965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16563931203478929885003953 12422948402609197413752965)
            ·
              refine ⟨2329302825489224515078681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12422948402609197413752965 2329302825489224515078681)
              ·
                refine ⟨1746977119116918386309011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2329302825489224515078681 1746977119116918386309011)
                ·
                  refine ⟨2620465678675377579463517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1746977119116918386309011 2620465678675377579463517)
                  ·
                    refine ⟨982674629503266592298819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2620465678675377579463517 982674629503266592298819)
                    ·
                      rfl

theorem cell22_2870628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 4, 2, 1, 3].length) (baseStart_2870628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2870628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2870628 prefixEnd_2870628 := by exact prefixLift 2870628
  have htrace : WordTrace (prefixWord ++ tailWord_2870628) baseStart_2870628 baseEnd_2870628 := by
    simpa [prefixWord, tailWord_2870628, baseEnd_2870628] using wordTrace_append hprefix tailTrace_2870628
  have hstable : (prefixWord ++ tailWord_2870628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2870628).length < 2 ^ (prefixWord ++ tailWord_2870628).sum := by decide
  have hdescent : baseEnd_2870628 < baseStart_2870628 := by decide
  rcases family_descends (prefixWord ++ tailWord_2870628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2870652 : List Nat := [2, 2, 2, 1, 1, 1, 5, 2, 6]
def baseStart_2870652 : Nat := 118140960795 + 2870652 * 2 ^ 59
def prefixEnd_2870652 : Nat := 4983230072969 + 3 ^ 40 * 2870652 * 2
def baseEnd_2870652 : Nat := 327560948397912843232915

theorem tailTrace_2870652 : CollatzResearch.WordTrace tailWord_2870652 prefixEnd_2870652 327560948397912843232915 := by
  unfold tailWord_2870652
  simp only [CollatzResearch.WordTrace]
  refine ⟨52350639998062773587227105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69800853330750364782969473 52350639998062773587227105)
  ·
    refine ⟨39262979998547080190420329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52350639998062773587227105 39262979998547080190420329)
    ·
      refine ⟨29447234998910310142815247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39262979998547080190420329 29447234998910310142815247)
      ·
        refine ⟨44170852498365465214222871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29447234998910310142815247 44170852498365465214222871)
        ·
          refine ⟨66256278747548197821334307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44170852498365465214222871 66256278747548197821334307)
          ·
            refine ⟨99384418121322296732001461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66256278747548197821334307 99384418121322296732001461)
            ·
              refine ⟨9317289198873965318625137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 99384418121322296732001461 9317289198873965318625137)
              ·
                refine ⟨6987966899155473988968853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9317289198873965318625137 6987966899155473988968853)
                ·
                  refine ⟨327560948397912843232915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6987966899155473988968853 327560948397912843232915)
                  ·
                    rfl

theorem cell22_2870652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 2, 6].length) (baseStart_2870652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2870652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2870652 prefixEnd_2870652 := by exact prefixLift 2870652
  have htrace : WordTrace (prefixWord ++ tailWord_2870652) baseStart_2870652 baseEnd_2870652 := by
    simpa [prefixWord, tailWord_2870652, baseEnd_2870652] using wordTrace_append hprefix tailTrace_2870652
  have hstable : (prefixWord ++ tailWord_2870652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2870652).length < 2 ^ (prefixWord ++ tailWord_2870652).sum := by decide
  have hdescent : baseEnd_2870652 < baseStart_2870652 := by decide
  rcases family_descends (prefixWord ++ tailWord_2870652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2870667 : List Nat := [1, 1, 1, 1, 4, 3, 1, 4, 1, 5]
def baseStart_2870667 : Nat := 118140960795 + 2870667 * 2 ^ 59
def prefixEnd_2870667 : Nat := 4983230072969 + 3 ^ 40 * 2870667 * 2
def baseEnd_2870667 : Nat := 982687980000283490573699

theorem tailTrace_2870667 : CollatzResearch.WordTrace tailWord_2870667 prefixEnd_2870667 982687980000283490573699 := by
  unfold tailWord_2870667
  simp only [CollatzResearch.WordTrace]
  refine ⟨104701827091071204736250255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69801218060714136490833503 104701827091071204736250255)
  ·
    refine ⟨157052740636606807104375383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104701827091071204736250255 157052740636606807104375383)
    ·
      refine ⟨235579110954910210656563075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157052740636606807104375383 235579110954910210656563075)
      ·
        refine ⟨353368666432365315984844613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235579110954910210656563075 353368666432365315984844613)
        ·
          refine ⟨66256624956068496747158365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 353368666432365315984844613 66256624956068496747158365)
          ·
            refine ⟨24846234358525686280184387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66256624956068496747158365 24846234358525686280184387)
            ·
              refine ⟨37269351537788529420276581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24846234358525686280184387 37269351537788529420276581)
              ·
                refine ⟨6988003413335349266301859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37269351537788529420276581 6988003413335349266301859)
                ·
                  refine ⟨10482005120003023899452789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6988003413335349266301859 10482005120003023899452789)
                  ·
                    refine ⟨982687980000283490573699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10482005120003023899452789 982687980000283490573699)
                    ·
                      rfl

theorem cell22_2870667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 4, 1, 5].length) (baseStart_2870667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2870667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2870667 prefixEnd_2870667 := by exact prefixLift 2870667
  have htrace : WordTrace (prefixWord ++ tailWord_2870667) baseStart_2870667 baseEnd_2870667 := by
    simpa [prefixWord, tailWord_2870667, baseEnd_2870667] using wordTrace_append hprefix tailTrace_2870667
  have hstable : (prefixWord ++ tailWord_2870667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2870667).length < 2 ^ (prefixWord ++ tailWord_2870667).sum := by decide
  have hdescent : baseEnd_2870667 < baseStart_2870667 := by decide
  rcases family_descends (prefixWord ++ tailWord_2870667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2870701 : List Nat := [1, 5, 2, 2, 1, 1, 3, 1, 1, 5]
def baseStart_2870701 : Nat := 118140960795 + 2870701 * 2 ^ 59
def prefixEnd_2870701 : Nat := 4983230072969 + 3 ^ 40 * 2870701 * 2
def baseEnd_2870701 : Nat := 982699618895118735223595

theorem tailTrace_2870701 : CollatzResearch.WordTrace tailWord_2870701 prefixEnd_2870701 982699618895118735223595 := by
  unfold tailWord_2870701
  simp only [CollatzResearch.WordTrace]
  refine ⟨104703067172948028542987957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69802044781965352361991971 104703067172948028542987957)
  ·
    refine ⟨9815912547463877675905121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 104703067172948028542987957 9815912547463877675905121)
    ·
      refine ⟨7361934410597908256928841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9815912547463877675905121 7361934410597908256928841)
      ·
        refine ⟨5521450807948431192696631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7361934410597908256928841 5521450807948431192696631)
        ·
          refine ⟨8282176211922646789044947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5521450807948431192696631 8282176211922646789044947)
          ·
            refine ⟨12423264317883970183567421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8282176211922646789044947 12423264317883970183567421)
            ·
              refine ⟨4658724119206488818837783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12423264317883970183567421 4658724119206488818837783)
              ·
                refine ⟨6988086178809733228256675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4658724119206488818837783 6988086178809733228256675)
                ·
                  refine ⟨10482129268214599842385013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6988086178809733228256675 10482129268214599842385013)
                  ·
                    refine ⟨982699618895118735223595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10482129268214599842385013 982699618895118735223595)
                    ·
                      rfl

theorem cell22_2870701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_2870701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2870701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2870701 prefixEnd_2870701 := by exact prefixLift 2870701
  have htrace : WordTrace (prefixWord ++ tailWord_2870701) baseStart_2870701 baseEnd_2870701 := by
    simpa [prefixWord, tailWord_2870701, baseEnd_2870701] using wordTrace_append hprefix tailTrace_2870701
  have hstable : (prefixWord ++ tailWord_2870701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2870701).length < 2 ^ (prefixWord ++ tailWord_2870701).sum := by decide
  have hdescent : baseEnd_2870701 < baseStart_2870701 := by decide
  rcases family_descends (prefixWord ++ tailWord_2870701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2870746 : List Nat := [3, 1, 1, 2, 3, 2, 3, 1, 3, 3]
def baseStart_2870746 : Nat := 118140960795 + 2870746 * 2 ^ 59
def prefixEnd_2870746 : Nat := 4983230072969 + 3 ^ 40 * 2870746 * 2
def baseEnd_2870746 : Nat := 982715023314753617848457

theorem tailTrace_2870746 : CollatzResearch.WordTrace tailWord_2870746 prefixEnd_2870746 982715023314753617848457 := by
  unfold tailWord_2870746
  simp only [CollatzResearch.WordTrace]
  refine ⟨26176177114446250307094023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69803138971856667485584061 26176177114446250307094023)
  ·
    refine ⟨39264265671669375460641035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26176177114446250307094023 39264265671669375460641035)
    ·
      refine ⟨58896398507504063190961553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39264265671669375460641035 58896398507504063190961553)
      ·
        refine ⟨44172298880628047393221165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58896398507504063190961553 44172298880628047393221165)
        ·
          refine ⟨16564612080235517772457937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44172298880628047393221165 16564612080235517772457937)
          ·
            refine ⟨12423459060176638329343453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16564612080235517772457937 12423459060176638329343453)
            ·
              refine ⟨4658797147566239373503795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12423459060176638329343453 4658797147566239373503795)
              ·
                refine ⟨6988195721349359060255693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4658797147566239373503795 6988195721349359060255693)
                ·
                  refine ⟨2620573395506009647595885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6988195721349359060255693 2620573395506009647595885)
                  ·
                    refine ⟨982715023314753617848457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2620573395506009647595885 982715023314753617848457)
                    ·
                      rfl

theorem cell22_2870746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 3, 1, 3, 3].length) (baseStart_2870746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2870746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2870746 prefixEnd_2870746 := by exact prefixLift 2870746
  have htrace : WordTrace (prefixWord ++ tailWord_2870746) baseStart_2870746 baseEnd_2870746 := by
    simpa [prefixWord, tailWord_2870746, baseEnd_2870746] using wordTrace_append hprefix tailTrace_2870746
  have hstable : (prefixWord ++ tailWord_2870746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2870746).length < 2 ^ (prefixWord ++ tailWord_2870746).sum := by decide
  have hdescent : baseEnd_2870746 < baseStart_2870746 := by decide
  rcases family_descends (prefixWord ++ tailWord_2870746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2870787 : List Nat := [1, 1, 1, 3, 2, 1, 2, 1, 10]
def baseStart_2870787 : Nat := 118140960795 + 2870787 * 2 ^ 59
def prefixEnd_2870787 : Nat := 4983230072969 + 3 ^ 40 * 2870787 * 2
def baseEnd_2870787 : Nat := 327576352817547725857777

theorem tailTrace_2870787 : CollatzResearch.WordTrace tailWord_2870787 prefixEnd_2870787 327576352817547725857777 := by
  unfold tailWord_2870787
  simp only [CollatzResearch.WordTrace]
  refine ⟨104706203850636465230618615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69804135900424310153745743 104706203850636465230618615)
  ·
    refine ⟨157059305775954697845927923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104706203850636465230618615 157059305775954697845927923)
    ·
      refine ⟨235588958663932046768891885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157059305775954697845927923 235588958663932046768891885)
      ·
        refine ⟨88345859498974517538334457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 235588958663932046768891885 88345859498974517538334457)
        ·
          refine ⟨66259394624230888153750843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88345859498974517538334457 66259394624230888153750843)
          ·
            refine ⟨99389091936346332230626265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66259394624230888153750843 99389091936346332230626265)
            ·
              refine ⟨74541818952259749172969699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99389091936346332230626265 74541818952259749172969699)
              ·
                refine ⟨111812728428389623759454549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74541818952259749172969699 111812728428389623759454549)
                ·
                  refine ⟨327576352817547725857777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 111812728428389623759454549 327576352817547725857777)
                  ·
                    rfl

theorem cell22_2870787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 10].length) (baseStart_2870787 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2870787 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2870787 prefixEnd_2870787 := by exact prefixLift 2870787
  have htrace : WordTrace (prefixWord ++ tailWord_2870787) baseStart_2870787 baseEnd_2870787 := by
    simpa [prefixWord, tailWord_2870787, baseEnd_2870787] using wordTrace_append hprefix tailTrace_2870787
  have hstable : (prefixWord ++ tailWord_2870787).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2870787).length < 2 ^ (prefixWord ++ tailWord_2870787).sum := by decide
  have hdescent : baseEnd_2870787 < baseStart_2870787 := by decide
  rcases family_descends (prefixWord ++ tailWord_2870787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2870849 : List Nat := [1, 2, 5, 1, 1, 1, 11]
def baseStart_2870849 : Nat := 118140960795 + 2870849 * 2 ^ 59
def prefixEnd_2870849 : Nat := 4983230072969 + 3 ^ 40 * 2870849 * 2
def baseEnd_2870849 : Nat := 36398158604433173426783

theorem tailTrace_2870849 : CollatzResearch.WordTrace tailWord_2870849 prefixEnd_2870849 36398158604433173426783 := by
  unfold tailWord_2870849
  simp only [CollatzResearch.WordTrace]
  refine ⟨104708465176411849819375601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69805643450941233212917067 104708465176411849819375601)
  ·
    refine ⟨78531348882308887364531701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104708465176411849819375601 78531348882308887364531701)
    ·
      refine ⟨7362313957716458190424847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 78531348882308887364531701 7362313957716458190424847)
      ·
        refine ⟨11043470936574687285637271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7362313957716458190424847 11043470936574687285637271)
        ·
          refine ⟨16565206404862030928455907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11043470936574687285637271 16565206404862030928455907)
          ·
            refine ⟨24847809607293046392683861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16565206404862030928455907 24847809607293046392683861)
            ·
              refine ⟨36398158604433173426783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 24847809607293046392683861 36398158604433173426783)
              ·
                rfl

theorem cell22_2870849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 11].length) (baseStart_2870849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2870849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2870849 prefixEnd_2870849 := by exact prefixLift 2870849
  have htrace : WordTrace (prefixWord ++ tailWord_2870849) baseStart_2870849 baseEnd_2870849 := by
    simpa [prefixWord, tailWord_2870849, baseEnd_2870849] using wordTrace_append hprefix tailTrace_2870849
  have hstable : (prefixWord ++ tailWord_2870849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2870849).length < 2 ^ (prefixWord ++ tailWord_2870849).sum := by decide
  have hdescent : baseEnd_2870849 < baseStart_2870849 := by decide
  rcases family_descends (prefixWord ++ tailWord_2870849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2870881 : List Nat := [1, 2, 3, 1, 1, 3, 1, 4, 3, 3]
def baseStart_2870881 : Nat := 118140960795 + 2870881 * 2 ^ 59
def prefixEnd_2870881 : Nat := 4983230072969 + 3 ^ 40 * 2870881 * 2
def baseEnd_2870881 : Nat := 982761236573658265723043

theorem tailTrace_2870881 : CollatzResearch.WordTrace tailWord_2870881 prefixEnd_2870881 982761236573658265723043 := by
  unfold tailWord_2870881
  simp only [CollatzResearch.WordTrace]
  refine ⟨104709632312295919284540497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69806421541530612856360331 104709632312295919284540497)
  ·
    refine ⟨78532224234221939463405373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104709632312295919284540497 78532224234221939463405373)
    ·
      refine ⟨29449584087833227298777015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78532224234221939463405373 29449584087833227298777015)
      ·
        refine ⟨44174376131749840948165523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29449584087833227298777015 44174376131749840948165523)
        ·
          refine ⟨66261564197624761422248285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44174376131749840948165523 66261564197624761422248285)
          ·
            refine ⟨24848086574109285533343107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66261564197624761422248285 24848086574109285533343107)
            ·
              refine ⟨37272129861163928300014661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24848086574109285533343107 37272129861163928300014661)
              ·
                refine ⟨6988524348968236556252749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37272129861163928300014661 6988524348968236556252749)
                ·
                  refine ⟨2620696630863088708594781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6988524348968236556252749 2620696630863088708594781)
                  ·
                    refine ⟨982761236573658265723043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2620696630863088708594781 982761236573658265723043)
                    ·
                      rfl

theorem cell22_2870881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 4, 3, 3].length) (baseStart_2870881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2870881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2870881 prefixEnd_2870881 := by exact prefixLift 2870881
  have htrace : WordTrace (prefixWord ++ tailWord_2870881) baseStart_2870881 baseEnd_2870881 := by
    simpa [prefixWord, tailWord_2870881, baseEnd_2870881] using wordTrace_append hprefix tailTrace_2870881
  have hstable : (prefixWord ++ tailWord_2870881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2870881).length < 2 ^ (prefixWord ++ tailWord_2870881).sum := by decide
  have hdescent : baseEnd_2870881 < baseStart_2870881 := by decide
  rcases family_descends (prefixWord ++ tailWord_2870881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2870966 : List Nat := [5, 1, 3, 1, 1, 3, 2, 2, 1, 3]
def baseStart_2870966 : Nat := 118140960795 + 2870966 * 2 ^ 59
def prefixEnd_2870966 : Nat := 4983230072969 + 3 ^ 40 * 2870966 * 2
def baseEnd_2870966 : Nat := 982790333810746377347783

theorem tailTrace_2870966 : CollatzResearch.WordTrace tailWord_2870966 prefixEnd_2870966 982790333810746377347783 := by
  unfold tailWord_2870966
  simp only [CollatzResearch.WordTrace]
  refine ⟨6544545782311748675086547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 69808488344658652534256501 6544545782311748675086547)
  ·
    refine ⟨9816818673467623012629821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6544545782311748675086547 9816818673467623012629821)
    ·
      refine ⟨3681307002550358629736183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9816818673467623012629821 3681307002550358629736183)
      ·
        refine ⟨5521960503825537944604275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3681307002550358629736183 5521960503825537944604275)
        ·
          refine ⟨8282940755738306916906413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5521960503825537944604275 8282940755738306916906413)
          ·
            refine ⟨3106102783401865093839905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8282940755738306916906413 3106102783401865093839905)
            ·
              refine ⟨2329577087551398820379929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3106102783401865093839905 2329577087551398820379929)
              ·
                refine ⟨1747182815663549115284947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2329577087551398820379929 1747182815663549115284947)
                ·
                  refine ⟨2620774223495323672927421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1747182815663549115284947 2620774223495323672927421)
                  ·
                    refine ⟨982790333810746377347783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2620774223495323672927421 982790333810746377347783)
                    ·
                      rfl

theorem cell22_2870966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_2870966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2870966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2870966 prefixEnd_2870966 := by exact prefixLift 2870966
  have htrace : WordTrace (prefixWord ++ tailWord_2870966) baseStart_2870966 baseEnd_2870966 := by
    simpa [prefixWord, tailWord_2870966, baseEnd_2870966] using wordTrace_append hprefix tailTrace_2870966
  have hstable : (prefixWord ++ tailWord_2870966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2870966).length < 2 ^ (prefixWord ++ tailWord_2870966).sum := by decide
  have hdescent : baseEnd_2870966 < baseStart_2870966 := by decide
  rcases family_descends (prefixWord ++ tailWord_2870966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2870971 : List Nat := [1, 1, 1, 1, 1, 2, 3, 5, 4, 3]
def baseStart_2870971 : Nat := 118140960795 + 2870971 * 2 ^ 59
def prefixEnd_2870971 : Nat := 4983230072969 + 3 ^ 40 * 2870971 * 2
def baseEnd_2870971 : Nat := 982792045412928030972767

theorem tailTrace_2870971 : CollatzResearch.WordTrace tailWord_2870971 prefixEnd_2870971 982792045412928030972767 := by
  unfold tailWord_2870971
  simp only [CollatzResearch.WordTrace]
  refine ⟨104712914881969864655316767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69808609921313243103544511 104712914881969864655316767)
  ·
    refine ⟨157069372322954796982975151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104712914881969864655316767 157069372322954796982975151)
    ·
      refine ⟨235604058484432195474462727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157069372322954796982975151 235604058484432195474462727)
      ·
        refine ⟨353406087726648293211694091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235604058484432195474462727 353406087726648293211694091)
        ·
          refine ⟨530109131589972439817541137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 353406087726648293211694091 530109131589972439817541137)
          ·
            refine ⟨397581848692479329863155853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 530109131589972439817541137 397581848692479329863155853)
            ·
              refine ⟨149093193259679748698683445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 397581848692479329863155853 149093193259679748698683445)
              ·
                refine ⟨13977486868094976440501573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 149093193259679748698683445 13977486868094976440501573)
                ·
                  refine ⟨2620778787767808082594045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13977486868094976440501573 2620778787767808082594045)
                  ·
                    refine ⟨982792045412928030972767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2620778787767808082594045 982792045412928030972767)
                    ·
                      rfl

theorem cell22_2870971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 5, 4, 3].length) (baseStart_2870971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2870971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2870971 prefixEnd_2870971 := by exact prefixLift 2870971
  have htrace : WordTrace (prefixWord ++ tailWord_2870971) baseStart_2870971 baseEnd_2870971 := by
    simpa [prefixWord, tailWord_2870971, baseEnd_2870971] using wordTrace_append hprefix tailTrace_2870971
  have hstable : (prefixWord ++ tailWord_2870971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2870971).length < 2 ^ (prefixWord ++ tailWord_2870971).sum := by decide
  have hdescent : baseEnd_2870971 < baseStart_2870971 := by decide
  rcases family_descends (prefixWord ++ tailWord_2870971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2870973 : List Nat := [1, 4, 1, 2, 1, 2, 3, 4, 4]
def baseStart_2870973 : Nat := 118140960795 + 2870973 * 2 ^ 59
def prefixEnd_2870973 : Nat := 4983230072969 + 3 ^ 40 * 2870973 * 2
def baseEnd_2870973 : Nat := 327597576684600230807587

theorem tailTrace_2870973 : CollatzResearch.WordTrace tailWord_2870973 prefixEnd_2870973 327597576684600230807587 := by
  unfold tailWord_2870973
  simp only [CollatzResearch.WordTrace]
  refine ⟨104712987827962618996889573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69808658551975079331259715 104712987827962618996889573)
  ·
    refine ⟨19633685217742991061916795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104712987827962618996889573 19633685217742991061916795)
    ·
      refine ⟨29450527826614486592875193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19633685217742991061916795 29450527826614486592875193)
      ·
        refine ⟨22087895869960864944656395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29450527826614486592875193 22087895869960864944656395)
        ·
          refine ⟨33131843804941297416984593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22087895869960864944656395 33131843804941297416984593)
          ·
            refine ⟨24848882853705973062738445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33131843804941297416984593 24848882853705973062738445)
            ·
              refine ⟨9318331070139739898526917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24848882853705973062738445 9318331070139739898526917)
              ·
                refine ⟨1747187075651201230973797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9318331070139739898526917 1747187075651201230973797)
                ·
                  refine ⟨327597576684600230807587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1747187075651201230973797 327597576684600230807587)
                  ·
                    rfl

theorem cell22_2870973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 4, 4].length) (baseStart_2870973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2870973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2870973 prefixEnd_2870973 := by exact prefixLift 2870973
  have htrace : WordTrace (prefixWord ++ tailWord_2870973) baseStart_2870973 baseEnd_2870973 := by
    simpa [prefixWord, tailWord_2870973, baseEnd_2870973] using wordTrace_append hprefix tailTrace_2870973
  have hstable : (prefixWord ++ tailWord_2870973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2870973).length < 2 ^ (prefixWord ++ tailWord_2870973).sum := by decide
  have hdescent : baseEnd_2870973 < baseStart_2870973 := by decide
  rcases family_descends (prefixWord ++ tailWord_2870973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2871127 : List Nat := [1, 1, 3, 2, 5, 1, 3, 1, 1, 4]
def baseStart_2871127 : Nat := 118140960795 + 2871127 * 2 ^ 59
def prefixEnd_2871127 : Nat := 4983230072969 + 3 ^ 40 * 2871127 * 2
def baseEnd_2871127 : Nat := 982845447400995624072289

theorem tailTrace_2871127 : CollatzResearch.WordTrace tailWord_2871127 prefixEnd_2871127 982845447400995624072289 := by
  unfold tailWord_2871127
  simp only [CollatzResearch.WordTrace]
  refine ⟨104718604669404703297995635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69812403112936468865330423 104718604669404703297995635)
  ·
    refine ⟨157077907004107054946993453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104718604669404703297995635 157077907004107054946993453)
    ·
      refine ⟨58904215126540145605122545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157077907004107054946993453 58904215126540145605122545)
      ·
        refine ⟨44178161344905109203841909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58904215126540145605122545 44178161344905109203841909)
        ·
          refine ⟨4141702626084853987860179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 44178161344905109203841909 4141702626084853987860179)
          ·
            refine ⟨6212553939127280981790269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4141702626084853987860179 6212553939127280981790269)
            ·
              refine ⟨2329707727172730368171351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6212553939127280981790269 2329707727172730368171351)
              ·
                refine ⟨3494561590759095552257027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2329707727172730368171351 3494561590759095552257027)
                ·
                  refine ⟨5241842386138643328385541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3494561590759095552257027 5241842386138643328385541)
                  ·
                    refine ⟨982845447400995624072289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5241842386138643328385541 982845447400995624072289)
                    ·
                      rfl

theorem cell22_2871127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 3, 1, 1, 4].length) (baseStart_2871127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2871127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2871127 prefixEnd_2871127 := by exact prefixLift 2871127
  have htrace : WordTrace (prefixWord ++ tailWord_2871127) baseStart_2871127 baseEnd_2871127 := by
    simpa [prefixWord, tailWord_2871127, baseEnd_2871127] using wordTrace_append hprefix tailTrace_2871127
  have hstable : (prefixWord ++ tailWord_2871127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2871127).length < 2 ^ (prefixWord ++ tailWord_2871127).sum := by decide
  have hdescent : baseEnd_2871127 < baseStart_2871127 := by decide
  rcases family_descends (prefixWord ++ tailWord_2871127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2871136 : List Nat := [2, 1, 1, 3, 3, 12]
def baseStart_2871136 : Nat := 118140960795 + 2871136 * 2 ^ 59
def prefixEnd_2871136 : Nat := 4983230072969 + 3 ^ 40 * 2871136 * 2
def baseEnd_2871136 : Nat := 12133932447962007414781

theorem tailTrace_2871136 : CollatzResearch.WordTrace tailWord_2871136 prefixEnd_2871136 12133932447962007414781 := by
  unfold tailWord_2871136
  simp only [CollatzResearch.WordTrace]
  refine ⟨52359466463186048917536631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69812621950914731890048841 52359466463186048917536631)
  ·
    refine ⟨78539199694779073376304947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52359466463186048917536631 78539199694779073376304947)
    ·
      refine ⟨117808799542168610064457421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78539199694779073376304947 117808799542168610064457421)
      ·
        refine ⟨44178299828313228774171533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117808799542168610064457421 44178299828313228774171533)
        ·
          refine ⟨16566862435617460790314325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44178299828313228774171533 16566862435617460790314325)
          ·
            refine ⟨12133932447962007414781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 16566862435617460790314325 12133932447962007414781)
            ·
              rfl

theorem cell22_2871136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 12].length) (baseStart_2871136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2871136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2871136 prefixEnd_2871136 := by exact prefixLift 2871136
  have htrace : WordTrace (prefixWord ++ tailWord_2871136) baseStart_2871136 baseEnd_2871136 := by
    simpa [prefixWord, tailWord_2871136, baseEnd_2871136] using wordTrace_append hprefix tailTrace_2871136
  have hstable : (prefixWord ++ tailWord_2871136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2871136).length < 2 ^ (prefixWord ++ tailWord_2871136).sum := by decide
  have hdescent : baseEnd_2871136 < baseStart_2871136 := by decide
  rcases family_descends (prefixWord ++ tailWord_2871136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2871151 : List Nat := [1, 1, 2, 1, 3, 1, 1, 1, 4, 7]
def baseStart_2871151 : Nat := 118140960795 + 2871151 * 2 ^ 59
def prefixEnd_2871151 : Nat := 4983230072969 + 3 ^ 40 * 2871151 * 2
def baseEnd_2871151 : Nat := 982853663091467561472215

theorem tailTrace_2871151 : CollatzResearch.WordTrace tailWord_2871151 prefixEnd_2871151 982853663091467561472215 := by
  unfold tailWord_2871151
  simp only [CollatzResearch.WordTrace]
  refine ⟨104719480021317755396869307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69812986680878503597912871 104719480021317755396869307)
  ·
    refine ⟨157079220031976633095303961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104719480021317755396869307 157079220031976633095303961)
    ·
      refine ⟨117809415023982474821477971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157079220031976633095303961 117809415023982474821477971)
      ·
        refine ⟨176714122535973712232216957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117809415023982474821477971 176714122535973712232216957)
        ·
          refine ⟨66267795950990142087081359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 176714122535973712232216957 66267795950990142087081359)
          ·
            refine ⟨99401693926485213130622039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66267795950990142087081359 99401693926485213130622039)
            ·
              refine ⟨149102540889727819695933059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99401693926485213130622039 149102540889727819695933059)
              ·
                refine ⟨223653811334591729543899589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 149102540889727819695933059 223653811334591729543899589)
                ·
                  refine ⟨41935089625235949289481173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 223653811334591729543899589 41935089625235949289481173)
                  ·
                    refine ⟨982853663091467561472215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41935089625235949289481173 982853663091467561472215)
                    ·
                      rfl

theorem cell22_2871151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 4, 7].length) (baseStart_2871151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2871151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2871151 prefixEnd_2871151 := by exact prefixLift 2871151
  have htrace : WordTrace (prefixWord ++ tailWord_2871151) baseStart_2871151 baseEnd_2871151 := by
    simpa [prefixWord, tailWord_2871151, baseEnd_2871151] using wordTrace_append hprefix tailTrace_2871151
  have hstable : (prefixWord ++ tailWord_2871151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2871151).length < 2 ^ (prefixWord ++ tailWord_2871151).sum := by decide
  have hdescent : baseEnd_2871151 < baseStart_2871151 := by decide
  rcases family_descends (prefixWord ++ tailWord_2871151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2871215 : List Nat := [1, 1, 2, 1, 2, 2, 7, 1, 5]
def baseStart_2871215 : Nat := 118140960795 + 2871215 * 2 ^ 59
def prefixEnd_2871215 : Nat := 4983230072969 + 3 ^ 40 * 2871215 * 2
def baseEnd_2871215 : Nat := 327625190533130909290673

theorem tailTrace_2871215 : CollatzResearch.WordTrace tailWord_2871215 prefixEnd_2871215 327625190533130909290673 := by
  unfold tailWord_2871215
  simp only [CollatzResearch.WordTrace]
  refine ⟨104721814293085894327199099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69814542862057262884799399 104721814293085894327199099)
  ·
    refine ⟨157082721439628841490798649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104721814293085894327199099 157082721439628841490798649)
    ·
      refine ⟨117812041079721631118098987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157082721439628841490798649 117812041079721631118098987)
      ·
        refine ⟨176718061619582446677148481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117812041079721631118098987 176718061619582446677148481)
        ·
          refine ⟨132538546214686835007861361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176718061619582446677148481 132538546214686835007861361)
          ·
            refine ⟨99403909661015126255896021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132538546214686835007861361 99403909661015126255896021)
            ·
              refine ⟨2329779132680042021622563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 99403909661015126255896021 2329779132680042021622563)
              ·
                refine ⟨3494668699020063032433845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2329779132680042021622563 3494668699020063032433845)
                ·
                  refine ⟨327625190533130909290673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3494668699020063032433845 327625190533130909290673)
                  ·
                    rfl

theorem cell22_2871215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 7, 1, 5].length) (baseStart_2871215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2871215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2871215 prefixEnd_2871215 := by exact prefixLift 2871215
  have htrace : WordTrace (prefixWord ++ tailWord_2871215) baseStart_2871215 baseEnd_2871215 := by
    simpa [prefixWord, tailWord_2871215, baseEnd_2871215] using wordTrace_append hprefix tailTrace_2871215
  have hstable : (prefixWord ++ tailWord_2871215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2871215).length < 2 ^ (prefixWord ++ tailWord_2871215).sum := by decide
  have hdescent : baseEnd_2871215 < baseStart_2871215 := by decide
  rcases family_descends (prefixWord ++ tailWord_2871215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2871266 : List Nat := [3, 3, 3, 1, 2, 2, 2, 1, 5]
def baseStart_2871266 : Nat := 118140960795 + 2871266 * 2 ^ 59
def prefixEnd_2871266 : Nat := 4983230072969 + 3 ^ 40 * 2871266 * 2
def baseEnd_2871266 : Nat := 327631009980548531615621

theorem tailTrace_2871266 : CollatzResearch.WordTrace tailWord_2871266 prefixEnd_2871266 327631009980548531615621 := by
  unfold tailWord_2871266
  simp only [CollatzResearch.WordTrace]
  refine ⟨26180918603975282509326413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69815782943934086691537101 26180918603975282509326413)
  ·
    refine ⟨9817844476490730940997405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26180918603975282509326413 9817844476490730940997405)
    ·
      refine ⟨3681691678684024102874027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9817844476490730940997405 3681691678684024102874027)
      ·
        refine ⟨5522537518026036154311041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3681691678684024102874027 5522537518026036154311041)
        ·
          refine ⟨4141903138519527115733281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5522537518026036154311041 4141903138519527115733281)
          ·
            refine ⟨3106427353889645336799961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4141903138519527115733281 3106427353889645336799961)
            ·
              refine ⟨2329820515417234002599971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3106427353889645336799961 2329820515417234002599971)
              ·
                refine ⟨3494730773125851003899957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2329820515417234002599971 3494730773125851003899957)
                ·
                  refine ⟨327631009980548531615621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3494730773125851003899957 327631009980548531615621)
                  ·
                    rfl

theorem cell22_2871266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 2, 1, 5].length) (baseStart_2871266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2871266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2871266 prefixEnd_2871266 := by exact prefixLift 2871266
  have htrace : WordTrace (prefixWord ++ tailWord_2871266) baseStart_2871266 baseEnd_2871266 := by
    simpa [prefixWord, tailWord_2871266, baseEnd_2871266] using wordTrace_append hprefix tailTrace_2871266
  have hstable : (prefixWord ++ tailWord_2871266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2871266).length < 2 ^ (prefixWord ++ tailWord_2871266).sum := by decide
  have hdescent : baseEnd_2871266 < baseStart_2871266 := by decide
  rcases family_descends (prefixWord ++ tailWord_2871266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2871288 : List Nat := [2, 1, 2, 1, 1, 3, 4, 8]
def baseStart_2871288 : Nat := 118140960795 + 2871288 * 2 ^ 59
def prefixEnd_2871288 : Nat := 4983230072969 + 3 ^ 40 * 2871288 * 2
def baseEnd_2871288 : Nat := 109211173443471652310755

theorem tailTrace_2871288 : CollatzResearch.WordTrace tailWord_2871288 prefixEnd_2871288 109211173443471652310755 := by
  unfold tailWord_2871288
  simp only [CollatzResearch.WordTrace]
  refine ⟨52362238410910713897303259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69816317881214285196404345 52362238410910713897303259)
  ·
    refine ⟨78543357616366070845954889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52362238410910713897303259 78543357616366070845954889)
    ·
      refine ⟨58907518212274553134466167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78543357616366070845954889 58907518212274553134466167)
      ·
        refine ⟨88361277318411829701699251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58907518212274553134466167 88361277318411829701699251)
        ·
          refine ⟨132541915977617744552548877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88361277318411829701699251 132541915977617744552548877)
          ·
            refine ⟨49703218491606654207205829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 132541915977617744552548877 49703218491606654207205829)
            ·
              refine ⟨9319353467176247663851093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49703218491606654207205829 9319353467176247663851093)
              ·
                refine ⟨109211173443471652310755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9319353467176247663851093 109211173443471652310755)
                ·
                  rfl

theorem cell22_2871288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 8].length) (baseStart_2871288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2871288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2871288 prefixEnd_2871288 := by exact prefixLift 2871288
  have htrace : WordTrace (prefixWord ++ tailWord_2871288) baseStart_2871288 baseEnd_2871288 := by
    simpa [prefixWord, tailWord_2871288, baseEnd_2871288] using wordTrace_append hprefix tailTrace_2871288
  have hstable : (prefixWord ++ tailWord_2871288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2871288).length < 2 ^ (prefixWord ++ tailWord_2871288).sum := by decide
  have hdescent : baseEnd_2871288 < baseStart_2871288 := by decide
  rcases family_descends (prefixWord ++ tailWord_2871288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2871395 : List Nat := [1, 1, 1, 5, 1, 1, 4, 2, 6]
def baseStart_2871395 : Nat := 118140960795 + 2871395 * 2 ^ 59
def prefixEnd_2871395 : Nat := 4983230072969 + 3 ^ 40 * 2871395 * 2
def baseEnd_2871395 : Nat := 327645729759310752790489

theorem tailTrace_2871395 : CollatzResearch.WordTrace tailWord_2871395 prefixEnd_2871395 327645729759310752790489 := by
  unfold tailWord_2871395
  simp only [CollatzResearch.WordTrace]
  refine ⟨104728379432433785068751639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69818919621622523379167759 104728379432433785068751639)
  ·
    refine ⟨157092569148650677603127459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104728379432433785068751639 157092569148650677603127459)
    ·
      refine ⟨235638853722976016404691189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157092569148650677603127459 235638853722976016404691189)
      ·
        refine ⟨22091142536529001537939799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 235638853722976016404691189 22091142536529001537939799)
        ·
          refine ⟨33136713804793502306909699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22091142536529001537939799 33136713804793502306909699)
          ·
            refine ⟨49705070707190253460364549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33136713804793502306909699 49705070707190253460364549)
            ·
              refine ⟨9319700757598172523818353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49705070707190253460364549 9319700757598172523818353)
              ·
                refine ⟨6989775568198629392863765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9319700757598172523818353 6989775568198629392863765)
                ·
                  refine ⟨327645729759310752790489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6989775568198629392863765 327645729759310752790489)
                  ·
                    rfl

theorem cell22_2871395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 2, 6].length) (baseStart_2871395 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2871395 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2871395 prefixEnd_2871395 := by exact prefixLift 2871395
  have htrace : WordTrace (prefixWord ++ tailWord_2871395) baseStart_2871395 baseEnd_2871395 := by
    simpa [prefixWord, tailWord_2871395, baseEnd_2871395] using wordTrace_append hprefix tailTrace_2871395
  have hstable : (prefixWord ++ tailWord_2871395).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2871395).length < 2 ^ (prefixWord ++ tailWord_2871395).sum := by decide
  have hdescent : baseEnd_2871395 < baseStart_2871395 := by decide
  rcases family_descends (prefixWord ++ tailWord_2871395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2871397 : List Nat := [1, 3, 1, 3, 2, 2, 1, 4, 1, 4]
def baseStart_2871397 : Nat := 118140960795 + 2871397 * 2 ^ 59
def prefixEnd_2871397 : Nat := 4983230072969 + 3 ^ 40 * 2871397 * 2
def baseEnd_2871397 : Nat := 982937873918804919821461

theorem tailTrace_2871397 : CollatzResearch.WordTrace tailWord_2871397 prefixEnd_2871397 982937873918804919821461 := by
  unfold tailWord_2871397
  simp only [CollatzResearch.WordTrace]
  refine ⟨104728452378426539410324445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69818968252284359606882963 104728452378426539410324445)
  ·
    refine ⟨39273169641909952278871667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104728452378426539410324445 39273169641909952278871667)
    ·
      refine ⟨58909754462864928418307501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39273169641909952278871667 58909754462864928418307501)
      ·
        refine ⟨22091157923574348156865313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58909754462864928418307501 22091157923574348156865313)
        ·
          refine ⟨16568368442680761117648985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22091157923574348156865313 16568368442680761117648985)
          ·
            refine ⟨12426276332010570838236739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16568368442680761117648985 12426276332010570838236739)
            ·
              refine ⟨18639414498015856257355109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12426276332010570838236739 18639414498015856257355109)
              ·
                refine ⟨3494890218377973048254083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18639414498015856257355109 3494890218377973048254083)
                ·
                  refine ⟨5242335327566959572381125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3494890218377973048254083 5242335327566959572381125)
                  ·
                    refine ⟨982937873918804919821461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5242335327566959572381125 982937873918804919821461)
                    ·
                      rfl

theorem cell22_2871397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 4, 1, 4].length) (baseStart_2871397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2871397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2871397 prefixEnd_2871397 := by exact prefixLift 2871397
  have htrace : WordTrace (prefixWord ++ tailWord_2871397) baseStart_2871397 baseEnd_2871397 := by
    simpa [prefixWord, tailWord_2871397, baseEnd_2871397] using wordTrace_append hprefix tailTrace_2871397
  have hstable : (prefixWord ++ tailWord_2871397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2871397).length < 2 ^ (prefixWord ++ tailWord_2871397).sum := by decide
  have hdescent : baseEnd_2871397 < baseStart_2871397 := by decide
  rcases family_descends (prefixWord ++ tailWord_2871397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2871414 : List Nat := [5, 1, 1, 2, 1, 2, 2, 3, 1, 4]
def baseStart_2871414 : Nat := 118140960795 + 2871414 * 2 ^ 59
def prefixEnd_2871414 : Nat := 4983230072969 + 3 ^ 40 * 2871414 * 2
def baseEnd_2871414 : Nat := 982943693366222542146409

theorem tailTrace_2871414 : CollatzResearch.WordTrace tailWord_2871414 prefixEnd_2871414 982943693366222542146409 := by
  unfold tailWord_2871414
  simp only [CollatzResearch.WordTrace]
  refine ⟨6545567026210309457105831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 69819381612909967542462197 6545567026210309457105831)
  ·
    refine ⟨9818350539315464185658747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6545567026210309457105831 9818350539315464185658747)
    ·
      refine ⟨14727525808973196278488121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9818350539315464185658747 14727525808973196278488121)
      ·
        refine ⟨11045644356729897208866091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14727525808973196278488121 11045644356729897208866091)
        ·
          refine ⟨16568466535094845813299137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11045644356729897208866091 16568466535094845813299137)
          ·
            refine ⟨12426349901321134359974353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16568466535094845813299137 12426349901321134359974353)
            ·
              refine ⟨9319762425990850769980765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12426349901321134359974353 9319762425990850769980765)
              ·
                refine ⟨3494910909746569038742787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9319762425990850769980765 3494910909746569038742787)
                ·
                  refine ⟨5242366364619853558114181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3494910909746569038742787 5242366364619853558114181)
                  ·
                    refine ⟨982943693366222542146409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5242366364619853558114181 982943693366222542146409)
                    ·
                      rfl

theorem cell22_2871414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 3, 1, 4].length) (baseStart_2871414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2871414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2871414 prefixEnd_2871414 := by exact prefixLift 2871414
  have htrace : WordTrace (prefixWord ++ tailWord_2871414) baseStart_2871414 baseEnd_2871414 := by
    simpa [prefixWord, tailWord_2871414, baseEnd_2871414] using wordTrace_append hprefix tailTrace_2871414
  have hstable : (prefixWord ++ tailWord_2871414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2871414).length < 2 ^ (prefixWord ++ tailWord_2871414).sum := by decide
  have hdescent : baseEnd_2871414 < baseStart_2871414 := by decide
  rcases family_descends (prefixWord ++ tailWord_2871414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2871427 : List Nat := [1, 1, 1, 3, 3, 3, 2, 1, 4, 3]
def baseStart_2871427 : Nat := 118140960795 + 2871427 * 2 ^ 59
def prefixEnd_2871427 : Nat := 4983230072969 + 3 ^ 40 * 2871427 * 2
def baseEnd_2871427 : Nat := 982948143531894841571369

theorem tailTrace_2871427 : CollatzResearch.WordTrace tailWord_2871427 prefixEnd_2871427 982948143531894841571369 := by
  unfold tailWord_2871427
  simp only [CollatzResearch.WordTrace]
  refine ⟨104729546568317854533916535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69819697712211903022611023 104729546568317854533916535)
  ·
    refine ⟨157094319852476781800874803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104729546568317854533916535 157094319852476781800874803)
    ·
      refine ⟨235641479778715172701312205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157094319852476781800874803 235641479778715172701312205)
      ·
        refine ⟨88365554917018189762992077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 235641479778715172701312205 88365554917018189762992077)
        ·
          refine ⟨33137083093881821161122029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88365554917018189762992077 33137083093881821161122029)
          ·
            refine ⟨12426406160205682935420761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33137083093881821161122029 12426406160205682935420761)
            ·
              refine ⟨9319804620154262201565571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12426406160205682935420761 9319804620154262201565571)
              ·
                refine ⟨13979706930231393302348357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9319804620154262201565571 13979706930231393302348357)
                ·
                  refine ⟨2621195049418386244190317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13979706930231393302348357 2621195049418386244190317)
                  ·
                    refine ⟨982948143531894841571369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2621195049418386244190317 982948143531894841571369)
                    ·
                      rfl

theorem cell22_2871427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 1, 4, 3].length) (baseStart_2871427 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2871427 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2871427 prefixEnd_2871427 := by exact prefixLift 2871427
  have htrace : WordTrace (prefixWord ++ tailWord_2871427) baseStart_2871427 baseEnd_2871427 := by
    simpa [prefixWord, tailWord_2871427, baseEnd_2871427] using wordTrace_append hprefix tailTrace_2871427
  have hstable : (prefixWord ++ tailWord_2871427).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2871427).length < 2 ^ (prefixWord ++ tailWord_2871427).sum := by decide
  have hdescent : baseEnd_2871427 < baseStart_2871427 := by decide
  rcases family_descends (prefixWord ++ tailWord_2871427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2871440 : List Nat := [2, 1, 1, 1, 1, 1, 8, 7]
def baseStart_2871440 : Nat := 118140960795 + 2871440 * 2 ^ 59
def prefixEnd_2871440 : Nat := 4983230072969 + 3 ^ 40 * 2871440 * 2
def baseEnd_2871440 : Nat := 109216954855285237888481

theorem tailTrace_2871440 : CollatzResearch.WordTrace tailWord_2871440 prefixEnd_2871440 109216954855285237888481 := by
  unfold tailWord_2871440
  simp only [CollatzResearch.WordTrace]
  refine ⟨52365010358635378877069887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69820013811513838502759849 52365010358635378877069887)
  ·
    refine ⟨78547515537953068315604831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52365010358635378877069887 78547515537953068315604831)
    ·
      refine ⟨117821273306929602473407247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78547515537953068315604831 117821273306929602473407247)
      ·
        refine ⟨176731909960394403710110871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117821273306929602473407247 176731909960394403710110871)
        ·
          refine ⟨265097864940591605565166307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176731909960394403710110871 265097864940591605565166307)
          ·
            refine ⟨397646797410887408347749461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 265097864940591605565166307 397646797410887408347749461)
            ·
              refine ⟨4659923407158836816575189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 397646797410887408347749461 4659923407158836816575189)
              ·
                refine ⟨109216954855285237888481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4659923407158836816575189 109216954855285237888481)
                ·
                  rfl

theorem cell22_2871440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 8, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 8, 7].length) (baseStart_2871440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2871440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2871440 prefixEnd_2871440 := by exact prefixLift 2871440
  have htrace : WordTrace (prefixWord ++ tailWord_2871440) baseStart_2871440 baseEnd_2871440 := by
    simpa [prefixWord, tailWord_2871440, baseEnd_2871440] using wordTrace_append hprefix tailTrace_2871440
  have hstable : (prefixWord ++ tailWord_2871440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2871440).length < 2 ^ (prefixWord ++ tailWord_2871440).sum := by decide
  have hdescent : baseEnd_2871440 < baseStart_2871440 := by decide
  rcases family_descends (prefixWord ++ tailWord_2871440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2871442 : List Nat := [3, 2, 3, 1, 1, 1, 1, 2, 4, 4]
def baseStart_2871442 : Nat := 118140960795 + 2871442 * 2 ^ 59
def prefixEnd_2871442 : Nat := 4983230072969 + 3 ^ 40 * 2871442 * 2
def baseEnd_2871442 : Nat := 982953278338439802446323

theorem tailTrace_2871442 : CollatzResearch.WordTrace tailWord_2871442 prefixEnd_2871442 982953278338439802446323 := by
  unfold tailWord_2871442
  simp only [CollatzResearch.WordTrace]
  refine ⟨26182523415815878023928145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69820062442175674730475053 26182523415815878023928145)
  ·
    refine ⟨19636892561861908517946109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26182523415815878023928145 19636892561861908517946109)
    ·
      refine ⟨7363834710698215694229791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19636892561861908517946109 7363834710698215694229791)
      ·
        refine ⟨11045752066047323541344687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7363834710698215694229791 11045752066047323541344687)
        ·
          refine ⟨16568628099070985312017031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11045752066047323541344687 16568628099070985312017031)
          ·
            refine ⟨24852942148606477968025547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16568628099070985312017031 24852942148606477968025547)
            ·
              refine ⟨37279413222909716952038321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24852942148606477968025547 37279413222909716952038321)
              ·
                refine ⟨27959559917182287714028741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37279413222909716952038321 27959559917182287714028741)
                ·
                  refine ⟨5242417484471678946380389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27959559917182287714028741 5242417484471678946380389)
                  ·
                    refine ⟨982953278338439802446323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5242417484471678946380389 982953278338439802446323)
                    ·
                      rfl

theorem cell22_2871442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_2871442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2871442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2871442 prefixEnd_2871442 := by exact prefixLift 2871442
  have htrace : WordTrace (prefixWord ++ tailWord_2871442) baseStart_2871442 baseEnd_2871442 := by
    simpa [prefixWord, tailWord_2871442, baseEnd_2871442] using wordTrace_append hprefix tailTrace_2871442
  have hstable : (prefixWord ++ tailWord_2871442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2871442).length < 2 ^ (prefixWord ++ tailWord_2871442).sum := by decide
  have hdescent : baseEnd_2871442 < baseStart_2871442 := by decide
  rcases family_descends (prefixWord ++ tailWord_2871442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2871598 : List Nat := [4, 1, 3, 3, 1, 2, 1, 1, 6]
def baseStart_2871598 : Nat := 118140960795 + 2871598 * 2 ^ 59
def prefixEnd_2871598 : Nat := 4983230072969 + 3 ^ 40 * 2871598 * 2
def baseEnd_2871598 : Nat := 327668893442169131848615

theorem tailTrace_2871598 : CollatzResearch.WordTrace tailWord_2871598 prefixEnd_2871598 327668893442169131848615 := by
  unfold tailWord_2871598
  simp only [CollatzResearch.WordTrace]
  refine ⟨13091972931337293842298931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69823855633798900492260965 13091972931337293842298931)
  ·
    refine ⟨19637959397005940763448397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13091972931337293842298931 19637959397005940763448397)
    ·
      refine ⟨7364234773877227786293149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19637959397005940763448397 7364234773877227786293149)
      ·
        refine ⟨2761588040203960419859931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7364234773877227786293149 2761588040203960419859931)
        ·
          refine ⟨4142382060305940629789897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2761588040203960419859931 4142382060305940629789897)
          ·
            refine ⟨3106786545229455472342423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4142382060305940629789897 3106786545229455472342423)
            ·
              refine ⟨4660179817844183208513635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3106786545229455472342423 4660179817844183208513635)
              ·
                refine ⟨6990269726766274812770453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4660179817844183208513635 6990269726766274812770453)
                ·
                  refine ⟨327668893442169131848615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6990269726766274812770453 327668893442169131848615)
                  ·
                    rfl

theorem cell22_2871598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 1, 1, 6].length) (baseStart_2871598 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2871598 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2871598 prefixEnd_2871598 := by exact prefixLift 2871598
  have htrace : WordTrace (prefixWord ++ tailWord_2871598) baseStart_2871598 baseEnd_2871598 := by
    simpa [prefixWord, tailWord_2871598, baseEnd_2871598] using wordTrace_append hprefix tailTrace_2871598
  have hstable : (prefixWord ++ tailWord_2871598).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2871598).length < 2 ^ (prefixWord ++ tailWord_2871598).sum := by decide
  have hdescent : baseEnd_2871598 < baseStart_2871598 := by decide
  rcases family_descends (prefixWord ++ tailWord_2871598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2871609 : List Nat := [1, 2, 1, 6, 1, 2, 2, 7]
def baseStart_2871609 : Nat := 118140960795 + 2871609 * 2 ^ 59
def prefixEnd_2871609 : Nat := 4983230072969 + 3 ^ 40 * 2871609 * 2
def baseEnd_2871609 : Nat := 109223382872367448168979

theorem tailTrace_2871609 : CollatzResearch.WordTrace tailWord_2871609 prefixEnd_2871609 109223382872367448168979 := by
  unfold tailWord_2871609
  simp only [CollatzResearch.WordTrace]
  refine ⟨104736184653658499617041881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69824123102438999744694587 104736184653658499617041881)
  ·
    refine ⟨78552138490243874712781411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104736184653658499617041881 78552138490243874712781411)
    ·
      refine ⟨117828207735365812069172117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78552138490243874712781411 117828207735365812069172117)
      ·
        refine ⟨5523197237595272440742443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 117828207735365812069172117 5523197237595272440742443)
        ·
          refine ⟨8284795856392908661113665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5523197237595272440742443 8284795856392908661113665)
          ·
            refine ⟨6213596892294681495835249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8284795856392908661113665 6213596892294681495835249)
            ·
              refine ⟨4660197669221011121876437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6213596892294681495835249 4660197669221011121876437)
              ·
                refine ⟨109223382872367448168979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4660197669221011121876437 109223382872367448168979)
                ·
                  rfl

theorem cell22_2871609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 2, 7].length) (baseStart_2871609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2871609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2871609 prefixEnd_2871609 := by exact prefixLift 2871609
  have htrace : WordTrace (prefixWord ++ tailWord_2871609) baseStart_2871609 baseEnd_2871609 := by
    simpa [prefixWord, tailWord_2871609, baseEnd_2871609] using wordTrace_append hprefix tailTrace_2871609
  have hstable : (prefixWord ++ tailWord_2871609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2871609).length < 2 ^ (prefixWord ++ tailWord_2871609).sum := by decide
  have hdescent : baseEnd_2871609 < baseStart_2871609 := by decide
  rcases family_descends (prefixWord ++ tailWord_2871609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2871624 : List Nat := [2, 1, 3, 1, 1, 2, 2, 4, 3, 3]
def baseStart_2871624 : Nat := 118140960795 + 2871624 * 2 ^ 59
def prefixEnd_2871624 : Nat := 4983230072969 + 3 ^ 40 * 2871624 * 2
def baseEnd_2871624 : Nat := 983015580657851994395765

theorem tailTrace_2871624 : CollatzResearch.WordTrace tailWord_2871624 prefixEnd_2871624 983015580657851994395765 := by
  unfold tailWord_2871624
  simp only [CollatzResearch.WordTrace]
  refine ⟨52368365874302078589418963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69824487832402771452558617 52368365874302078589418963)
  ·
    refine ⟨78552548811453117884128445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52368365874302078589418963 78552548811453117884128445)
    ·
      refine ⟨29457205804294919206548167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78552548811453117884128445 29457205804294919206548167)
      ·
        refine ⟨44185808706442378809822251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29457205804294919206548167 44185808706442378809822251)
        ·
          refine ⟨66278713059663568214733377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44185808706442378809822251 66278713059663568214733377)
          ·
            refine ⟨49709034794747676161050033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66278713059663568214733377 49709034794747676161050033)
            ·
              refine ⟨37281776096060757120787525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49709034794747676161050033 37281776096060757120787525)
              ·
                refine ⟨6990333018011391960147661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37281776096060757120787525 6990333018011391960147661)
                ·
                  refine ⟨2621374881754271985055373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6990333018011391960147661 2621374881754271985055373)
                  ·
                    refine ⟨983015580657851994395765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2621374881754271985055373 983015580657851994395765)
                    ·
                      rfl

theorem cell22_2871624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 4, 3, 3].length) (baseStart_2871624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2871624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2871624 prefixEnd_2871624 := by exact prefixLift 2871624
  have htrace : WordTrace (prefixWord ++ tailWord_2871624) baseStart_2871624 baseEnd_2871624 := by
    simpa [prefixWord, tailWord_2871624, baseEnd_2871624] using wordTrace_append hprefix tailTrace_2871624
  have hstable : (prefixWord ++ tailWord_2871624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2871624).length < 2 ^ (prefixWord ++ tailWord_2871624).sum := by decide
  have hdescent : baseEnd_2871624 < baseStart_2871624 := by decide
  rcases family_descends (prefixWord ++ tailWord_2871624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2871641 : List Nat := [1, 2, 1, 2, 2, 2, 1, 7, 1, 3]
def baseStart_2871641 : Nat := 118140960795 + 2871641 * 2 ^ 59
def prefixEnd_2871641 : Nat := 4983230072969 + 3 ^ 40 * 2871641 * 2
def baseEnd_2871641 : Nat := 983021400105269616720713

theorem tailTrace_2871641 : CollatzResearch.WordTrace tailWord_2871641 prefixEnd_2871641 983021400105269616720713 := by
  unfold tailWord_2871641
  simp only [CollatzResearch.WordTrace]
  refine ⟨104737351789542569082206777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69824901193028379388137851 104737351789542569082206777)
  ·
    refine ⟨78553013842156926811655083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104737351789542569082206777 78553013842156926811655083)
    ·
      refine ⟨117829520763235390217482625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78553013842156926811655083 117829520763235390217482625)
      ·
        refine ⟨88372140572426542663111969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117829520763235390217482625 88372140572426542663111969)
        ·
          refine ⟨66279105429319906997333977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88372140572426542663111969 66279105429319906997333977)
          ·
            refine ⟨49709329071989930248000483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66279105429319906997333977 49709329071989930248000483)
            ·
              refine ⟨74563993607984895372000725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49709329071989930248000483 74563993607984895372000725)
              ·
                refine ⟨1747593600187145985281267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 74563993607984895372000725 1747593600187145985281267)
                ·
                  refine ⟨2621390400280718977921901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1747593600187145985281267 2621390400280718977921901)
                  ·
                    refine ⟨983021400105269616720713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2621390400280718977921901 983021400105269616720713)
                    ·
                      rfl

theorem cell22_2871641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 7, 1, 3].length) (baseStart_2871641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2871641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2871641 prefixEnd_2871641 := by exact prefixLift 2871641
  have htrace : WordTrace (prefixWord ++ tailWord_2871641) baseStart_2871641 baseEnd_2871641 := by
    simpa [prefixWord, tailWord_2871641, baseEnd_2871641] using wordTrace_append hprefix tailTrace_2871641
  have hstable : (prefixWord ++ tailWord_2871641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2871641).length < 2 ^ (prefixWord ++ tailWord_2871641).sum := by decide
  have hdescent : baseEnd_2871641 < baseStart_2871641 := by decide
  rcases family_descends (prefixWord ++ tailWord_2871641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2871669 : List Nat := [1, 3, 4, 1, 2, 1, 1, 1, 1, 7]
def baseStart_2871669 : Nat := 118140960795 + 2871669 * 2 ^ 59
def prefixEnd_2871669 : Nat := 4983230072969 + 3 ^ 40 * 2871669 * 2
def baseEnd_2871669 : Nat := 983030985077486877020627

theorem tailTrace_2871669 : CollatzResearch.WordTrace tailWord_2871669 prefixEnd_2871669 983030985077486877020627 := by
  unfold tailWord_2871669
  simp only [CollatzResearch.WordTrace]
  refine ⟨104738373033441129864226061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69825582022294086576150707 104738373033441129864226061)
  ·
    refine ⟨39276889887540423699084773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104738373033441129864226061 39276889887540423699084773)
    ·
      refine ⟨7364416853913829443578395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39276889887540423699084773 7364416853913829443578395)
      ·
        refine ⟨11046625280870744165367593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7364416853913829443578395 11046625280870744165367593)
        ·
          refine ⟨8284968960653058124025695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11046625280870744165367593 8284968960653058124025695)
          ·
            refine ⟨12427453440979587186038543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8284968960653058124025695 12427453440979587186038543)
            ·
              refine ⟨18641180161469380779057815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12427453440979587186038543 18641180161469380779057815)
              ·
                refine ⟨27961770242204071168586723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18641180161469380779057815 27961770242204071168586723)
                ·
                  refine ⟨41942655363306106752880085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27961770242204071168586723 41942655363306106752880085)
                  ·
                    refine ⟨983030985077486877020627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41942655363306106752880085 983030985077486877020627)
                    ·
                      rfl

theorem cell22_2871669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_2871669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2871669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2871669 prefixEnd_2871669 := by exact prefixLift 2871669
  have htrace : WordTrace (prefixWord ++ tailWord_2871669) baseStart_2871669 baseEnd_2871669 := by
    simpa [prefixWord, tailWord_2871669, baseEnd_2871669] using wordTrace_append hprefix tailTrace_2871669
  have hstable : (prefixWord ++ tailWord_2871669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2871669).length < 2 ^ (prefixWord ++ tailWord_2871669).sum := by decide
  have hdescent : baseEnd_2871669 < baseStart_2871669 := by decide
  rcases family_descends (prefixWord ++ tailWord_2871669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2871684 : List Nat := [2, 3, 2, 1, 1, 2, 1, 3, 3, 4]
def baseStart_2871684 : Nat := 118140960795 + 2871684 * 2 ^ 59
def prefixEnd_2871684 : Nat := 4983230072969 + 3 ^ 40 * 2871684 * 2
def baseEnd_2871684 : Nat := 983036119884031837895581

theorem tailTrace_2871684 : CollatzResearch.WordTrace tailWord_2871684 prefixEnd_2871684 983036119884031837895581 := by
  unfold tailWord_2871684
  simp only [CollatzResearch.WordTrace]
  refine ⟨52369460064193393713011053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69825946752257858284014737 52369460064193393713011053)
  ·
    refine ⟨19638547524072522642379145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52369460064193393713011053 19638547524072522642379145)
    ·
      refine ⟨14728910643054391981784359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19638547524072522642379145 14728910643054391981784359)
      ·
        refine ⟨22093365964581587972676539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14728910643054391981784359 22093365964581587972676539)
        ·
          refine ⟨33140048946872381959014809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22093365964581587972676539 33140048946872381959014809)
          ·
            refine ⟨24855036710154286469261107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33140048946872381959014809 24855036710154286469261107)
            ·
              refine ⟨37282555065231429703891661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24855036710154286469261107 37282555065231429703891661)
              ·
                refine ⟨13980958149461786138959373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37282555065231429703891661 13980958149461786138959373)
                ·
                  refine ⟨5242859306048169802109765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13980958149461786138959373 5242859306048169802109765)
                  ·
                    refine ⟨983036119884031837895581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5242859306048169802109765 983036119884031837895581)
                    ·
                      rfl

theorem cell22_2871684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 3, 3, 4].length) (baseStart_2871684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2871684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2871684 prefixEnd_2871684 := by exact prefixLift 2871684
  have htrace : WordTrace (prefixWord ++ tailWord_2871684) baseStart_2871684 baseEnd_2871684 := by
    simpa [prefixWord, tailWord_2871684, baseEnd_2871684] using wordTrace_append hprefix tailTrace_2871684
  have hstable : (prefixWord ++ tailWord_2871684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2871684).length < 2 ^ (prefixWord ++ tailWord_2871684).sum := by decide
  have hdescent : baseEnd_2871684 < baseStart_2871684 := by decide
  rcases family_descends (prefixWord ++ tailWord_2871684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2871716 : List Nat := [2, 3, 1, 2, 1, 1, 4, 4, 4]
def baseStart_2871716 : Nat := 118140960795 + 2871716 * 2 ^ 59
def prefixEnd_2871716 : Nat := 4983230072969 + 3 ^ 40 * 2871716 * 2
def baseEnd_2871716 : Nat := 327682358045998140365161

theorem tailTrace_2871716 : CollatzResearch.WordTrace tailWord_2871716 prefixEnd_2871716 327682358045998140365161 := by
  unfold tailWord_2871716
  simp only [CollatzResearch.WordTrace]
  refine ⟨52370043632135428445593501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69826724842847237927458001 52370043632135428445593501)
  ·
    refine ⟨19638766362050785667097563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52370043632135428445593501 19638766362050785667097563)
    ·
      refine ⟨29458149543076178500646345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19638766362050785667097563 29458149543076178500646345)
      ·
        refine ⟨22093612157307133875484759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29458149543076178500646345 22093612157307133875484759)
        ·
          refine ⟨33140418235960700813227139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22093612157307133875484759 33140418235960700813227139)
          ·
            refine ⟨49710627353941051219840709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33140418235960700813227139 49710627353941051219840709)
            ·
              refine ⟨9320742628863947103720133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49710627353941051219840709 9320742628863947103720133)
              ·
                refine ⟨1747639242911990081947525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9320742628863947103720133 1747639242911990081947525)
                ·
                  refine ⟨327682358045998140365161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1747639242911990081947525 327682358045998140365161)
                  ·
                    rfl

theorem cell22_2871716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 4, 4].length) (baseStart_2871716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2871716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2871716 prefixEnd_2871716 := by exact prefixLift 2871716
  have htrace : WordTrace (prefixWord ++ tailWord_2871716) baseStart_2871716 baseEnd_2871716 := by
    simpa [prefixWord, tailWord_2871716, baseEnd_2871716] using wordTrace_append hprefix tailTrace_2871716
  have hstable : (prefixWord ++ tailWord_2871716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2871716).length < 2 ^ (prefixWord ++ tailWord_2871716).sum := by decide
  have hdescent : baseEnd_2871716 < baseStart_2871716 := by decide
  rcases family_descends (prefixWord ++ tailWord_2871716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2871722 : List Nat := [3, 1, 6, 1, 1, 1, 3, 1, 5]
def baseStart_2871722 : Nat := 118140960795 + 2871722 * 2 ^ 59
def prefixEnd_2871722 : Nat := 4983230072969 + 3 ^ 40 * 2871722 * 2
def baseEnd_2871722 : Nat := 327683042686870801815155

theorem tailTrace_2871722 : CollatzResearch.WordTrace tailWord_2871722 prefixEnd_2871722 327683042686870801815155 := by
  unfold tailWord_2871722
  simp only [CollatzResearch.WordTrace]
  refine ⟨26185076525562279978976355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69826870734832746610603613 26185076525562279978976355)
  ·
    refine ⟨39277614788343419968464533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26185076525562279978976355 39277614788343419968464533)
    ·
      refine ⟨1841138193203597811021775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 39277614788343419968464533 1841138193203597811021775)
      ·
        refine ⟨2761707289805396716532663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1841138193203597811021775 2761707289805396716532663)
        ·
          refine ⟨4142560934708095074798995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2761707289805396716532663 4142560934708095074798995)
          ·
            refine ⟨6213841402062142612198493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4142560934708095074798995 6213841402062142612198493)
            ·
              refine ⟨2330190525773303479574435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6213841402062142612198493 2330190525773303479574435)
              ·
                refine ⟨3495285788659955219361653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2330190525773303479574435 3495285788659955219361653)
                ·
                  refine ⟨327683042686870801815155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3495285788659955219361653 327683042686870801815155)
                  ·
                    rfl

theorem cell22_2871722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 3, 1, 5].length) (baseStart_2871722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2871722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2871722 prefixEnd_2871722 := by exact prefixLift 2871722
  have htrace : WordTrace (prefixWord ++ tailWord_2871722) baseStart_2871722 baseEnd_2871722 := by
    simpa [prefixWord, tailWord_2871722, baseEnd_2871722] using wordTrace_append hprefix tailTrace_2871722
  have hstable : (prefixWord ++ tailWord_2871722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2871722).length < 2 ^ (prefixWord ++ tailWord_2871722).sum := by decide
  have hdescent : baseEnd_2871722 < baseStart_2871722 := by decide
  rcases family_descends (prefixWord ++ tailWord_2871722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2871729 : List Nat := [1, 2, 2, 4, 1, 2, 1, 2, 1, 6]
def baseStart_2871729 : Nat := 118140960795 + 2871729 * 2 ^ 59
def prefixEnd_2871729 : Nat := 4983230072969 + 3 ^ 40 * 2871729 * 2
def baseEnd_2871729 : Nat := 983051524303666720520443

theorem tailTrace_2871729 : CollatzResearch.WordTrace tailWord_2871729 prefixEnd_2871729 983051524303666720520443 := by
  unfold tailWord_2871729
  simp only [CollatzResearch.WordTrace]
  refine ⟨104740561413223760111410241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69827040942149173407606827 104740561413223760111410241)
  ·
    refine ⟨78555421059917820083557681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104740561413223760111410241 78555421059917820083557681)
    ·
      refine ⟨58916565794938365062668261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78555421059917820083557681 58916565794938365062668261)
      ·
        refine ⟨11046856086550943449250299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58916565794938365062668261 11046856086550943449250299)
        ·
          refine ⟨16570284129826415173875449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11046856086550943449250299 16570284129826415173875449)
          ·
            refine ⟨12427713097369811380406587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16570284129826415173875449 12427713097369811380406587)
            ·
              refine ⟨18641569646054717070609881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12427713097369811380406587 18641569646054717070609881)
              ·
                refine ⟨13981177234541037802957411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18641569646054717070609881 13981177234541037802957411)
                ·
                  refine ⟨20971765851811556704436117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13981177234541037802957411 20971765851811556704436117)
                  ·
                    refine ⟨983051524303666720520443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20971765851811556704436117 983051524303666720520443)
                    ·
                      rfl

theorem cell22_2871729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 2, 1, 6].length) (baseStart_2871729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2871729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2871729 prefixEnd_2871729 := by exact prefixLift 2871729
  have htrace : WordTrace (prefixWord ++ tailWord_2871729) baseStart_2871729 baseEnd_2871729 := by
    simpa [prefixWord, tailWord_2871729, baseEnd_2871729] using wordTrace_append hprefix tailTrace_2871729
  have hstable : (prefixWord ++ tailWord_2871729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2871729).length < 2 ^ (prefixWord ++ tailWord_2871729).sum := by decide
  have hdescent : baseEnd_2871729 < baseStart_2871729 := by decide
  rcases family_descends (prefixWord ++ tailWord_2871729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2871804 : List Nat := [2, 2, 2, 1, 2, 1, 1, 2, 4, 5]
def baseStart_2871804 : Nat := 118140960795 + 2871804 * 2 ^ 59
def prefixEnd_2871804 : Nat := 4983230072969 + 3 ^ 40 * 2871804 * 2
def baseEnd_2871804 : Nat := 983077198336391524895213

theorem tailTrace_2871804 : CollatzResearch.WordTrace tailWord_2871804 prefixEnd_2871804 983077198336391524895213 := by
  unfold tailWord_2871804
  simp only [CollatzResearch.WordTrace]
  refine ⟨52371648443976023960195233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69828864591968031946926977 52371648443976023960195233)
  ·
    refine ⟨39278736332982017970146425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52371648443976023960195233 39278736332982017970146425)
    ·
      refine ⟨29459052249736513477609819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39278736332982017970146425 29459052249736513477609819)
      ·
        refine ⟨44188578374604770216414729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29459052249736513477609819 44188578374604770216414729)
        ·
          refine ⟨33141433780953577662311047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44188578374604770216414729 33141433780953577662311047)
          ·
            refine ⟨49712150671430366493466571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33141433780953577662311047 49712150671430366493466571)
            ·
              refine ⟨74568226007145549740199857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49712150671430366493466571 74568226007145549740199857)
              ·
                refine ⟨55926169505359162305149893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74568226007145549740199857 55926169505359162305149893)
                ·
                  refine ⟨10486156782254842932215605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55926169505359162305149893 10486156782254842932215605)
                  ·
                    refine ⟨983077198336391524895213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10486156782254842932215605 983077198336391524895213)
                    ·
                      rfl

theorem cell22_2871804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 4, 5].length) (baseStart_2871804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2871804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2871804 prefixEnd_2871804 := by exact prefixLift 2871804
  have htrace : WordTrace (prefixWord ++ tailWord_2871804) baseStart_2871804 baseEnd_2871804 := by
    simpa [prefixWord, tailWord_2871804, baseEnd_2871804] using wordTrace_append hprefix tailTrace_2871804
  have hstable : (prefixWord ++ tailWord_2871804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2871804).length < 2 ^ (prefixWord ++ tailWord_2871804).sum := by decide
  have hdescent : baseEnd_2871804 < baseStart_2871804 := by decide
  rcases family_descends (prefixWord ++ tailWord_2871804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2871836 : List Nat := [2, 2, 3, 1, 2, 2, 1, 2, 3, 4]
def baseStart_2871836 : Nat := 118140960795 + 2871836 * 2 ^ 59
def prefixEnd_2871836 : Nat := 4983230072969 + 3 ^ 40 * 2871836 * 2
def baseEnd_2871836 : Nat := 983088152590354108095115

theorem tailTrace_2871836 : CollatzResearch.WordTrace tailWord_2871836 prefixEnd_2871836 983088152590354108095115 := by
  unfold tailWord_2871836
  simp only [CollatzResearch.WordTrace]
  refine ⟨52372232011918058692777681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69829642682557411590370241 52372232011918058692777681)
  ·
    refine ⟨39279174008938544019583261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52372232011918058692777681 39279174008938544019583261)
    ·
      refine ⟨14729690253351954007343723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39279174008938544019583261 14729690253351954007343723)
      ·
        refine ⟨22094535380027931011015585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14729690253351954007343723 22094535380027931011015585)
        ·
          refine ⟨16570901535020948258261689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22094535380027931011015585 16570901535020948258261689)
          ·
            refine ⟨12428176151265711193696267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16570901535020948258261689 12428176151265711193696267)
            ·
              refine ⟨18642264226898566790544401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12428176151265711193696267 18642264226898566790544401)
              ·
                refine ⟨13981698170173925092908301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18642264226898566790544401 13981698170173925092908301)
                ·
                  refine ⟨5243136813815221909840613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13981698170173925092908301 5243136813815221909840613)
                  ·
                    refine ⟨983088152590354108095115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5243136813815221909840613 983088152590354108095115)
                    ·
                      rfl

theorem cell22_2871836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 2, 3, 4].length) (baseStart_2871836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2871836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2871836 prefixEnd_2871836 := by exact prefixLift 2871836
  have htrace : WordTrace (prefixWord ++ tailWord_2871836) baseStart_2871836 baseEnd_2871836 := by
    simpa [prefixWord, tailWord_2871836, baseEnd_2871836] using wordTrace_append hprefix tailTrace_2871836
  have hstable : (prefixWord ++ tailWord_2871836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2871836).length < 2 ^ (prefixWord ++ tailWord_2871836).sum := by decide
  have hdescent : baseEnd_2871836 < baseStart_2871836 := by decide
  rcases family_descends (prefixWord ++ tailWord_2871836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2871866 : List Nat := [3, 1, 1, 1, 3, 3, 2, 2, 1, 5]
def baseStart_2871866 : Nat := 118140960795 + 2871866 * 2 ^ 59
def prefixEnd_2871866 : Nat := 4983230072969 + 3 ^ 40 * 2871866 * 2
def baseEnd_2871866 : Nat := 983098422203444029845023

theorem tailTrace_2871866 : CollatzResearch.WordTrace tailWord_2871866 prefixEnd_2871866 983098422203444029845023 := by
  unfold tailWord_2871866
  simp only [CollatzResearch.WordTrace]
  refine ⟨26186389553431858127286863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69830372142484955006098301 26186389553431858127286863)
  ·
    refine ⟨39279584330147787190930295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26186389553431858127286863 39279584330147787190930295)
    ·
      refine ⟨58919376495221680786395443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39279584330147787190930295 58919376495221680786395443)
      ·
        refine ⟨88379064742832521179593165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58919376495221680786395443 88379064742832521179593165)
        ·
          refine ⟨33142149278562195442347437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88379064742832521179593165 33142149278562195442347437)
          ·
            refine ⟨12428305979460823290880289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33142149278562195442347437 12428305979460823290880289)
            ·
              refine ⟨9321229484595617468160217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12428305979460823290880289 9321229484595617468160217)
              ·
                refine ⟨6990922113446713101120163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9321229484595617468160217 6990922113446713101120163)
                ·
                  refine ⟨10486383170170069651680245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6990922113446713101120163 10486383170170069651680245)
                  ·
                    refine ⟨983098422203444029845023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10486383170170069651680245 983098422203444029845023)
                    ·
                      rfl

theorem cell22_2871866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 2, 1, 5].length) (baseStart_2871866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2871866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2871866 prefixEnd_2871866 := by exact prefixLift 2871866
  have htrace : WordTrace (prefixWord ++ tailWord_2871866) baseStart_2871866 baseEnd_2871866 := by
    simpa [prefixWord, tailWord_2871866, baseEnd_2871866] using wordTrace_append hprefix tailTrace_2871866
  have hstable : (prefixWord ++ tailWord_2871866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2871866).length < 2 ^ (prefixWord ++ tailWord_2871866).sum := by decide
  have hdescent : baseEnd_2871866 < baseStart_2871866 := by decide
  rcases family_descends (prefixWord ++ tailWord_2871866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2871868 : List Nat := [2, 2, 2, 2, 3, 1, 1, 5, 4]
def baseStart_2871868 : Nat := 118140960795 + 2871868 * 2 ^ 59
def prefixEnd_2871868 : Nat := 4983230072969 + 3 ^ 40 * 2871868 * 2
def baseEnd_2871868 : Nat := 327699702281438897098339

theorem tailTrace_2871868 : CollatzResearch.WordTrace tailWord_2871868 prefixEnd_2871868 327699702281438897098339 := by
  unfold tailWord_2871868
  simp only [CollatzResearch.WordTrace]
  refine ⟨52372815579860093425360129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69830420773146791233813505 52372815579860093425360129)
  ·
    refine ⟨39279611684895070069020097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52372815579860093425360129 39279611684895070069020097)
    ·
      refine ⟨29459708763671302551765073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39279611684895070069020097 29459708763671302551765073)
      ·
        refine ⟨22094781572753476913823805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29459708763671302551765073 22094781572753476913823805)
        ·
          refine ⟨8285543089782553842683927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22094781572753476913823805 8285543089782553842683927)
          ·
            refine ⟨12428314634673830764025891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8285543089782553842683927 12428314634673830764025891)
            ·
              refine ⟨18642471952010746146038837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12428314634673830764025891 18642471952010746146038837)
              ·
                refine ⟨1747731745501007451191141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18642471952010746146038837 1747731745501007451191141)
                ·
                  refine ⟨327699702281438897098339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1747731745501007451191141 327699702281438897098339)
                  ·
                    rfl

theorem cell22_2871868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 5, 4].length) (baseStart_2871868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2871868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2871868 prefixEnd_2871868 := by exact prefixLift 2871868
  have htrace : WordTrace (prefixWord ++ tailWord_2871868) baseStart_2871868 baseEnd_2871868 := by
    simpa [prefixWord, tailWord_2871868, baseEnd_2871868] using wordTrace_append hprefix tailTrace_2871868
  have hstable : (prefixWord ++ tailWord_2871868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2871868).length < 2 ^ (prefixWord ++ tailWord_2871868).sum := by decide
  have hdescent : baseEnd_2871868 < baseStart_2871868 := by decide
  rcases family_descends (prefixWord ++ tailWord_2871868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2871883 : List Nat := [1, 1, 1, 1, 3, 1, 7, 2, 2, 3]
def baseStart_2871883 : Nat := 118140960795 + 2871883 * 2 ^ 59
def prefixEnd_2871883 : Nat := 4983230072969 + 3 ^ 40 * 2871883 * 2
def baseEnd_2871883 : Nat := 983104241650861652169971

theorem tailTrace_2871883 : CollatzResearch.WordTrace tailWord_2871883 prefixEnd_2871883 983104241650861652169971 := by
  unfold tailWord_2871883
  simp only [CollatzResearch.WordTrace]
  refine ⟨104746178254665844412516303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69830785503110562941677535 104746178254665844412516303)
  ·
    refine ⟨157119267381998766618774455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104746178254665844412516303 157119267381998766618774455)
    ·
      refine ⟨235678901072998149928161683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157119267381998766618774455 235678901072998149928161683)
      ·
        refine ⟨353518351609497224892242525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235678901072998149928161683 353518351609497224892242525)
        ·
          refine ⟨132569381853561459334590947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 353518351609497224892242525 132569381853561459334590947)
          ·
            refine ⟨198854072780342189001886421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132569381853561459334590947 198854072780342189001886421)
            ·
              refine ⟨4660642330789270054731713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 198854072780342189001886421 4660642330789270054731713)
              ·
                refine ⟨3495481748091952541048785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4660642330789270054731713 3495481748091952541048785)
                ·
                  refine ⟨2621611311068964405786589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3495481748091952541048785 2621611311068964405786589)
                  ·
                    refine ⟨983104241650861652169971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2621611311068964405786589 983104241650861652169971)
                    ·
                      rfl

theorem cell22_2871883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 7, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 7, 2, 2, 3].length) (baseStart_2871883 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2871883 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2871883 prefixEnd_2871883 := by exact prefixLift 2871883
  have htrace : WordTrace (prefixWord ++ tailWord_2871883) baseStart_2871883 baseEnd_2871883 := by
    simpa [prefixWord, tailWord_2871883, baseEnd_2871883] using wordTrace_append hprefix tailTrace_2871883
  have hstable : (prefixWord ++ tailWord_2871883).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2871883).length < 2 ^ (prefixWord ++ tailWord_2871883).sum := by decide
  have hdescent : baseEnd_2871883 < baseStart_2871883 := by decide
  rcases family_descends (prefixWord ++ tailWord_2871883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2871885 : List Nat := [1, 6, 1, 1, 2, 1, 2, 4, 4]
def baseStart_2871885 : Nat := 118140960795 + 2871885 * 2 ^ 59
def prefixEnd_2871885 : Nat := 4983230072969 + 3 ^ 40 * 2871885 * 2
def baseEnd_2871885 : Nat := 327701642097244771206655

theorem tailTrace_2871885 : CollatzResearch.WordTrace tailWord_2871885 prefixEnd_2871885 327701642097244771206655 := by
  unfold tailWord_2871885
  simp only [CollatzResearch.WordTrace]
  refine ⟨104746251200658598754089109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69830834133772399169392739 104746251200658598754089109)
  ·
    refine ⟨4909980525030871816597927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 104746251200658598754089109 4909980525030871816597927)
    ·
      refine ⟨7364970787546307724896891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4909980525030871816597927 7364970787546307724896891)
      ·
        refine ⟨11047456181319461587345337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7364970787546307724896891 11047456181319461587345337)
        ·
          refine ⟨8285592135989596190509003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11047456181319461587345337 8285592135989596190509003)
          ·
            refine ⟨12428388203984394285763505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8285592135989596190509003 12428388203984394285763505)
            ·
              refine ⟨9321291152988295714322629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12428388203984394285763505 9321291152988295714322629)
              ·
                refine ⟨1747742091185305446435493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9321291152988295714322629 1747742091185305446435493)
                ·
                  refine ⟨327701642097244771206655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1747742091185305446435493 327701642097244771206655)
                  ·
                    rfl

theorem cell22_2871885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 4, 4].length) (baseStart_2871885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2871885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2871885 prefixEnd_2871885 := by exact prefixLift 2871885
  have htrace : WordTrace (prefixWord ++ tailWord_2871885) baseStart_2871885 baseEnd_2871885 := by
    simpa [prefixWord, tailWord_2871885, baseEnd_2871885] using wordTrace_append hprefix tailTrace_2871885
  have hstable : (prefixWord ++ tailWord_2871885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2871885).length < 2 ^ (prefixWord ++ tailWord_2871885).sum := by decide
  have hdescent : baseEnd_2871885 < baseStart_2871885 := by decide
  rcases family_descends (prefixWord ++ tailWord_2871885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2871900 : List Nat := [2, 2, 4, 1, 3, 2, 1, 1, 1, 5]
def baseStart_2871900 : Nat := 118140960795 + 2871900 * 2 ^ 59
def prefixEnd_2871900 : Nat := 4983230072969 + 3 ^ 40 * 2871900 * 2
def baseEnd_2871900 : Nat := 983110061098279274494919

theorem tailTrace_2871900 : CollatzResearch.WordTrace tailWord_2871900 prefixEnd_2871900 983110061098279274494919 := by
  unfold tailWord_2871900
  simp only [CollatzResearch.WordTrace]
  refine ⟨52373399147802128157942577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69831198863736170877256769 52373399147802128157942577)
  ·
    refine ⟨39280049360851596118456933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52373399147802128157942577 39280049360851596118456933)
    ·
      refine ⟨7365009255159674272210675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39280049360851596118456933 7365009255159674272210675)
      ·
        refine ⟨11047513882739511408316013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7365009255159674272210675 11047513882739511408316013)
        ·
          refine ⟨4142817706027316778118505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11047513882739511408316013 4142817706027316778118505)
          ·
            refine ⟨3107113279520487583588879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4142817706027316778118505 3107113279520487583588879)
            ·
              refine ⟨4660669919280731375383319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3107113279520487583588879 4660669919280731375383319)
              ·
                refine ⟨6991004878921097063074979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4660669919280731375383319 6991004878921097063074979)
                ·
                  refine ⟨10486507318381645594612469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6991004878921097063074979 10486507318381645594612469)
                  ·
                    refine ⟨983110061098279274494919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10486507318381645594612469 983110061098279274494919)
                    ·
                      rfl

theorem cell22_2871900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 1, 1, 1, 5].length) (baseStart_2871900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2871900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2871900 prefixEnd_2871900 := by exact prefixLift 2871900
  have htrace : WordTrace (prefixWord ++ tailWord_2871900) baseStart_2871900 baseEnd_2871900 := by
    simpa [prefixWord, tailWord_2871900, baseEnd_2871900] using wordTrace_append hprefix tailTrace_2871900
  have hstable : (prefixWord ++ tailWord_2871900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2871900).length < 2 ^ (prefixWord ++ tailWord_2871900).sum := by decide
  have hdescent : baseEnd_2871900 < baseStart_2871900 := by decide
  rcases family_descends (prefixWord ++ tailWord_2871900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2871941 : List Nat := [1, 3, 1, 1, 4, 2, 2, 1, 7]
def baseStart_2871941 : Nat := 118140960795 + 2871941 * 2 ^ 59
def prefixEnd_2871941 : Nat := 4983230072969 + 3 ^ 40 * 2871941 * 2
def baseEnd_2871941 : Nat := 327708032078722944739931

theorem tailTrace_2871941 : CollatzResearch.WordTrace tailWord_2871941 prefixEnd_2871941 327708032078722944739931 := by
  unfold tailWord_2871941
  simp only [CollatzResearch.WordTrace]
  refine ⟨104748293688455720318127677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69832195792303813545418451 104748293688455720318127677)
  ·
    refine ⟨39280610133170895119297879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104748293688455720318127677 39280610133170895119297879)
    ·
      refine ⟨58920915199756342678946819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39280610133170895119297879 58920915199756342678946819)
      ·
        refine ⟨88381372799634514018420229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58920915199756342678946819 88381372799634514018420229)
        ·
          refine ⟨16571507399931471378453793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 88381372799634514018420229 16571507399931471378453793)
          ·
            refine ⟨12428630549948603533840345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16571507399931471378453793 12428630549948603533840345)
            ·
              refine ⟨9321472912461452650380259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12428630549948603533840345 9321472912461452650380259)
              ·
                refine ⟨13982209368692178975570389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9321472912461452650380259 13982209368692178975570389)
                ·
                  refine ⟨327708032078722944739931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13982209368692178975570389 327708032078722944739931)
                  ·
                    rfl

theorem cell22_2871941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 1, 7].length) (baseStart_2871941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2871941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2871941 prefixEnd_2871941 := by exact prefixLift 2871941
  have htrace : WordTrace (prefixWord ++ tailWord_2871941) baseStart_2871941 baseEnd_2871941 := by
    simpa [prefixWord, tailWord_2871941, baseEnd_2871941] using wordTrace_append hprefix tailTrace_2871941
  have hstable : (prefixWord ++ tailWord_2871941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2871941).length < 2 ^ (prefixWord ++ tailWord_2871941).sum := by decide
  have hdescent : baseEnd_2871941 < baseStart_2871941 := by decide
  rcases family_descends (prefixWord ++ tailWord_2871941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2872020 : List Nat := [2, 4, 1, 3, 2, 1, 1, 2, 6]
def baseStart_2872020 : Nat := 118140960795 + 2872020 * 2 ^ 59
def prefixEnd_2872020 : Nat := 4983230072969 + 3 ^ 40 * 2872020 * 2
def baseEnd_2872020 : Nat := 327717046516879653831517

theorem tailTrace_2872020 : CollatzResearch.WordTrace tailWord_2872020 prefixEnd_2872020 327717046516879653831517 := by
  unfold tailWord_2872020
  simp only [CollatzResearch.WordTrace]
  refine ⟨52375587527584758405126757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69834116703446344540169009 52375587527584758405126757)
  ·
    refine ⟨9820422661422142200961267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52375587527584758405126757 9820422661422142200961267)
    ·
      refine ⟨14730633992133213301441901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9820422661422142200961267 14730633992133213301441901)
      ·
        refine ⟨5523987747049954988040713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14730633992133213301441901 5523987747049954988040713)
        ·
          refine ⟨4142990810287466241030535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5523987747049954988040713 4142990810287466241030535)
          ·
            refine ⟨6214486215431199361545803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4142990810287466241030535 6214486215431199361545803)
            ·
              refine ⟨9321729323146799042318705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6214486215431199361545803 9321729323146799042318705)
              ·
                refine ⟨6991296992360099281739029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9321729323146799042318705 6991296992360099281739029)
                ·
                  refine ⟨327717046516879653831517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6991296992360099281739029 327717046516879653831517)
                  ·
                    rfl

theorem cell22_2872020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 2, 6].length) (baseStart_2872020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2872020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2872020 prefixEnd_2872020 := by exact prefixLift 2872020
  have htrace : WordTrace (prefixWord ++ tailWord_2872020) baseStart_2872020 baseEnd_2872020 := by
    simpa [prefixWord, tailWord_2872020, baseEnd_2872020] using wordTrace_append hprefix tailTrace_2872020
  have hstable : (prefixWord ++ tailWord_2872020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2872020).length < 2 ^ (prefixWord ++ tailWord_2872020).sum := by decide
  have hdescent : baseEnd_2872020 < baseStart_2872020 := by decide
  rcases family_descends (prefixWord ++ tailWord_2872020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2872033 : List Nat := [1, 2, 3, 1, 4, 2, 1, 1, 1, 6]
def baseStart_2872033 : Nat := 118140960795 + 2872033 * 2 ^ 59
def prefixEnd_2872033 : Nat := 4983230072969 + 3 ^ 40 * 2872033 * 2
def baseEnd_2872033 : Nat := 983155589716311260919511

theorem tailTrace_2872033 : CollatzResearch.WordTrace tailWord_2872033 prefixEnd_2872033 983155589716311260919511 := by
  unfold tailWord_2872033
  simp only [CollatzResearch.WordTrace]
  refine ⟨104751649204122420030476753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69834432802748280020317835 104751649204122420030476753)
  ·
    refine ⟨78563736903091815022857565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104751649204122420030476753 78563736903091815022857565)
    ·
      refine ⟨29461401338659430633571587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78563736903091815022857565 29461401338659430633571587)
      ·
        refine ⟨44192102007989145950357381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29461401338659430633571587 44192102007989145950357381)
        ·
          refine ⟨8286019126497964865692009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44192102007989145950357381 8286019126497964865692009)
          ·
            refine ⟨6214514344873473649269007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8286019126497964865692009 6214514344873473649269007)
            ·
              refine ⟨9321771517310210473903511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6214514344873473649269007 9321771517310210473903511)
              ·
                refine ⟨13982657275965315710855267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9321771517310210473903511 13982657275965315710855267)
                ·
                  refine ⟨20973985913947973566282901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13982657275965315710855267 20973985913947973566282901)
                  ·
                    refine ⟨983155589716311260919511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20973985913947973566282901 983155589716311260919511)
                    ·
                      rfl

theorem cell22_2872033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 1, 1, 6].length) (baseStart_2872033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2872033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2872033 prefixEnd_2872033 := by exact prefixLift 2872033
  have htrace : WordTrace (prefixWord ++ tailWord_2872033) baseStart_2872033 baseEnd_2872033 := by
    simpa [prefixWord, tailWord_2872033, baseEnd_2872033] using wordTrace_append hprefix tailTrace_2872033
  have hstable : (prefixWord ++ tailWord_2872033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2872033).length < 2 ^ (prefixWord ++ tailWord_2872033).sum := by decide
  have hdescent : baseEnd_2872033 < baseStart_2872033 := by decide
  rcases family_descends (prefixWord ++ tailWord_2872033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2872110 : List Nat := [4, 1, 3, 2, 1, 1, 2, 1, 7]
def baseStart_2872110 : Nat := 118140960795 + 2872110 * 2 ^ 59
def prefixEnd_2872110 : Nat := 4983230072969 + 3 ^ 40 * 2872110 * 2
def baseEnd_2872110 : Nat := 327727316129969575581425

theorem tailTrace_2872110 : CollatzResearch.WordTrace tailWord_2872110 prefixEnd_2872110 327727316129969575581425 := by
  unfold tailWord_2872110
  simp only [CollatzResearch.WordTrace]
  refine ⟨13094307203105432772628723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69836305083228974787353189 13094307203105432772628723)
  ·
    refine ⟨19641460804658149158943085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13094307203105432772628723 19641460804658149158943085)
    ·
      refine ⟨7365547801746805934603657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19641460804658149158943085 7365547801746805934603657)
      ·
        refine ⟨5524160851310104450952743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7365547801746805934603657 5524160851310104450952743)
        ·
          refine ⟨8286241276965156676429115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5524160851310104450952743 8286241276965156676429115)
          ·
            refine ⟨12429361915447735014643673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8286241276965156676429115 12429361915447735014643673)
            ·
              refine ⟨9322021436585801260982755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12429361915447735014643673 9322021436585801260982755)
              ·
                refine ⟨13983032154878701891474133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9322021436585801260982755 13983032154878701891474133)
                ·
                  refine ⟨327727316129969575581425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13983032154878701891474133 327727316129969575581425)
                  ·
                    rfl

theorem cell22_2872110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 1, 7].length) (baseStart_2872110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2872110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2872110 prefixEnd_2872110 := by exact prefixLift 2872110
  have htrace : WordTrace (prefixWord ++ tailWord_2872110) baseStart_2872110 baseEnd_2872110 := by
    simpa [prefixWord, tailWord_2872110, baseEnd_2872110] using wordTrace_append hprefix tailTrace_2872110
  have hstable : (prefixWord ++ tailWord_2872110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2872110).length < 2 ^ (prefixWord ++ tailWord_2872110).sum := by decide
  have hdescent : baseEnd_2872110 < baseStart_2872110 := by decide
  rcases family_descends (prefixWord ++ tailWord_2872110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2872114 : List Nat := [3, 2, 1, 1, 3, 1, 5, 2, 1, 3]
def baseStart_2872114 : Nat := 118140960795 + 2872114 * 2 ^ 59
def prefixEnd_2872114 : Nat := 4983230072969 + 3 ^ 40 * 2872114 * 2
def baseEnd_2872114 : Nat := 983183317671654049644263

theorem tailTrace_2872114 : CollatzResearch.WordTrace tailWord_2872114 prefixEnd_2872114 983183317671654049644263 := by
  unfold tailWord_2872114
  simp only [CollatzResearch.WordTrace]
  refine ⟨26188650879207242716043849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69836402344552647242783597 26188650879207242716043849)
  ·
    refine ⟨19641488159405432037032887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26188650879207242716043849 19641488159405432037032887)
    ·
      refine ⟨29462232239108148055549331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19641488159405432037032887 29462232239108148055549331)
      ·
        refine ⟨44193348358662222083323997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29462232239108148055549331 44193348358662222083323997)
        ·
          refine ⟨16572505634498333281246499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44193348358662222083323997 16572505634498333281246499)
          ·
            refine ⟨24858758451747499921869749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16572505634498333281246499 24858758451747499921869749)
            ·
              refine ⟨2330508604851328117675289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24858758451747499921869749 2330508604851328117675289)
              ·
                refine ⟨1747881453638496088256467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2330508604851328117675289 1747881453638496088256467)
                ·
                  refine ⟨2621822180457744132384701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1747881453638496088256467 2621822180457744132384701)
                  ·
                    refine ⟨983183317671654049644263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2621822180457744132384701 983183317671654049644263)
                    ·
                      rfl

theorem cell22_2872114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 5, 2, 1, 3].length) (baseStart_2872114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2872114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2872114 prefixEnd_2872114 := by exact prefixLift 2872114
  have htrace : WordTrace (prefixWord ++ tailWord_2872114) baseStart_2872114 baseEnd_2872114 := by
    simpa [prefixWord, tailWord_2872114, baseEnd_2872114] using wordTrace_append hprefix tailTrace_2872114
  have hstable : (prefixWord ++ tailWord_2872114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2872114).length < 2 ^ (prefixWord ++ tailWord_2872114).sum := by decide
  have hdescent : baseEnd_2872114 < baseStart_2872114 := by decide
  rcases family_descends (prefixWord ++ tailWord_2872114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2872127 : List Nat := [1, 1, 2, 2, 5, 3, 2, 1, 5]
def baseStart_2872127 : Nat := 118140960795 + 2872127 * 2 ^ 59
def prefixEnd_2872127 : Nat := 4983230072969 + 3 ^ 40 * 2872127 * 2
def baseEnd_2872127 : Nat := 327729255945775449689741

theorem tailTrace_2872127 : CollatzResearch.WordTrace tailWord_2872127 prefixEnd_2872127 327729255945775449689741 := by
  unfold tailWord_2872127
  simp only [CollatzResearch.WordTrace]
  refine ⟨104755077665781874084398635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69836718443854582722932423 104755077665781874084398635)
  ·
    refine ⟨157132616498672811126597953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104755077665781874084398635 157132616498672811126597953)
    ·
      refine ⟨117849462374004608344948465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157132616498672811126597953 117849462374004608344948465)
      ·
        refine ⟨88387096780503456258711349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117849462374004608344948465 88387096780503456258711349)
        ·
          refine ⟨8286290323172199024254189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 88387096780503456258711349 8286290323172199024254189)
          ·
            refine ⟨3107358871189574634095321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8286290323172199024254189 3107358871189574634095321)
            ·
              refine ⟨2330519153392180975571491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3107358871189574634095321 2330519153392180975571491)
              ·
                refine ⟨3495778730088271463357237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2330519153392180975571491 3495778730088271463357237)
                ·
                  refine ⟨327729255945775449689741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3495778730088271463357237 327729255945775449689741)
                  ·
                    rfl

theorem cell22_2872127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 2, 1, 5].length) (baseStart_2872127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2872127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2872127 prefixEnd_2872127 := by exact prefixLift 2872127
  have htrace : WordTrace (prefixWord ++ tailWord_2872127) baseStart_2872127 baseEnd_2872127 := by
    simpa [prefixWord, tailWord_2872127, baseEnd_2872127] using wordTrace_append hprefix tailTrace_2872127
  have hstable : (prefixWord ++ tailWord_2872127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2872127).length < 2 ^ (prefixWord ++ tailWord_2872127).sum := by decide
  have hdescent : baseEnd_2872127 < baseStart_2872127 := by decide
  rcases family_descends (prefixWord ++ tailWord_2872127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2872140 : List Nat := [2, 2, 1, 3, 3, 2, 1, 1, 3, 4]
def baseStart_2872140 : Nat := 118140960795 + 2872140 * 2 ^ 59
def prefixEnd_2872140 : Nat := 4983230072969 + 3 ^ 40 * 2872140 * 2
def baseEnd_2872140 : Nat := 983192218002998648494183

theorem tailTrace_2872140 : CollatzResearch.WordTrace tailWord_2872140 prefixEnd_2872140 983192218002998648494183 := by
  unfold tailWord_2872140
  simp only [CollatzResearch.WordTrace]
  refine ⟨52377775907367388652310937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69837034543156518203081249 52377775907367388652310937)
  ·
    refine ⟨39283331930525541489233203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52377775907367388652310937 39283331930525541489233203)
    ·
      refine ⟨58924997895788312233849805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39283331930525541489233203 58924997895788312233849805)
      ·
        refine ⟨22096874210920617087693677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58924997895788312233849805 22096874210920617087693677)
        ·
          refine ⟨8286327829095231407885129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22096874210920617087693677 8286327829095231407885129)
          ·
            refine ⟨6214745871821423555913847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8286327829095231407885129 6214745871821423555913847)
            ·
              refine ⟨9322118807732135333870771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6214745871821423555913847 9322118807732135333870771)
              ·
                refine ⟨13983178211598203000806157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9322118807732135333870771 13983178211598203000806157)
                ·
                  refine ⟨5243691829349326125302309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13983178211598203000806157 5243691829349326125302309)
                  ·
                    refine ⟨983192218002998648494183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5243691829349326125302309 983192218002998648494183)
                    ·
                      rfl

theorem cell22_2872140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 1, 3, 4].length) (baseStart_2872140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2872140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2872140 prefixEnd_2872140 := by exact prefixLift 2872140
  have htrace : WordTrace (prefixWord ++ tailWord_2872140) baseStart_2872140 baseEnd_2872140 := by
    simpa [prefixWord, tailWord_2872140, baseEnd_2872140] using wordTrace_append hprefix tailTrace_2872140
  have hstable : (prefixWord ++ tailWord_2872140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2872140).length < 2 ^ (prefixWord ++ tailWord_2872140).sum := by decide
  have hdescent : baseEnd_2872140 < baseStart_2872140 := by decide
  rcases family_descends (prefixWord ++ tailWord_2872140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2872153 : List Nat := [1, 2, 1, 2, 2, 4, 1, 1, 3, 5]
def baseStart_2872153 : Nat := 118140960795 + 2872153 * 2 ^ 59
def prefixEnd_2872153 : Nat := 4983230072969 + 3 ^ 40 * 2872153 * 2
def baseEnd_2872153 : Nat := 983196668168670947919143

theorem tailTrace_2872153 : CollatzResearch.WordTrace tailWord_2872153 prefixEnd_2872153 983196668168670947919143 := by
  unfold tailWord_2872153
  simp only [CollatzResearch.WordTrace]
  refine ⟨104756025963687680524845113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69837350642458453683230075 104756025963687680524845113)
  ·
    refine ⟨78567019472765760393633835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104756025963687680524845113 78567019472765760393633835)
    ·
      refine ⟨117850529209148640590450753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78567019472765760393633835 117850529209148640590450753)
      ·
        refine ⟨88387896906861480442838065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117850529209148640590450753 88387896906861480442838065)
        ·
          refine ⟨66290922680146110332128549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88387896906861480442838065 66290922680146110332128549)
          ·
            refine ⟨12429548002527395687274103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66290922680146110332128549 12429548002527395687274103)
            ·
              refine ⟨18644322003791093530911155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12429548002527395687274103 18644322003791093530911155)
              ·
                refine ⟨27966483005686640296366733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18644322003791093530911155 27966483005686640296366733)
                ·
                  refine ⟨10487431127132490111137525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27966483005686640296366733 10487431127132490111137525)
                  ·
                    refine ⟨983196668168670947919143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10487431127132490111137525 983196668168670947919143)
                    ·
                      rfl

theorem cell22_2872153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 1, 3, 5].length) (baseStart_2872153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2872153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2872153 prefixEnd_2872153 := by exact prefixLift 2872153
  have htrace : WordTrace (prefixWord ++ tailWord_2872153) baseStart_2872153 baseEnd_2872153 := by
    simpa [prefixWord, tailWord_2872153, baseEnd_2872153] using wordTrace_append hprefix tailTrace_2872153
  have hstable : (prefixWord ++ tailWord_2872153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2872153).length < 2 ^ (prefixWord ++ tailWord_2872153).sum := by decide
  have hdescent : baseEnd_2872153 < baseStart_2872153 := by decide
  rcases family_descends (prefixWord ++ tailWord_2872153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2872202 : List Nat := [3, 1, 2, 4, 1, 1, 3, 1, 2, 4]
def baseStart_2872202 : Nat := 118140960795 + 2872202 * 2 ^ 59
def prefixEnd_2872202 : Nat := 4983230072969 + 3 ^ 40 * 2872202 * 2
def baseEnd_2872202 : Nat := 983213441870051153443993

theorem tailTrace_2872202 : CollatzResearch.WordTrace tailWord_2872202 prefixEnd_2872202 983213441870051153443993 := by
  unfold tailWord_2872202
  simp only [CollatzResearch.WordTrace]
  refine ⟨26189453285127540473344715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69838542093673441262252573 26189453285127540473344715)
  ·
    refine ⟨39284179927691310710017073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26189453285127540473344715 39284179927691310710017073)
    ·
      refine ⟨29463134945768483032512805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39284179927691310710017073 29463134945768483032512805)
      ·
        refine ⟨5524337802331590568596151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29463134945768483032512805 5524337802331590568596151)
        ·
          refine ⟨8286506703497385852894227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5524337802331590568596151 8286506703497385852894227)
          ·
            refine ⟨12429760055246078779341341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8286506703497385852894227 12429760055246078779341341)
            ·
              refine ⟨4661160020717279542253003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12429760055246078779341341 4661160020717279542253003)
              ·
                refine ⟨6991740031075919313379505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4661160020717279542253003 6991740031075919313379505)
                ·
                  refine ⟨5243805023306939485034629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6991740031075919313379505 5243805023306939485034629)
                  ·
                    refine ⟨983213441870051153443993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5243805023306939485034629 983213441870051153443993)
                    ·
                      rfl

theorem cell22_2872202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 3, 1, 2, 4].length) (baseStart_2872202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2872202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2872202 prefixEnd_2872202 := by exact prefixLift 2872202
  have htrace : WordTrace (prefixWord ++ tailWord_2872202) baseStart_2872202 baseEnd_2872202 := by
    simpa [prefixWord, tailWord_2872202, baseEnd_2872202] using wordTrace_append hprefix tailTrace_2872202
  have hstable : (prefixWord ++ tailWord_2872202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2872202).length < 2 ^ (prefixWord ++ tailWord_2872202).sum := by decide
  have hdescent : baseEnd_2872202 < baseStart_2872202 := by decide
  rcases family_descends (prefixWord ++ tailWord_2872202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2872215 : List Nat := [1, 1, 3, 3, 1, 2, 1, 2, 5, 3]
def baseStart_2872215 : Nat := 118140960795 + 2872215 * 2 ^ 59
def prefixEnd_2872215 : Nat := 4983230072969 + 3 ^ 40 * 2872215 * 2
def baseEnd_2872215 : Nat := 983217892035723452868953

theorem tailTrace_2872215 : CollatzResearch.WordTrace tailWord_2872215 prefixEnd_2872215 983217892035723452868953 := by
  unfold tailWord_2872215
  simp only [CollatzResearch.WordTrace]
  refine ⟨104758287289463065113602099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69838858192975376742401399 104758287289463065113602099)
  ·
    refine ⟨157137430934194597670403149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104758287289463065113602099 157137430934194597670403149)
    ·
      refine ⟨58926536600322974126401181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157137430934194597670403149 58926536600322974126401181)
      ·
        refine ⟨22097451225121115297400443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58926536600322974126401181 22097451225121115297400443)
        ·
          refine ⟨33146176837681672946100665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22097451225121115297400443 33146176837681672946100665)
          ·
            refine ⟨24859632628261254709575499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33146176837681672946100665 24859632628261254709575499)
            ·
              refine ⟨37289448942391882064363249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24859632628261254709575499 37289448942391882064363249)
              ·
                refine ⟨27967086706793911548272437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37289448942391882064363249 27967086706793911548272437)
                ·
                  refine ⟨2621914378761929207650541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27967086706793911548272437 2621914378761929207650541)
                  ·
                    refine ⟨983217892035723452868953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2621914378761929207650541 983217892035723452868953)
                    ·
                      rfl

theorem cell22_2872215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 2, 5, 3].length) (baseStart_2872215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2872215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2872215 prefixEnd_2872215 := by exact prefixLift 2872215
  have htrace : WordTrace (prefixWord ++ tailWord_2872215) baseStart_2872215 baseEnd_2872215 := by
    simpa [prefixWord, tailWord_2872215, baseEnd_2872215] using wordTrace_append hprefix tailTrace_2872215
  have hstable : (prefixWord ++ tailWord_2872215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2872215).length < 2 ^ (prefixWord ++ tailWord_2872215).sum := by decide
  have hdescent : baseEnd_2872215 < baseStart_2872215 := by decide
  rcases family_descends (prefixWord ++ tailWord_2872215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2872243 : List Nat := [1, 1, 1, 2, 3, 1, 2, 3, 1, 7]
def baseStart_2872243 : Nat := 118140960795 + 2872243 * 2 ^ 59
def prefixEnd_2872243 : Nat := 4983230072969 + 3 ^ 40 * 2872243 * 2
def baseEnd_2872243 : Nat := 983227477007940713168867

theorem tailTrace_2872243 : CollatzResearch.WordTrace tailWord_2872243 prefixEnd_2872243 983227477007940713168867 := by
  unfold tailWord_2872243
  simp only [CollatzResearch.WordTrace]
  refine ⟨104759308533361625895621383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69839539022241083930414255 104759308533361625895621383)
  ·
    refine ⟨157138962800042438843432075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104759308533361625895621383 157138962800042438843432075)
    ·
      refine ⟨235708444200063658265148113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157138962800042438843432075 235708444200063658265148113)
      ·
        refine ⟨176781333150047743698861085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 235708444200063658265148113 176781333150047743698861085)
        ·
          refine ⟨66292999931267903887072907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 176781333150047743698861085 66292999931267903887072907)
          ·
            refine ⟨99439499896901855830609361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66292999931267903887072907 99439499896901855830609361)
            ·
              refine ⟨74579624922676391872957021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99439499896901855830609361 74579624922676391872957021)
              ·
                refine ⟨27967359346003646952358883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74579624922676391872957021 27967359346003646952358883)
                ·
                  refine ⟨41951039019005470428538325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27967359346003646952358883 41951039019005470428538325)
                  ·
                    refine ⟨983227477007940713168867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41951039019005470428538325 983227477007940713168867)
                    ·
                      rfl

theorem cell22_2872243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 3, 1, 7].length) (baseStart_2872243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2872243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2872243 prefixEnd_2872243 := by exact prefixLift 2872243
  have htrace : WordTrace (prefixWord ++ tailWord_2872243) baseStart_2872243 baseEnd_2872243 := by
    simpa [prefixWord, tailWord_2872243, baseEnd_2872243] using wordTrace_append hprefix tailTrace_2872243
  have hstable : (prefixWord ++ tailWord_2872243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2872243).length < 2 ^ (prefixWord ++ tailWord_2872243).sum := by decide
  have hdescent : baseEnd_2872243 < baseStart_2872243 := by decide
  rcases family_descends (prefixWord ++ tailWord_2872243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2872341 : List Nat := [1, 3, 2, 1, 4, 3, 2, 2, 4]
def baseStart_2872341 : Nat := 118140960795 + 2872341 * 2 ^ 59
def prefixEnd_2872341 : Nat := 4983230072969 + 3 ^ 40 * 2872341 * 2
def baseEnd_2872341 : Nat := 327753674803567041406189

theorem tailTrace_2872341 : CollatzResearch.WordTrace tailWord_2872341 prefixEnd_2872341 327753674803567041406189 := by
  unfold tailWord_2872341
  simp only [CollatzResearch.WordTrace]
  refine ⟨104762882887006588632688877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69841921924671059088459251 104762882887006588632688877)
  ·
    refine ⟨39286081082627470737258329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104762882887006588632688877 39286081082627470737258329)
    ·
      refine ⟨29464560811970603052943747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39286081082627470737258329 29464560811970603052943747)
      ·
        refine ⟨44196841217955904579415621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29464560811970603052943747 44196841217955904579415621)
        ·
          refine ⟨8286907728366732108640429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44196841217955904579415621 8286907728366732108640429)
          ·
            refine ⟨3107590398137524540740161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8286907728366732108640429 3107590398137524540740161)
            ·
              refine ⟨2330692798603143405555121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3107590398137524540740161 2330692798603143405555121)
              ·
                refine ⟨1748019598952357554166341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2330692798603143405555121 1748019598952357554166341)
                ·
                  refine ⟨327753674803567041406189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1748019598952357554166341 327753674803567041406189)
                  ·
                    rfl

theorem cell22_2872341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 2, 2, 4].length) (baseStart_2872341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2872341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2872341 prefixEnd_2872341 := by exact prefixLift 2872341
  have htrace : WordTrace (prefixWord ++ tailWord_2872341) baseStart_2872341 baseEnd_2872341 := by
    simpa [prefixWord, tailWord_2872341, baseEnd_2872341] using wordTrace_append hprefix tailTrace_2872341
  have hstable : (prefixWord ++ tailWord_2872341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2872341).length < 2 ^ (prefixWord ++ tailWord_2872341).sum := by decide
  have hdescent : baseEnd_2872341 < baseStart_2872341 := by decide
  rcases family_descends (prefixWord ++ tailWord_2872341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2872410 : List Nat := [3, 1, 1, 2, 1, 1, 2, 1, 2, 8]
def baseStart_2872410 : Nat := 118140960795 + 2872410 * 2 ^ 59
def prefixEnd_2872410 : Nat := 4983230072969 + 3 ^ 40 * 2872410 * 2
def baseEnd_2872410 : Nat := 983284644520807944243355

theorem tailTrace_2872410 : CollatzResearch.WordTrace tailWord_2872410 prefixEnd_2872410 983284644520807944243355 := by
  unfold tailWord_2872410
  simp only [CollatzResearch.WordTrace]
  refine ⟨26191349880939153354237671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69843599682504408944633789 26191349880939153354237671)
  ·
    refine ⟨39287024821408730031356507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26191349880939153354237671 39287024821408730031356507)
    ·
      refine ⟨58930537232113095047034761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39287024821408730031356507 58930537232113095047034761)
      ·
        refine ⟨44197902924084821285276071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58930537232113095047034761 44197902924084821285276071)
        ·
          refine ⟨66296854386127231927914107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44197902924084821285276071 66296854386127231927914107)
          ·
            refine ⟨99445281579190847891871161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66296854386127231927914107 99445281579190847891871161)
            ·
              refine ⟨74583961184393135918903371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99445281579190847891871161 74583961184393135918903371)
              ·
                refine ⟨111875941776589703878355057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74583961184393135918903371 111875941776589703878355057)
                ·
                  refine ⟨83906956332442277908766293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 111875941776589703878355057 83906956332442277908766293)
                  ·
                    refine ⟨983284644520807944243355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 83906956332442277908766293 983284644520807944243355)
                    ·
                      rfl

theorem cell22_2872410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 2, 8].length) (baseStart_2872410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2872410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2872410 prefixEnd_2872410 := by exact prefixLift 2872410
  have htrace : WordTrace (prefixWord ++ tailWord_2872410) baseStart_2872410 baseEnd_2872410 := by
    simpa [prefixWord, tailWord_2872410, baseEnd_2872410] using wordTrace_append hprefix tailTrace_2872410
  have hstable : (prefixWord ++ tailWord_2872410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2872410).length < 2 ^ (prefixWord ++ tailWord_2872410).sum := by decide
  have hdescent : baseEnd_2872410 < baseStart_2872410 := by decide
  rcases family_descends (prefixWord ++ tailWord_2872410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2872412 : List Nat := [2, 2, 4, 1, 1, 1, 1, 3, 2, 5]
def baseStart_2872412 : Nat := 118140960795 + 2872412 * 2 ^ 59
def prefixEnd_2872412 : Nat := 4983230072969 + 3 ^ 40 * 2872412 * 2
def baseEnd_2872412 : Nat := 983285329161680605693349

theorem tailTrace_2872412 : CollatzResearch.WordTrace tailWord_2872412 prefixEnd_2872412 983285329161680605693349 := by
  unfold tailWord_2872412
  simp only [CollatzResearch.WordTrace]
  refine ⟨52382736234874683879261745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69843648313166245172348993 52382736234874683879261745)
  ·
    refine ⟨39287052176156012909446309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52382736234874683879261745 39287052176156012909446309)
    ·
      refine ⟨7366322283029252420521183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39287052176156012909446309 7366322283029252420521183)
      ·
        refine ⟨11049483424543878630781775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7366322283029252420521183 11049483424543878630781775)
        ·
          refine ⟨16574225136815817946172663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11049483424543878630781775 16574225136815817946172663)
          ·
            refine ⟨24861337705223726919258995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16574225136815817946172663 24861337705223726919258995)
            ·
              refine ⟨37292006557835590378888493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24861337705223726919258995 37292006557835590378888493)
              ·
                refine ⟨13984502459188346392083185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37292006557835590378888493 13984502459188346392083185)
                ·
                  refine ⟨10488376844391259794062389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13984502459188346392083185 10488376844391259794062389)
                  ·
                    refine ⟨983285329161680605693349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10488376844391259794062389 983285329161680605693349)
                    ·
                      rfl

theorem cell22_2872412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_2872412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2872412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2872412 prefixEnd_2872412 := by exact prefixLift 2872412
  have htrace : WordTrace (prefixWord ++ tailWord_2872412) baseStart_2872412 baseEnd_2872412 := by
    simpa [prefixWord, tailWord_2872412, baseEnd_2872412] using wordTrace_append hprefix tailTrace_2872412
  have hstable : (prefixWord ++ tailWord_2872412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2872412).length < 2 ^ (prefixWord ++ tailWord_2872412).sum := by decide
  have hdescent : baseEnd_2872412 < baseStart_2872412 := by decide
  rcases family_descends (prefixWord ++ tailWord_2872412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2872478 : List Nat := [4, 3, 1, 1, 2, 3, 1, 2, 1, 4]
def baseStart_2872478 : Nat := 118140960795 + 2872478 * 2 ^ 59
def prefixEnd_2872478 : Nat := 4983230072969 + 3 ^ 40 * 2872478 * 2
def baseEnd_2872478 : Nat := 983307922310478433543147

theorem tailTrace_2872478 : CollatzResearch.WordTrace tailWord_2872478 prefixEnd_2872478 983307922310478433543147 := by
  unfold tailWord_2872478
  simp only [CollatzResearch.WordTrace]
  refine ⟨13095984960938782628803261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69845253125006840686950725 13095984960938782628803261)
  ·
    refine ⟨4910994360352043485801223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13095984960938782628803261 4910994360352043485801223)
    ·
      refine ⟨7366491540528065228701835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4910994360352043485801223 7366491540528065228701835)
      ·
        refine ⟨11049737310792097843052753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7366491540528065228701835 11049737310792097843052753)
        ·
          refine ⟨8287302983094073382289565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11049737310792097843052753 8287302983094073382289565)
          ·
            refine ⟨3107738618660277518358587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8287302983094073382289565 3107738618660277518358587)
            ·
              refine ⟨4661607927990416277537881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3107738618660277518358587 4661607927990416277537881)
              ·
                refine ⟨3496205945992812208153411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4661607927990416277537881 3496205945992812208153411)
                ·
                  refine ⟨5244308918989218312230117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3496205945992812208153411 5244308918989218312230117)
                  ·
                    refine ⟨983307922310478433543147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5244308918989218312230117 983307922310478433543147)
                    ·
                      rfl

theorem cell22_2872478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 1, 2, 1, 4].length) (baseStart_2872478 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2872478 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2872478 prefixEnd_2872478 := by exact prefixLift 2872478
  have htrace : WordTrace (prefixWord ++ tailWord_2872478) baseStart_2872478 baseEnd_2872478 := by
    simpa [prefixWord, tailWord_2872478, baseEnd_2872478] using wordTrace_append hprefix tailTrace_2872478
  have hstable : (prefixWord ++ tailWord_2872478).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2872478).length < 2 ^ (prefixWord ++ tailWord_2872478).sum := by decide
  have hdescent : baseEnd_2872478 < baseStart_2872478 := by decide
  rcases family_descends (prefixWord ++ tailWord_2872478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2872536 : List Nat := [2, 1, 2, 2, 5, 1, 1, 2, 3, 3]
def baseStart_2872536 : Nat := 118140960795 + 2872536 * 2 ^ 59
def prefixEnd_2872536 : Nat := 4983230072969 + 3 ^ 40 * 2872536 * 2
def baseEnd_2872536 : Nat := 983327776895785615592969

theorem tailTrace_2872536 : CollatzResearch.WordTrace tailWord_2872536 prefixEnd_2872536 983327776895785615592969 := by
  unfold tailWord_2872536
  simp only [CollatzResearch.WordTrace]
  refine ⟨52384997560650068468018731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69846663414200091290691641 52384997560650068468018731)
  ·
    refine ⟨78577496340975102702028097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52384997560650068468018731 78577496340975102702028097)
    ·
      refine ⟨58933122255731327026521073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78577496340975102702028097 58933122255731327026521073)
      ·
        refine ⟨44199841691798495269890805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58933122255731327026521073 44199841691798495269890805)
        ·
          refine ⟨4143735158606108931552263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 44199841691798495269890805 4143735158606108931552263)
          ·
            refine ⟨6215602737909163397328395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4143735158606108931552263 6215602737909163397328395)
            ·
              refine ⟨9323404106863745095992593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6215602737909163397328395 9323404106863745095992593)
              ·
                refine ⟨6992553080147808821994445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9323404106863745095992593 6992553080147808821994445)
                ·
                  refine ⟨2622207405055428308247917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6992553080147808821994445 2622207405055428308247917)
                  ·
                    refine ⟨983327776895785615592969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2622207405055428308247917 983327776895785615592969)
                    ·
                      rfl

theorem cell22_2872536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 2, 3, 3].length) (baseStart_2872536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2872536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2872536 prefixEnd_2872536 := by exact prefixLift 2872536
  have htrace : WordTrace (prefixWord ++ tailWord_2872536) baseStart_2872536 baseEnd_2872536 := by
    simpa [prefixWord, tailWord_2872536, baseEnd_2872536] using wordTrace_append hprefix tailTrace_2872536
  have hstable : (prefixWord ++ tailWord_2872536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2872536).length < 2 ^ (prefixWord ++ tailWord_2872536).sum := by decide
  have hdescent : baseEnd_2872536 < baseStart_2872536 := by decide
  rcases family_descends (prefixWord ++ tailWord_2872536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2872611 : List Nat := [1, 1, 1, 4, 2, 3, 3, 3, 4]
def baseStart_2872611 : Nat := 118140960795 + 2872611 * 2 ^ 59
def prefixEnd_2872611 : Nat := 4983230072969 + 3 ^ 40 * 2872611 * 2
def baseEnd_2872611 : Nat := 327784483642836806655913

theorem tailTrace_2872611 : CollatzResearch.WordTrace tailWord_2872611 prefixEnd_2872611 327784483642836806655913 := by
  unfold tailWord_2872611
  simp only [CollatzResearch.WordTrace]
  refine ⟨104772730596028424745017687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69848487064018949830011791 104772730596028424745017687)
  ·
    refine ⟨157159095894042637117526531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104772730596028424745017687 157159095894042637117526531)
    ·
      refine ⟨235738643841063955676289797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157159095894042637117526531 235738643841063955676289797)
      ·
        refine ⟨44200995720199491689304337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 235738643841063955676289797 44200995720199491689304337)
        ·
          refine ⟨33150746790149618766978253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44200995720199491689304337 33150746790149618766978253)
          ·
            refine ⟨12431530046306107037616845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33150746790149618766978253 12431530046306107037616845)
            ·
              refine ⟨4661823767364790139106317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12431530046306107037616845 4661823767364790139106317)
              ·
                refine ⟨1748183912761796302164869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4661823767364790139106317 1748183912761796302164869)
                ·
                  refine ⟨327784483642836806655913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1748183912761796302164869 327784483642836806655913)
                  ·
                    rfl

theorem cell22_2872611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 3, 3, 4].length) (baseStart_2872611 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2872611 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2872611 prefixEnd_2872611 := by exact prefixLift 2872611
  have htrace : WordTrace (prefixWord ++ tailWord_2872611) baseStart_2872611 baseEnd_2872611 := by
    simpa [prefixWord, tailWord_2872611, baseEnd_2872611] using wordTrace_append hprefix tailTrace_2872611
  have hstable : (prefixWord ++ tailWord_2872611).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2872611).length < 2 ^ (prefixWord ++ tailWord_2872611).sum := by decide
  have hdescent : baseEnd_2872611 < baseStart_2872611 := by decide
  rcases family_descends (prefixWord ++ tailWord_2872611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2872624 : List Nat := [2, 1, 1, 1, 2, 2, 5, 2, 2, 4]
def baseStart_2872624 : Nat := 118140960795 + 2872624 * 2 ^ 59
def prefixEnd_2872624 : Nat := 4983230072969 + 3 ^ 40 * 2872624 * 2
def baseEnd_2872624 : Nat := 983357901094182719392699

theorem tailTrace_2872624 : CollatzResearch.WordTrace tailWord_2872624 prefixEnd_2872624 983357901094182719392699 := by
  unfold tailWord_2872624
  simp only [CollatzResearch.WordTrace]
  refine ⟨52386602372490663982620463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69848803163320885310160617 52386602372490663982620463)
  ·
    refine ⟨78579903558735995973930695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52386602372490663982620463 78579903558735995973930695)
    ·
      refine ⟨117869855338103993960896043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78579903558735995973930695 117869855338103993960896043)
      ·
        refine ⟨176804783007155990941344065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117869855338103993960896043 176804783007155990941344065)
        ·
          refine ⟨132603587255366993206008049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176804783007155990941344065 132603587255366993206008049)
          ·
            refine ⟨99452690441525244904506037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132603587255366993206008049 99452690441525244904506037)
            ·
              refine ⟨9323689728892991709797441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 99452690441525244904506037 9323689728892991709797441)
              ·
                refine ⟨6992767296669743782348081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9323689728892991709797441 6992767296669743782348081)
                ·
                  refine ⟨5244575472502307836761061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6992767296669743782348081 5244575472502307836761061)
                  ·
                    refine ⟨983357901094182719392699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5244575472502307836761061 983357901094182719392699)
                    ·
                      rfl

theorem cell22_2872624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 2, 2, 4].length) (baseStart_2872624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2872624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2872624 prefixEnd_2872624 := by exact prefixLift 2872624
  have htrace : WordTrace (prefixWord ++ tailWord_2872624) baseStart_2872624 baseEnd_2872624 := by
    simpa [prefixWord, tailWord_2872624, baseEnd_2872624] using wordTrace_append hprefix tailTrace_2872624
  have hstable : (prefixWord ++ tailWord_2872624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2872624).length < 2 ^ (prefixWord ++ tailWord_2872624).sum := by decide
  have hdescent : baseEnd_2872624 < baseStart_2872624 := by decide
  rcases family_descends (prefixWord ++ tailWord_2872624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2872626 : List Nat := [3, 2, 1, 1, 4, 1, 2, 1, 4, 3]
def baseStart_2872626 : Nat := 118140960795 + 2872626 * 2 ^ 59
def prefixEnd_2872626 : Nat := 4983230072969 + 3 ^ 40 * 2872626 * 2
def baseEnd_2872626 : Nat := 983358585735055380842693

theorem tailTrace_2872626 : CollatzResearch.WordTrace tailWord_2872626 prefixEnd_2872626 983358585735055380842693 := by
  unfold tailWord_2872626
  simp only [CollatzResearch.WordTrace]
  refine ⟨26193319422743520576703433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69848851793982721537875821 26193319422743520576703433)
  ·
    refine ⟨19644989567057640432527575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26193319422743520576703433 19644989567057640432527575)
    ·
      refine ⟨29467484350586460648791363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19644989567057640432527575 29467484350586460648791363)
      ·
        refine ⟨44201226525879690973187045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29467484350586460648791363 44201226525879690973187045)
        ·
          refine ⟨8287729973602442057472571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44201226525879690973187045 8287729973602442057472571)
          ·
            refine ⟨12431594960403663086208857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8287729973602442057472571 12431594960403663086208857)
            ·
              refine ⟨9323696220302747314656643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12431594960403663086208857 9323696220302747314656643)
              ·
                refine ⟨13985544330454120971984965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9323696220302747314656643 13985544330454120971984965)
                ·
                  refine ⟨2622289561960147682247181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13985544330454120971984965 2622289561960147682247181)
                  ·
                    refine ⟨983358585735055380842693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2622289561960147682247181 983358585735055380842693)
                    ·
                      rfl

theorem cell22_2872626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 1, 4, 3].length) (baseStart_2872626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2872626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2872626 prefixEnd_2872626 := by exact prefixLift 2872626
  have htrace : WordTrace (prefixWord ++ tailWord_2872626) baseStart_2872626 baseEnd_2872626 := by
    simpa [prefixWord, tailWord_2872626, baseEnd_2872626] using wordTrace_append hprefix tailTrace_2872626
  have hstable : (prefixWord ++ tailWord_2872626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2872626).length < 2 ^ (prefixWord ++ tailWord_2872626).sum := by decide
  have hdescent : baseEnd_2872626 < baseStart_2872626 := by decide
  rcases family_descends (prefixWord ++ tailWord_2872626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2872639 : List Nat := [1, 1, 2, 2, 4, 3, 2, 7]
def baseStart_2872639 : Nat := 118140960795 + 2872639 * 2 ^ 59
def prefixEnd_2872639 : Nat := 4983230072969 + 3 ^ 40 * 2872639 * 2
def baseEnd_2872639 : Nat := 109262559544525297807517

theorem tailTrace_2872639 : CollatzResearch.WordTrace tailWord_2872639 prefixEnd_2872639 109262559544525297807517 := by
  unfold tailWord_2872639
  simp only [CollatzResearch.WordTrace]
  refine ⟨104773751839926985527036971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69849167893284657018024647 104773751839926985527036971)
  ·
    refine ⟨157160627759890478290555457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104773751839926985527036971 157160627759890478290555457)
    ·
      refine ⟨117870470819917858717916593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157160627759890478290555457 117870470819917858717916593)
      ·
        refine ⟨88402853114938394038437445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117870470819917858717916593 88402853114938394038437445)
        ·
          refine ⟨16575534959050948882207021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 88402853114938394038437445 16575534959050948882207021)
          ·
            refine ⟨6215825609644105830827633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16575534959050948882207021 6215825609644105830827633)
            ·
              refine ⟨4661869207233079373120725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6215825609644105830827633 4661869207233079373120725)
              ·
                refine ⟨109262559544525297807517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4661869207233079373120725 109262559544525297807517)
                ·
                  rfl

theorem cell22_2872639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 2, 7].length) (baseStart_2872639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2872639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2872639 prefixEnd_2872639 := by exact prefixLift 2872639
  have htrace : WordTrace (prefixWord ++ tailWord_2872639) baseStart_2872639 baseEnd_2872639 := by
    simpa [prefixWord, tailWord_2872639, baseEnd_2872639] using wordTrace_append hprefix tailTrace_2872639
  have hstable : (prefixWord ++ tailWord_2872639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2872639).length < 2 ^ (prefixWord ++ tailWord_2872639).sum := by decide
  have hdescent : baseEnd_2872639 < baseStart_2872639 := by decide
  rcases family_descends (prefixWord ++ tailWord_2872639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2872688 : List Nat := [2, 1, 1, 1, 4, 2, 3, 4, 1, 3]
def baseStart_2872688 : Nat := 118140960795 + 2872688 * 2 ^ 59
def prefixEnd_2872688 : Nat := 4983230072969 + 3 ^ 40 * 2872688 * 2
def baseEnd_2872688 : Nat := 983379809602107885792503

theorem tailTrace_2872688 : CollatzResearch.WordTrace tailWord_2872688 prefixEnd_2872688 983379809602107885792503 := by
  unfold tailWord_2872688
  simp only [CollatzResearch.WordTrace]
  refine ⟨52387769508374733447785359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69850359344499644597047145 52387769508374733447785359)
  ·
    refine ⟨78581654262562100171678039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52387769508374733447785359 78581654262562100171678039)
    ·
      refine ⟨117872481393843150257517059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78581654262562100171678039 117872481393843150257517059)
      ·
        refine ⟨176808722090764725386275589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117872481393843150257517059 176808722090764725386275589)
        ·
          refine ⟨33151635392018386009926673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 176808722090764725386275589 33151635392018386009926673)
          ·
            refine ⟨24863726544013789507445005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33151635392018386009926673 24863726544013789507445005)
            ·
              refine ⟨9323897454005171065291877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24863726544013789507445005 9323897454005171065291877)
              ·
                refine ⟨1748230772625969574742227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9323897454005171065291877 1748230772625969574742227)
                ·
                  refine ⟨2622346158938954362113341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1748230772625969574742227 2622346158938954362113341)
                  ·
                    refine ⟨983379809602107885792503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2622346158938954362113341 983379809602107885792503)
                    ·
                      rfl

theorem cell22_2872688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 4, 1, 3].length) (baseStart_2872688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2872688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2872688 prefixEnd_2872688 := by exact prefixLift 2872688
  have htrace : WordTrace (prefixWord ++ tailWord_2872688) baseStart_2872688 baseEnd_2872688 := by
    simpa [prefixWord, tailWord_2872688, baseEnd_2872688] using wordTrace_append hprefix tailTrace_2872688
  have hstable : (prefixWord ++ tailWord_2872688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2872688).length < 2 ^ (prefixWord ++ tailWord_2872688).sum := by decide
  have hdescent : baseEnd_2872688 < baseStart_2872688 := by decide
  rcases family_descends (prefixWord ++ tailWord_2872688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2872699 : List Nat := [1, 1, 1, 1, 1, 6, 3, 1, 2, 5]
def baseStart_2872699 : Nat := 118140960795 + 2872699 * 2 ^ 59
def prefixEnd_2872699 : Nat := 4983230072969 + 3 ^ 40 * 2872699 * 2
def baseEnd_2872699 : Nat := 983383575126907523767469

theorem tailTrace_2872699 : CollatzResearch.WordTrace tailWord_2872699 prefixEnd_2872699 983383575126907523767469 := by
  unfold tailWord_2872699
  simp only [CollatzResearch.WordTrace]
  refine ⟨104775940219709615774221151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69850626813139743849480767 104775940219709615774221151)
  ·
    refine ⟨157163910329564423661331727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104775940219709615774221151 157163910329564423661331727)
    ·
      refine ⟨235745865494346635491997591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157163910329564423661331727 235745865494346635491997591)
      ·
        refine ⟨353618798241519953237996387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235745865494346635491997591 353618798241519953237996387)
        ·
          refine ⟨530428197362279929856994581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 353618798241519953237996387 530428197362279929856994581)
          ·
            refine ⟨24863821751356871712046621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 530428197362279929856994581 24863821751356871712046621)
            ·
              refine ⟨9323933156758826892017483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24863821751356871712046621 9323933156758826892017483)
              ·
                refine ⟨13985899735138240338026225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9323933156758826892017483 13985899735138240338026225)
                ·
                  refine ⟨10489424801353680253519669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13985899735138240338026225 10489424801353680253519669)
                  ·
                    refine ⟨983383575126907523767469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10489424801353680253519669 983383575126907523767469)
                    ·
                      rfl

theorem cell22_2872699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 1, 2, 5].length) (baseStart_2872699 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2872699 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2872699 prefixEnd_2872699 := by exact prefixLift 2872699
  have htrace : WordTrace (prefixWord ++ tailWord_2872699) baseStart_2872699 baseEnd_2872699 := by
    simpa [prefixWord, tailWord_2872699, baseEnd_2872699] using wordTrace_append hprefix tailTrace_2872699
  have hstable : (prefixWord ++ tailWord_2872699).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2872699).length < 2 ^ (prefixWord ++ tailWord_2872699).sum := by decide
  have hdescent : baseEnd_2872699 < baseStart_2872699 := by decide
  rcases family_descends (prefixWord ++ tailWord_2872699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2872759 : List Nat := [1, 1, 3, 1, 3, 2, 1, 1, 3, 6]
def baseStart_2872759 : Nat := 118140960795 + 2872759 * 2 ^ 59
def prefixEnd_2872759 : Nat := 4983230072969 + 3 ^ 40 * 2872759 * 2
def baseEnd_2872759 : Nat := 983404114353087367267285

theorem tailTrace_2872759 : CollatzResearch.WordTrace tailWord_2872759 prefixEnd_2872759 983404114353087367267285 := by
  unfold tailWord_2872759
  simp only [CollatzResearch.WordTrace]
  refine ⟨104778128599492246021405331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69852085732994830680936887 104778128599492246021405331)
  ·
    refine ⟨157167192899238369032107997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104778128599492246021405331 157167192899238369032107997)
    ·
      refine ⟨58937697337214388387040499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157167192899238369032107997 58937697337214388387040499)
      ·
        refine ⟨88406546005821582580560749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58937697337214388387040499 88406546005821582580560749)
        ·
          refine ⟨33152454752183093467710281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88406546005821582580560749 33152454752183093467710281)
          ·
            refine ⟨24864341064137320100782711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33152454752183093467710281 24864341064137320100782711)
            ·
              refine ⟨37296511596205980151174067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24864341064137320100782711 37296511596205980151174067)
              ·
                refine ⟨55944767394308970226761101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37296511596205980151174067 55944767394308970226761101)
                ·
                  refine ⟨20979287772865863835035413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55944767394308970226761101 20979287772865863835035413)
                  ·
                    refine ⟨983404114353087367267285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20979287772865863835035413 983404114353087367267285)
                    ·
                      rfl

theorem cell22_2872759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 3, 6].length) (baseStart_2872759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2872759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2872759 prefixEnd_2872759 := by exact prefixLift 2872759
  have htrace : WordTrace (prefixWord ++ tailWord_2872759) baseStart_2872759 baseEnd_2872759 := by
    simpa [prefixWord, tailWord_2872759, baseEnd_2872759] using wordTrace_append hprefix tailTrace_2872759
  have hstable : (prefixWord ++ tailWord_2872759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2872759).length < 2 ^ (prefixWord ++ tailWord_2872759).sum := by decide
  have hdescent : baseEnd_2872759 < baseStart_2872759 := by decide
  rcases family_descends (prefixWord ++ tailWord_2872759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2872776 : List Nat := [2, 1, 3, 1, 3, 1, 2, 3, 2, 4]
def baseStart_2872776 : Nat := 118140960795 + 2872776 * 2 ^ 59
def prefixEnd_2872776 : Nat := 4983230072969 + 3 ^ 40 * 2872776 * 2
def baseEnd_2872776 : Nat := 983409933800504989592233

theorem tailTrace_2872776 : CollatzResearch.WordTrace tailWord_2872776 prefixEnd_2872776 983409933800504989592233 := by
  unfold tailWord_2872776
  simp only [CollatzResearch.WordTrace]
  refine ⟨52389374320215328962387091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69852499093620438616516121 52389374320215328962387091)
  ·
    refine ⟨78584061480322993443580637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52389374320215328962387091 78584061480322993443580637)
    ·
      refine ⟨29469023055121122541342739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78584061480322993443580637 29469023055121122541342739)
      ·
        refine ⟨44203534582681683812014109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29469023055121122541342739 44203534582681683812014109)
        ·
          refine ⟨16576325468505631429505291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44203534582681683812014109 16576325468505631429505291)
          ·
            refine ⟨24864488202758447144257937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16576325468505631429505291 24864488202758447144257937)
            ·
              refine ⟨18648366152068835358193453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24864488202758447144257937 18648366152068835358193453)
              ·
                refine ⟨6993137307025813259322545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18648366152068835358193453 6993137307025813259322545)
                ·
                  refine ⟨5244852980269359944491909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6993137307025813259322545 5244852980269359944491909)
                  ·
                    refine ⟨983409933800504989592233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5244852980269359944491909 983409933800504989592233)
                    ·
                      rfl

theorem cell22_2872776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 3, 2, 4].length) (baseStart_2872776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2872776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2872776 prefixEnd_2872776 := by exact prefixLift 2872776
  have htrace : WordTrace (prefixWord ++ tailWord_2872776) baseStart_2872776 baseEnd_2872776 := by
    simpa [prefixWord, tailWord_2872776, baseEnd_2872776] using wordTrace_append hprefix tailTrace_2872776
  have hstable : (prefixWord ++ tailWord_2872776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2872776).length < 2 ^ (prefixWord ++ tailWord_2872776).sum := by decide
  have hdescent : baseEnd_2872776 < baseStart_2872776 := by decide
  rcases family_descends (prefixWord ++ tailWord_2872776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2872780 : List Nat := [2, 2, 1, 4, 2, 3, 1, 3, 4]
def baseStart_2872780 : Nat := 118140960795 + 2872780 * 2 ^ 59
def prefixEnd_2872780 : Nat := 4983230072969 + 3 ^ 40 * 2872780 * 2
def baseEnd_2872780 : Nat := 327803767694083437497407

theorem tailTrace_2872780 : CollatzResearch.WordTrace tailWord_2872780 prefixEnd_2872780 327803767694083437497407 := by
  unfold tailWord_2872780
  simp only [CollatzResearch.WordTrace]
  refine ⟨52389447266208083303959897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69852596354944111071946529 52389447266208083303959897)
  ·
    refine ⟨39292085449656062477969923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52389447266208083303959897 39292085449656062477969923)
    ·
      refine ⟨58938128174484093716954885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39292085449656062477969923 58938128174484093716954885)
      ·
        refine ⟨11050899032715767571929041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58938128174484093716954885 11050899032715767571929041)
        ·
          refine ⟨8288174274536825678946781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11050899032715767571929041 8288174274536825678946781)
          ·
            refine ⟨3108065352951309629605043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8288174274536825678946781 3108065352951309629605043)
            ·
              refine ⟨4662098029426964444407565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3108065352951309629605043 4662098029426964444407565)
              ·
                refine ⟨1748286761035111666652837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4662098029426964444407565 1748286761035111666652837)
                ·
                  refine ⟨327803767694083437497407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1748286761035111666652837 327803767694083437497407)
                  ·
                    rfl

theorem cell22_2872780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 1, 3, 4].length) (baseStart_2872780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2872780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2872780 prefixEnd_2872780 := by exact prefixLift 2872780
  have htrace : WordTrace (prefixWord ++ tailWord_2872780) baseStart_2872780 baseEnd_2872780 := by
    simpa [prefixWord, tailWord_2872780, baseEnd_2872780] using wordTrace_append hprefix tailTrace_2872780
  have hstable : (prefixWord ++ tailWord_2872780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2872780).length < 2 ^ (prefixWord ++ tailWord_2872780).sum := by decide
  have hdescent : baseEnd_2872780 < baseStart_2872780 := by decide
  rcases family_descends (prefixWord ++ tailWord_2872780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2872819 : List Nat := [1, 1, 1, 2, 2, 2, 2, 2, 9]
def baseStart_2872819 : Nat := 118140960795 + 2872819 * 2 ^ 59
def prefixEnd_2872819 : Nat := 4983230072969 + 3 ^ 40 * 2872819 * 2
def baseEnd_2872819 : Nat := 327808217859755736922367

theorem tailTrace_2872819 : CollatzResearch.WordTrace tailWord_2872819 prefixEnd_2872819 327808217859755736922367 := by
  unfold tailWord_2872819
  simp only [CollatzResearch.WordTrace]
  refine ⟨104780316979274876268589511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69853544652849917512393007 104780316979274876268589511)
  ·
    refine ⟨157170475468912314402884267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104780316979274876268589511 157170475468912314402884267)
    ·
      refine ⟨235755713203368471604326401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157170475468912314402884267 235755713203368471604326401)
      ·
        refine ⟨176816784902526353703244801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 235755713203368471604326401 176816784902526353703244801)
        ·
          refine ⟨132612588676894765277433601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176816784902526353703244801 132612588676894765277433601)
          ·
            refine ⟨99459441507671073958075201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132612588676894765277433601 99459441507671073958075201)
            ·
              refine ⟨74594581130753305468556401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99459441507671073958075201 74594581130753305468556401)
              ·
                refine ⟨55945935848064979101417301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74594581130753305468556401 55945935848064979101417301)
                ·
                  refine ⟨327808217859755736922367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 55945935848064979101417301 327808217859755736922367)
                  ·
                    rfl

theorem cell22_2872819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 9].length) (baseStart_2872819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2872819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2872819 prefixEnd_2872819 := by exact prefixLift 2872819
  have htrace : WordTrace (prefixWord ++ tailWord_2872819) baseStart_2872819 baseEnd_2872819 := by
    simpa [prefixWord, tailWord_2872819, baseEnd_2872819] using wordTrace_append hprefix tailTrace_2872819
  have hstable : (prefixWord ++ tailWord_2872819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2872819).length < 2 ^ (prefixWord ++ tailWord_2872819).sum := by decide
  have hdescent : baseEnd_2872819 < baseStart_2872819 := by decide
  rcases family_descends (prefixWord ++ tailWord_2872819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2872853 : List Nat := [1, 3, 2, 1, 3, 3, 2, 2, 5]
def baseStart_2872853 : Nat := 118140960795 + 2872853 * 2 ^ 59
def prefixEnd_2872853 : Nat := 4983230072969 + 3 ^ 40 * 2872853 * 2
def baseEnd_2872853 : Nat := 327812097491367485138999

theorem tailTrace_2872853 : CollatzResearch.WordTrace tailWord_2872853 prefixEnd_2872853 327812097491367485138999 := by
  unfold tailWord_2872853
  simp only [CollatzResearch.WordTrace]
  refine ⟨104781557061151700075327213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69854371374101133383551475 104781557061151700075327213)
  ·
    refine ⟨39293083897931887528247705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104781557061151700075327213 39293083897931887528247705)
    ·
      refine ⟨29469812923448915646185779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39293083897931887528247705 29469812923448915646185779)
      ·
        refine ⟨44204719385173373469278669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29469812923448915646185779 44204719385173373469278669)
        ·
          refine ⟨16576769769440015050979501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44204719385173373469278669 16576769769440015050979501)
          ·
            refine ⟨6216288663540005644117313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16576769769440015050979501 6216288663540005644117313)
            ·
              refine ⟨4662216497655004233087985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6216288663540005644117313 4662216497655004233087985)
              ·
                refine ⟨3496662373241253174815989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4662216497655004233087985 3496662373241253174815989)
                ·
                  refine ⟨327812097491367485138999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3496662373241253174815989 327812097491367485138999)
                  ·
                    rfl

theorem cell22_2872853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 2, 2, 5].length) (baseStart_2872853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2872853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2872853 prefixEnd_2872853 := by exact prefixLift 2872853
  have htrace : WordTrace (prefixWord ++ tailWord_2872853) baseStart_2872853 baseEnd_2872853 := by
    simpa [prefixWord, tailWord_2872853, baseEnd_2872853] using wordTrace_append hprefix tailTrace_2872853
  have hstable : (prefixWord ++ tailWord_2872853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2872853).length < 2 ^ (prefixWord ++ tailWord_2872853).sum := by decide
  have hdescent : baseEnd_2872853 < baseStart_2872853 := by decide
  rcases family_descends (prefixWord ++ tailWord_2872853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2872911 : List Nat := [1, 1, 2, 1, 1, 2, 3, 3, 4, 4]
def baseStart_2872911 : Nat := 118140960795 + 2872911 * 2 ^ 59
def prefixEnd_2872911 : Nat := 4983230072969 + 3 ^ 40 * 2872911 * 2
def baseEnd_2872911 : Nat := 983456147059409637466819

theorem tailTrace_2872911 : CollatzResearch.WordTrace tailWord_2872911 prefixEnd_2872911 983456147059409637466819 := by
  unfold tailWord_2872911
  simp only [CollatzResearch.WordTrace]
  refine ⟨104783672494941575980938587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69855781663294383987292391 104783672494941575980938587)
  ·
    refine ⟨157175508742412363971407881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104783672494941575980938587 157175508742412363971407881)
    ·
      refine ⟨117881631556809272978555911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157175508742412363971407881 117881631556809272978555911)
      ·
        refine ⟨176822447335213909467833867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117881631556809272978555911 176822447335213909467833867)
        ·
          refine ⟨265233671002820864201750801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176822447335213909467833867 265233671002820864201750801)
          ·
            refine ⟨198925253252115648151313101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 265233671002820864201750801 198925253252115648151313101)
            ·
              refine ⟨74596969969543368056742413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 198925253252115648151313101 74596969969543368056742413)
              ·
                refine ⟨27973863738578763021278405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74596969969543368056742413 27973863738578763021278405)
                ·
                  refine ⟨5245099450983518066489701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27973863738578763021278405 5245099450983518066489701)
                  ·
                    refine ⟨983456147059409637466819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5245099450983518066489701 983456147059409637466819)
                    ·
                      rfl

theorem cell22_2872911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 3, 4, 4].length) (baseStart_2872911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2872911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2872911 prefixEnd_2872911 := by exact prefixLift 2872911
  have htrace : WordTrace (prefixWord ++ tailWord_2872911) baseStart_2872911 baseEnd_2872911 := by
    simpa [prefixWord, tailWord_2872911, baseEnd_2872911] using wordTrace_append hprefix tailTrace_2872911
  have hstable : (prefixWord ++ tailWord_2872911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2872911).length < 2 ^ (prefixWord ++ tailWord_2872911).sum := by decide
  have hdescent : baseEnd_2872911 < baseStart_2872911 := by decide
  rcases family_descends (prefixWord ++ tailWord_2872911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2872913 : List Nat := [1, 2, 2, 1, 3, 2, 3, 1, 4, 3]
def baseStart_2872913 : Nat := 118140960795 + 2872913 * 2 ^ 59
def prefixEnd_2872913 : Nat := 4983230072969 + 3 ^ 40 * 2872913 * 2
def baseEnd_2872913 : Nat := 983456831700282298916813

theorem tailTrace_2872913 : CollatzResearch.WordTrace tailWord_2872913 prefixEnd_2872913 983456831700282298916813 := by
  unfold tailWord_2872913
  simp only [CollatzResearch.WordTrace]
  refine ⟨104783745440934330322511393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69855830293956220215007595 104783745440934330322511393)
  ·
    refine ⟨78587809080700747741883545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104783745440934330322511393 78587809080700747741883545)
    ·
      refine ⟨58940856810525560806412659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78587809080700747741883545 58940856810525560806412659)
      ·
        refine ⟨88411285215788341209618989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58940856810525560806412659 88411285215788341209618989)
        ·
          refine ⟨33154231955920627953607121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88411285215788341209618989 33154231955920627953607121)
          ·
            refine ⟨24865673966940470965205341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33154231955920627953607121 24865673966940470965205341)
            ·
              refine ⟨9324627737602676611952003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24865673966940470965205341 9324627737602676611952003)
              ·
                refine ⟨13986941606404014917928005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9324627737602676611952003 13986941606404014917928005)
                ·
                  refine ⟨2622551551200752797111501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13986941606404014917928005 2622551551200752797111501)
                  ·
                    refine ⟨983456831700282298916813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2622551551200752797111501 983456831700282298916813)
                    ·
                      rfl

theorem cell22_2872913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 1, 4, 3].length) (baseStart_2872913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2872913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2872913 prefixEnd_2872913 := by exact prefixLift 2872913
  have htrace : WordTrace (prefixWord ++ tailWord_2872913) baseStart_2872913 baseEnd_2872913 := by
    simpa [prefixWord, tailWord_2872913, baseEnd_2872913] using wordTrace_append hprefix tailTrace_2872913
  have hstable : (prefixWord ++ tailWord_2872913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2872913).length < 2 ^ (prefixWord ++ tailWord_2872913).sum := by decide
  have hdescent : baseEnd_2872913 < baseStart_2872913 := by decide
  rcases family_descends (prefixWord ++ tailWord_2872913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2872956 : List Nat := [2, 2, 2, 1, 1, 2, 1, 2, 1, 8]
def baseStart_2872956 : Nat := 118140960795 + 2872956 * 2 ^ 59
def prefixEnd_2872956 : Nat := 4983230072969 + 3 ^ 40 * 2872956 * 2
def baseEnd_2872956 : Nat := 983471551479044520091681

theorem tailTrace_2872956 : CollatzResearch.WordTrace tailWord_2872956 prefixEnd_2872956 983471551479044520091681 := by
  unfold tailWord_2872956
  simp only [CollatzResearch.WordTrace]
  refine ⟨52392656889889274333163361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69856875853185699110884481 52392656889889274333163361)
  ·
    refine ⟨39294492667416955749872521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52392656889889274333163361 39294492667416955749872521)
    ·
      refine ⟨29470869500562716812404391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39294492667416955749872521 29470869500562716812404391)
      ·
        refine ⟨44206304250844075218606587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29470869500562716812404391 44206304250844075218606587)
        ·
          refine ⟨66309456376266112827909881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44206304250844075218606587 66309456376266112827909881)
          ·
            refine ⟨49732092282199584620932411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66309456376266112827909881 49732092282199584620932411)
            ·
              refine ⟨74598138423299376931398617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49732092282199584620932411 74598138423299376931398617)
              ·
                refine ⟨55948603817474532698548963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74598138423299376931398617 55948603817474532698548963)
                ·
                  refine ⟨83922905726211799047823445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55948603817474532698548963 83922905726211799047823445)
                  ·
                    refine ⟨983471551479044520091681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 83922905726211799047823445 983471551479044520091681)
                    ·
                      rfl

theorem cell22_2872956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 1, 8].length) (baseStart_2872956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2872956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2872956 prefixEnd_2872956 := by exact prefixLift 2872956
  have htrace : WordTrace (prefixWord ++ tailWord_2872956) baseStart_2872956 baseEnd_2872956 := by
    simpa [prefixWord, tailWord_2872956, baseEnd_2872956] using wordTrace_append hprefix tailTrace_2872956
  have hstable : (prefixWord ++ tailWord_2872956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2872956).length < 2 ^ (prefixWord ++ tailWord_2872956).sum := by decide
  have hdescent : baseEnd_2872956 < baseStart_2872956 := by decide
  rcases family_descends (prefixWord ++ tailWord_2872956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2872971 : List Nat := [1, 1, 1, 1, 4, 1, 3, 3, 7]
def baseStart_2872971 : Nat := 118140960795 + 2872971 * 2 ^ 59
def prefixEnd_2872971 : Nat := 4983230072969 + 3 ^ 40 * 2872971 * 2
def baseEnd_2872971 : Nat := 327825562095196493655545

theorem tailTrace_2872971 : CollatzResearch.WordTrace tailWord_2872971 prefixEnd_2872971 327825562095196493655545 := by
  unfold tailWord_2872971
  simp only [CollatzResearch.WordTrace]
  refine ⟨104785860874724206228122767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69857240583149470818748511 104785860874724206228122767)
  ·
    refine ⟨157178791312086309342184151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104785860874724206228122767 157178791312086309342184151)
    ·
      refine ⟨235768186968129464013276227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157178791312086309342184151 235768186968129464013276227)
      ·
        refine ⟨353652280452194196019914341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235768186968129464013276227 353652280452194196019914341)
        ·
          refine ⟨66309802584786411753733939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 353652280452194196019914341 66309802584786411753733939)
          ·
            refine ⟨99464703877179617630600909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66309802584786411753733939 99464703877179617630600909)
            ·
              refine ⟨37299263953942356611475341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99464703877179617630600909 37299263953942356611475341)
              ·
                refine ⟨13987223982728383729303253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37299263953942356611475341 13987223982728383729303253)
                ·
                  refine ⟨327825562095196493655545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13987223982728383729303253 327825562095196493655545)
                  ·
                    rfl

theorem cell22_2872971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 3, 7].length) (baseStart_2872971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2872971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2872971 prefixEnd_2872971 := by exact prefixLift 2872971
  have htrace : WordTrace (prefixWord ++ tailWord_2872971) baseStart_2872971 baseEnd_2872971 := by
    simpa [prefixWord, tailWord_2872971, baseEnd_2872971] using wordTrace_append hprefix tailTrace_2872971
  have hstable : (prefixWord ++ tailWord_2872971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2872971).length < 2 ^ (prefixWord ++ tailWord_2872971).sum := by decide
  have hdescent : baseEnd_2872971 < baseStart_2872971 := by decide
  rcases family_descends (prefixWord ++ tailWord_2872971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2873037 : List Nat := [1, 6, 2, 1, 1, 2, 1, 1, 2, 5]
def baseStart_2873037 : Nat := 118140960795 + 2873037 * 2 ^ 59
def prefixEnd_2873037 : Nat := 4983230072969 + 3 ^ 40 * 2873037 * 2
def baseEnd_2873037 : Nat := 983499279434387308816433

theorem tailTrace_2873037 : CollatzResearch.WordTrace tailWord_2873037 prefixEnd_2873037 983499279434387308816433 := by
  unfold tailWord_2873037
  simp only [CollatzResearch.WordTrace]
  refine ⟨104788268092485099500025365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69858845394990066333350243 104788268092485099500025365)
  ·
    refine ⟨4911950066835239039063689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 104788268092485099500025365 4911950066835239039063689)
    ·
      refine ⟨3683962550126429279297767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4911950066835239039063689 3683962550126429279297767)
      ·
        refine ⟨5525943825189643918946651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3683962550126429279297767 5525943825189643918946651)
        ·
          refine ⟨8288915737784465878419977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5525943825189643918946651 8288915737784465878419977)
          ·
            refine ⟨6216686803338349408814983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8288915737784465878419977 6216686803338349408814983)
            ·
              refine ⟨9325030205007524113222475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6216686803338349408814983 9325030205007524113222475)
              ·
                refine ⟨13987545307511286169833713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9325030205007524113222475 13987545307511286169833713)
                ·
                  refine ⟨10490658980633464627375285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13987545307511286169833713 10490658980633464627375285)
                  ·
                    refine ⟨983499279434387308816433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10490658980633464627375285 983499279434387308816433)
                    ·
                      rfl

theorem cell22_2873037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_2873037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2873037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2873037 prefixEnd_2873037 := by exact prefixLift 2873037
  have htrace : WordTrace (prefixWord ++ tailWord_2873037) baseStart_2873037 baseEnd_2873037 := by
    simpa [prefixWord, tailWord_2873037, baseEnd_2873037] using wordTrace_append hprefix tailTrace_2873037
  have hstable : (prefixWord ++ tailWord_2873037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2873037).length < 2 ^ (prefixWord ++ tailWord_2873037).sum := by decide
  have hdescent : baseEnd_2873037 < baseStart_2873037 := by decide
  rcases family_descends (prefixWord ++ tailWord_2873037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2873069 : List Nat := [1, 5, 1, 2, 1, 4, 2, 1, 1, 4]
def baseStart_2873069 : Nat := 118140960795 + 2873069 * 2 ^ 59
def prefixEnd_2873069 : Nat := 4983230072969 + 3 ^ 40 * 2873069 * 2
def baseEnd_2873069 : Nat := 983510233688349892016335

theorem tailTrace_2873069 : CollatzResearch.WordTrace tailWord_2873069 prefixEnd_2873069 983510233688349892016335 := by
  unfold tailWord_2873069
  simp only [CollatzResearch.WordTrace]
  refine ⟨104789435228369168965190261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69859623485579445976793507 104789435228369168965190261)
  ·
    refine ⟨9824009552659609590486587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 104789435228369168965190261 9824009552659609590486587)
    ·
      refine ⟨14736014328989414385729881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9824009552659609590486587 14736014328989414385729881)
      ·
        refine ⟨11052010746742060789297411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14736014328989414385729881 11052010746742060789297411)
        ·
          refine ⟨16578016120113091183946117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11052010746742060789297411 16578016120113091183946117)
          ·
            refine ⟨3108378022521204596989897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16578016120113091183946117 3108378022521204596989897)
            ·
              refine ⟨2331283516890903447742423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3108378022521204596989897 2331283516890903447742423)
              ·
                refine ⟨3496925275336355171613635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2331283516890903447742423 3496925275336355171613635)
                ·
                  refine ⟨5245387913004532757420453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3496925275336355171613635 5245387913004532757420453)
                  ·
                    refine ⟨983510233688349892016335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5245387913004532757420453 983510233688349892016335)
                    ·
                      rfl

theorem cell22_2873069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 2, 1, 1, 4].length) (baseStart_2873069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2873069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2873069 prefixEnd_2873069 := by exact prefixLift 2873069
  have htrace : WordTrace (prefixWord ++ tailWord_2873069) baseStart_2873069 baseEnd_2873069 := by
    simpa [prefixWord, tailWord_2873069, baseEnd_2873069] using wordTrace_append hprefix tailTrace_2873069
  have hstable : (prefixWord ++ tailWord_2873069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2873069).length < 2 ^ (prefixWord ++ tailWord_2873069).sum := by decide
  have hdescent : baseEnd_2873069 < baseStart_2873069 := by decide
  rcases family_descends (prefixWord ++ tailWord_2873069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2873118 : List Nat := [4, 3, 2, 2, 1, 2, 1, 3, 4]
def baseStart_2873118 : Nat := 118140960795 + 2873118 * 2 ^ 59
def prefixEnd_2873118 : Nat := 4983230072969 + 3 ^ 40 * 2873118 * 2
def baseEnd_2873118 : Nat := 327842335796576699180395

theorem tailTrace_2873118 : CollatzResearch.WordTrace tailWord_2873118 prefixEnd_2873118 327842335796576699180395 := by
  unfold tailWord_2873118
  simp only [CollatzResearch.WordTrace]
  refine ⟨13098902800648956291715501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69860814936794433555816005 13098902800648956291715501)
  ·
    refine ⟨4912088550243358609393313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13098902800648956291715501 4912088550243358609393313)
    ·
      refine ⟨3684066412682518957044985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4912088550243358609393313 3684066412682518957044985)
      ·
        refine ⟨2763049809511889217783739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3684066412682518957044985 2763049809511889217783739)
        ·
          refine ⟨4144574714267833826675609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2763049809511889217783739 4144574714267833826675609)
          ·
            refine ⟨3108431035700875370006707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4144574714267833826675609 3108431035700875370006707)
            ·
              refine ⟨4662646553551313055010061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3108431035700875370006707 4662646553551313055010061)
              ·
                refine ⟨1748492457581742395628773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4662646553551313055010061 1748492457581742395628773)
                ·
                  refine ⟨327842335796576699180395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1748492457581742395628773 327842335796576699180395)
                  ·
                    rfl

theorem cell22_2873118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 1, 3, 4].length) (baseStart_2873118 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2873118 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2873118 prefixEnd_2873118 := by exact prefixLift 2873118
  have htrace : WordTrace (prefixWord ++ tailWord_2873118) baseStart_2873118 baseEnd_2873118 := by
    simpa [prefixWord, tailWord_2873118, baseEnd_2873118] using wordTrace_append hprefix tailTrace_2873118
  have hstable : (prefixWord ++ tailWord_2873118).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2873118).length < 2 ^ (prefixWord ++ tailWord_2873118).sum := by decide
  have hdescent : baseEnd_2873118 < baseStart_2873118 := by decide
  rcases family_descends (prefixWord ++ tailWord_2873118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2873123 : List Nat := [1, 1, 1, 4, 2, 1, 3, 2, 7]
def baseStart_2873123 : Nat := 118140960795 + 2873123 * 2 ^ 59
def prefixEnd_2873123 : Nat := 4983230072969 + 3 ^ 40 * 2873123 * 2
def baseEnd_2873123 : Nat := 327842906330637250388723

theorem tailTrace_2873123 : CollatzResearch.WordTrace tailWord_2873123 prefixEnd_2873123 327842906330637250388723 := by
  unfold tailWord_2873123
  simp only [CollatzResearch.WordTrace]
  refine ⟨104791404770173536187656023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69860936513449024125104015 104791404770173536187656023)
  ·
    refine ⟨157187107155260304281484035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104791404770173536187656023 157187107155260304281484035)
    ·
      refine ⟨235780660732890456422226053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157187107155260304281484035 235780660732890456422226053)
      ·
        refine ⟨44208873887416960579167385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 235780660732890456422226053 44208873887416960579167385)
        ·
          refine ⟨33156655415562720434375539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44208873887416960579167385 33156655415562720434375539)
          ·
            refine ⟨49734983123344080651563309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33156655415562720434375539 49734983123344080651563309)
            ·
              refine ⟨18650618671254030244336241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49734983123344080651563309 18650618671254030244336241)
              ·
                refine ⟨13987964003440522683252181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18650618671254030244336241 13987964003440522683252181)
                ·
                  refine ⟨327842906330637250388723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13987964003440522683252181 327842906330637250388723)
                  ·
                    rfl

theorem cell22_2873123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 2, 7].length) (baseStart_2873123 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2873123 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2873123 prefixEnd_2873123 := by exact prefixLift 2873123
  have htrace : WordTrace (prefixWord ++ tailWord_2873123) baseStart_2873123 baseEnd_2873123 := by
    simpa [prefixWord, tailWord_2873123, baseEnd_2873123] using wordTrace_append hprefix tailTrace_2873123
  have hstable : (prefixWord ++ tailWord_2873123).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2873123).length < 2 ^ (prefixWord ++ tailWord_2873123).sum := by decide
  have hdescent : baseEnd_2873123 < baseStart_2873123 := by decide
  rcases family_descends (prefixWord ++ tailWord_2873123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2873168 : List Nat := [2, 1, 1, 1, 1, 4, 1, 3, 8]
def baseStart_2873168 : Nat := 118140960795 + 2873168 * 2 ^ 59
def prefixEnd_2873168 : Nat := 4983230072969 + 3 ^ 40 * 2873168 * 2
def baseEnd_2873168 : Nat := 327848041137182211263677

theorem tailTrace_2873168 : CollatzResearch.WordTrace tailWord_2873168 prefixEnd_2873168 327848041137182211263677 := by
  unfold tailWord_2873168
  simp only [CollatzResearch.WordTrace]
  refine ⟨52396523027505254436522079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69862030703340339248696105 52396523027505254436522079)
  ·
    refine ⟨78594784541257881654783119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52396523027505254436522079 78594784541257881654783119)
    ·
      refine ⟨117892176811886822482174679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78594784541257881654783119 117892176811886822482174679)
      ·
        refine ⟨176838265217830233723262019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117892176811886822482174679 176838265217830233723262019)
        ·
          refine ⟨265257397826745350584893029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176838265217830233723262019 265257397826745350584893029)
          ·
            refine ⟨49735762092514753234667443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 265257397826745350584893029 49735762092514753234667443)
            ·
              refine ⟨74603643138772129852001165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49735762092514753234667443 74603643138772129852001165)
              ·
                refine ⟨27976366177039548694500437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74603643138772129852001165 27976366177039548694500437)
                ·
                  refine ⟨327848041137182211263677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27976366177039548694500437 327848041137182211263677)
                  ·
                    rfl

theorem cell22_2873168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 3, 8].length) (baseStart_2873168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2873168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2873168 prefixEnd_2873168 := by exact prefixLift 2873168
  have htrace : WordTrace (prefixWord ++ tailWord_2873168) baseStart_2873168 baseEnd_2873168 := by
    simpa [prefixWord, tailWord_2873168, baseEnd_2873168] using wordTrace_append hprefix tailTrace_2873168
  have hstable : (prefixWord ++ tailWord_2873168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2873168).length < 2 ^ (prefixWord ++ tailWord_2873168).sum := by decide
  have hdescent : baseEnd_2873168 < baseStart_2873168 := by decide
  rcases family_descends (prefixWord ++ tailWord_2873168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2873238 : List Nat := [5, 3, 1, 1, 2, 1, 1, 3, 1, 4]
def baseStart_2873238 : Nat := 118140960795 + 2873238 * 2 ^ 59
def prefixEnd_2873238 : Nat := 4983230072969 + 3 ^ 40 * 2873238 * 2
def baseEnd_2873238 : Nat := 983568085842089784540817

theorem tailTrace_2873238 : CollatzResearch.WordTrace tailWord_2873238 prefixEnd_2873238 983568085842089784540817 := by
  unfold tailWord_2873238
  simp only [CollatzResearch.WordTrace]
  refine ⟨6549724947797306926755773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 69863732776504607218728245 6549724947797306926755773)
  ·
    refine ⟨2456146855423990097533415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6549724947797306926755773 2456146855423990097533415)
    ·
      refine ⟨3684220283135985146300123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2456146855423990097533415 3684220283135985146300123)
      ·
        refine ⟨5526330424703977719450185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3684220283135985146300123 5526330424703977719450185)
        ·
          refine ⟨4144747818527983289587639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5526330424703977719450185 4144747818527983289587639)
          ·
            refine ⟨6217121727791974934381459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4144747818527983289587639 6217121727791974934381459)
            ·
              refine ⟨9325682591687962401572189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6217121727791974934381459 9325682591687962401572189)
              ·
                refine ⟨3497130971882985900589571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9325682591687962401572189 3497130971882985900589571)
                ·
                  refine ⟨5245696457824478850884357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3497130971882985900589571 5245696457824478850884357)
                  ·
                    refine ⟨983568085842089784540817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5245696457824478850884357 983568085842089784540817)
                    ·
                      rfl

theorem cell22_2873238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_2873238 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2873238 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2873238 prefixEnd_2873238 := by exact prefixLift 2873238
  have htrace : WordTrace (prefixWord ++ tailWord_2873238) baseStart_2873238 baseEnd_2873238 := by
    simpa [prefixWord, tailWord_2873238, baseEnd_2873238] using wordTrace_append hprefix tailTrace_2873238
  have hstable : (prefixWord ++ tailWord_2873238).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2873238).length < 2 ^ (prefixWord ++ tailWord_2873238).sum := by decide
  have hdescent : baseEnd_2873238 < baseStart_2873238 := by decide
  rcases family_descends (prefixWord ++ tailWord_2873238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2873268 : List Nat := [2, 5, 2, 1, 3, 1, 1, 1, 1, 5]
def baseStart_2873268 : Nat := 118140960795 + 2873268 * 2 ^ 59
def prefixEnd_2873268 : Nat := 4983230072969 + 3 ^ 40 * 2873268 * 2
def baseEnd_2873268 : Nat := 983578355455179706290725

theorem tailTrace_2873268 : CollatzResearch.WordTrace tailWord_2873268 prefixEnd_2873268 983578355455179706290725 := by
  unfold tailWord_2873268
  simp only [CollatzResearch.WordTrace]
  refine ⟨52398346677324112975842229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69864462236432150634456305 52398346677324112975842229)
  ·
    refine ⟨4912345000999135591485209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 52398346677324112975842229 4912345000999135591485209)
    ·
      refine ⟨3684258750749351693613907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4912345000999135591485209 3684258750749351693613907)
      ·
        refine ⟨5526388126124027540420861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3684258750749351693613907 5526388126124027540420861)
        ·
          refine ⟨2072395547296510327657823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5526388126124027540420861 2072395547296510327657823)
          ·
            refine ⟨3108593320944765491486735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2072395547296510327657823 3108593320944765491486735)
            ·
              refine ⟨4662889981417148237230103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3108593320944765491486735 4662889981417148237230103)
              ·
                refine ⟨6994334972125722355845155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4662889981417148237230103 6994334972125722355845155)
                ·
                  refine ⟨10491502458188583533767733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6994334972125722355845155 10491502458188583533767733)
                  ·
                    refine ⟨983578355455179706290725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10491502458188583533767733 983578355455179706290725)
                    ·
                      rfl

theorem cell22_2873268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_2873268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2873268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2873268 prefixEnd_2873268 := by exact prefixLift 2873268
  have htrace : WordTrace (prefixWord ++ tailWord_2873268) baseStart_2873268 baseEnd_2873268 := by
    simpa [prefixWord, tailWord_2873268, baseEnd_2873268] using wordTrace_append hprefix tailTrace_2873268
  have hstable : (prefixWord ++ tailWord_2873268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2873268).length < 2 ^ (prefixWord ++ tailWord_2873268).sum := by decide
  have hdescent : baseEnd_2873268 < baseStart_2873268 := by decide
  rcases family_descends (prefixWord ++ tailWord_2873268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2873290 : List Nat := [3, 1, 2, 1, 2, 1, 2, 2, 1, 7]
def baseStart_2873290 : Nat := 118140960795 + 2873290 * 2 ^ 59
def prefixEnd_2873290 : Nat := 4983230072969 + 3 ^ 40 * 2873290 * 2
def baseEnd_2873290 : Nat := 983585886504778982240657

theorem tailTrace_2873290 : CollatzResearch.WordTrace tailWord_2873290 prefixEnd_2873290 983585886504778982240657 := by
  unfold tailWord_2873290
  simp only [CollatzResearch.WordTrace]
  refine ⟨26199373940142130927246331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69864997173712349139323549 26199373940142130927246331)
  ·
    refine ⟨39299060910213196390869497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26199373940142130927246331 39299060910213196390869497)
    ·
      refine ⟨29474295682659897293152123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39299060910213196390869497 29474295682659897293152123)
      ·
        refine ⟨44211443523989845939728185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29474295682659897293152123 44211443523989845939728185)
        ·
          refine ⟨33158582642992384454796139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44211443523989845939728185 33158582642992384454796139)
          ·
            refine ⟨49737873964488576682194209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33158582642992384454796139 49737873964488576682194209)
            ·
              refine ⟨37303405473366432511645657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49737873964488576682194209 37303405473366432511645657)
              ·
                refine ⟨27977554105024824383734243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37303405473366432511645657 27977554105024824383734243)
                ·
                  refine ⟨41966331157537236575601365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27977554105024824383734243 41966331157537236575601365)
                  ·
                    refine ⟨983585886504778982240657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41966331157537236575601365 983585886504778982240657)
                    ·
                      rfl

theorem cell22_2873290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 2, 1, 7].length) (baseStart_2873290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2873290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2873290 prefixEnd_2873290 := by exact prefixLift 2873290
  have htrace : WordTrace (prefixWord ++ tailWord_2873290) baseStart_2873290 baseEnd_2873290 := by
    simpa [prefixWord, tailWord_2873290, baseEnd_2873290] using wordTrace_append hprefix tailTrace_2873290
  have hstable : (prefixWord ++ tailWord_2873290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2873290).length < 2 ^ (prefixWord ++ tailWord_2873290).sum := by decide
  have hdescent : baseEnd_2873290 < baseStart_2873290 := by decide
  rcases family_descends (prefixWord ++ tailWord_2873290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2873322 : List Nat := [3, 1, 3, 1, 2, 1, 2, 2, 3, 4]
def baseStart_2873322 : Nat := 118140960795 + 2873322 * 2 ^ 59
def prefixEnd_2873322 : Nat := 4983230072969 + 3 ^ 40 * 2873322 * 2
def baseEnd_2873322 : Nat := 983596840758741565440559

theorem tailTrace_2873322 : CollatzResearch.WordTrace tailWord_2873322 prefixEnd_2873322 983596840758741565440559 := by
  unfold tailWord_2873322
  simp only [CollatzResearch.WordTrace]
  refine ⟨26199665724113148293537555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69865775264301728782766813 26199665724113148293537555)
  ·
    refine ⟨39299498586169722440306333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26199665724113148293537555 39299498586169722440306333)
    ·
      refine ⟨14737311969813645915114875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39299498586169722440306333 14737311969813645915114875)
      ·
        refine ⟨22105967954720468872672313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14737311969813645915114875 22105967954720468872672313)
        ·
          refine ⟨16579475966040351654504235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22105967954720468872672313 16579475966040351654504235)
          ·
            refine ⟨24869213949060527481756353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16579475966040351654504235 24869213949060527481756353)
            ·
              refine ⟨18651910461795395611317265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24869213949060527481756353 18651910461795395611317265)
              ·
                refine ⟨13988932846346546708487949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18651910461795395611317265 13988932846346546708487949)
                ·
                  refine ⟨5245849817379955015682981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13988932846346546708487949 5245849817379955015682981)
                  ·
                    refine ⟨983596840758741565440559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5245849817379955015682981 983596840758741565440559)
                    ·
                      rfl

theorem cell22_2873322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 2, 3, 4].length) (baseStart_2873322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2873322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2873322 prefixEnd_2873322 := by exact prefixLift 2873322
  have htrace : WordTrace (prefixWord ++ tailWord_2873322) baseStart_2873322 baseEnd_2873322 := by
    simpa [prefixWord, tailWord_2873322, baseEnd_2873322] using wordTrace_append hprefix tailTrace_2873322
  have hstable : (prefixWord ++ tailWord_2873322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2873322).length < 2 ^ (prefixWord ++ tailWord_2873322).sum := by decide
  have hdescent : baseEnd_2873322 < baseStart_2873322 := by decide
  rcases family_descends (prefixWord ++ tailWord_2873322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2873326 : List Nat := [4, 1, 2, 1, 3, 3, 2, 1, 5]
def baseStart_2873326 : Nat := 118140960795 + 2873326 * 2 ^ 59
def prefixEnd_2873326 : Nat := 4983230072969 + 3 ^ 40 * 2873326 * 2
def baseEnd_2873326 : Nat := 327866070013495629446849

theorem tailTrace_2873326 : CollatzResearch.WordTrace tailWord_2873326 prefixEnd_2873326 327866070013495629446849 := by
  unfold tailWord_2873326
  simp only [CollatzResearch.WordTrace]
  refine ⟨13099851098554762732161979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69865872525625401238197221 13099851098554762732161979)
  ·
    refine ⟨19649776647832144098242969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13099851098554762732161979 19649776647832144098242969)
    ·
      refine ⟨14737332485874108073682227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19649776647832144098242969 14737332485874108073682227)
      ·
        refine ⟨22105998728811162110523341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14737332485874108073682227 22105998728811162110523341)
        ·
          refine ⟨8289749523304185791446253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22105998728811162110523341 8289749523304185791446253)
          ·
            refine ⟨3108656071239069671792345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8289749523304185791446253 3108656071239069671792345)
            ·
              refine ⟨2331492053429302253844259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3108656071239069671792345 2331492053429302253844259)
              ·
                refine ⟨3497238080143953380766389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2331492053429302253844259 3497238080143953380766389)
                ·
                  refine ⟨327866070013495629446849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3497238080143953380766389 327866070013495629446849)
                  ·
                    rfl

theorem cell22_2873326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 2, 1, 5].length) (baseStart_2873326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2873326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2873326 prefixEnd_2873326 := by exact prefixLift 2873326
  have htrace : WordTrace (prefixWord ++ tailWord_2873326) baseStart_2873326 baseEnd_2873326 := by
    simpa [prefixWord, tailWord_2873326, baseEnd_2873326] using wordTrace_append hprefix tailTrace_2873326
  have hstable : (prefixWord ++ tailWord_2873326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2873326).length < 2 ^ (prefixWord ++ tailWord_2873326).sum := by decide
  have hdescent : baseEnd_2873326 < baseStart_2873326 := by decide
  rcases family_descends (prefixWord ++ tailWord_2873326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2873335 : List Nat := [1, 1, 3, 1, 1, 1, 1, 1, 7, 5]
def baseStart_2873335 : Nat := 118140960795 + 2873335 * 2 ^ 59
def prefixEnd_2873335 : Nat := 4983230072969 + 3 ^ 40 * 2873335 * 2
def baseEnd_2873335 : Nat := 983601290924413864865519

theorem tailTrace_2873335 : CollatzResearch.WordTrace tailWord_2873335 prefixEnd_2873335 983601290924413864865519 := by
  unfold tailWord_2873335
  simp only [CollatzResearch.WordTrace]
  refine ⟨104799137045405496394373459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69866091363603664262915639 104799137045405496394373459)
  ·
    refine ⟨157198705568108244591560189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104799137045405496394373459 157198705568108244591560189)
    ·
      refine ⟨58949514588040591721835071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157198705568108244591560189 58949514588040591721835071)
      ·
        refine ⟨88424271882060887582752607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58949514588040591721835071 88424271882060887582752607)
        ·
          refine ⟨132636407823091331374128911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88424271882060887582752607 132636407823091331374128911)
          ·
            refine ⟨198954611734636997061193367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132636407823091331374128911 198954611734636997061193367)
            ·
              refine ⟨298431917601955495591790051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 198954611734636997061193367 298431917601955495591790051)
              ·
                refine ⟨447647876402933243387685077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 298431917601955495591790051 447647876402933243387685077)
                ·
                  refine ⟨10491747103193747891898869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 447647876402933243387685077 10491747103193747891898869)
                  ·
                    refine ⟨983601290924413864865519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10491747103193747891898869 983601290924413864865519)
                    ·
                      rfl

theorem cell22_2873335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 7, 5].length) (baseStart_2873335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2873335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2873335 prefixEnd_2873335 := by exact prefixLift 2873335
  have htrace : WordTrace (prefixWord ++ tailWord_2873335) baseStart_2873335 baseEnd_2873335 := by
    simpa [prefixWord, tailWord_2873335, baseEnd_2873335] using wordTrace_append hprefix tailTrace_2873335
  have hstable : (prefixWord ++ tailWord_2873335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2873335).length < 2 ^ (prefixWord ++ tailWord_2873335).sum := by decide
  have hdescent : baseEnd_2873335 < baseStart_2873335 := by decide
  rcases family_descends (prefixWord ++ tailWord_2873335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2873352 : List Nat := [2, 1, 3, 2, 1, 2, 3, 2, 1, 5]
def baseStart_2873352 : Nat := 118140960795 + 2873352 * 2 ^ 59
def prefixEnd_2873352 : Nat := 4983230072969 + 3 ^ 40 * 2873352 * 2
def baseEnd_2873352 : Nat := 983607110371831487190467

theorem tailTrace_2873352 : CollatzResearch.WordTrace tailWord_2873352 prefixEnd_2873352 983607110371831487190467 := by
  unfold tailWord_2873352
  simp only [CollatzResearch.WordTrace]
  refine ⟨52399878543171954148871155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69866504724229272198494873 52399878543171954148871155)
  ·
    refine ⟨78599817814757931223306733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52399878543171954148871155 78599817814757931223306733)
    ·
      refine ⟨29474931680534224208740025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78599817814757931223306733 29474931680534224208740025)
      ·
        refine ⟨22106198760400668156555019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29474931680534224208740025 22106198760400668156555019)
        ·
          refine ⟨33159298140601002234832529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22106198760400668156555019 33159298140601002234832529)
          ·
            refine ⟨24869473605450751676124397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33159298140601002234832529 24869473605450751676124397)
            ·
              refine ⟨9326052602044031878546649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24869473605450751676124397 9326052602044031878546649)
              ·
                refine ⟨6994539451533023908909987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9326052602044031878546649 6994539451533023908909987)
                ·
                  refine ⟨10491809177299535863364981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6994539451533023908909987 10491809177299535863364981)
                  ·
                    refine ⟨983607110371831487190467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10491809177299535863364981 983607110371831487190467)
                    ·
                      rfl

theorem cell22_2873352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 2, 1, 5].length) (baseStart_2873352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2873352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2873352 prefixEnd_2873352 := by exact prefixLift 2873352
  have htrace : WordTrace (prefixWord ++ tailWord_2873352) baseStart_2873352 baseEnd_2873352 := by
    simpa [prefixWord, tailWord_2873352, baseEnd_2873352] using wordTrace_append hprefix tailTrace_2873352
  have hstable : (prefixWord ++ tailWord_2873352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2873352).length < 2 ^ (prefixWord ++ tailWord_2873352).sum := by decide
  have hdescent : baseEnd_2873352 < baseStart_2873352 := by decide
  rcases family_descends (prefixWord ++ tailWord_2873352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2873364 : List Nat := [2, 4, 3, 2, 2, 1, 2, 2, 1, 3]
def baseStart_2873364 : Nat := 118140960795 + 2873364 * 2 ^ 59
def prefixEnd_2873364 : Nat := 4983230072969 + 3 ^ 40 * 2873364 * 2
def baseEnd_2873364 : Nat := 983611218217067455890431

theorem tailTrace_2873364 : CollatzResearch.WordTrace tailWord_2873364 prefixEnd_2873364 983611218217067455890431 := by
  unfold tailWord_2873364
  simp only [CollatzResearch.WordTrace]
  refine ⟨52400097381150217173589573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69866796508200289564786097 52400097381150217173589573)
  ·
    refine ⟨9825018258965665720048045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52400097381150217173589573 9825018258965665720048045)
    ·
      refine ⟨3684381847112124645018017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9825018258965665720048045 3684381847112124645018017)
      ·
        refine ⟨2763286385334093483763513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3684381847112124645018017 2763286385334093483763513)
        ·
          refine ⟨2072464789000570112822635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2763286385334093483763513 2072464789000570112822635)
          ·
            refine ⟨3108697183500855169233953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2072464789000570112822635 3108697183500855169233953)
            ·
              refine ⟨2331522887625641376925465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3108697183500855169233953 2331522887625641376925465)
              ·
                refine ⟨1748642165719231032694099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2331522887625641376925465 1748642165719231032694099)
                ·
                  refine ⟨2622963248578846549041149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1748642165719231032694099 2622963248578846549041149)
                  ·
                    refine ⟨983611218217067455890431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2622963248578846549041149 983611218217067455890431)
                    ·
                      rfl

theorem cell22_2873364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_2873364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2873364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2873364 prefixEnd_2873364 := by exact prefixLift 2873364
  have htrace : WordTrace (prefixWord ++ tailWord_2873364) baseStart_2873364 baseEnd_2873364 := by
    simpa [prefixWord, tailWord_2873364, baseEnd_2873364] using wordTrace_append hprefix tailTrace_2873364
  have hstable : (prefixWord ++ tailWord_2873364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2873364).length < 2 ^ (prefixWord ++ tailWord_2873364).sum := by decide
  have hdescent : baseEnd_2873364 < baseStart_2873364 := by decide
  rcases family_descends (prefixWord ++ tailWord_2873364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2873365 : List Nat := [1, 3, 2, 1, 15]
def baseStart_2873365 : Nat := 118140960795 + 2873365 * 2 ^ 59
def prefixEnd_2873365 : Nat := 4983230072969 + 3 ^ 40 * 2873365 * 2
def baseEnd_2873365 : Nat := 4047784199742813936689

theorem tailTrace_2873365 : CollatzResearch.WordTrace tailWord_2873365 prefixEnd_2873365 4047784199742813936689 := by
  unfold tailWord_2873365
  simp only [CollatzResearch.WordTrace]
  refine ⟨104800231235296811517965549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69866820823531207678643699 104800231235296811517965549)
  ·
    refine ⟨39300086713236304319237081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104800231235296811517965549 39300086713236304319237081)
    ·
      refine ⟨29475065034927228239427811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39300086713236304319237081 29475065034927228239427811)
      ·
        refine ⟨44212597552390842359141717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29475065034927228239427811 44212597552390842359141717)
        ·
          refine ⟨4047784199742813936689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 15 44212597552390842359141717 4047784199742813936689)
          ·
            rfl

theorem cell22_2873365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 15].length) (baseStart_2873365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2873365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2873365 prefixEnd_2873365 := by exact prefixLift 2873365
  have htrace : WordTrace (prefixWord ++ tailWord_2873365) baseStart_2873365 baseEnd_2873365 := by
    simpa [prefixWord, tailWord_2873365, baseEnd_2873365] using wordTrace_append hprefix tailTrace_2873365
  have hstable : (prefixWord ++ tailWord_2873365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2873365).length < 2 ^ (prefixWord ++ tailWord_2873365).sum := by decide
  have hdescent : baseEnd_2873365 < baseStart_2873365 := by decide
  rcases family_descends (prefixWord ++ tailWord_2873365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2873386 : List Nat := [3, 1, 4, 1, 2, 1, 2, 3, 2, 3]
def baseStart_2873386 : Nat := 118140960795 + 2873386 * 2 ^ 59
def prefixEnd_2873386 : Nat := 4983230072969 + 3 ^ 40 * 2873386 * 2
def baseEnd_2873386 : Nat := 983618749266666731840363

theorem tailTrace_2873386 : CollatzResearch.WordTrace tailWord_2873386 prefixEnd_2873386 983618749266666731840363 := by
  unfold tailWord_2873386
  simp only [CollatzResearch.WordTrace]
  refine ⟨26200249292055183026120003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69867331445480488069653341 26200249292055183026120003)
  ·
    refine ⟨39300373938082774539180005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26200249292055183026120003 39300373938082774539180005)
    ·
      refine ⟨7368820113390520226096251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39300373938082774539180005 7368820113390520226096251)
      ·
        refine ⟨11053230170085780339144377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7368820113390520226096251 11053230170085780339144377)
        ·
          refine ⟨8289922627564335254358283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11053230170085780339144377 8289922627564335254358283)
          ·
            refine ⟨12434883941346502881537425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8289922627564335254358283 12434883941346502881537425)
            ·
              refine ⟨9326162956009877161153069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12434883941346502881537425 9326162956009877161153069)
              ·
                refine ⟨3497311108503703935432401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9326162956009877161153069 3497311108503703935432401)
                ·
                  refine ⟨2622983331377777951574301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3497311108503703935432401 2622983331377777951574301)
                  ·
                    refine ⟨983618749266666731840363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2622983331377777951574301 983618749266666731840363)
                    ·
                      rfl

theorem cell22_2873386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 3, 2, 3].length) (baseStart_2873386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2873386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2873386 prefixEnd_2873386 := by exact prefixLift 2873386
  have htrace : WordTrace (prefixWord ++ tailWord_2873386) baseStart_2873386 baseEnd_2873386 := by
    simpa [prefixWord, tailWord_2873386, baseEnd_2873386] using wordTrace_append hprefix tailTrace_2873386
  have hstable : (prefixWord ++ tailWord_2873386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2873386).length < 2 ^ (prefixWord ++ tailWord_2873386).sum := by decide
  have hdescent : baseEnd_2873386 < baseStart_2873386 := by decide
  rcases family_descends (prefixWord ++ tailWord_2873386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2873401 : List Nat := [1, 2, 1, 5, 3, 2, 1, 1, 2, 4]
def baseStart_2873401 : Nat := 118140960795 + 2873401 * 2 ^ 59
def prefixEnd_2873401 : Nat := 4983230072969 + 3 ^ 40 * 2873401 * 2
def baseEnd_2873401 : Nat := 983623884073211692715317

theorem tailTrace_2873401 : CollatzResearch.WordTrace tailWord_2873401 prefixEnd_2873401 983623884073211692715317 := by
  unfold tailWord_2873401
  simp only [CollatzResearch.WordTrace]
  refine ⟨104801544263166389666276057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69867696175444259777517371 104801544263166389666276057)
  ·
    refine ⟨78601158197374792249707043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104801544263166389666276057 78601158197374792249707043)
    ·
      refine ⟨117901737296062188374560565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78601158197374792249707043 117901737296062188374560565)
      ·
        refine ⟨11053287871505830160115053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 117901737296062188374560565 11053287871505830160115053)
        ·
          refine ⟨4144982951814686310043145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11053287871505830160115053 4144982951814686310043145)
          ·
            refine ⟨3108737213861014732532359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4144982951814686310043145 3108737213861014732532359)
            ·
              refine ⟨4663105820791522098798539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3108737213861014732532359 4663105820791522098798539)
              ·
                refine ⟨6994658731187283148197809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4663105820791522098798539 6994658731187283148197809)
                ·
                  refine ⟨5245994048390462361148357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6994658731187283148197809 5245994048390462361148357)
                  ·
                    refine ⟨983623884073211692715317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5245994048390462361148357 983623884073211692715317)
                    ·
                      rfl

theorem cell22_2873401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 1, 1, 2, 4].length) (baseStart_2873401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2873401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2873401 prefixEnd_2873401 := by exact prefixLift 2873401
  have htrace : WordTrace (prefixWord ++ tailWord_2873401) baseStart_2873401 baseEnd_2873401 := by
    simpa [prefixWord, tailWord_2873401, baseEnd_2873401] using wordTrace_append hprefix tailTrace_2873401
  have hstable : (prefixWord ++ tailWord_2873401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2873401).length < 2 ^ (prefixWord ++ tailWord_2873401).sum := by decide
  have hdescent : baseEnd_2873401 < baseStart_2873401 := by decide
  rcases family_descends (prefixWord ++ tailWord_2873401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2873431 : List Nat := [1, 1, 3, 2, 2, 1, 4, 4, 1, 3]
def baseStart_2873431 : Nat := 118140960795 + 2873431 * 2 ^ 59
def prefixEnd_2873431 : Nat := 4983230072969 + 3 ^ 40 * 2873431 * 2
def baseEnd_2873431 : Nat := 983634153686301614465225

theorem tailTrace_2873431 : CollatzResearch.WordTrace tailWord_2873431 prefixEnd_2873431 983634153686301614465225 := by
  unfold tailWord_2873431
  simp only [CollatzResearch.WordTrace]
  refine ⟨104802638453057704789868147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69868425635371803193245431 104802638453057704789868147)
  ·
    refine ⟨157203957679586557184802221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104802638453057704789868147 157203957679586557184802221)
    ·
      refine ⟨58951484129844958944300833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157203957679586557184802221 58951484129844958944300833)
      ·
        refine ⟨44213613097383719208225625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58951484129844958944300833 44213613097383719208225625)
        ·
          refine ⟨33160209823037789406169219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44213613097383719208225625 33160209823037789406169219)
          ·
            refine ⟨49740314734556684109253829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33160209823037789406169219 49740314734556684109253829)
            ·
              refine ⟨9326309012729378270485093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49740314734556684109253829 9326309012729378270485093)
              ·
                refine ⟨1748682939886758425715955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9326309012729378270485093 1748682939886758425715955)
                ·
                  refine ⟨2623024409830137638573933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1748682939886758425715955 2623024409830137638573933)
                  ·
                    refine ⟨983634153686301614465225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2623024409830137638573933 983634153686301614465225)
                    ·
                      rfl

theorem cell22_2873431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 4, 1, 3].length) (baseStart_2873431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2873431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2873431 prefixEnd_2873431 := by exact prefixLift 2873431
  have htrace : WordTrace (prefixWord ++ tailWord_2873431) baseStart_2873431 baseEnd_2873431 := by
    simpa [prefixWord, tailWord_2873431, baseEnd_2873431] using wordTrace_append hprefix tailTrace_2873431
  have hstable : (prefixWord ++ tailWord_2873431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2873431).length < 2 ^ (prefixWord ++ tailWord_2873431).sum := by decide
  have hdescent : baseEnd_2873431 < baseStart_2873431 := by decide
  rcases family_descends (prefixWord ++ tailWord_2873431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2873508 : List Nat := [2, 3, 1, 2, 4, 2, 1, 2, 1, 4]
def baseStart_2873508 : Nat := 118140960795 + 2873508 * 2 ^ 59
def prefixEnd_2873508 : Nat := 4983230072969 + 3 ^ 40 * 2873508 * 2
def baseEnd_2873508 : Nat := 983660512359899080289989

theorem tailTrace_2873508 : CollatzResearch.WordTrace tailWord_2873508 prefixEnd_2873508 983660512359899080289989 := by
  unfold tailWord_2873508
  simp only [CollatzResearch.WordTrace]
  refine ⟨52402723436889373470210589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69870297915852497960280785 52402723436889373470210589)
  ·
    refine ⟨19651021288833515051328971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52402723436889373470210589 19651021288833515051328971)
    ·
      refine ⟨29476531933250272576993457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19651021288833515051328971 29476531933250272576993457)
      ·
        refine ⟨22107398949937704432745093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29476531933250272576993457 22107398949937704432745093)
        ·
          refine ⟨4145137303113319581139705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22107398949937704432745093 4145137303113319581139705)
          ·
            refine ⟨3108852977334989685854779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4145137303113319581139705 3108852977334989685854779)
            ·
              refine ⟨4663279466002484528782169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3108852977334989685854779 4663279466002484528782169)
              ·
                refine ⟨3497459599501863396586627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4663279466002484528782169 3497459599501863396586627)
                ·
                  refine ⟨5246189399252795094879941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3497459599501863396586627 5246189399252795094879941)
                  ·
                    refine ⟨983660512359899080289989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5246189399252795094879941 983660512359899080289989)
                    ·
                      rfl

theorem cell22_2873508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 1, 2, 1, 4].length) (baseStart_2873508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2873508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2873508 prefixEnd_2873508 := by exact prefixLift 2873508
  have htrace : WordTrace (prefixWord ++ tailWord_2873508) baseStart_2873508 baseEnd_2873508 := by
    simpa [prefixWord, tailWord_2873508, baseEnd_2873508] using wordTrace_append hprefix tailTrace_2873508
  have hstable : (prefixWord ++ tailWord_2873508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2873508).length < 2 ^ (prefixWord ++ tailWord_2873508).sum := by decide
  have hdescent : baseEnd_2873508 < baseStart_2873508 := by decide
  rcases family_descends (prefixWord ++ tailWord_2873508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2873521 : List Nat := [1, 2, 2, 5, 2, 1, 1, 2, 1, 5]
def baseStart_2873521 : Nat := 118140960795 + 2873521 * 2 ^ 59
def prefixEnd_2873521 : Nat := 4983230072969 + 3 ^ 40 * 2873521 * 2
def baseEnd_2873521 : Nat := 983664962525571379714949

theorem tailTrace_2873521 : CollatzResearch.WordTrace tailWord_2873521 prefixEnd_2873521 983664962525571379714949 := by
  unfold tailWord_2873521
  simp only [CollatzResearch.WordTrace]
  refine ⟨104805921022731650160644417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69870614015154433440429611 104805921022731650160644417)
  ·
    refine ⟨78604440767048737620483313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104805921022731650160644417 78604440767048737620483313)
    ·
      refine ⟨58953330575286553215362485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78604440767048737620483313 58953330575286553215362485)
      ·
        refine ⟨5526874741433114363940233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 58953330575286553215362485 5526874741433114363940233)
        ·
          refine ⟨4145156056074835772955175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5526874741433114363940233 4145156056074835772955175)
          ·
            refine ⟨6217734084112253659432763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4145156056074835772955175 6217734084112253659432763)
            ·
              refine ⟨9326601126168380489149145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6217734084112253659432763 9326601126168380489149145)
              ·
                refine ⟨6994950844626285366861859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9326601126168380489149145 6994950844626285366861859)
                ·
                  refine ⟨10492426266939428050292789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6994950844626285366861859 10492426266939428050292789)
                  ·
                    refine ⟨983664962525571379714949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10492426266939428050292789 983664962525571379714949)
                    ·
                      rfl

theorem cell22_2873521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 2, 1, 5].length) (baseStart_2873521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2873521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2873521 prefixEnd_2873521 := by exact prefixLift 2873521
  have htrace : WordTrace (prefixWord ++ tailWord_2873521) baseStart_2873521 baseEnd_2873521 := by
    simpa [prefixWord, tailWord_2873521, baseEnd_2873521] using wordTrace_append hprefix tailTrace_2873521
  have hstable : (prefixWord ++ tailWord_2873521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2873521).length < 2 ^ (prefixWord ++ tailWord_2873521).sum := by decide
  have hdescent : baseEnd_2873521 < baseStart_2873521 := by decide
  rcases family_descends (prefixWord ++ tailWord_2873521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2873525 : List Nat := [1, 3, 3, 4, 1, 1, 3, 1, 1, 4]
def baseStart_2873525 : Nat := 118140960795 + 2873525 * 2 ^ 59
def prefixEnd_2873525 : Nat := 4983230072969 + 3 ^ 40 * 2873525 * 2
def baseEnd_2873525 : Nat := 983666331807316702614937

theorem tailTrace_2873525 : CollatzResearch.WordTrace tailWord_2873525 prefixEnd_2873525 983666331807316702614937 := by
  unfold tailWord_2873525
  simp only [CollatzResearch.WordTrace]
  refine ⟨104806066914717158843790029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69870711276478105895860019 104806066914717158843790029)
  ·
    refine ⟨39302275093018934566421261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104806066914717158843790029 39302275093018934566421261)
    ·
      refine ⟨14738353159882100462407973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39302275093018934566421261 14738353159882100462407973)
      ·
        refine ⟨2763441217477893836701495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14738353159882100462407973 2763441217477893836701495)
        ·
          refine ⟨4145161826216840755052243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2763441217477893836701495 4145161826216840755052243)
          ·
            refine ⟨6217742739325261132578365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4145161826216840755052243 6217742739325261132578365)
            ·
              refine ⟨2331653527246972924716887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6217742739325261132578365 2331653527246972924716887)
              ·
                refine ⟨3497480290870459387075331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2331653527246972924716887 3497480290870459387075331)
                ·
                  refine ⟨5246220436305689080612997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3497480290870459387075331 5246220436305689080612997)
                  ·
                    refine ⟨983666331807316702614937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5246220436305689080612997 983666331807316702614937)
                    ·
                      rfl

theorem cell22_2873525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 3, 1, 1, 4].length) (baseStart_2873525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2873525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2873525 prefixEnd_2873525 := by exact prefixLift 2873525
  have htrace : WordTrace (prefixWord ++ tailWord_2873525) baseStart_2873525 baseEnd_2873525 := by
    simpa [prefixWord, tailWord_2873525, baseEnd_2873525] using wordTrace_append hprefix tailTrace_2873525
  have hstable : (prefixWord ++ tailWord_2873525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2873525).length < 2 ^ (prefixWord ++ tailWord_2873525).sum := by decide
  have hdescent : baseEnd_2873525 < baseStart_2873525 := by decide
  rcases family_descends (prefixWord ++ tailWord_2873525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2873534 : List Nat := [4, 2, 1, 1, 4, 10]
def baseStart_2873534 : Nat := 118140960795 + 2873534 * 2 ^ 59
def prefixEnd_2873534 : Nat := 4983230072969 + 3 ^ 40 * 2873534 * 2
def baseEnd_2873534 : Nat := 12144066823348687396789

theorem tailTrace_2873534 : CollatzResearch.WordTrace tailWord_2873534 prefixEnd_2873534 12144066823348687396789 := by
  unfold tailWord_2873534
  simp only [CollatzResearch.WordTrace]
  refine ⟨13100799396460569172608457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69870930114456368920578437 13100799396460569172608457)
  ·
    refine ⟨9825599547345426879456343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13100799396460569172608457 9825599547345426879456343)
    ·
      refine ⟨14738399321018140319184515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9825599547345426879456343 14738399321018140319184515)
      ·
        refine ⟨22107598981527210478776773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14738399321018140319184515 22107598981527210478776773)
        ·
          refine ⟨4145174809036351964770645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22107598981527210478776773 4145174809036351964770645)
          ·
            refine ⟨12144066823348687396789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4145174809036351964770645 12144066823348687396789)
            ·
              rfl

theorem cell22_2873534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 10].length) (baseStart_2873534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2873534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2873534 prefixEnd_2873534 := by exact prefixLift 2873534
  have htrace : WordTrace (prefixWord ++ tailWord_2873534) baseStart_2873534 baseEnd_2873534 := by
    simpa [prefixWord, tailWord_2873534, baseEnd_2873534] using wordTrace_append hprefix tailTrace_2873534
  have hstable : (prefixWord ++ tailWord_2873534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2873534).length < 2 ^ (prefixWord ++ tailWord_2873534).sum := by decide
  have hdescent : baseEnd_2873534 < baseStart_2873534 := by decide
  rcases family_descends (prefixWord ++ tailWord_2873534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2873540 : List Nat := [2, 3, 3, 1, 2, 3, 2, 2, 4]
def baseStart_2873540 : Nat := 118140960795 + 2873540 * 2 ^ 59
def prefixEnd_2873540 : Nat := 4983230072969 + 3 ^ 40 * 2873540 * 2
def baseEnd_2873540 : Nat := 327890488871287221163297

theorem tailTrace_2873540 : CollatzResearch.WordTrace tailWord_2873540 prefixEnd_2873540 327890488871287221163297 := by
  unfold tailWord_2873540
  simp only [CollatzResearch.WordTrace]
  refine ⟨52403307004831408202793037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69871076006441877603724049 52403307004831408202793037)
  ·
    refine ⟨19651240126811778076047389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52403307004831408202793037 19651240126811778076047389)
    ·
      refine ⟨7369215047554416778517771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19651240126811778076047389 7369215047554416778517771)
      ·
        refine ⟨11053822571331625167776657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7369215047554416778517771 11053822571331625167776657)
        ·
          refine ⟨8290366928498718875832493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11053822571331625167776657 8290366928498718875832493)
          ·
            refine ⟨3108887598187019578437185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8290366928498718875832493 3108887598187019578437185)
            ·
              refine ⟨2331665698640264683827889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3108887598187019578437185 2331665698640264683827889)
              ·
                refine ⟨1748749273980198512870917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2331665698640264683827889 1748749273980198512870917)
                ·
                  refine ⟨327890488871287221163297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1748749273980198512870917 327890488871287221163297)
                  ·
                    rfl

theorem cell22_2873540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 2, 2, 4].length) (baseStart_2873540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2873540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2873540 prefixEnd_2873540 := by exact prefixLift 2873540
  have htrace : WordTrace (prefixWord ++ tailWord_2873540) baseStart_2873540 baseEnd_2873540 := by
    simpa [prefixWord, tailWord_2873540, baseEnd_2873540] using wordTrace_append hprefix tailTrace_2873540
  have hstable : (prefixWord ++ tailWord_2873540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2873540).length < 2 ^ (prefixWord ++ tailWord_2873540).sum := by decide
  have hdescent : baseEnd_2873540 < baseStart_2873540 := by decide
  rcases family_descends (prefixWord ++ tailWord_2873540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2873547 : List Nat := [1, 1, 1, 1, 3, 2, 3, 1, 1, 8]
def baseStart_2873547 : Nat := 118140960795 + 2873547 * 2 ^ 59
def prefixEnd_2873547 : Nat := 4983230072969 + 3 ^ 40 * 2873547 * 2
def baseEnd_2873547 : Nat := 983673862856915978564869

theorem tailTrace_2873547 : CollatzResearch.WordTrace tailWord_2873547 prefixEnd_2873547 983673862856915978564869 := by
  unfold tailWord_2873547
  simp only [CollatzResearch.WordTrace]
  refine ⟨104806869320637456601090895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69871246213758304400727263 104806869320637456601090895)
  ·
    refine ⟨157210303980956184901636343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104806869320637456601090895 157210303980956184901636343)
    ·
      refine ⟨235815455971434277352454515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157210303980956184901636343 235815455971434277352454515)
      ·
        refine ⟨353723183957151416028681773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235815455971434277352454515 353723183957151416028681773)
        ·
          refine ⟨132646193983931781010755665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 353723183957151416028681773 132646193983931781010755665)
          ·
            refine ⟨99484645487948835758066749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132646193983931781010755665 99484645487948835758066749)
            ·
              refine ⟨37306742057980813409275031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99484645487948835758066749 37306742057980813409275031)
              ·
                refine ⟨55960113086971220113912547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37306742057980813409275031 55960113086971220113912547)
                ·
                  refine ⟨83940169630456830170868821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55960113086971220113912547 83940169630456830170868821)
                  ·
                    refine ⟨983673862856915978564869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 83940169630456830170868821 983673862856915978564869)
                    ·
                      rfl

theorem cell22_2873547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 8].length) (baseStart_2873547 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2873547 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2873547 prefixEnd_2873547 := by exact prefixLift 2873547
  have htrace : WordTrace (prefixWord ++ tailWord_2873547) baseStart_2873547 baseEnd_2873547 := by
    simpa [prefixWord, tailWord_2873547, baseEnd_2873547] using wordTrace_append hprefix tailTrace_2873547
  have hstable : (prefixWord ++ tailWord_2873547).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2873547).length < 2 ^ (prefixWord ++ tailWord_2873547).sum := by decide
  have hdescent : baseEnd_2873547 < baseStart_2873547 := by decide
  rcases family_descends (prefixWord ++ tailWord_2873547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2873570 : List Nat := [3, 3, 4, 1, 1, 1, 1, 1, 1, 6]
def baseStart_2873570 : Nat := 118140960795 + 2873570 * 2 ^ 59
def prefixEnd_2873570 : Nat := 4983230072969 + 3 ^ 40 * 2873570 * 2
def baseEnd_2873570 : Nat := 983681736226951585239799

theorem tailTrace_2873570 : CollatzResearch.WordTrace tailWord_2873570 prefixEnd_2873570 983681736226951585239799 := by
  unfold tailWord_2873570
  simp only [CollatzResearch.WordTrace]
  refine ⟨26201927049888532882294541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69871805466369421019452109 26201927049888532882294541)
  ·
    refine ⟨9825722643708199830860453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26201927049888532882294541 9825722643708199830860453)
    ·
      refine ⟨1842322995695287468286335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9825722643708199830860453 1842322995695287468286335)
      ·
        refine ⟨2763484493542931202429503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1842322995695287468286335 2763484493542931202429503)
        ·
          refine ⟨4145226740314396803644255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2763484493542931202429503 4145226740314396803644255)
          ·
            refine ⟨6217840110471595205466383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4145226740314396803644255 6217840110471595205466383)
            ·
              refine ⟨9326760165707392808199575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6217840110471595205466383 9326760165707392808199575)
              ·
                refine ⟨13990140248561089212299363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9326760165707392808199575 13990140248561089212299363)
                ·
                  refine ⟨20985210372841633818449045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13990140248561089212299363 20985210372841633818449045)
                  ·
                    refine ⟨983681736226951585239799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20985210372841633818449045 983681736226951585239799)
                    ·
                      rfl

theorem cell22_2873570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_2873570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2873570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2873570 prefixEnd_2873570 := by exact prefixLift 2873570
  have htrace : WordTrace (prefixWord ++ tailWord_2873570) baseStart_2873570 baseEnd_2873570 := by
    simpa [prefixWord, tailWord_2873570, baseEnd_2873570] using wordTrace_append hprefix tailTrace_2873570
  have hstable : (prefixWord ++ tailWord_2873570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2873570).length < 2 ^ (prefixWord ++ tailWord_2873570).sum := by decide
  have hdescent : baseEnd_2873570 < baseStart_2873570 := by decide
  rcases family_descends (prefixWord ++ tailWord_2873570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2873583 : List Nat := [1, 1, 2, 1, 6, 1, 1, 5, 1, 3]
def baseStart_2873583 : Nat := 118140960795 + 2873583 * 2 ^ 59
def prefixEnd_2873583 : Nat := 4983230072969 + 3 ^ 40 * 2873583 * 2
def baseEnd_2873583 : Nat := 983686186392623884664759

theorem tailTrace_2873583 : CollatzResearch.WordTrace tailWord_2873583 prefixEnd_2873583 983686186392623884664759 := by
  unfold tailWord_2873583
  simp only [CollatzResearch.WordTrace]
  refine ⟨104808182348507034749401403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69872121565671356499600935 104808182348507034749401403)
  ·
    refine ⟨157212273522760552124102105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104808182348507034749401403 157212273522760552124102105)
    ·
      refine ⟨117909205142070414093076579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157212273522760552124102105 117909205142070414093076579)
      ·
        refine ⟨176863807713105621139614869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117909205142070414093076579 176863807713105621139614869)
        ·
          refine ⟨8290490986551825990919447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 176863807713105621139614869 8290490986551825990919447)
          ·
            refine ⟨12435736479827738986379171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8290490986551825990919447 12435736479827738986379171)
            ·
              refine ⟨18653604719741608479568757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12435736479827738986379171 18653604719741608479568757)
              ·
                refine ⟨1748775442475775794959571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18653604719741608479568757 1748775442475775794959571)
                ·
                  refine ⟨2623163163713663692439357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1748775442475775794959571 2623163163713663692439357)
                  ·
                    refine ⟨983686186392623884664759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2623163163713663692439357 983686186392623884664759)
                    ·
                      rfl

theorem cell22_2873583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 5, 1, 3].length) (baseStart_2873583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2873583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2873583 prefixEnd_2873583 := by exact prefixLift 2873583
  have htrace : WordTrace (prefixWord ++ tailWord_2873583) baseStart_2873583 baseEnd_2873583 := by
    simpa [prefixWord, tailWord_2873583, baseEnd_2873583] using wordTrace_append hprefix tailTrace_2873583
  have hstable : (prefixWord ++ tailWord_2873583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2873583).length < 2 ^ (prefixWord ++ tailWord_2873583).sum := by decide
  have hdescent : baseEnd_2873583 < baseStart_2873583 := by decide
  rcases family_descends (prefixWord ++ tailWord_2873583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2873594 : List Nat := [3, 1, 1, 1, 1, 5, 1, 2, 2, 5]
def baseStart_2873594 : Nat := 118140960795 + 2873594 * 2 ^ 59
def prefixEnd_2873594 : Nat := 4983230072969 + 3 ^ 40 * 2873594 * 2
def baseEnd_2873594 : Nat := 983689951917423522639725

theorem tailTrace_2873594 : CollatzResearch.WordTrace tailWord_2873594 prefixEnd_2873594 983689951917423522639725 := by
  unfold tailWord_2873594
  simp only [CollatzResearch.WordTrace]
  refine ⟨26202145887866795907012959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69872389034311455752034557 26202145887866795907012959)
  ·
    refine ⟨39303218831800193860519439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26202145887866795907012959 39303218831800193860519439)
    ·
      refine ⟨58954828247700290790779159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39303218831800193860519439 58954828247700290790779159)
      ·
        refine ⟨88432242371550436186168739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58954828247700290790779159 88432242371550436186168739)
        ·
          refine ⟨132648363557325654279253109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88432242371550436186168739 132648363557325654279253109)
          ·
            refine ⟨12435784083499280088679979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 132648363557325654279253109 12435784083499280088679979)
            ·
              refine ⟨18653676125248920133019969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12435784083499280088679979 18653676125248920133019969)
              ·
                refine ⟨13990257093936690099764977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18653676125248920133019969 13990257093936690099764977)
                ·
                  refine ⟨10492692820452517574823733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13990257093936690099764977 10492692820452517574823733)
                  ·
                    refine ⟨983689951917423522639725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10492692820452517574823733 983689951917423522639725)
                    ·
                      rfl

theorem cell22_2873594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 2, 2, 5].length) (baseStart_2873594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2873594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2873594 prefixEnd_2873594 := by exact prefixLift 2873594
  have htrace : WordTrace (prefixWord ++ tailWord_2873594) baseStart_2873594 baseEnd_2873594 := by
    simpa [prefixWord, tailWord_2873594, baseEnd_2873594] using wordTrace_append hprefix tailTrace_2873594
  have hstable : (prefixWord ++ tailWord_2873594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2873594).length < 2 ^ (prefixWord ++ tailWord_2873594).sum := by decide
  have hdescent : baseEnd_2873594 < baseStart_2873594 := by decide
  rcases family_descends (prefixWord ++ tailWord_2873594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2873596 : List Nat := [2, 2, 2, 1, 4, 1, 3, 2, 5]
def baseStart_2873596 : Nat := 118140960795 + 2873596 * 2 ^ 59
def prefixEnd_2873596 : Nat := 4983230072969 + 3 ^ 40 * 2873596 * 2
def baseEnd_2873596 : Nat := 327896878852765394696573

theorem tailTrace_2873596 : CollatzResearch.WordTrace tailWord_2873596 prefixEnd_2873596 327896878852765394696573 := by
  unfold tailWord_2873596
  simp only [CollatzResearch.WordTrace]
  refine ⟨52404328248729968984812321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69872437664973291979749761 52404328248729968984812321)
  ·
    refine ⟨39303246186547476738609241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52404328248729968984812321 39303246186547476738609241)
    ·
      refine ⟨29477434639910607553956931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39303246186547476738609241 29477434639910607553956931)
      ·
        refine ⟨44216151959865911330935397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29477434639910607553956931 44216151959865911330935397)
        ·
          refine ⟨8290528492474858374550387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44216151959865911330935397 8290528492474858374550387)
          ·
            refine ⟨12435792738712287561825581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8290528492474858374550387 12435792738712287561825581)
            ·
              refine ⟨4663422277017107835684593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12435792738712287561825581 4663422277017107835684593)
              ·
                refine ⟨3497566707762830876763445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4663422277017107835684593 3497566707762830876763445)
                ·
                  refine ⟨327896878852765394696573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3497566707762830876763445 327896878852765394696573)
                  ·
                    rfl

theorem cell22_2873596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 3, 2, 5].length) (baseStart_2873596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2873596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2873596 prefixEnd_2873596 := by exact prefixLift 2873596
  have htrace : WordTrace (prefixWord ++ tailWord_2873596) baseStart_2873596 baseEnd_2873596 := by
    simpa [prefixWord, tailWord_2873596, baseEnd_2873596] using wordTrace_append hprefix tailTrace_2873596
  have hstable : (prefixWord ++ tailWord_2873596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2873596).length < 2 ^ (prefixWord ++ tailWord_2873596).sum := by decide
  have hdescent : baseEnd_2873596 < baseStart_2873596 := by decide
  rcases family_descends (prefixWord ++ tailWord_2873596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2873624 : List Nat := [2, 1, 2, 3, 1, 2, 1, 4, 6]
def baseStart_2873624 : Nat := 118140960795 + 2873624 * 2 ^ 59
def prefixEnd_2873624 : Nat := 4983230072969 + 3 ^ 40 * 2873624 * 2
def baseEnd_2873624 : Nat := 327900073843504481463211

theorem tailTrace_2873624 : CollatzResearch.WordTrace tailWord_2873624 prefixEnd_2873624 327900073843504481463211 := by
  unfold tailWord_2873624
  simp only [CollatzResearch.WordTrace]
  refine ⟨52404838870679249375821963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69873118494238999167762617 52404838870679249375821963)
  ·
    refine ⟨78607258306018874063732945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52404838870679249375821963 78607258306018874063732945)
    ·
      refine ⟨58955443729514155547799709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78607258306018874063732945 58955443729514155547799709)
      ·
        refine ⟨22108291398567808330424891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58955443729514155547799709 22108291398567808330424891)
        ·
          refine ⟨33162437097851712495637337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22108291398567808330424891 33162437097851712495637337)
          ·
            refine ⟨24871827823388784371728003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33162437097851712495637337 24871827823388784371728003)
            ·
              refine ⟨37307741735083176557592005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24871827823388784371728003 37307741735083176557592005)
              ·
                refine ⟨6995201575328095604548501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37307741735083176557592005 6995201575328095604548501)
                ·
                  refine ⟨327900073843504481463211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6995201575328095604548501 327900073843504481463211)
                  ·
                    rfl

theorem cell22_2873624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 4, 6].length) (baseStart_2873624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2873624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2873624 prefixEnd_2873624 := by exact prefixLift 2873624
  have htrace : WordTrace (prefixWord ++ tailWord_2873624) baseStart_2873624 baseEnd_2873624 := by
    simpa [prefixWord, tailWord_2873624, baseEnd_2873624] using wordTrace_append hprefix tailTrace_2873624
  have hstable : (prefixWord ++ tailWord_2873624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2873624).length < 2 ^ (prefixWord ++ tailWord_2873624).sum := by decide
  have hdescent : baseEnd_2873624 < baseStart_2873624 := by decide
  rcases family_descends (prefixWord ++ tailWord_2873624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2873656 : List Nat := [2, 1, 2, 1, 3, 1, 4, 1, 4, 3]
def baseStart_2873656 : Nat := 118140960795 + 2873656 * 2 ^ 59
def prefixEnd_2873656 : Nat := 4983230072969 + 3 ^ 40 * 2873656 * 2
def baseEnd_2873656 : Nat := 983711175784476027589535

theorem tailTrace_2873656 : CollatzResearch.WordTrace tailWord_2873656 prefixEnd_2873656 983711175784476027589535 := by
  unfold tailWord_2873656
  simp only [CollatzResearch.WordTrace]
  refine ⟨52405422438621284108404411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69873896584828378811205881 52405422438621284108404411)
  ·
    refine ⟨78608133657931926162606617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52405422438621284108404411 78608133657931926162606617)
    ·
      refine ⟨58956100243448944621954963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78608133657931926162606617 58956100243448944621954963)
      ·
        refine ⟨88434150365173416932932445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58956100243448944621954963 88434150365173416932932445)
        ·
          refine ⟨33162806386940031349849667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88434150365173416932932445 33162806386940031349849667)
          ·
            refine ⟨49744209580410047024774501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33162806386940031349849667 49744209580410047024774501)
            ·
              refine ⟨9327039296326883817145219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49744209580410047024774501 9327039296326883817145219)
              ·
                refine ⟨13990558944490325725717829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9327039296326883817145219 13990558944490325725717829)
                ·
                  refine ⟨2623229802091936073572093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13990558944490325725717829 2623229802091936073572093)
                  ·
                    refine ⟨983711175784476027589535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2623229802091936073572093 983711175784476027589535)
                    ·
                      rfl

theorem cell22_2873656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 1, 4, 3].length) (baseStart_2873656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2873656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2873656 prefixEnd_2873656 := by exact prefixLift 2873656
  have htrace : WordTrace (prefixWord ++ tailWord_2873656) baseStart_2873656 baseEnd_2873656 := by
    simpa [prefixWord, tailWord_2873656, baseEnd_2873656] using wordTrace_append hprefix tailTrace_2873656
  have hstable : (prefixWord ++ tailWord_2873656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2873656).length < 2 ^ (prefixWord ++ tailWord_2873656).sum := by decide
  have hdescent : baseEnd_2873656 < baseStart_2873656 := by decide
  rcases family_descends (prefixWord ++ tailWord_2873656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2873744 : List Nat := [2, 1, 1, 1, 1, 1, 2, 1, 4, 8]
def baseStart_2873744 : Nat := 118140960795 + 2873744 * 2 ^ 59
def prefixEnd_2873744 : Nat := 4983230072969 + 3 ^ 40 * 2873744 * 2
def baseEnd_2873744 : Nat := 983741299982873131389265

theorem tailTrace_2873744 : CollatzResearch.WordTrace tailWord_2873744 prefixEnd_2873744 983741299982873131389265 := by
  unfold tailWord_2873744
  simp only [CollatzResearch.WordTrace]
  refine ⟨52407027250461879623006143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69876036333949172830674857 52407027250461879623006143)
  ·
    refine ⟨78610540875692819434509215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52407027250461879623006143 78610540875692819434509215)
    ·
      refine ⟨117915811313539229151763823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78610540875692819434509215 117915811313539229151763823)
      ·
        refine ⟨176873716970308843727645735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117915811313539229151763823 176873716970308843727645735)
        ·
          refine ⟨265310575455463265591468603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176873716970308843727645735 265310575455463265591468603)
          ·
            refine ⟨397965863183194898387202905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 265310575455463265591468603 397965863183194898387202905)
            ·
              refine ⟨298474397387396173790402179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 397965863183194898387202905 298474397387396173790402179)
              ·
                refine ⟨447711596081094260685603269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 298474397387396173790402179 447711596081094260685603269)
                ·
                  refine ⟨83945924265205173878550613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 447711596081094260685603269 83945924265205173878550613)
                  ·
                    refine ⟨983741299982873131389265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 83945924265205173878550613 983741299982873131389265)
                    ·
                      rfl

theorem cell22_2873744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 4, 8].length) (baseStart_2873744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2873744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2873744 prefixEnd_2873744 := by exact prefixLift 2873744
  have htrace : WordTrace (prefixWord ++ tailWord_2873744) baseStart_2873744 baseEnd_2873744 := by
    simpa [prefixWord, tailWord_2873744, baseEnd_2873744] using wordTrace_append hprefix tailTrace_2873744
  have hstable : (prefixWord ++ tailWord_2873744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2873744).length < 2 ^ (prefixWord ++ tailWord_2873744).sum := by decide
  have hdescent : baseEnd_2873744 < baseStart_2873744 := by decide
  rcases family_descends (prefixWord ++ tailWord_2873744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2873752 : List Nat := [2, 1, 2, 5, 1, 2, 2, 3, 1, 3]
def baseStart_2873752 : Nat := 118140960795 + 2873752 * 2 ^ 59
def prefixEnd_2873752 : Nat := 4983230072969 + 3 ^ 40 * 2873752 * 2
def baseEnd_2873752 : Nat := 983744038546363777189241

theorem tailTrace_2873752 : CollatzResearch.WordTrace tailWord_2873752 prefixEnd_2873752 983744038546363777189241 := by
  unfold tailWord_2873752
  simp only [CollatzResearch.WordTrace]
  refine ⟨52407173142447388306151755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69876230856596517741535673 52407173142447388306151755)
  ·
    refine ⟨78610759713671082459227633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52407173142447388306151755 78610759713671082459227633)
    ·
      refine ⟨58958069785253311844420725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78610759713671082459227633 58958069785253311844420725)
      ·
        refine ⟨5527319042367497985414443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 58958069785253311844420725 5527319042367497985414443)
        ·
          refine ⟨8290978563551246978121665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5527319042367497985414443 8290978563551246978121665)
          ·
            refine ⟨6218233922663435233591249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8290978563551246978121665 6218233922663435233591249)
            ·
              refine ⟨4663675441997576425193437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6218233922663435233591249 4663675441997576425193437)
              ·
                refine ⟨1748878290749091159447539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4663675441997576425193437 1748878290749091159447539)
                ·
                  refine ⟨2623317436123636739171309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1748878290749091159447539 2623317436123636739171309)
                  ·
                    refine ⟨983744038546363777189241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2623317436123636739171309 983744038546363777189241)
                    ·
                      rfl

theorem cell22_2873752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 2, 3, 1, 3].length) (baseStart_2873752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2873752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2873752 prefixEnd_2873752 := by exact prefixLift 2873752
  have htrace : WordTrace (prefixWord ++ tailWord_2873752) baseStart_2873752 baseEnd_2873752 := by
    simpa [prefixWord, tailWord_2873752, baseEnd_2873752] using wordTrace_append hprefix tailTrace_2873752
  have hstable : (prefixWord ++ tailWord_2873752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2873752).length < 2 ^ (prefixWord ++ tailWord_2873752).sum := by decide
  have hdescent : baseEnd_2873752 < baseStart_2873752 := by decide
  rcases family_descends (prefixWord ++ tailWord_2873752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2873823 : List Nat := [1, 1, 2, 3, 3, 3, 1, 2, 2, 4]
def baseStart_2873823 : Nat := 118140960795 + 2873823 * 2 ^ 59
def prefixEnd_2873823 : Nat := 4983230072969 + 3 ^ 40 * 2873823 * 2
def baseEnd_2873823 : Nat := 983768343297343258664023

theorem tailTrace_2873823 : CollatzResearch.WordTrace tailWord_2873823 prefixEnd_2873823 983768343297343258664023 := by
  unfold tailWord_2873823
  simp only [CollatzResearch.WordTrace]
  refine ⟨104816935867637555738138123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69877957245091703825425415 104816935867637555738138123)
  ·
    refine ⟨157225403801456333607207185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104816935867637555738138123 157225403801456333607207185)
    ·
      refine ⟨117919052851092250205405389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157225403801456333607207185 117919052851092250205405389)
      ·
        refine ⟨44219644819159593827027021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117919052851092250205405389 44219644819159593827027021)
        ·
          refine ⟨16582366807184847685135133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44219644819159593827027021 16582366807184847685135133)
          ·
            refine ⟨6218387552694317881925675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16582366807184847685135133 6218387552694317881925675)
            ·
              refine ⟨9327581329041476822888513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6218387552694317881925675 9327581329041476822888513)
              ·
                refine ⟨6995685996781107617166385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9327581329041476822888513 6995685996781107617166385)
                ·
                  refine ⟨5246764497585830712874789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6995685996781107617166385 5246764497585830712874789)
                  ·
                    refine ⟨983768343297343258664023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5246764497585830712874789 983768343297343258664023)
                    ·
                      rfl

theorem cell22_2873823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 2, 2, 4].length) (baseStart_2873823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2873823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2873823 prefixEnd_2873823 := by exact prefixLift 2873823
  have htrace : WordTrace (prefixWord ++ tailWord_2873823) baseStart_2873823 baseEnd_2873823 := by
    simpa [prefixWord, tailWord_2873823, baseEnd_2873823] using wordTrace_append hprefix tailTrace_2873823
  have hstable : (prefixWord ++ tailWord_2873823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2873823).length < 2 ^ (prefixWord ++ tailWord_2873823).sum := by decide
  have hdescent : baseEnd_2873823 < baseStart_2873823 := by decide
  rcases family_descends (prefixWord ++ tailWord_2873823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2873827 : List Nat := [1, 1, 1, 6, 3, 1, 3, 2, 4]
def baseStart_2873827 : Nat := 118140960795 + 2873827 * 2 ^ 59
def prefixEnd_2873827 : Nat := 4983230072969 + 3 ^ 40 * 2873827 * 2
def baseEnd_2873827 : Nat := 327923237526362860521337

theorem tailTrace_2873827 : CollatzResearch.WordTrace tailWord_2873827 prefixEnd_2873827 327923237526362860521337 := by
  unfold tailWord_2873827
  simp only [CollatzResearch.WordTrace]
  refine ⟨104817081759623064421283735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69878054506415376280855823 104817081759623064421283735)
  ·
    refine ⟨157225622639434596631925603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104817081759623064421283735 157225622639434596631925603)
    ·
      refine ⟨235838433959151894947888405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157225622639434596631925603 235838433959151894947888405)
      ·
        refine ⟨11054926591835245075682269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 235838433959151894947888405 11054926591835245075682269)
        ·
          refine ⟨4145597471938216903380851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11054926591835245075682269 4145597471938216903380851)
          ·
            refine ⟨6218396207907325355071277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4145597471938216903380851 6218396207907325355071277)
            ·
              refine ⟨2331898577965247008151729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6218396207907325355071277 2331898577965247008151729)
              ·
                refine ⟨1748923933473935256113797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2331898577965247008151729 1748923933473935256113797)
                ·
                  refine ⟨327923237526362860521337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1748923933473935256113797 327923237526362860521337)
                  ·
                    rfl

theorem cell22_2873827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 3, 2, 4].length) (baseStart_2873827 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2873827 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2873827 prefixEnd_2873827 := by exact prefixLift 2873827
  have htrace : WordTrace (prefixWord ++ tailWord_2873827) baseStart_2873827 baseEnd_2873827 := by
    simpa [prefixWord, tailWord_2873827, baseEnd_2873827] using wordTrace_append hprefix tailTrace_2873827
  have hstable : (prefixWord ++ tailWord_2873827).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2873827).length < 2 ^ (prefixWord ++ tailWord_2873827).sum := by decide
  have hdescent : baseEnd_2873827 < baseStart_2873827 := by decide
  rcases family_descends (prefixWord ++ tailWord_2873827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2873838 : List Nat := [4, 1, 2, 1, 2, 3, 2, 7]
def baseStart_2873838 : Nat := 118140960795 + 2873838 * 2 ^ 59
def prefixEnd_2873838 : Nat := 4983230072969 + 3 ^ 40 * 2873838 * 2
def baseEnd_2873838 : Nat := 109308164233765357726553

theorem tailTrace_2873838 : CollatzResearch.WordTrace tailWord_2873838 prefixEnd_2873838 109308164233765357726553 := by
  unfold tailWord_2873838
  simp only [CollatzResearch.WordTrace]
  refine ⟨13102185370322901662491771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69878321975055475533289445 13102185370322901662491771)
  ·
    refine ⟨19653278055484352493737657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13102185370322901662491771 19653278055484352493737657)
    ·
      refine ⟨14739958541613264370303243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19653278055484352493737657 14739958541613264370303243)
      ·
        refine ⟨22109937812419896555454865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14739958541613264370303243 22109937812419896555454865)
        ·
          refine ⟨16582453359314922416591149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22109937812419896555454865 16582453359314922416591149)
          ·
            refine ⟨6218420009743095906221681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16582453359314922416591149 6218420009743095906221681)
            ·
              refine ⟨4663815007307321929666261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6218420009743095906221681 4663815007307321929666261)
              ·
                refine ⟨109308164233765357726553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4663815007307321929666261 109308164233765357726553)
                ·
                  rfl

theorem cell22_2873838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 2, 7].length) (baseStart_2873838 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2873838 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2873838 prefixEnd_2873838 := by exact prefixLift 2873838
  have htrace : WordTrace (prefixWord ++ tailWord_2873838) baseStart_2873838 baseEnd_2873838 := by
    simpa [prefixWord, tailWord_2873838, baseEnd_2873838] using wordTrace_append hprefix tailTrace_2873838
  have hstable : (prefixWord ++ tailWord_2873838).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2873838).length < 2 ^ (prefixWord ++ tailWord_2873838).sum := by decide
  have hdescent : baseEnd_2873838 < baseStart_2873838 := by decide
  rcases family_descends (prefixWord ++ tailWord_2873838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2873842 : List Nat := [3, 2, 1, 4, 2, 1, 1, 3, 2, 3]
def baseStart_2873842 : Nat := 118140960795 + 2873842 * 2 ^ 59
def prefixEnd_2873842 : Nat := 4983230072969 + 3 ^ 40 * 2873842 * 2
def baseEnd_2873842 : Nat := 983774847385633542438965

theorem tailTrace_2873842 : CollatzResearch.WordTrace tailWord_2873842 prefixEnd_2873842 983774847385633542438965 := by
  unfold tailWord_2873842
  simp only [CollatzResearch.WordTrace]
  refine ⟨26204407213642180495769945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69878419236379147988719853 26204407213642180495769945)
  ·
    refine ⟨19653305410231635371827459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26204407213642180495769945 19653305410231635371827459)
    ·
      refine ⟨29479958115347453057741189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19653305410231635371827459 29479958115347453057741189)
      ·
        refine ⟨5527492146627647448326473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29479958115347453057741189 5527492146627647448326473)
        ·
          refine ⟨4145619109970735586244855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5527492146627647448326473 4145619109970735586244855)
          ·
            refine ⟨6218428664956103379367283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4145619109970735586244855 6218428664956103379367283)
            ·
              refine ⟨9327642997434155069050925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6218428664956103379367283 9327642997434155069050925)
              ·
                refine ⟨3497866124037808150894097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9327642997434155069050925 3497866124037808150894097)
                ·
                  refine ⟨2623399593028356113170573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3497866124037808150894097 2623399593028356113170573)
                  ·
                    refine ⟨983774847385633542438965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2623399593028356113170573 983774847385633542438965)
                    ·
                      rfl

theorem cell22_2873842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 3, 2, 3].length) (baseStart_2873842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2873842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2873842 prefixEnd_2873842 := by exact prefixLift 2873842
  have htrace : WordTrace (prefixWord ++ tailWord_2873842) baseStart_2873842 baseEnd_2873842 := by
    simpa [prefixWord, tailWord_2873842, baseEnd_2873842] using wordTrace_append hprefix tailTrace_2873842
  have hstable : (prefixWord ++ tailWord_2873842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2873842).length < 2 ^ (prefixWord ++ tailWord_2873842).sum := by decide
  have hdescent : baseEnd_2873842 < baseStart_2873842 := by decide
  rcases family_descends (prefixWord ++ tailWord_2873842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2873853 : List Nat := [1, 4, 1, 1, 1, 3, 2, 1, 5, 3]
def baseStart_2873853 : Nat := 118140960795 + 2873853 * 2 ^ 59
def prefixEnd_2873853 : Nat := 4983230072969 + 3 ^ 40 * 2873853 * 2
def baseEnd_2873853 : Nat := 983778612910433180413931

theorem tailTrace_2873853 : CollatzResearch.WordTrace tailWord_2873853 prefixEnd_2873853 983778612910433180413931 := by
  unfold tailWord_2873853
  simp only [CollatzResearch.WordTrace]
  refine ⟨104818030057528870861730213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69878686705019247241153475 104818030057528870861730213)
  ·
    refine ⟨19653380635786663286574415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104818030057528870861730213 19653380635786663286574415)
    ·
      refine ⟨29480070953679994929861623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19653380635786663286574415 29480070953679994929861623)
      ·
        refine ⟨44220106430519992394792435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29480070953679994929861623 44220106430519992394792435)
        ·
          refine ⟨66330159645779988592188653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44220106430519992394792435 66330159645779988592188653)
          ·
            refine ⟨24873809867167495722070745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66330159645779988592188653 24873809867167495722070745)
            ·
              refine ⟨18655357400375621791553059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24873809867167495722070745 18655357400375621791553059)
              ·
                refine ⟨27983036100563432687329589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18655357400375621791553059 27983036100563432687329589)
                ·
                  refine ⟨2623409634427821814437149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27983036100563432687329589 2623409634427821814437149)
                  ·
                    refine ⟨983778612910433180413931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2623409634427821814437149 983778612910433180413931)
                    ·
                      rfl

theorem cell22_2873853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 1, 5, 3].length) (baseStart_2873853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2873853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2873853 prefixEnd_2873853 := by exact prefixLift 2873853
  have htrace : WordTrace (prefixWord ++ tailWord_2873853) baseStart_2873853 baseEnd_2873853 := by
    simpa [prefixWord, tailWord_2873853, baseEnd_2873853] using wordTrace_append hprefix tailTrace_2873853
  have hstable : (prefixWord ++ tailWord_2873853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2873853).length < 2 ^ (prefixWord ++ tailWord_2873853).sum := by decide
  have hdescent : baseEnd_2873853 < baseStart_2873853 := by decide
  rcases family_descends (prefixWord ++ tailWord_2873853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2873881 : List Nat := [1, 2, 1, 2, 1, 1, 2, 3, 4, 5]
def baseStart_2873881 : Nat := 118140960795 + 2873881 * 2 ^ 59
def prefixEnd_2873881 : Nat := 4983230072969 + 3 ^ 40 * 2873881 * 2
def baseEnd_2873881 : Nat := 983788197882650440713845

theorem tailTrace_2873881 : CollatzResearch.WordTrace tailWord_2873881 prefixEnd_2873881 983788197882650440713845 := by
  unfold tailWord_2873881
  simp only [CollatzResearch.WordTrace]
  refine ⟨104819051301427431643749497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69879367534284954429166331 104819051301427431643749497)
  ·
    refine ⟨78614288476070573732812123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104819051301427431643749497 78614288476070573732812123)
    ·
      refine ⟨117921432714105860599218185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78614288476070573732812123 117921432714105860599218185)
      ·
        refine ⟨88441074535579395449413639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117921432714105860599218185 88441074535579395449413639)
        ·
          refine ⟨132661611803369093174120459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88441074535579395449413639 132661611803369093174120459)
          ·
            refine ⟨198992417705053639761180689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132661611803369093174120459 198992417705053639761180689)
            ·
              refine ⟨149244313278790229820885517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 198992417705053639761180689 149244313278790229820885517)
              ·
                refine ⟨55966617479546336182832069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 149244313278790229820885517 55966617479546336182832069)
                ·
                  refine ⟨10493740777414938034281013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55966617479546336182832069 10493740777414938034281013)
                  ·
                    refine ⟨983788197882650440713845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10493740777414938034281013 983788197882650440713845)
                    ·
                      rfl

theorem cell22_2873881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 4, 5].length) (baseStart_2873881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2873881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2873881 prefixEnd_2873881 := by exact prefixLift 2873881
  have htrace : WordTrace (prefixWord ++ tailWord_2873881) baseStart_2873881 baseEnd_2873881 := by
    simpa [prefixWord, tailWord_2873881, baseEnd_2873881] using wordTrace_append hprefix tailTrace_2873881
  have hstable : (prefixWord ++ tailWord_2873881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2873881).length < 2 ^ (prefixWord ++ tailWord_2873881).sum := by decide
  have hdescent : baseEnd_2873881 < baseStart_2873881 := by decide
  rcases family_descends (prefixWord ++ tailWord_2873881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2873898 : List Nat := [3, 1, 4, 1, 1, 2, 1, 1, 1, 7]
def baseStart_2873898 : Nat := 118140960795 + 2873898 * 2 ^ 59
def prefixEnd_2873898 : Nat := 4983230072969 + 3 ^ 40 * 2873898 * 2
def baseEnd_2873898 : Nat := 983794017330068063038793

theorem tailTrace_2873898 : CollatzResearch.WordTrace tailWord_2873898 prefixEnd_2873898 983794017330068063038793 := by
  unfold tailWord_2873898
  simp only [CollatzResearch.WordTrace]
  refine ⟨26204917835591460886779587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69879780894910562364745565 26204917835591460886779587)
  ·
    refine ⟨39307376753387191330169381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26204917835591460886779587 39307376753387191330169381)
    ·
      refine ⟨7370133141260098374406759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39307376753387191330169381 7370133141260098374406759)
      ·
        refine ⟨11055199711890147561610139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7370133141260098374406759 11055199711890147561610139)
        ·
          refine ⟨16582799567835221342415209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11055199711890147561610139 16582799567835221342415209)
          ·
            refine ⟨12437099675876416006811407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16582799567835221342415209 12437099675876416006811407)
            ·
              refine ⟨18655649513814624010217111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12437099675876416006811407 18655649513814624010217111)
              ·
                refine ⟨27983474270721936015325667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18655649513814624010217111 27983474270721936015325667)
                ·
                  refine ⟨41975211406082904022988501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27983474270721936015325667 41975211406082904022988501)
                  ·
                    refine ⟨983794017330068063038793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41975211406082904022988501 983794017330068063038793)
                    ·
                      rfl

theorem cell22_2873898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_2873898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2873898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2873898 prefixEnd_2873898 := by exact prefixLift 2873898
  have htrace : WordTrace (prefixWord ++ tailWord_2873898) baseStart_2873898 baseEnd_2873898 := by
    simpa [prefixWord, tailWord_2873898, baseEnd_2873898] using wordTrace_append hprefix tailTrace_2873898
  have hstable : (prefixWord ++ tailWord_2873898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2873898).length < 2 ^ (prefixWord ++ tailWord_2873898).sum := by decide
  have hdescent : baseEnd_2873898 < baseStart_2873898 := by decide
  rcases family_descends (prefixWord ++ tailWord_2873898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2873913 : List Nat := [1, 2, 1, 5, 1, 1, 1, 3, 3, 4]
def baseStart_2873913 : Nat := 118140960795 + 2873913 * 2 ^ 59
def prefixEnd_2873913 : Nat := 4983230072969 + 3 ^ 40 * 2873913 * 2
def baseEnd_2873913 : Nat := 983799152136613023913747

theorem tailTrace_2873913 : CollatzResearch.WordTrace tailWord_2873913 prefixEnd_2873913 983799152136613023913747 := by
  unfold tailWord_2873913
  simp only [CollatzResearch.WordTrace]
  refine ⟨104820218437311501108914393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69880145624874334072609595 104820218437311501108914393)
  ·
    refine ⟨78615163827983625831685795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104820218437311501108914393 78615163827983625831685795)
    ·
      refine ⟨117922745741975438747528693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78615163827983625831685795 117922745741975438747528693)
      ·
        refine ⟨11055257413310197382580815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 117922745741975438747528693 11055257413310197382580815)
        ·
          refine ⟨16582886119965296073871223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11055257413310197382580815 16582886119965296073871223)
          ·
            refine ⟨24874329179947944110806835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16582886119965296073871223 24874329179947944110806835)
            ·
              refine ⟨37311493769921916166210253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24874329179947944110806835 37311493769921916166210253)
              ·
                refine ⟨13991810163720718562328845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37311493769921916166210253 13991810163720718562328845)
                ·
                  refine ⟨5246928811395269460873317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13991810163720718562328845 5246928811395269460873317)
                  ·
                    refine ⟨983799152136613023913747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5246928811395269460873317 983799152136613023913747)
                    ·
                      rfl

theorem cell22_2873913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 3, 3, 4].length) (baseStart_2873913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2873913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2873913 prefixEnd_2873913 := by exact prefixLift 2873913
  have htrace : WordTrace (prefixWord ++ tailWord_2873913) baseStart_2873913 baseEnd_2873913 := by
    simpa [prefixWord, tailWord_2873913, baseEnd_2873913] using wordTrace_append hprefix tailTrace_2873913
  have hstable : (prefixWord ++ tailWord_2873913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2873913).length < 2 ^ (prefixWord ++ tailWord_2873913).sum := by decide
  have hdescent : baseEnd_2873913 < baseStart_2873913 := by decide
  rcases family_descends (prefixWord ++ tailWord_2873913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2873930 : List Nat := [3, 1, 2, 1, 1, 5, 1, 3, 1, 4]
def baseStart_2873930 : Nat := 118140960795 + 2873930 * 2 ^ 59
def prefixEnd_2873930 : Nat := 4983230072969 + 3 ^ 40 * 2873930 * 2
def baseEnd_2873930 : Nat := 983804971584030646238695

theorem tailTrace_2873930 : CollatzResearch.WordTrace tailWord_2873930 prefixEnd_2873930 983804971584030646238695 := by
  unfold tailWord_2873930
  simp only [CollatzResearch.WordTrace]
  refine ⟨26205209619562478253070811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69880558985499942008188829 26205209619562478253070811)
  ·
    refine ⟨39307814429343717379606217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26205209619562478253070811 39307814429343717379606217)
    ·
      refine ⟨29480860822007788034704663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39307814429343717379606217 29480860822007788034704663)
      ·
        refine ⟨44221291233011682052056995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29480860822007788034704663 44221291233011682052056995)
        ·
          refine ⟨66331936849517523078085493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44221291233011682052056995 66331936849517523078085493)
          ·
            refine ⟨6218619079642267788570515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 66331936849517523078085493 6218619079642267788570515)
            ·
              refine ⟨9327928619463401682855773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6218619079642267788570515 9327928619463401682855773)
              ·
                refine ⟨3497973232298775631070915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9327928619463401682855773 3497973232298775631070915)
                ·
                  refine ⟨5246959848448163446606373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3497973232298775631070915 5246959848448163446606373)
                  ·
                    refine ⟨983804971584030646238695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5246959848448163446606373 983804971584030646238695)
                    ·
                      rfl

theorem cell22_2873930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 3, 1, 4].length) (baseStart_2873930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2873930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2873930 prefixEnd_2873930 := by exact prefixLift 2873930
  have htrace : WordTrace (prefixWord ++ tailWord_2873930) baseStart_2873930 baseEnd_2873930 := by
    simpa [prefixWord, tailWord_2873930, baseEnd_2873930] using wordTrace_append hprefix tailTrace_2873930
  have hstable : (prefixWord ++ tailWord_2873930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2873930).length < 2 ^ (prefixWord ++ tailWord_2873930).sum := by decide
  have hdescent : baseEnd_2873930 < baseStart_2873930 := by decide
  rcases family_descends (prefixWord ++ tailWord_2873930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2874052 : List Nat := [2, 3, 3, 1, 1, 3, 2, 2, 5]
def baseStart_2874052 : Nat := 118140960795 + 2874052 * 2 ^ 59
def prefixEnd_2874052 : Nat := 4983230072969 + 3 ^ 40 * 2874052 * 2
def baseEnd_2874052 : Nat := 327948911559087664896107

theorem tailTrace_2874052 : CollatzResearch.WordTrace tailWord_2874052 prefixEnd_2874052 327948911559087664896107 := by
  unfold tailWord_2874052
  simp only [CollatzResearch.WordTrace]
  refine ⟨52412644091903963924112205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69883525455871951898816273 52412644091903963924112205)
  ·
    refine ⟨19654741534463986471542077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52412644091903963924112205 19654741534463986471542077)
    ·
      refine ⟨7370528075423994926828279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19654741534463986471542077 7370528075423994926828279)
      ·
        refine ⟨11055792113135992390242419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7370528075423994926828279 11055792113135992390242419)
        ·
          refine ⟨16583688169703988585363629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11055792113135992390242419 16583688169703988585363629)
          ·
            refine ⟨6218883063638995719511361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16583688169703988585363629 6218883063638995719511361)
            ·
              refine ⟨4664162297729246789633521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6218883063638995719511361 4664162297729246789633521)
              ·
                refine ⟨3498121723296935092225141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4664162297729246789633521 3498121723296935092225141)
                ·
                  refine ⟨327948911559087664896107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3498121723296935092225141 327948911559087664896107)
                  ·
                    rfl

theorem cell22_2874052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 2, 2, 5].length) (baseStart_2874052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2874052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2874052 prefixEnd_2874052 := by exact prefixLift 2874052
  have htrace : WordTrace (prefixWord ++ tailWord_2874052) baseStart_2874052 baseEnd_2874052 := by
    simpa [prefixWord, tailWord_2874052, baseEnd_2874052] using wordTrace_append hprefix tailTrace_2874052
  have hstable : (prefixWord ++ tailWord_2874052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2874052).length < 2 ^ (prefixWord ++ tailWord_2874052).sum := by decide
  have hdescent : baseEnd_2874052 < baseStart_2874052 := by decide
  rcases family_descends (prefixWord ++ tailWord_2874052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2874056 : List Nat := [2, 1, 3, 1, 2, 5, 2, 2, 1, 3]
def baseStart_2874056 : Nat := 118140960795 + 2874056 * 2 ^ 59
def prefixEnd_2874056 : Nat := 4983230072969 + 3 ^ 40 * 2874056 * 2
def baseEnd_2874056 : Nat := 983848103959008317588309

theorem tailTrace_2874056 : CollatzResearch.WordTrace tailWord_2874056 prefixEnd_2874056 983848103959008317588309 := by
  unfold tailWord_2874056
  simp only [CollatzResearch.WordTrace]
  refine ⟨52412717037896718265685011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69883622717195624354246681 52412717037896718265685011)
  ·
    refine ⟨78619075556845077398527517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52412717037896718265685011 78619075556845077398527517)
    ·
      refine ⟨29482153333816904024447819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78619075556845077398527517 29482153333816904024447819)
      ·
        refine ⟨44223230000725356036671729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29482153333816904024447819 44223230000725356036671729)
        ·
          refine ⟨33167422500544017027503797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44223230000725356036671729 33167422500544017027503797)
          ·
            refine ⟨3109445859426001596328481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 33167422500544017027503797 3109445859426001596328481)
            ·
              refine ⟨2332084394569501197246361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3109445859426001596328481 2332084394569501197246361)
              ·
                refine ⟨1749063295927125897934771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2332084394569501197246361 1749063295927125897934771)
                ·
                  refine ⟨2623594943890688846902157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1749063295927125897934771 2623594943890688846902157)
                  ·
                    refine ⟨983848103959008317588309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2623594943890688846902157 983848103959008317588309)
                    ·
                      rfl

theorem cell22_2874056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 2, 2, 1, 3].length) (baseStart_2874056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2874056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2874056 prefixEnd_2874056 := by exact prefixLift 2874056
  have htrace : WordTrace (prefixWord ++ tailWord_2874056) baseStart_2874056 baseEnd_2874056 := by
    simpa [prefixWord, tailWord_2874056, baseEnd_2874056] using wordTrace_append hprefix tailTrace_2874056
  have hstable : (prefixWord ++ tailWord_2874056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2874056).length < 2 ^ (prefixWord ++ tailWord_2874056).sum := by decide
  have hdescent : baseEnd_2874056 < baseStart_2874056 := by decide
  rcases family_descends (prefixWord ++ tailWord_2874056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2874095 : List Nat := [1, 1, 2, 1, 5, 2, 2, 2, 1, 5]
def baseStart_2874095 : Nat := 118140960795 + 2874095 * 2 ^ 59
def prefixEnd_2874095 : Nat := 4983230072969 + 3 ^ 40 * 2874095 * 2
def baseEnd_2874095 : Nat := 983861454456025215863189

theorem tailTrace_2874095 : CollatzResearch.WordTrace tailWord_2874095 prefixEnd_2874095 983861454456025215863189 := by
  unfold tailWord_2874095
  simp only [CollatzResearch.WordTrace]
  refine ⟨104826856522652146192039739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69884571015101430794693159 104826856522652146192039739)
  ·
    refine ⟨157240284783978219288059609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104826856522652146192039739 157240284783978219288059609)
    ·
      refine ⟨117930213587983664466044707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157240284783978219288059609 117930213587983664466044707)
      ·
        refine ⟨176895320381975496699067061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117930213587983664466044707 176895320381975496699067061)
        ·
          refine ⟨16583936285810202815537537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 176895320381975496699067061 16583936285810202815537537)
          ·
            refine ⟨12437952214357652111653153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16583936285810202815537537 12437952214357652111653153)
            ·
              refine ⟨9328464160768239083739865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12437952214357652111653153 9328464160768239083739865)
              ·
                refine ⟨6996348120576179312804899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9328464160768239083739865 6996348120576179312804899)
                ·
                  refine ⟨10494522180864268969207349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6996348120576179312804899 10494522180864268969207349)
                  ·
                    refine ⟨983861454456025215863189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10494522180864268969207349 983861454456025215863189)
                    ·
                      rfl

theorem cell22_2874095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 2, 1, 5].length) (baseStart_2874095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2874095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2874095 prefixEnd_2874095 := by exact prefixLift 2874095
  have htrace : WordTrace (prefixWord ++ tailWord_2874095) baseStart_2874095 baseEnd_2874095 := by
    simpa [prefixWord, tailWord_2874095, baseEnd_2874095] using wordTrace_append hprefix tailTrace_2874095
  have hstable : (prefixWord ++ tailWord_2874095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2874095).length < 2 ^ (prefixWord ++ tailWord_2874095).sum := by decide
  have hdescent : baseEnd_2874095 < baseStart_2874095 := by decide
  rcases family_descends (prefixWord ++ tailWord_2874095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2874097 : List Nat := [1, 2, 2, 2, 2, 2, 4, 3, 4]
def baseStart_2874097 : Nat := 118140960795 + 2874097 * 2 ^ 59
def prefixEnd_2874097 : Nat := 4983230072969 + 3 ^ 40 * 2874097 * 2
def baseEnd_2874097 : Nat := 327954046365632625771061

theorem tailTrace_2874097 : CollatzResearch.WordTrace tailWord_2874097 prefixEnd_2874097 327954046365632625771061 := by
  unfold tailWord_2874097
  simp only [CollatzResearch.WordTrace]
  refine ⟨104826929468644900533612545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69884619645763267022408363 104826929468644900533612545)
  ·
    refine ⟨78620197101483675400209409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104826929468644900533612545 78620197101483675400209409)
    ·
      refine ⟨58965147826112756550157057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78620197101483675400209409 58965147826112756550157057)
      ·
        refine ⟨44223860869584567412617793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58965147826112756550157057 44223860869584567412617793)
        ·
          refine ⟨33167895652188425559463345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44223860869584567412617793 33167895652188425559463345)
          ·
            refine ⟨24875921739141319169597509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33167895652188425559463345 24875921739141319169597509)
            ·
              refine ⟨4664235326088997344299533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24875921739141319169597509 4664235326088997344299533)
              ·
                refine ⟨1749088247283374004112325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4664235326088997344299533 1749088247283374004112325)
                ·
                  refine ⟨327954046365632625771061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1749088247283374004112325 327954046365632625771061)
                  ·
                    rfl

theorem cell22_2874097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 4, 3, 4].length) (baseStart_2874097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2874097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2874097 prefixEnd_2874097 := by exact prefixLift 2874097
  have htrace : WordTrace (prefixWord ++ tailWord_2874097) baseStart_2874097 baseEnd_2874097 := by
    simpa [prefixWord, tailWord_2874097, baseEnd_2874097] using wordTrace_append hprefix tailTrace_2874097
  have hstable : (prefixWord ++ tailWord_2874097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2874097).length < 2 ^ (prefixWord ++ tailWord_2874097).sum := by decide
  have hdescent : baseEnd_2874097 < baseStart_2874097 := by decide
  rcases family_descends (prefixWord ++ tailWord_2874097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2874114 : List Nat := [3, 4, 1, 1, 1, 2, 2, 4, 4]
def baseStart_2874114 : Nat := 118140960795 + 2874114 * 2 ^ 59
def prefixEnd_2874114 : Nat := 4983230072969 + 3 ^ 40 * 2874114 * 2
def baseEnd_2874114 : Nat := 327955986181438499879377

theorem tailTrace_2874114 : CollatzResearch.WordTrace tailWord_2874114 prefixEnd_2874114 327955986181438499879377 := by
  unfold tailWord_2874114
  simp only [CollatzResearch.WordTrace]
  refine ⟨26206887377395828109245349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69885033006388874957987597 26206887377395828109245349)
  ·
    refine ⟨4913791383261717770483503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26206887377395828109245349 4913791383261717770483503)
    ·
      refine ⟨7370687074892576655725255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4913791383261717770483503 7370687074892576655725255)
      ·
        refine ⟨11056030612338864983587883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7370687074892576655725255 11056030612338864983587883)
        ·
          refine ⟨16584045918508297475381825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11056030612338864983587883 16584045918508297475381825)
          ·
            refine ⟨12438034438881223106536369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16584045918508297475381825 12438034438881223106536369)
            ·
              refine ⟨9328525829160917329902277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12438034438881223106536369 9328525829160917329902277)
              ·
                refine ⟨1749098592967671999356677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9328525829160917329902277 1749098592967671999356677)
                ·
                  refine ⟨327955986181438499879377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1749098592967671999356677 327955986181438499879377)
                  ·
                    rfl

theorem cell22_2874114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 4, 4].length) (baseStart_2874114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2874114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2874114 prefixEnd_2874114 := by exact prefixLift 2874114
  have htrace : WordTrace (prefixWord ++ tailWord_2874114) baseStart_2874114 baseEnd_2874114 := by
    simpa [prefixWord, tailWord_2874114, baseEnd_2874114] using wordTrace_append hprefix tailTrace_2874114
  have hstable : (prefixWord ++ tailWord_2874114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2874114).length < 2 ^ (prefixWord ++ tailWord_2874114).sum := by decide
  have hdescent : baseEnd_2874114 < baseStart_2874114 := by decide
  rcases family_descends (prefixWord ++ tailWord_2874114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2874180 : List Nat := [2, 3, 4, 2, 1, 2, 2, 1, 2, 3]
def baseStart_2874180 : Nat := 118140960795 + 2874180 * 2 ^ 59
def prefixEnd_2874180 : Nat := 4983230072969 + 3 ^ 40 * 2874180 * 2
def baseEnd_2874180 : Nat := 983890551693113327487929

theorem tailTrace_2874180 : CollatzResearch.WordTrace tailWord_2874180 prefixEnd_2874180 983890551693113327487929 := by
  unfold tailWord_2874180
  simp only [CollatzResearch.WordTrace]
  refine ⟨52414978363672102854441997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69886637818229470472589329 52414978363672102854441997)
  ·
    refine ⟨19655616886377038570415749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52414978363672102854441997 19655616886377038570415749)
    ·
      refine ⟨3685428166195694731952953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19655616886377038570415749 3685428166195694731952953)
      ·
        refine ⟨2764071124646771048964715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3685428166195694731952953 2764071124646771048964715)
        ·
          refine ⟨4146106686970156573447073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2764071124646771048964715 4146106686970156573447073)
          ·
            refine ⟨3109580015227617430085305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4146106686970156573447073 3109580015227617430085305)
            ·
              refine ⟨2332185011420713072563979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3109580015227617430085305 2332185011420713072563979)
              ·
                refine ⟨3498277517131069608845969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2332185011420713072563979 3498277517131069608845969)
                ·
                  refine ⟨2623708137848302206634477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3498277517131069608845969 2623708137848302206634477)
                  ·
                    refine ⟨983890551693113327487929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2623708137848302206634477 983890551693113327487929)
                    ·
                      rfl

theorem cell22_2874180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_2874180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2874180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2874180 prefixEnd_2874180 := by exact prefixLift 2874180
  have htrace : WordTrace (prefixWord ++ tailWord_2874180) baseStart_2874180 baseEnd_2874180 := by
    simpa [prefixWord, tailWord_2874180, baseEnd_2874180] using wordTrace_append hprefix tailTrace_2874180
  have hstable : (prefixWord ++ tailWord_2874180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2874180).length < 2 ^ (prefixWord ++ tailWord_2874180).sum := by decide
  have hdescent : baseEnd_2874180 < baseStart_2874180 := by decide
  rcases family_descends (prefixWord ++ tailWord_2874180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2874247 : List Nat := [1, 1, 4, 2, 3, 1, 1, 3, 1, 5]
def baseStart_2874247 : Nat := 118140960795 + 2874247 * 2 ^ 59
def prefixEnd_2874247 : Nat := 4983230072969 + 3 ^ 40 * 2874247 * 2
def baseEnd_2874247 : Nat := 983913487162347486062723

theorem tailTrace_2874247 : CollatzResearch.WordTrace tailWord_2874247 prefixEnd_2874247 983913487162347486062723 := by
  unfold tailWord_2874247
  simp only [CollatzResearch.WordTrace]
  refine ⟨104832400418101476151572995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69888266945400984101048663 104832400418101476151572995)
  ·
    refine ⟨157248600627152214227359493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104832400418101476151572995 157248600627152214227359493)
    ·
      refine ⟨29484112617591040167629905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 157248600627152214227359493 29484112617591040167629905)
      ·
        refine ⟨22113084463193280125722429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29484112617591040167629905 22113084463193280125722429)
        ·
          refine ⟨8292406673697480047145911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22113084463193280125722429 8292406673697480047145911)
          ·
            refine ⟨12438610010546220070718867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8292406673697480047145911 12438610010546220070718867)
            ·
              refine ⟨18657915015819330106078301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12438610010546220070718867 18657915015819330106078301)
              ·
                refine ⟨6996718130932248789779363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18657915015819330106078301 6996718130932248789779363)
                ·
                  refine ⟨10495077196398373184669045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6996718130932248789779363 10495077196398373184669045)
                  ·
                    refine ⟨983913487162347486062723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10495077196398373184669045 983913487162347486062723)
                    ·
                      rfl

theorem cell22_2874247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 3, 1, 5].length) (baseStart_2874247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2874247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2874247 prefixEnd_2874247 := by exact prefixLift 2874247
  have htrace : WordTrace (prefixWord ++ tailWord_2874247) baseStart_2874247 baseEnd_2874247 := by
    simpa [prefixWord, tailWord_2874247, baseEnd_2874247] using wordTrace_append hprefix tailTrace_2874247
  have hstable : (prefixWord ++ tailWord_2874247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2874247).length < 2 ^ (prefixWord ++ tailWord_2874247).sum := by decide
  have hdescent : baseEnd_2874247 < baseStart_2874247 := by decide
  rcases family_descends (prefixWord ++ tailWord_2874247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2874266 : List Nat := [3, 1, 1, 4, 3, 1, 2, 3, 4]
def baseStart_2874266 : Nat := 118140960795 + 2874266 * 2 ^ 59
def prefixEnd_2874266 : Nat := 4983230072969 + 3 ^ 40 * 2874266 * 2
def baseEnd_2874266 : Nat := 327973330416879256612555

theorem tailTrace_2874266 : CollatzResearch.WordTrace tailWord_2874266 prefixEnd_2874266 327973330416879256612555 := by
  unfold tailWord_2874266
  simp only [CollatzResearch.WordTrace]
  refine ⟨26208273351258160599128663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69888728936688428264343101 26208273351258160599128663)
  ·
    refine ⟨39312410026887240898692995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26208273351258160599128663 39312410026887240898692995)
    ·
      refine ⟨58968615040330861348039493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39312410026887240898692995 58968615040330861348039493)
      ·
        refine ⟨11056615320062036502757405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58968615040330861348039493 11056615320062036502757405)
        ·
          refine ⟨4146230745023263688534027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11056615320062036502757405 4146230745023263688534027)
          ·
            refine ⟨6219346117534895532801041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4146230745023263688534027 6219346117534895532801041)
            ·
              refine ⟨4664509588151171649600781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6219346117534895532801041 4664509588151171649600781)
              ·
                refine ⟨1749191095556689368600293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4664509588151171649600781 1749191095556689368600293)
                ·
                  refine ⟨327973330416879256612555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1749191095556689368600293 327973330416879256612555)
                  ·
                    rfl

theorem cell22_2874266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 2, 3, 4].length) (baseStart_2874266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2874266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2874266 prefixEnd_2874266 := by exact prefixLift 2874266
  have htrace : WordTrace (prefixWord ++ tailWord_2874266) baseStart_2874266 baseEnd_2874266 := by
    simpa [prefixWord, tailWord_2874266, baseEnd_2874266] using wordTrace_append hprefix tailTrace_2874266
  have hstable : (prefixWord ++ tailWord_2874266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2874266).length < 2 ^ (prefixWord ++ tailWord_2874266).sum := by decide
  have hdescent : baseEnd_2874266 < baseStart_2874266 := by decide
  rcases family_descends (prefixWord ++ tailWord_2874266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2874268 : List Nat := [2, 2, 3, 3, 2, 2, 2, 1, 1, 4]
def baseStart_2874268 : Nat := 118140960795 + 2874268 * 2 ^ 59
def prefixEnd_2874268 : Nat := 4983230072969 + 3 ^ 40 * 2874268 * 2
def baseEnd_2874268 : Nat := 983920675891510431287659

theorem tailTrace_2874268 : CollatzResearch.WordTrace tailWord_2874268 prefixEnd_2874268 983920675891510431287659 := by
  unfold tailWord_2874268
  simp only [CollatzResearch.WordTrace]
  refine ⟨52416583175512698369043729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69888777567350264492058305 52416583175512698369043729)
  ·
    refine ⟨39312437381634523776782797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52416583175512698369043729 39312437381634523776782797)
    ·
      refine ⟨14742164018112946416293549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39312437381634523776782797 14742164018112946416293549)
      ·
        refine ⟨5528311506792354906110081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14742164018112946416293549 5528311506792354906110081)
        ·
          refine ⟨4146233630094266179582561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5528311506792354906110081 4146233630094266179582561)
          ·
            refine ⟨3109675222570699634686921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4146233630094266179582561 3109675222570699634686921)
            ·
              refine ⟨2332256416928024726015191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3109675222570699634686921 2332256416928024726015191)
              ·
                refine ⟨3498384625392037089022787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2332256416928024726015191 3498384625392037089022787)
                ·
                  refine ⟨5247576938088055633534181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3498384625392037089022787 5247576938088055633534181)
                  ·
                    refine ⟨983920675891510431287659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5247576938088055633534181 983920675891510431287659)
                    ·
                      rfl

theorem cell22_2874268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 2, 1, 1, 4].length) (baseStart_2874268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2874268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2874268 prefixEnd_2874268 := by exact prefixLift 2874268
  have htrace : WordTrace (prefixWord ++ tailWord_2874268) baseStart_2874268 baseEnd_2874268 := by
    simpa [prefixWord, tailWord_2874268, baseEnd_2874268] using wordTrace_append hprefix tailTrace_2874268
  have hstable : (prefixWord ++ tailWord_2874268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2874268).length < 2 ^ (prefixWord ++ tailWord_2874268).sum := by decide
  have hdescent : baseEnd_2874268 < baseStart_2874268 := by decide
  rcases family_descends (prefixWord ++ tailWord_2874268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2874317 : List Nat := [1, 6, 3, 1, 1, 2, 1, 3, 4]
def baseStart_2874317 : Nat := 118140960795 + 2874317 * 2 ^ 59
def prefixEnd_2874317 : Nat := 4983230072969 + 3 ^ 40 * 2874317 * 2
def baseEnd_2874317 : Nat := 327979149864296878937503

theorem tailTrace_2874317 : CollatzResearch.WordTrace tailWord_2874317 prefixEnd_2874317 327979149864296878937503 := by
  unfold tailWord_2874317
  simp only [CollatzResearch.WordTrace]
  refine ⟨104834953527847878106621205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69889969018565252071080803 104834953527847878106621205)
  ·
    refine ⟨4914138446617869286247869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 104834953527847878106621205 4914138446617869286247869)
    ·
      refine ⟨1842801917481700982342951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4914138446617869286247869 1842801917481700982342951)
      ·
        refine ⟨2764202876222551473514427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1842801917481700982342951 2764202876222551473514427)
        ·
          refine ⟨4146304314333827210271641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2764202876222551473514427 4146304314333827210271641)
          ·
            refine ⟨3109728235750370407703731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4146304314333827210271641 3109728235750370407703731)
            ·
              refine ⟨4664592353625555611555597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3109728235750370407703731 4664592353625555611555597)
              ·
                refine ⟨1749222132609583354333349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4664592353625555611555597 1749222132609583354333349)
                ·
                  refine ⟨327979149864296878937503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1749222132609583354333349 327979149864296878937503)
                  ·
                    rfl

theorem cell22_2874317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 1, 3, 4].length) (baseStart_2874317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2874317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2874317 prefixEnd_2874317 := by exact prefixLift 2874317
  have htrace : WordTrace (prefixWord ++ tailWord_2874317) baseStart_2874317 baseEnd_2874317 := by
    simpa [prefixWord, tailWord_2874317, baseEnd_2874317] using wordTrace_append hprefix tailTrace_2874317
  have hstable : (prefixWord ++ tailWord_2874317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2874317).length < 2 ^ (prefixWord ++ tailWord_2874317).sum := by decide
  have hdescent : baseEnd_2874317 < baseStart_2874317 := by decide
  rcases family_descends (prefixWord ++ tailWord_2874317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2874352 : List Nat := [2, 1, 1, 1, 3, 2, 1, 4, 3, 4]
def baseStart_2874352 : Nat := 118140960795 + 2874352 * 2 ^ 59
def prefixEnd_2874352 : Nat := 4983230072969 + 3 ^ 40 * 2874352 * 2
def baseEnd_2874352 : Nat := 983949430808162212187401

theorem tailTrace_2874352 : CollatzResearch.WordTrace tailWord_2874352 prefixEnd_2874352 983949430808162212187401 := by
  unfold tailWord_2874352
  simp only [CollatzResearch.WordTrace]
  refine ⟨52418115041360539542072655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69890820055147386056096873 52418115041360539542072655)
  ·
    refine ⟨78627172562040809313108983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52418115041360539542072655 78627172562040809313108983)
    ·
      refine ⟨117940758843061213969663475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78627172562040809313108983 117940758843061213969663475)
      ·
        refine ⟨176911138264591820954495213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117940758843061213969663475 176911138264591820954495213)
        ·
          refine ⟨66341676849221932857935705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 176911138264591820954495213 66341676849221932857935705)
          ·
            refine ⟨49756257636916449643451779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66341676849221932857935705 49756257636916449643451779)
            ·
              refine ⟨74634386455374674465177669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49756257636916449643451779 74634386455374674465177669)
              ·
                refine ⟨13993947460382751462220813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74634386455374674465177669 13993947460382751462220813)
                ·
                  refine ⟨5247730297643531798332805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13993947460382751462220813 5247730297643531798332805)
                  ·
                    refine ⟨983949430808162212187401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5247730297643531798332805 983949430808162212187401)
                    ·
                      rfl

theorem cell22_2874352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 4, 3, 4].length) (baseStart_2874352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2874352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2874352 prefixEnd_2874352 := by exact prefixLift 2874352
  have htrace : WordTrace (prefixWord ++ tailWord_2874352) baseStart_2874352 baseEnd_2874352 := by
    simpa [prefixWord, tailWord_2874352, baseEnd_2874352] using wordTrace_append hprefix tailTrace_2874352
  have hstable : (prefixWord ++ tailWord_2874352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2874352).length < 2 ^ (prefixWord ++ tailWord_2874352).sum := by decide
  have hdescent : baseEnd_2874352 < baseStart_2874352 := by decide
  rcases family_descends (prefixWord ++ tailWord_2874352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
